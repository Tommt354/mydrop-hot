import asyncio
import logging
import os
import base64
import json
import aiohttp
import time
import hashlib
import io
import asyncpg
from difflib import SequenceMatcher
from aiogram import Bot, Dispatcher, types, F
from aiogram.filters import Command, StateFilter
from aiogram.fsm.context import FSMContext
from aiogram.fsm.state import State, StatesGroup
from aiogram.fsm.storage.memory import MemoryStorage
from aiogram.types import InlineKeyboardMarkup, InlineKeyboardButton
from dotenv import load_dotenv

load_dotenv()

TELEGRAM_TOKEN = os.getenv("TELEGRAM_TOKEN")
MYDROP_API_KEY = os.getenv("MYDROP_API_KEY", "3e6dc872be67d3a1afe60c4ae59e7311ff8e8f81")
GEMINI_API_KEY = os.getenv("GEMINI_API_KEY")
DATABASE_URL   = os.getenv("DATABASE_URL")

NP_API_KEY = os.getenv("NP_API_KEY", "195c198ccc7069d0c066e5feab6a0925")
NP_API_URL = "https://api.novaposhta.ua/v2.0/json/"
MYDROP_BASE    = "https://backend.mydrop.com.ua/vendor/api"
MYDROP_HEADERS = {"X-API-KEY": MYDROP_API_KEY, "Content-Type": "application/json"}
GEMINI_MODEL   = "gemini-2.5-flash"
GEMINI_URL     = f"https://generativelanguage.googleapis.com/v1beta/models/{GEMINI_MODEL}:generateContent"

logging.basicConfig(level=logging.INFO, format="%(asctime)s | %(levelname)s | %(message)s")
log = logging.getLogger(__name__)

bot = Bot(token=TELEGRAM_TOKEN)
dp  = Dispatcher(storage=MemoryStorage())

_api_cache: dict = {"products": None, "ts": 0}
_ds_cache: dict  = {"list": None, "ts": 0}
_photo_catalog: list = []

DB_POOL = None
_dossier_cache: dict = {}

MAX_RESULTS  = 8    # максимум варіантів для менеджера
MIN_SCORE    = 8.0  # мінімальний поріг збігу
SHOW_ALL_THRESHOLD = 5.0  # різниця від топу щоб показати варіант


# ══════════════════════════════════════════════
# Nova Poshta API
# ══════════════════════════════════════════════
async def np_search_city(query: str) -> list:
    try:
        async with aiohttp.ClientSession() as s:
            async with s.post(NP_API_URL, json={
                "apiKey": NP_API_KEY,
                "modelName": "Address",
                "calledMethod": "searchSettlements",
                "methodProperties": {"CityName": query, "Limit": 7, "Page": 1}
            }, timeout=aiohttp.ClientTimeout(total=10)) as r:
                data = await r.json()
                items = (data.get("data") or [{}])[0].get("Addresses") or []
                result = []
                for i in items:
                    city_ref = i.get("DeliveryCity") or i.get("Ref", "")
                    result.append({
                        "name":       i.get("Present", ""),      # повна назва для показу
                        "short_name": i.get("MainDescription", i.get("Present", "").split(",")[0].strip()),
                        "ref":        i.get("Ref", ""),
                        "city_ref":   city_ref,
                    })
                return result
    except Exception as e:
        log.error(f"np_search_city: {e}")
        return []


async def np_search_warehouse(city_ref: str, warehouse_num: str = "") -> list:
    """
    Завантажує ВСІ відділення міста (до 150), фільтрує локально.
    warehouse_num — номер відділення для пошуку збігу (опціонально).
    """
    try:
        all_items = []
        for page in range(1, 4):  # максимум 3 сторінки × 50 = 150 відділень
            async with aiohttp.ClientSession() as s:
                async with s.post(NP_API_URL, json={
                    "apiKey": NP_API_KEY,
                    "modelName": "Address",
                    "calledMethod": "getWarehouses",
                    "methodProperties": {"CityRef": city_ref, "Limit": 50, "Page": page}
                }, timeout=aiohttp.ClientTimeout(total=10)) as r:
                    data   = await r.json()
                    items  = data.get("data") or []
                    all_items.extend(items)
                    if len(items) < 50:
                        break  # остання сторінка

        result = []
        for i in all_items:
            ref  = i.get("Ref") or i.get("SiteKey") or ""  # Ref може бути порожнім — fallback до SiteKey
            desc = i.get("Description", "")
            num  = i.get("Number", "")
            # Нормалізуємо номер: беремо тільки цифри якщо Number не просте число
            num_digits = "".join(filter(str.isdigit, str(num))) if num else ""
            result.append({"name": desc, "ref": ref, "number": num, "num_digits": num_digits})

        if not warehouse_num:
            return result

        # Фільтрація локально по номеру: шукаємо в Number АБО в Description
        num_clean = warehouse_num.strip().lstrip("0") or warehouse_num.strip()
        exact   = [w for w in result if w["num_digits"] == num_clean
                   or w["number"] == warehouse_num
                   or f"№{num_clean}" in w["name"]
                   or f"#{num_clean}" in w["name"]
                   or (f" {num_clean} " in f" {w['name']} ")]
        return exact if exact else result  # якщо не знайшли — повертаємо всі

    except Exception as e:
        log.error(f"np_search_warehouse: {e}")
        return []


# ══════════════════════════════════════════════
# Сезонність з назви
# ══════════════════════════════════════════════
SEASON_KEYWORDS = {
    "фліс":       "фліс",
    "fleece":     "фліс",
    "зима":       "зима",
    "winter":     "зима",
    "утеплен":    "зима",
    "демісезон":  "демісезон",
    "demi":       "демісезон",
    "весна":      "демісезон",
    "осінь":      "демісезон",
    "осін":       "демісезон",
    "двунитка":   "двунитка",
    "двонитка":   "двунитка",
    "літо":       "літо",
    "summer":     "літо",
    "літн":       "літо",
}

def extract_season(name: str) -> str:
    name_lower = name.lower()
    for kw, season in SEASON_KEYWORDS.items():
        if kw in name_lower:
            return season
    return ""


# ══════════════════════════════════════════════
# База даних
# ══════════════════════════════════════════════
async def init_db():
    global DB_POOL
    if not DATABASE_URL:
        log.warning("DATABASE_URL не задано!")
        return
    DB_POOL = await asyncpg.create_pool(
        DATABASE_URL,
        min_size=1, max_size=10,
        command_timeout=30,
        max_inactive_connection_lifetime=60,  # закривати мертві з'єднання через 60с
    )
    async with DB_POOL.acquire() as conn:
        await conn.execute("""
            CREATE TABLE IF NOT EXISTS dossiers (
                sku TEXT PRIMARY KEY, product_id INTEGER, name TEXT,
                dossier JSONB NOT NULL, photo_url TEXT DEFAULT '',
                created_at TIMESTAMP DEFAULT NOW(), updated_at TIMESTAMP DEFAULT NOW()
            );
            CREATE TABLE IF NOT EXISTS learned (
                photo_hash TEXT PRIMARY KEY, product JSONB NOT NULL,
                created_at TIMESTAMP DEFAULT NOW()
            );
        """)
    log.info("DB OK")


async def _reconnect_db():
    """Пробує перестворити пул якщо мережа тимчасово впала."""
    global DB_POOL
    if not DATABASE_URL:
        return False
    for attempt in range(1, 6):
        try:
            log.warning(f"DB reconnect спроба {attempt}/5...")
            if DB_POOL:
                try:
                    await DB_POOL.close()
                except Exception:
                    pass
            DB_POOL = await asyncio.wait_for(
                asyncpg.create_pool(
                    DATABASE_URL,
                    min_size=1, max_size=10,
                    command_timeout=30,
                    max_inactive_connection_lifetime=60,
                ),
                timeout=15
            )
            log.info("DB reconnect успішно!")
            return True
        except Exception as e:
            log.error(f"DB reconnect {attempt}/5 помилка: {e}")
            await asyncio.sleep(5 * attempt)
    return False


async def _db_execute(coro_factory):
    """Виконує DB-запит, при помилці мережі — один reconnect і retry."""
    global DB_POOL
    if not DB_POOL:
        return None
    try:
        return await coro_factory(DB_POOL)
    except (OSError, asyncpg.TooManyConnectionsError,
            asyncpg.PostgresConnectionError, asyncpg.InterfaceError) as e:
        log.error(f"DB помилка з'єднання: {e} — спробую reconnect")
        if await _reconnect_db():
            try:
                return await coro_factory(DB_POOL)
            except Exception as e2:
                log.error(f"DB retry помилка: {e2}")
        return None
    except Exception as e:
        log.error(f"DB помилка: {e}")
        return None


async def db_save_learned(photo_hash: str, product: dict):
    product_json = json.dumps(product, ensure_ascii=False)

    async def _run(pool):
        async with pool.acquire() as conn:
            await conn.execute(
                "INSERT INTO learned (photo_hash, product) VALUES ($1, $2) "
                "ON CONFLICT (photo_hash) DO UPDATE SET product = EXCLUDED.product",
                photo_hash, product_json
            )
        return True

    await _db_execute(_run)


async def db_get_learned(photo_hash: str):
    async def _run(pool):
        async with pool.acquire() as conn:
            row = await conn.fetchrow(
                "SELECT product FROM learned WHERE photo_hash=$1", photo_hash
            )
            return json.loads(row["product"]) if row else None

    return await _db_execute(_run)


async def load_dossiers_cache():
    global _dossier_cache

    async def _run(pool):
        async with pool.acquire() as conn:
            rows = await conn.fetch("SELECT sku, dossier FROM dossiers")
            return {r["sku"]: json.loads(r["dossier"]) for r in rows}

    result = await _db_execute(_run)
    if result is not None:
        _dossier_cache = result
        log.info(f"Кеш досьє: {len(_dossier_cache)} товарів")
    else:
        log.warning("load_dossiers_cache: не вдалось завантажити — DB недоступна")


# ══════════════════════════════════════════════
# Утиліти
# ══════════════════════════════════════════════
def get_photo_hash(data: bytes) -> str:
    return hashlib.md5(data).hexdigest()

def get_mime(data: bytes) -> str:
    if data[:8] == b'\x89PNG\r\n\x1a\n': return "image/png"
    if data[:6] in (b'GIF87a', b'GIF89a'): return "image/gif"
    if data[:4] == b'RIFF' and data[8:12] == b'WEBP': return "image/webp"
    return "image/jpeg"

def build_catalog_from_xlsx(xlsx_bytes: bytes) -> list:
    import openpyxl
    wb = openpyxl.load_workbook(io.BytesIO(xlsx_bytes))
    ws = wb.active
    catalog = []
    for row in ws.iter_rows(min_row=2):
        name = row[1].value
        sku  = row[2].value if len(row) > 2 else None
        if not name:
            continue
        catalog.append({"name": str(name).strip(), "sku": str(sku or "").strip()})
    return catalog


# ══════════════════════════════════════════════
# Gemini — аналіз фото
# ══════════════════════════════════════════════
DOSSIER_PROMPT = """Відповідай ТІЛЬКИ валідним JSON без пояснень і без ```json.

Приклад:
{"top_type":"зіпер","bottom_type":"штани","items_count":2,"color":"чорний","brand":"Stone Island","material":"трикотаж","print_description":"нашивка-компас зелена кругла на лівому рукаві та лівій штанині","inscriptions":"STONE ISLAND","background":"сірий бетон"}

Поля:
top_type: зіпер/худі/світшот/футболка/куртка/вітровка/пуховик/інше або "" якщо немає верху
bottom_type: штани/шорти/спідниця/інше або "" якщо немає низу
items_count: точна кількість предметів одягу на фото (число)
color: основний колір або кольори через кому (укр)
brand: назва бренду з логотипу або напису — розпізнай точно, або ""
material: фліс/трикотаж/плащівка/котон/двунитка/інше або ""
print_description: для кожного принту/нашивки — колір, що зображено, розташування. Коротко. або ""
inscriptions: всі написи дослівно або ""
background: фон фото (1-3 слова укр)"""

RETRY_PROMPT = """Повторно опиши одяг на фото. Попередній аналіз помилився: {error_hint}
Відповідай ТІЛЬКИ валідним JSON без пояснень і без ```json.

Приклад:
{{"top_type":"зіпер","bottom_type":"штани","items_count":2,"color":"чорний","brand":"Stone Island","material":"трикотаж","print_description":"нашивка-компас зелена кругла на лівому рукаві","inscriptions":"STONE ISLAND","background":"сірий бетон"}}

Поля:
top_type: зіпер/худі/світшот/футболка/куртка/вітровка/пуховик/інше або ""
bottom_type: штани/шорти/спідниця/інше або ""
items_count: точна кількість предметів (число)
color: основний колір (укр)
brand: бренд або ""
material: фліс/трикотаж/плащівка/котон/двунитка/інше або ""
print_description: опис принтів або ""
inscriptions: написи або ""
background: фон (1-3 слова)"""


async def gemini_analyze(photo_bytes: bytes, error_hint: str = ""):
    img_b64 = base64.standard_b64encode(photo_bytes).decode()
    mime    = get_mime(photo_bytes)
    prompt  = RETRY_PROMPT.format(error_hint=error_hint) if error_hint else DOSSIER_PROMPT
    payload = {
        "contents": [{"parts": [
            {"inline_data": {"mime_type": mime, "data": img_b64}},
            {"text": prompt}
        ]}],
        "generationConfig": {
            "temperature": 0.1,
            "maxOutputTokens": 2048,
            "thinkingConfig": {"thinkingBudget": 0}
        }
    }
    raw = ""
    try:
        async with aiohttp.ClientSession() as s:
            async with s.post(
                f"{GEMINI_URL}?key={GEMINI_API_KEY}",
                json=payload,
                timeout=aiohttp.ClientTimeout(total=30)
            ) as r:
                result = await r.json()
                candidates = result.get("candidates", [])
                if not candidates:
                    log.error(f"Немає candidates: {result}")
                    return None
                raw = candidates[0]["content"]["parts"][0]["text"].strip()
                raw = raw.replace("```json", "").replace("```", "").strip()
                last_brace = raw.rfind("}")
                if last_brace != -1:
                    raw = raw[:last_brace + 1]
                return json.loads(raw)
    except Exception as e:
        log.error(f"gemini_analyze: {e} | raw: {raw[:80]}")
        return None


# ══════════════════════════════════════════════
# Скоринг досьє
# ══════════════════════════════════════════════
def score_dossier_match(query: dict, candidate: dict) -> float:
    score = 0.0

    # ── Кількість предметів — жорстке правило ──
    qn = query.get("items_count")
    cn = candidate.get("items_count")
    if qn and cn:
        if qn == cn:
            score += 8.0
        else:
            score -= 15.0  # жорстке покарання

    # ── Тип верху — дуже важливий ──
    qt = (query.get("top_type") or "").lower()
    ct = (candidate.get("top_type") or "").lower()
    if qt and ct:
        if qt == ct:
            score += 12.0
        else:
            score -= 10.0

    # ── Тип низу ──
    qb = (query.get("bottom_type") or "").lower()
    cb = (candidate.get("bottom_type") or "").lower()
    if qb and cb:
        if qb == cb:
            score += 6.0
        else:
            score -= 5.0

    # ── Бренд — найвища вага ──
    qbr = (query.get("brand") or "").lower().strip()
    cbr = (candidate.get("brand") or "").lower().strip()
    if qbr and cbr:
        if qbr == cbr:
            score += 20.0
        elif qbr in cbr or cbr in qbr:
            score += 10.0
        else:
            score -= 8.0
    elif qbr and not cbr:
        score -= 3.0

    # ── Колір — висока вага ──
    qc = (query.get("color") or "").lower()
    cc = (candidate.get("color") or "").lower()
    if qc and cc:
        q_colors = set(qc.replace(",", " ").split())
        c_colors = set(cc.replace(",", " ").split())
        overlap  = q_colors & c_colors
        if overlap:
            score += len(overlap) * 6.0
        else:
            score -= 5.0

    # ── Матеріал — важливо для фліс vs трикотаж ──
    qm = (query.get("material") or "").lower()
    cm = (candidate.get("material") or "").lower()
    if qm and cm:
        if qm == cm:
            score += 8.0
        else:
            score -= 4.0

    # ── Сезон з назви каталогу ──
    qs = (query.get("season") or "").lower()
    cs = (candidate.get("season") or "").lower()
    if qs and cs:
        if qs == cs:
            score += 6.0
        else:
            score -= 4.0

    # ── Написи — бонус ──
    qi = (query.get("inscriptions") or "").lower()
    ci = (candidate.get("inscriptions") or "").lower()
    if qi and ci:
        q_words = set(qi.split())
        c_words = set(ci.split())
        overlap = q_words & c_words
        score += len(overlap) * 6.0

    # ── Принт — бонус ──
    qp = (query.get("print_description") or "").lower()
    cp = (candidate.get("print_description") or "").lower()
    if qp and cp:
        q_words = set(w for w in qp.replace(";", " ").replace(",", " ").split() if len(w) >= 3)
        c_words = set(w for w in cp.replace(";", " ").replace(",", " ").split() if len(w) >= 3)
        overlap = q_words & c_words
        score += len(overlap) * 4.0

    return score


async def dossier_search(photo_bytes: bytes,
                          extra_query: str = "",
                          rejected_names: set = None,
                          error_hint: str = "") -> list:
    if not _dossier_cache:
        return []

    rejected_names = rejected_names or set()
    query_dossier  = await gemini_analyze(photo_bytes, error_hint=error_hint)
    if not query_dossier:
        return []

    log.info(
        f"Досьє: верх={query_dossier.get('top_type')} низ={query_dossier.get('bottom_type')} "
        f"к-сть={query_dossier.get('items_count')} колір={query_dossier.get('color')} "
        f"бренд={query_dossier.get('brand')} матеріал={query_dossier.get('material')}"
    )

    if extra_query:
        existing = query_dossier.get("inscriptions") or ""
        query_dossier["inscriptions"] = (existing + " " + extra_query.lower()).strip()
        # Також перевіряємо сезон з уточнення
        season_from_query = extract_season(extra_query)
        if season_from_query:
            query_dossier["season"] = season_from_query

    results = []
    for sku, dossier in _dossier_cache.items():
        if (dossier.get("name") or "").lower() in rejected_names:
            continue
        sc = score_dossier_match(query_dossier, dossier)
        if sc >= MIN_SCORE:
            results.append((sc, sku, dossier))

    results.sort(key=lambda x: x[0], reverse=True)

    if not results:
        log.info("dossier_search: збігів не знайдено")
        return []

    best_score = results[0][0]
    log.info(f"Топ збіг: '{results[0][2].get('name')}' score:{best_score:.1f}")

    def make_item(sku, dossier):
        for item in _photo_catalog:
            if item.get("sku") == sku:
                return item
        return {"name": dossier.get("name", ""), "sku": sku}

    found = []
    for sc, sku, dos in results[:MAX_RESULTS]:
        if best_score - sc <= SHOW_ALL_THRESHOLD:
            found.append(make_item(sku, dos))
        else:
            break

    if not found:
        found = [make_item(results[0][1], results[0][2])]

    log.info(f"Показуємо {len(found)} варіантів менеджеру")
    return found


# ══════════════════════════════════════════════
# МійДроп API
# ══════════════════════════════════════════════
async def fetch_api_products() -> list:
    if _api_cache["products"] and (time.time() - _api_cache["ts"]) < 300:
        return _api_cache["products"]
    try:
        async with aiohttp.ClientSession() as s:
            async with s.get(f"{MYDROP_BASE}/export/products/json",
                             headers=MYDROP_HEADERS,
                             timeout=aiohttp.ClientTimeout(total=20)) as r:
                data = await r.json(content_type=None)
                all_p = data if isinstance(data, list) else data.get("products", [])
                def is_true(v):
                    return v is True or str(v).lower() == "true" or v == 1
                products = [p for p in all_p
                            if not is_true(p.get("hidden")) and not is_true(p.get("archived"))]
                _api_cache["products"] = products
                _api_cache["ts"] = time.time()
                return products
    except Exception as e:
        log.error(f"fetch_api_products: {e}")
        return _api_cache["products"] or []


async def build_api_catalog_index() -> list:
    global _photo_catalog
    if _photo_catalog:
        return _photo_catalog
    products = await fetch_api_products()
    if not products:
        return []
    index = []
    for p in products:
        images    = p.get("images") or []
        photo_url = ""
        if images:
            first     = images[0]
            photo_url = first.get("full_url") or ""
            if not photo_url:
                fn = first.get("filename") or ""
                if fn:
                    photo_url = f"https://backend.mydrop.com.ua/vendor/products/uploads/{fn}"
        if not photo_url:
            continue  # пропускаємо без фото
        index.append({
            "name":      p.get("title") or "",
            "sku":       p.get("sku") or "",
            "id":        p.get("id"),
            "photo_url": photo_url,
        })
    _photo_catalog = index
    log.info(f"Каталог-індекс: {len(index)} товарів")
    return index


async def fetch_dropshippers() -> list:
    if _ds_cache["list"] and (time.time() - _ds_cache["ts"]) < 300:
        return _ds_cache["list"]
    try:
        async with aiohttp.ClientSession() as s:
            async with s.get("https://backend.mydrop.com.ua/vendor/vendor_dropshippers",
                             headers=MYDROP_HEADERS,
                             params={"page": 1, "per_page": 50},
                             timeout=aiohttp.ClientTimeout(total=10)) as r:
                data = await r.json(content_type=None)
                ds = data.get("results", [])
                _ds_cache["list"] = ds
                _ds_cache["ts"] = time.time()
                return ds
    except Exception as e:
        log.error(f"fetch_dropshippers: {e}")
        return _ds_cache["list"] or []


async def fetch_child_products(product_id: int) -> list:
    """Отримує складові комплекту по ID товару."""
    if not product_id:
        return []
    try:
        async with aiohttp.ClientSession() as s:
            async with s.get(
                f"https://backend.mydrop.com.ua/vendor/products/{product_id}",
                headers=MYDROP_HEADERS,
                timeout=aiohttp.ClientTimeout(total=10)
            ) as r:
                if r.status != 200:
                    return []
                data = await r.json(content_type=None)
                children = data.get("childProducts") or []
                result = []
                for child in children:
                    cp = child.get("childProduct") or {}
                    title = cp.get("title") or ""
                    cp_id = cp.get("id")
                    sizes = cp.get("sizes") or []
                    # Збираємо доступні розміри
                    available_sizes = [s.get("title", "") for s in sizes]
                    result.append({
                        "title": title,
                        "id": cp_id,
                        "available_sizes": available_sizes
                    })
                return result
    except Exception as e:
        log.error(f"fetch_child_products: {e}")
        return []


async def api_create_order(payload: dict):
    async with aiohttp.ClientSession() as s:
        async with s.post(f"{MYDROP_BASE}/orders", headers=MYDROP_HEADERS,
                          json=payload, timeout=aiohttp.ClientTimeout(total=15)) as r:
            return await r.json(content_type=None), r.status


def find_api_product_by_name(name: str, api_products: list):
    name_lower = name.lower()
    best_score, best = 0, None
    for p in api_products:
        title = (p.get("title") or "").lower()
        score = SequenceMatcher(None, name_lower, title).ratio()
        if score > best_score:
            best_score, best = score, p
    return best if best and best_score > 0.3 else None


def smart_search(query: str, catalog: list, limit: int = 8) -> list:
    q_words = [w for w in query.lower().split() if len(w) >= 2]
    if not q_words:
        return []
    results = []
    for item in catalog:
        full  = item["name"].lower() + " " + item.get("sku", "").lower()
        score = sum(1.0 if w in full else
                    0.7 if any(w in p or p in w for p in full.split() if len(p) >= 2) else 0
                    for w in q_words) / len(q_words)
        if score > 0:
            results.append((score, item))
    results.sort(key=lambda x: x[0], reverse=True)
    return [item for _, item in results[:limit]]


# ══════════════════════════════════════════════
# Нормалізація розміру
# ══════════════════════════════════════════════
_CYRILLIC_TO_LATIN = str.maketrans("СМЛсмл", "SMLsml")  # Кирилиця → Латиниця

_SIZE_ALIASES: dict = {
    # Латинські (canonical)
    "xs": "XS", "s": "S", "m": "M", "l": "L", "xl": "XL",
    "xxl": "XXL", "2xl": "XXL", "xxxl": "3XL", "3xl": "3XL", "4xl": "4XL",
    # Кирилиця → латиниця
    "хс": "XS", "с": "S", "м": "M", "л": "L", "хл": "XL",
    "ххл": "XXL", "2хл": "XXL",
    # Числові
    "44": "S", "46": "M", "48": "L", "50": "XL", "52": "XXL", "54": "3XL",
}

def normalize_size(raw: str) -> str:
    """Приводить розмір до стандартного вигляду, який МийДроп знаходить у варіаціях."""
    if not raw or raw == "-":
        return raw
    s = raw.strip().translate(_CYRILLIC_TO_LATIN).upper()
    # Видаляємо пробіли між буквами: "X L" → "XL"
    s = s.replace(" ", "")
    return _SIZE_ALIASES.get(s.lower(), s)


# ══════════════════════════════════════════════
# Парсинг замовлення через Gemini
# ══════════════════════════════════════════════
PARSE_ORDER_PROMPT = """Витягни дані замовлення з тексту і поверни ТІЛЬКИ валідний JSON без пояснень і без ```json.

Текст замовлення: {text}

Приклад відповіді:
{{"name":"Іван Петренко","phone":"+380991234567","size":"XL","sizes":null,"amount":1,"child_sizes":null,"city":"Київ","warehouse":"5","cod":1500,"ds_id":259307}}

Правила:
- name: ПІБ клієнта (або порожньо якщо немає)
- phone: телефон у форматі +380XXXXXXXXX (якщо починається з 0 — додай +38)
- size: розмір одягу (S/M/L/XL тощо, або "-" якщо не вказано). Якщо кілька РІЗНИХ розмірів — залиш ""
- sizes: масив якщо замовлено КІЛЬКА РІЗНИХ розмірів (напр. "М і С" → ["M","S"], "M та XL" → ["M","XL"]), або null
- amount: кількість одиниць (ціле число ≥ 1). Якщо sizes → amount = len(sizes). Приклад: "2 шт" → 2
- child_sizes: об'єкт якщо вказані різні розміри для складових комплекту (напр. "худі М штани С" → {{"худі":"M","штани":"S"}}), або null
- city: місто доставки
- warehouse: номер відділення Нової Пошти (тільки число)
- cod: сума накладеного платежу (число, 0 якщо передплата)
- ds_id: ЗАВЖДИ останній рядок тексту якщо це ціле число (ID дропшипера). Не плутай з cod!

Якщо якогось поля немає — залиш порожнім рядком або null."""


async def parse_order_with_ai(text: str):
    """Парсить замовлення з вільного тексту через Gemini."""
    if not text or not text.strip():
        return None
    prompt = PARSE_ORDER_PROMPT.format(text=text.strip())
    try:
        payload = {
            "contents": [{"parts": [{"text": prompt}]}],
            "generationConfig": {
                "temperature": 0.1,
                "maxOutputTokens": 400,
                "thinkingConfig": {"thinkingBudget": 0}
            }
        }
        async with aiohttp.ClientSession() as s:
            async with s.post(
                f"{GEMINI_URL}?key={GEMINI_API_KEY}",
                json=payload,
                timeout=aiohttp.ClientTimeout(total=15)
            ) as r:
                result = await r.json()
                candidates = result.get("candidates", [])
                if not candidates:
                    return None
                raw = candidates[0]["content"]["parts"][0]["text"].strip()
                raw = raw.replace("```json", "").replace("```", "").strip()
                last_brace = raw.rfind("}")
                if last_brace != -1:
                    raw = raw[:last_brace + 1]
                data = json.loads(raw)

                # Нормалізуємо телефон
                phone = str(data.get("phone") or "").replace(" ", "").replace("-", "")
                if phone.startswith("0"):
                    phone = "+38" + phone
                elif phone.startswith("38") and not phone.startswith("+"):
                    phone = "+" + phone

                # Нормалізуємо COD
                cod = data.get("cod")
                try:
                    cod = float(str(cod).replace(" ", "")) if cod else 0.0
                except:
                    cod = 0.0

                # ds_id
                ds_id = data.get("ds_id")
                try:
                    ds_id = int(ds_id) if ds_id else None
                except:
                    ds_id = None

                # sizes — масив різних розмірів
                sizes = data.get("sizes")
                if isinstance(sizes, list) and sizes:
                    sizes = [str(s).strip().upper() for s in sizes if s]
                    if not sizes:
                        sizes = None
                else:
                    sizes = None

                # amount
                try:
                    amount = int(data.get("amount") or 1)
                    if amount < 1:
                        amount = 1
                except:
                    amount = 1
                if sizes:
                    amount = len(sizes)  # sizes мають пріоритет

                # child_sizes — розміри для складових комплекту
                child_sizes = data.get("child_sizes")
                if not isinstance(child_sizes, dict) or not child_sizes:
                    child_sizes = None

                order = {
                    "name":        str(data.get("name") or "").strip(),
                    "phone":       phone,
                    "size":        normalize_size(str(data.get("size") or "-").strip() or "-"),
                    "sizes":       [normalize_size(s) for s in sizes] if sizes else None,
                    "amount":      amount,
                    "child_sizes": {k: normalize_size(v) for k, v in child_sizes.items()} if child_sizes else None,
                    "city":        str(data.get("city") or "").strip(),
                    "warehouse":   str(data.get("warehouse") or "").strip(),
                    "cod":         cod,
                    "price":       cod,
                    "ds_id":       ds_id,
                }

                # Перевірка мінімальних полів
                if not order["name"] or not order["phone"] or not order["city"]:
                    return None

                log.info(
                    f"AI парсинг: {order['name']} {order['phone']} {order['city']} "
                    f"відд.{order['warehouse']} {order['cod']}грн "
                    f"розмір={order['size']} sizes={sizes} amount={amount} child_sizes={child_sizes}"
                )
                return order

    except Exception as e:
        log.error(f"parse_order_with_ai: {e}")
        return None


async def parse_order_smart(text: str):
    """
    Парсить замовлення: спочатку AI, потім text-парсер.
    ds_id ЗАВЖДИ береться з останнього рядка якщо там число.
    """
    ai_data   = await parse_order_with_ai(text)
    text_data = parse_order_text(text)

    # Надійне витягання ds_id з останнього рядка (незалежно від AI)
    last_line_ds_id = None
    lines = [l.strip() for l in text.strip().splitlines() if l.strip()]
    if len(lines) >= 7:  # є хоча б 7 рядків → останній може бути ds_id
        try:
            val = int(lines[-1])
            cod_val = int(float((ai_data or text_data or {}).get("cod") or 0))
            is_cod  = (val == cod_val and cod_val > 0)
            if val > 0 and not is_cod:
                last_line_ds_id = val
                log.info(f"Кандидат ds_id з останнього рядка: {val}")
            elif is_cod:
                log.info(f"Останній рядок {val} = наложка, ігнорую як ds_id")
        except ValueError:
            pass

    if ai_data:
        if not ai_data.get("ds_id"):
            if last_line_ds_id:
                ai_data["ds_id"] = last_line_ds_id
                log.info(f"ds_id з останнього рядка: {last_line_ds_id}")
            elif text_data and text_data.get("ds_id"):
                ai_data["ds_id"] = text_data["ds_id"]
                log.info(f"ds_id з text-парсера: {text_data['ds_id']}")
        return ai_data

    if text_data and not text_data.get("ds_id") and last_line_ds_id:
        text_data["ds_id"] = last_line_ds_id
    return text_data


def parse_order_text(text: str):
    """Старий парсер — fallback якщо AI недоступний."""
    if not text:
        return None
    lines = [l.strip() for l in text.strip().splitlines() if l.strip()]
    if len(lines) < 6:
        return None
    try:
        phone = lines[1].replace(" ", "").replace("-", "")
        if phone.startswith("0"):
            phone = "+380" + phone[1:]
        elif not phone.startswith("+"):
            phone = "+380" + phone
        cod   = float(lines[5])
        ds_id = None
        if len(lines) >= 7:
            try:
                val = int(lines[-1])
                # Не плутаємо наложку з ds_id: якщо останній рядок = COD — це не ID
                if val > 0 and val != int(cod):
                    ds_id = val
            except ValueError:
                pass
        return {
            "name": lines[0], "phone": phone,
            "size": None if lines[2] == "-" else normalize_size(lines[2]),
            "sizes": None, "amount": 1, "child_sizes": None,
            "city": lines[3], "warehouse": lines[4],
            "cod": cod, "price": cod, "ds_id": ds_id
        }
    except Exception:
        return None


# ══════════════════════════════════════════════
# Клавіатури
# ══════════════════════════════════════════════
def kb_confirm() -> InlineKeyboardMarkup:
    return InlineKeyboardMarkup(inline_keyboard=[[
        InlineKeyboardButton(text="✅ Так",               callback_data="prod_yes"),
        InlineKeyboardButton(text="➡️ Наступний варіант", callback_data="prod_next"),
    ], [
        InlineKeyboardButton(text="✏️ Уточнити",          callback_data="prod_refine"),
        InlineKeyboardButton(text="🔍 Вручну",             callback_data="prod_manual"),
    ]])

def kb_confirm_multi() -> InlineKeyboardMarkup:
    return InlineKeyboardMarkup(inline_keyboard=[[
        InlineKeyboardButton(text="✅ Так",               callback_data="multi_yes"),
        InlineKeyboardButton(text="➡️ Наступний варіант", callback_data="multi_next"),
    ], [
        InlineKeyboardButton(text="✏️ Уточнити",          callback_data="multi_refine"),
        InlineKeyboardButton(text="🔍 Вручну",             callback_data="multi_manual"),
    ]])

def kb_items(items: list) -> InlineKeyboardMarkup:
    buttons = [[InlineKeyboardButton(text=item["name"][:55], callback_data=f"pick_{i}")]
               for i, item in enumerate(items[:8])]
    buttons.append([InlineKeyboardButton(text="✏️ Інший запит", callback_data="pick_manual")])
    return InlineKeyboardMarkup(inline_keyboard=buttons)

def kb_ds(dropshippers: list) -> InlineKeyboardMarkup:
    buttons = [[InlineKeyboardButton(
        text=f"{ds.get('name') or ds.get('dropshipper',{}).get('name','?')} (ID {ds.get('id')})",
        callback_data=f"ds_{ds.get('id')}")] for ds in dropshippers[:10]]
    buttons.append([InlineKeyboardButton(text="✏️ Ввести ID вручну", callback_data="ds_manual")])
    buttons.append([InlineKeyboardButton(text="🚫 Без дропшипера",   callback_data="ds_none")])
    return InlineKeyboardMarkup(inline_keyboard=buttons)

def kb_final() -> InlineKeyboardMarkup:
    return InlineKeyboardMarkup(inline_keyboard=[[
        InlineKeyboardButton(text="✅ Відправити", callback_data="final_yes"),
        InlineKeyboardButton(text="❌ Скасувати",  callback_data="final_no"),
    ]])

def kb_ambiguous(items: list) -> InlineKeyboardMarkup:
    buttons = [[InlineKeyboardButton(text=f"📦 {item['name'][:50]}", callback_data=f"amb_{i}")]
               for i, item in enumerate(items)]
    buttons.append([InlineKeyboardButton(text="🔍 Шукати вручну", callback_data="amb_manual")])
    return InlineKeyboardMarkup(inline_keyboard=buttons)

ORDER_HINT = (
    "📋 <b>Формат підпису до фото (6–7 рядків):</b>\n\n"
    "<code>Іван Петренко\n+380991234567\nXL\nКиїв\n5\n1500\n42</code>\n\n"
    "1 — ПІБ | 2 — Телефон | 3 — Розмір (-)\n"
    "4 — Місто | 5 — Відділення НП\n"
    "6 — Накладений (0=передплата) | 7 — ID дропшипера"
)


# ══════════════════════════════════════════════
# FSM
# ══════════════════════════════════════════════
class Order(StatesGroup):
    confirm_product     = State()
    confirm_ambiguous   = State()
    refine_search       = State()
    manual_search       = State()
    confirm_multi       = State()
    manual_search_multi = State()
    refine_multi        = State()
    ask_city            = State()
    ask_warehouse       = State()
    ask_ds_choice       = State()
    ask_ds_id           = State()
    final_confirm       = State()


# ══════════════════════════════════════════════
# Переходи
# ══════════════════════════════════════════════
async def proceed_to_ds(target, state: FSMContext):
    data  = await state.get_data()
    order = data.get("order", {})
    m     = target if isinstance(target, types.Message) else target.message

    # Якщо місто не підтверджене — шукаємо через НП
    if not data.get("city_ref"):
        city_query = order.get("city", "")
        if city_query:
            cities = await np_search_city(city_query)
            if len(cities) == 1:
                # Одне місто — беремо автоматично
                await state.update_data(city_ref=cities[0]["city_ref"],
                                        city_name=cities[0]["name"],
                                        city_short=cities[0].get("short_name", cities[0]["name"]))
                await proceed_to_warehouse(m, state)
                return
            elif len(cities) > 1:
                await state.set_state(Order.ask_city)
                await state.update_data(np_cities=cities)
                buttons = [[InlineKeyboardButton(text=c["name"][:60], callback_data=f"city_{i}")]
                           for i, c in enumerate(cities)]
                await m.answer("🏙 Уточни місто:", reply_markup=InlineKeyboardMarkup(inline_keyboard=buttons))
                return
        # Якщо не знайшли — просимо ввести вручну
        await state.set_state(Order.ask_city)
        await m.answer("🏙 Введи місто для пошуку:")
        return

    # Якщо відділення не підтверджене
    if not data.get("warehouse_ref"):
        await proceed_to_warehouse(m, state)
        return

    # Все є — вибір дропшипера
    await proceed_to_dropshipper(m, state)


async def proceed_to_warehouse(m: types.Message, state: FSMContext):
    data          = await state.get_data()
    order         = data.get("order", {})
    city_ref      = data.get("city_ref", "")
    warehouse_num = str(order.get("warehouse") or "").strip()

    warehouses = await np_search_warehouse(city_ref, warehouse_num)

    if not warehouses:
        await state.set_state(Order.ask_warehouse)
        await m.answer("🏢 Не знайшов відділень. Введи номер відділення НП:")
        return

    # Якщо знайдено рівно 1 і це точний збіг — авто-вибір
    if len(warehouses) == 1:
        wh = warehouses[0]
        ref = wh["ref"]
        if ref:
            await state.update_data(
                warehouse_ref=ref,
                warehouse_name=wh["name"],
                warehouse_number=wh["num_digits"] or wh["number"],
            )
            log.info(f"Авто-вибір відділення: {wh['name']} ref={ref[:8]}")
            await proceed_to_dropshipper(m, state)
            return
        # ref порожній — показуємо кнопку щоб user підтвердив
        warehouses_to_show = warehouses
    else:
        warehouses_to_show = warehouses

    # Показуємо список (показуємо до 8, решта — "ввести вручну")
    await state.set_state(Order.ask_warehouse)
    await state.update_data(np_warehouses=warehouses_to_show[:20])
    hint = f" (шукав відд. {warehouse_num})" if warehouse_num else ""
    buttons = [[InlineKeyboardButton(text=w["name"][:60], callback_data=f"wh_{i}")]
               for i, w in enumerate(warehouses_to_show[:20])]
    buttons.append([InlineKeyboardButton(text="✏️ Ввести номер вручну", callback_data="wh_manual")])
    await m.answer(f"🏢 Вибери відділення НП{hint}:",
                   reply_markup=InlineKeyboardMarkup(inline_keyboard=buttons))


async def proceed_to_dropshipper(m: types.Message, state: FSMContext):
    data  = await state.get_data()
    order = data.get("order", {})
    if order.get("ds_id"):
        await show_final_confirm(m, state)
        return
    ds = await fetch_dropshippers()
    if ds:
        await state.set_state(Order.ask_ds_choice)
        await m.answer("👥 <b>Оберіть дропшипера:</b>", parse_mode="HTML", reply_markup=kb_ds(ds))
    else:
        await state.set_state(Order.ask_ds_id)
        await m.answer("👥 Введи <b>ID дропшипера</b>:", parse_mode="HTML")


async def show_final_confirm(m: types.Message, state: FSMContext):
    data    = await state.get_data()
    order   = data["order"]
    product = data.get("selected_product", {})
    prepay  = "💳 Передплата" if order["cod"] == 0 else f"💰 {int(order['cod'])} грн (накладений)"
    confirmed = data.get("confirmed_products")
    if confirmed:
        products_text = "\n".join(
            f"📦 <b>{p.get('title') or p.get('name','?')}</b>"
            for p in confirmed
        )
    else:
        name = product.get("title") or product.get("name", "—")
        products_text = f"📦 <b>{name}</b>"

    # Рядок розміру/кількості
    sizes       = order.get("sizes")
    child_sizes = order.get("child_sizes")
    amount      = order.get("amount", 1) or 1
    size        = order.get("size") or "—"
    if child_sizes:
        sz_lines   = "\n".join(f"   {k}: <b>{v}</b>" for k, v in child_sizes.items())
        size_line  = f"📏 Розміри комплекту:\n{sz_lines}"
    elif sizes and len(sizes) > 1:
        size_line  = f"📏 Розміри: <b>{', '.join(sizes)}</b> ({len(sizes)} шт)"
    elif amount > 1:
        size_line  = f"📏 Розмір: <b>{size}</b> × {amount} шт"
    else:
        size_line  = f"📏 Розмір: <b>{size}</b>"

    ds_id          = order.get("ds_id") or "—"
    city_name      = data.get("city_name") or order.get("city") or "—"
    warehouse_name = data.get("warehouse_name") or f"відд. {order.get('warehouse') or '—'}"

    # Попередження якщо refs відсутні
    warnings = []
    if not data.get("city_ref"):
        warnings.append("⚠️ місто не підтверджено через НП")
    if not data.get("warehouse_ref"):
        warnings.append("⚠️ відділення не підтверджено через НП")
    warn_text = ("\n\n🚨 <b>УВАГА:</b>\n" + "\n".join(warnings)) if warnings else ""

    await state.set_state(Order.final_confirm)
    await m.answer(
        "📋 <b>Перевір замовлення:</b>\n\n"
        f"{products_text}\n"
        f"{size_line}\n\n"
        "──────────────\n"
        f"👤 <b>{order['name']}</b>\n"
        f"📱 {order['phone']}\n\n"
        "──────────────\n"
        f"🏙 <b>{city_name}</b>\n"
        f"🏢 {warehouse_name}\n"
        f"{prepay}\n"
        f"👥 Дропшипер ID: <b>{ds_id}</b>\n"
        "──────────────"
        f"{warn_text}\n\n"
        "✅ Все вірно?",
        parse_mode="HTML", reply_markup=kb_final()
    )


async def present_search_results(msg, state, results, photo_hash=None):
    if not results:
        await state.set_state(Order.manual_search)
        await msg.answer("🤔 Не знайшов товар. Введи пошуковий запит:", parse_mode="HTML")
        return
    if len(results) == 1:
        found        = results[0]
        api_products = await fetch_api_products()
        api_product  = find_api_product_by_name(found["name"], api_products)
        product      = api_product or {"title": found["name"], "sku": found.get("sku",""), "id": None}
        await state.update_data(selected_product=product, last_catalog_name=found["name"])
        await state.set_state(Order.confirm_product)
        await msg.answer(
            f"🔎 <b>Знайдений товар:</b>\n\n🟢 <b>{found['name']}</b>\n🔑 SKU: {found.get('sku') or '—'}\n\nЦе правильний товар?",
            parse_mode="HTML", reply_markup=kb_confirm()
        )
    else:
        await state.update_data(ambiguous_results=results, photo_hash=photo_hash)
        await state.set_state(Order.confirm_ambiguous)
        text = f"🤔 <b>Знайшов {len(results)} схожих — оберіть правильний:</b>\n\n"
        for i, item in enumerate(results, 1):
            text += f"{i}️⃣ <b>{item['name']}</b>\n   SKU: {item.get('sku') or '—'}\n\n"
        await msg.answer(text, parse_mode="HTML", reply_markup=kb_ambiguous(results))


# ══════════════════════════════════════════════
# Media group
# ══════════════════════════════════════════════
_media_groups: dict = {}


async def process_media_group(media_group_id: str, state_factory, bot_instance):
    await asyncio.sleep(1.5)
    group = _media_groups.pop(media_group_id, None)
    if not group:
        return
    msgs = group["msgs"]
    if not msgs:
        return
    first_msg = msgs[0]
    caption = ""
    for m in msgs:
        if m.caption:
            caption = m.caption
            break
    order_data = await parse_order_smart(caption)
    if not order_data:
        await first_msg.answer(f"⚠️ Відсутній або невірний підпис.\n\n{ORDER_HINT}", parse_mode="HTML")
        return
    photo_list = []
    for msg in msgs:
        if not msg.photo:
            continue
        file = await bot_instance.get_file(msg.photo[-1].file_id)
        url  = f"https://api.telegram.org/file/bot{TELEGRAM_TOKEN}/{file.file_path}"
        async with aiohttp.ClientSession() as s:
            async with s.get(url) as r:
                photo_bytes = await r.read()
        photo_list.append(photo_bytes)
    if not photo_list:
        return
    from aiogram.fsm.storage.base import StorageKey
    storage_key = StorageKey(bot_id=bot_instance.id, chat_id=first_msg.chat.id, user_id=first_msg.from_user.id)
    state = FSMContext(storage=dp.storage, key=storage_key)
    await state.clear()
    notice = await first_msg.answer(f"🔍 Знайдено {len(photo_list)} фото. Шукаю товари...")
    found_products = []
    for i, photo_bytes in enumerate(photo_list, 1):
        ph     = get_photo_hash(photo_bytes)
        pb_hex = photo_bytes.hex()   # зберігаємо завжди — потрібно для Next/Refine
        learned = await db_get_learned(ph)
        if learned:
            found_products.append({"photo_hash": ph, "api_product": learned, "confirmed": True, "photo_bytes_hex": pb_hex})
        else:
            results = await dossier_search(photo_bytes)
            if results:
                found        = results[0]
                api_products = await fetch_api_products()
                api_product  = find_api_product_by_name(found["name"], api_products)
                product      = api_product or {"title": found["name"], "sku": found.get("sku",""), "id": None}
                found_products.append({"photo_hash": ph, "api_product": product, "confirmed": False, "photo_bytes_hex": pb_hex})
            else:
                found_products.append({"photo_hash": ph, "api_product": None, "confirmed": False, "photo_bytes_hex": pb_hex})
    await notice.delete()
    await state.update_data(order=order_data, multi_products=found_products,
                             multi_idx=0, confirmed_products=[], rejected_names=[])
    await state.set_state(Order.confirm_multi)
    await show_multi_confirm(first_msg, state, 0, found_products)


async def show_multi_confirm(msg, state, idx, products):
    if idx >= len(products):
        await proceed_to_ds(msg, state)
        return
    item = products[idx]
    p    = item.get("api_product")
    if not p:
        await state.update_data(multi_idx=idx)
        await state.set_state(Order.manual_search_multi)
        await msg.answer(f"🤔 Фото {idx+1} з {len(products)}: не знайдено.\nВведи пошуковий запит:", parse_mode="HTML")
        return
    name = p.get("title") or p.get("name", "—")
    sku  = p.get("sku", "—")
    await state.update_data(multi_idx=idx)
    await msg.answer(
        f"📦 <b>Товар {idx+1} з {len(products)}:</b>\n\n🟢 <b>{name}</b>\n🔑 SKU: {sku}\n\nЦе правильний товар?",
        parse_mode="HTML", reply_markup=kb_confirm_multi()
    )


# ══════════════════════════════════════════════
# Команди
# ══════════════════════════════════════════════
@dp.message(Command("start"))
async def cmd_start(msg: types.Message, state: FSMContext):
    await state.clear()
    cat = f"📦 Каталог: <b>{len(_photo_catalog)} товарів</b>" if _photo_catalog else "📦 Каталог: завантажується"
    dos = f"🗂 Досьє: <b>{len(_dossier_cache)} товарів</b>" if _dossier_cache else "🗂 Досьє: <b>не завантажені</b> — запусти /refresh"
    await msg.answer(f"👋 <b>МійДроп — бот для менеджера</b>\n\n{cat}\n{dos}\n\n{ORDER_HINT}", parse_mode="HTML")


@dp.message(Command("cancel"))
async def cmd_cancel(msg: types.Message, state: FSMContext):
    await state.clear()
    await msg.answer("❌ Скасовано.")


@dp.message(Command("refresh"))
async def cmd_refresh(msg: types.Message):
    global _photo_catalog
    _api_cache["ts"] = 0
    _ds_cache["ts"]  = 0
    _photo_catalog   = []
    notice = await msg.answer("🔄 Оновлюю...")
    await build_api_catalog_index()
    await load_dossiers_cache()
    await notice.edit_text(
        f"✅ Оновлено!\n📦 {len(_photo_catalog)} товарів\n🗂 {len(_dossier_cache)} досьє"
    )


@dp.message(Command("cleanup"))
async def cmd_cleanup(msg: types.Message):
    """Видаляє досьє товарів яких більше немає в активному каталозі."""
    if not DB_POOL:
        await msg.answer("❌ DB не підключена.")
        return
    notice = await msg.answer("🧹 Очищую базу від видалених товарів...")
    await build_api_catalog_index()
    active_skus = {item["sku"] for item in _photo_catalog if item.get("sku")}

    async def _run(pool):
        async with pool.acquire() as conn:
            rows      = await conn.fetch("SELECT sku FROM dossiers")
            db_skus   = {r["sku"] for r in rows}
            to_delete = db_skus - active_skus
            if to_delete:
                await conn.execute("DELETE FROM dossiers WHERE sku = ANY($1)", list(to_delete))
                log.info(f"Cleanup: видалено {len(to_delete)} застарілих досьє")
            return to_delete

    to_delete = await _db_execute(_run) or set()
    await load_dossiers_cache()
    deleted = len(to_delete) if to_delete else 0
    await notice.edit_text(
        f"✅ Очищено! Видалено: {deleted} | Залишилось: {len(_dossier_cache)} досьє"
    )


@dp.message(Command("delete"))
async def cmd_delete(msg: types.Message):
    parts = msg.text.split(maxsplit=1)
    if len(parts) < 2:
        await msg.answer("Вкажи ID: <code>/delete 12345</code>", parse_mode="HTML")
        return
    order_id = parts[1].strip()
    notice   = await msg.answer(f"⏳ Скасовую #{order_id}...")
    try:
        async with aiohttp.ClientSession() as s:
            async with s.put(
                f"{MYDROP_BASE}/orders/{order_id}",
                headers=MYDROP_HEADERS,
                json={"status": "Скасовано", "manualStatus": True},
                timeout=aiohttp.ClientTimeout(total=10)
            ) as r:
                status = r.status
                try:
                    result = await r.json(content_type=None)
                except Exception:
                    result = {}
        if status in (200, 201):
            await notice.edit_text(f"✅ Замовлення #{order_id} скасовано!")
        else:
            err = result.get("message") or result.get("error") or str(result)
            await notice.edit_text(f"❌ Помилка: {err}")
    except Exception as e:
        await notice.edit_text(f"❌ Помилка: {e}")


# ══════════════════════════════════════════════
# Фото
# ══════════════════════════════════════════════
@dp.message(F.photo)
async def handle_photo(msg: types.Message, state: FSMContext):
    if msg.media_group_id:
        mgid = msg.media_group_id
        if mgid not in _media_groups:
            _media_groups[mgid] = {"msgs": [], "task": None}
        _media_groups[mgid]["msgs"].append(msg)
        if _media_groups[mgid]["task"]:
            _media_groups[mgid]["task"].cancel()
        _media_groups[mgid]["task"] = asyncio.create_task(
            process_media_group(mgid, dp.fsm, bot)
        )
        return

    await state.clear()
    order_data = await parse_order_smart(msg.caption or "")
    if not order_data:
        await msg.answer(f"⚠️ Відсутній або невірний підпис.\n\n{ORDER_HINT}", parse_mode="HTML")
        return

    file = await bot.get_file(msg.photo[-1].file_id)
    url  = f"https://api.telegram.org/file/bot{TELEGRAM_TOKEN}/{file.file_path}"
    async with aiohttp.ClientSession() as s:
        async with s.get(url) as r:
            photo_bytes = await r.read()

    ph = get_photo_hash(photo_bytes)
    learned = await db_get_learned(ph)
    if learned:
        await state.update_data(order=order_data, selected_product=learned, photo_hash=ph)
        await state.set_state(Order.confirm_product)
        await msg.answer(
            f"✅ <b>З пам'яті:</b>\n\n📦 <b>{learned.get('title') or learned.get('name')}</b>\n\nЦе правильний товар?",
            parse_mode="HTML", reply_markup=kb_confirm()
        )
        return

    if not _dossier_cache:
        await state.update_data(order=order_data, photo_hash=ph,
                                 photo_bytes=photo_bytes.hex(), rejected_names=[], extra_query="")
        await state.set_state(Order.manual_search)
        await msg.answer("🗂 Досьє не завантажені. Введи запит вручну:", parse_mode="HTML")
        return

    notice = await msg.answer(f"🔍 Аналізую фото серед {len(_dossier_cache)} товарів...")
    results = await dossier_search(photo_bytes)
    await notice.delete()

    await state.update_data(order=order_data, photo_hash=ph,
                             photo_bytes=photo_bytes.hex(), rejected_names=[], extra_query="")
    await present_search_results(msg, state, results, photo_hash=ph)


# ══════════════════════════════════════════════
# Текст
# ══════════════════════════════════════════════
@dp.message(StateFilter(None), F.text)
async def handle_text(msg: types.Message, state: FSMContext):
    if msg.text.startswith("/"):
        return
    order_data = await parse_order_smart(msg.text)
    if order_data:
        await state.update_data(order=order_data)
        await state.set_state(Order.manual_search)
        await msg.answer("🔍 Введи пошуковий запит:", parse_mode="HTML")
    else:
        await msg.answer(f"Не розпізнано формат.\n\n{ORDER_HINT}", parse_mode="HTML")


# ══════════════════════════════════════════════
# Підтвердження товару
# ══════════════════════════════════════════════
@dp.callback_query(Order.confirm_product, F.data == "prod_yes")
async def product_confirmed(cb: types.CallbackQuery, state: FSMContext):
    await cb.message.edit_reply_markup()
    data = await state.get_data()
    ph   = data.get("photo_hash")
    if ph:
        await db_save_learned(ph, data["selected_product"])
    await proceed_to_ds(cb, state)


@dp.callback_query(Order.confirm_product, F.data == "prod_next")
async def product_next(cb: types.CallbackQuery, state: FSMContext):
    await cb.message.edit_reply_markup()
    data           = await state.get_data()
    catalog_name   = data.get("last_catalog_name", "")
    rejected_names = set(data.get("rejected_names", []))
    extra_query    = data.get("extra_query", "")
    photo_bytes    = bytes.fromhex(data.get("photo_bytes", ""))
    if catalog_name:
        rejected_names.add(catalog_name.lower())
    await state.update_data(rejected_names=list(rejected_names))
    error_hint = f"товар '{catalog_name}' не підходить" if catalog_name else ""
    results = await dossier_search(photo_bytes, extra_query=extra_query,
                                    rejected_names=rejected_names, error_hint=error_hint)
    await present_search_results(cb.message, state, results)


@dp.callback_query(Order.confirm_product, F.data == "prod_refine")
async def product_refine(cb: types.CallbackQuery, state: FSMContext):
    await cb.message.edit_reply_markup()
    await state.set_state(Order.refine_search)
    await cb.message.answer("✏️ Уточни: бренд, колір, матеріал (фліс/двунитка/трикотаж):")


@dp.message(Order.refine_search)
async def refine_query(msg: types.Message, state: FSMContext):
    data           = await state.get_data()
    photo_bytes    = bytes.fromhex(data.get("photo_bytes", ""))
    rejected_names = set(data.get("rejected_names", []))
    extra_query    = msg.text.strip()
    await state.update_data(extra_query=extra_query)
    results = await dossier_search(photo_bytes, extra_query=extra_query, rejected_names=rejected_names)
    await present_search_results(msg, state, results)


@dp.callback_query(Order.confirm_product, F.data == "prod_manual")
async def product_manual(cb: types.CallbackQuery, state: FSMContext):
    await cb.message.edit_reply_markup()
    await state.set_state(Order.manual_search)
    await cb.message.answer("🔍 Введи пошуковий запит:")


@dp.callback_query(Order.confirm_ambiguous, F.data.startswith("amb_"))
async def ambiguous_pick(cb: types.CallbackQuery, state: FSMContext):
    await cb.message.edit_reply_markup()
    raw = cb.data[4:]
    if raw == "manual":
        await state.set_state(Order.manual_search)
        await cb.message.answer("🔍 Введи пошуковий запит:")
        return
    data    = await state.get_data()
    results = data.get("ambiguous_results", [])
    found   = results[int(raw)]
    ph      = data.get("photo_hash")
    api_products = await fetch_api_products()
    api_product  = find_api_product_by_name(found["name"], api_products)
    product      = api_product or {"title": found["name"], "sku": found.get("sku",""), "id": None}
    if ph:
        await db_save_learned(ph, product)
    await state.update_data(selected_product=product, last_catalog_name=found["name"])
    await proceed_to_ds(cb.message, state)


# ══════════════════════════════════════════════
# Ручний пошук
# ══════════════════════════════════════════════
@dp.message(Order.manual_search)
async def manual_search_query(msg: types.Message, state: FSMContext):
    matches = smart_search(msg.text.strip(), _photo_catalog)
    if not matches:
        await msg.answer("❌ Нічого не знайдено.", parse_mode="HTML")
        return
    await state.update_data(search_results=matches)
    await msg.answer(f"🔍 Знайдено {len(matches)} товарів:", reply_markup=kb_items(matches))


@dp.callback_query(Order.manual_search, F.data.startswith("pick_"))
async def manual_pick(cb: types.CallbackQuery, state: FSMContext):
    await cb.message.edit_reply_markup()
    raw = cb.data[5:]
    if raw == "manual":
        await cb.message.answer("✏️ Введи інший запит:")
        return
    data    = await state.get_data()
    results = data.get("search_results", [])
    idx     = int(raw)
    if idx >= len(results):
        await cb.message.answer("❌ Помилка.")
        return
    item         = results[idx]
    api_products = await fetch_api_products()
    api_product  = find_api_product_by_name(item["name"], api_products)
    product      = api_product or {"title": item["name"], "sku": item.get("sku",""), "id": None}
    ph           = data.get("photo_hash")
    if ph:
        await db_save_learned(ph, product)
    await state.update_data(selected_product=product)
    await proceed_to_ds(cb, state)


# ══════════════════════════════════════════════
# Multi callbacks
# ══════════════════════════════════════════════
@dp.callback_query(Order.confirm_multi, F.data == "multi_yes")
async def multi_yes(cb: types.CallbackQuery, state: FSMContext):
    await cb.message.edit_reply_markup()
    data      = await state.get_data()
    products  = data.get("multi_products", [])
    idx       = data.get("multi_idx", 0)
    confirmed = data.get("confirmed_products", [])
    item      = products[idx]
    ph        = item.get("photo_hash")
    product   = item.get("api_product", {})
    if ph:
        await db_save_learned(ph, product)
    confirmed.append(product)
    next_idx = idx + 1
    await state.update_data(confirmed_products=confirmed, multi_idx=next_idx)
    if next_idx >= len(products):
        await proceed_to_ds(cb.message, state)
    else:
        await state.set_state(Order.confirm_multi)
        await show_multi_confirm(cb.message, state, next_idx, products)


@dp.callback_query(Order.confirm_multi, F.data == "multi_next")
async def multi_next(cb: types.CallbackQuery, state: FSMContext):
    await cb.message.edit_reply_markup()
    data           = await state.get_data()
    products       = data.get("multi_products", [])
    idx            = data.get("multi_idx", 0)
    rejected_names = set(data.get("rejected_names", []))
    item           = products[idx]
    current_name   = (item.get("api_product") or {}).get("title") or ""
    if current_name:
        rejected_names.add(current_name.lower())
    await state.update_data(rejected_names=list(rejected_names))
    photo_bytes_hex = item.get("photo_bytes_hex") or ""
    if not photo_bytes_hex:
        await state.set_state(Order.manual_search_multi)
        await cb.message.answer("🔍 Введи пошуковий запит:")
        return
    error_hint = f"товар '{current_name}' не підходить" if current_name else ""
    results = await dossier_search(bytes.fromhex(photo_bytes_hex),
                                    rejected_names=rejected_names, error_hint=error_hint)
    if results:
        found        = results[0]
        api_products = await fetch_api_products()
        api_product  = find_api_product_by_name(found["name"], api_products)
        product      = api_product or {"title": found["name"], "sku": found.get("sku",""), "id": None}
        products[idx]["api_product"] = product
        await state.update_data(multi_products=products)
        await state.set_state(Order.confirm_multi)
        await cb.message.answer(
            f"📦 <b>Товар {idx+1} (новий варіант):</b>\n\n🟢 <b>{found['name']}</b>\n🔑 SKU: {found.get('sku') or '—'}\n\nЦе правильний товар?",
            parse_mode="HTML", reply_markup=kb_confirm_multi()
        )
    else:
        await state.set_state(Order.manual_search_multi)
        await cb.message.answer("❌ Не знайшов. Введи запит вручну:")


@dp.callback_query(Order.confirm_multi, F.data == "multi_refine")
async def multi_refine(cb: types.CallbackQuery, state: FSMContext):
    await cb.message.edit_reply_markup()
    await state.set_state(Order.refine_multi)
    await cb.message.answer("✏️ Уточни: бренд, колір, матеріал:")


@dp.message(Order.refine_multi)
async def refine_multi_query(msg: types.Message, state: FSMContext):
    data            = await state.get_data()
    products        = data.get("multi_products", [])
    idx             = data.get("multi_idx", 0)
    rejected_names  = set(data.get("rejected_names", []))
    extra_query     = msg.text.strip()
    item            = products[idx]
    photo_bytes_hex = item.get("photo_bytes_hex") or ""
    if not photo_bytes_hex:
        await state.set_state(Order.manual_search_multi)
        await msg.answer("🔍 Введи запит вручну:")
        return
    results = await dossier_search(bytes.fromhex(photo_bytes_hex),
                                    extra_query=extra_query, rejected_names=rejected_names)
    if results:
        found        = results[0]
        api_products = await fetch_api_products()
        api_product  = find_api_product_by_name(found["name"], api_products)
        product      = api_product or {"title": found["name"], "sku": found.get("sku",""), "id": None}
        products[idx]["api_product"] = product
        await state.update_data(multi_products=products)
        await state.set_state(Order.confirm_multi)
        await msg.answer(
            f"📦 <b>Товар {idx+1}:</b>\n\n🟢 <b>{found['name']}</b>\n🔑 SKU: {found.get('sku') or '—'}\n\nЦе правильний товар?",
            parse_mode="HTML", reply_markup=kb_confirm_multi()
        )
    else:
        await state.set_state(Order.manual_search_multi)
        await msg.answer("❌ Не знайдено. Введи запит вручну:")


@dp.callback_query(Order.confirm_multi, F.data == "multi_manual")
async def multi_manual(cb: types.CallbackQuery, state: FSMContext):
    await cb.message.edit_reply_markup()
    await state.set_state(Order.manual_search_multi)
    await cb.message.answer("🔍 Введи пошуковий запит:")


@dp.message(Order.manual_search_multi)
async def manual_search_multi(msg: types.Message, state: FSMContext):
    matches = smart_search(msg.text.strip(), _photo_catalog)
    if not matches:
        await msg.answer("❌ Нічого не знайдено. Спробуй ще.")
        return
    await state.update_data(search_results_multi=matches)
    buttons = [[InlineKeyboardButton(text=item["name"][:55], callback_data=f"mpick_{i}")]
               for i, item in enumerate(matches[:8])]
    await msg.answer("🔍 Знайдено:", reply_markup=InlineKeyboardMarkup(inline_keyboard=buttons))


@dp.callback_query(Order.manual_search_multi, F.data.startswith("mpick_"))
async def manual_pick_multi(cb: types.CallbackQuery, state: FSMContext):
    await cb.message.edit_reply_markup()
    data      = await state.get_data()
    results   = data.get("search_results_multi", [])
    prod_idx  = data.get("multi_idx", 0)
    products  = data.get("multi_products", [])
    confirmed = data.get("confirmed_products", [])
    item      = results[int(cb.data[6:])]
    api_prods = await fetch_api_products()
    api_prod  = find_api_product_by_name(item["name"], api_prods)
    product   = api_prod or {"title": item["name"], "sku": item.get("sku",""), "id": None}
    ph = products[prod_idx].get("photo_hash")
    if ph:
        await db_save_learned(ph, product)
    confirmed.append(product)
    next_idx = prod_idx + 1
    await state.update_data(confirmed_products=confirmed, multi_idx=next_idx)
    if next_idx >= len(products):
        await proceed_to_ds(cb.message, state)
    else:
        await state.set_state(Order.confirm_multi)
        await show_multi_confirm(cb.message, state, next_idx, products)


# ══════════════════════════════════════════════
# Вибір міста НП
# ══════════════════════════════════════════════
@dp.callback_query(Order.ask_city, F.data.startswith("city_"))
async def city_picked(cb: types.CallbackQuery, state: FSMContext):
    await cb.message.edit_reply_markup()
    data   = await state.get_data()
    cities = data.get("np_cities", [])
    idx    = int(cb.data[5:])
    city   = cities[idx]
    await state.update_data(city_ref=city["city_ref"], city_name=city["name"],
                            city_short=city.get("short_name", city["name"]))
    await proceed_to_warehouse(cb.message, state)


@dp.message(Order.ask_city)
async def city_entered(msg: types.Message, state: FSMContext):
    cities = await np_search_city(msg.text.strip())
    if not cities:
        await msg.answer("❌ Місто не знайдено. Спробуй ще раз:")
        return
    if len(cities) == 1:
        await state.update_data(city_ref=cities[0]["city_ref"], city_name=cities[0]["name"],
                                city_short=cities[0].get("short_name", cities[0]["name"]))
        await proceed_to_warehouse(msg, state)
        return
    await state.update_data(np_cities=cities)
    buttons = [[InlineKeyboardButton(text=c["name"][:60], callback_data=f"city_{i}")]
               for i, c in enumerate(cities)]
    await msg.answer("🏙 Вибери місто:", reply_markup=InlineKeyboardMarkup(inline_keyboard=buttons))


# ══════════════════════════════════════════════
# Вибір відділення НП
# ══════════════════════════════════════════════
@dp.callback_query(Order.ask_warehouse, F.data.startswith("wh_"))
async def warehouse_picked(cb: types.CallbackQuery, state: FSMContext):
    await cb.message.edit_reply_markup()
    raw = cb.data[3:]
    if raw == "manual":
        await state.set_state(Order.ask_warehouse)
        await cb.message.answer("✏️ Введи номер відділення НП:")
        return
    data       = await state.get_data()
    warehouses = data.get("np_warehouses", [])
    idx        = int(raw)
    wh         = warehouses[idx]
    order      = data.get("order", {})
    # Зберігаємо коректний номер — тільки цифри якщо є, інакше "1"
    wh_num = wh.get("num_digits") or wh.get("number") or ""
    order["warehouse"] = wh_num
    await state.update_data(
        warehouse_ref=wh["ref"],
        warehouse_name=wh["name"],
        warehouse_number=wh_num,
        order=order,
    )
    log.info(f"Вибрано відділення: {wh['name']} ref={wh['ref'][:8] if wh['ref'] else '—'} num={wh_num}")
    await proceed_to_dropshipper(cb.message, state)


@dp.message(Order.ask_warehouse)
async def warehouse_entered(msg: types.Message, state: FSMContext):
    data       = await state.get_data()
    city_ref   = data.get("city_ref", "")
    num        = msg.text.strip()
    warehouses = await np_search_warehouse(city_ref, num)
    if warehouses and warehouses[0]["ref"]:
        wh     = warehouses[0]
        wh_num = wh.get("num_digits") or wh.get("number") or num
        order  = data.get("order", {})
        order["warehouse"] = wh_num
        await state.update_data(warehouse_ref=wh["ref"], warehouse_name=wh["name"],
                                warehouse_number=wh_num, order=order)
        await proceed_to_dropshipper(msg, state)
    else:
        await msg.answer(
            "❌ <b>Відділення не знайдено в Новій Пошті.</b>\n\n"
            "Перевір номер і спробуй ще раз, або вибери зі списку вище.",
            parse_mode="HTML"
        )


# ══════════════════════════════════════════════
# Дропшипер
# ══════════════════════════════════════════════
@dp.callback_query(Order.ask_ds_choice, F.data.startswith("ds_"))
async def ds_picked(cb: types.CallbackQuery, state: FSMContext):
    await cb.message.edit_reply_markup()
    raw = cb.data[3:]
    if raw == "manual":
        await state.set_state(Order.ask_ds_id)
        await cb.message.answer("✏️ Введи ID дропшипера:")
        return
    if raw == "none":
        data  = await state.get_data()
        order = data["order"]
        order["ds_id"] = None
        await state.update_data(order=order)
        await show_final_confirm(cb.message, state)
        return
    data = await state.get_data()
    order = data["order"]
    order["ds_id"] = int(raw)
    await state.update_data(order=order)
    await show_final_confirm(cb.message, state)


@dp.message(Order.ask_ds_id)
async def ds_entered(msg: types.Message, state: FSMContext):
    try:
        ds_id = int(msg.text.strip())
    except ValueError:
        await msg.answer("⚠️ Введи числовий ID: <code>42</code>", parse_mode="HTML")
        return
    data = await state.get_data()
    order = data["order"]
    order["ds_id"] = ds_id
    await state.update_data(order=order)
    await show_final_confirm(msg, state)


# ══════════════════════════════════════════════
# Відправка замовлення
# ══════════════════════════════════════════════
@dp.callback_query(Order.final_confirm, F.data == "final_yes")
async def final_submit(cb: types.CallbackQuery, state: FSMContext):
    await cb.message.edit_reply_markup()
    data  = await state.get_data()
    order = data["order"]

    # ── Жорстка валідація — без рефів не відправляємо ──
    missing = []
    if not data.get("city_ref"):
        missing.append("🏙 місто не вибрано зі списку НП")
    if not data.get("warehouse_ref"):
        missing.append("🏢 відділення не вибрано зі списку НП")
    if missing:
        await cb.message.answer(
            "❌ <b>Замовлення не відправлено!</b>\n\n"
            "Не вдалось вибрати зі списку:\n"
            + "\n".join(f"• {m}" for m in missing)
            + "\n\n⚠️ Бот нічого не вписує сам — всі поля мають бути вибрані зі списку. "
            "Скажи менеджеру оформити це замовлення вручну в МийДроп.",
            parse_mode="HTML"
        )
        await state.clear()
        return

    notice = await cb.message.answer("⏳ Відправляю в МійДроп...")
    confirmed     = data.get("confirmed_products")
    products_list = confirmed if confirmed else [data.get("selected_product", {})]
    products_payload = []
    base_price = int(order["cod"]) if order["cod"] > 0 else int(order.get("price") or 0)
    sizes       = order.get("sizes")
    child_sizes = order.get("child_sizes")
    amount      = order.get("amount", 1) or 1

    for p in products_list:
        base_item = {"amount": 1, "price": base_price}
        if p.get("sku"):
            base_item["sku"] = p["sku"]
        else:
            base_item["title"] = p.get("title") or p.get("name", "")

        # ── Комплект: перевіряємо child_products ──
        product_id = p.get("id")
        children   = []
        if product_id:
            children = await fetch_child_products(product_id)

        if children:
            child_items = []
            size = order.get("size") or ""
            for c in children:
                c_title_lower = c["title"].lower()
                chosen_size   = None

                # Якщо є child_sizes — шукаємо збіг по назві складової
                if child_sizes:
                    for key, sz in child_sizes.items():
                        if key.lower() in c_title_lower or c_title_lower in key.lower():
                            chosen_size = sz
                            break

                # Fallback: стандартна логіка по available_sizes
                if not chosen_size:
                    available       = c.get("available_sizes", [])
                    available_lower = [s.lower() for s in available]
                    if size and size.lower() in available_lower:
                        chosen_size = available[available_lower.index(size.lower())]
                    elif any("універс" in s.lower() for s in available_lower):
                        chosen_size = next(s for s in available if "універс" in s.lower())
                    elif available:
                        chosen_size = available[0]
                    else:
                        chosen_size = size

                child_items.append({"title": c["title"], "size_title": chosen_size})
                log.info(f"  Складова: '{c['title']}' розмір: '{chosen_size}'")

            base_item["child_products"] = child_items
            log.info(f"Комплект: {len(children)} складових для '{p.get('title')}'")
            products_payload.append(base_item)

        elif sizes and len(sizes) > 1:
            # Кілька різних розмірів → окремий рядок на кожен розмір
            for sz in sizes:
                item = dict(base_item)
                item["size_title"] = sz
                item["amount"]     = 1
                products_payload.append(item)
            log.info(f"Multi-size: {sizes} для '{p.get('title') or p.get('name')}'")

        else:
            # Один розмір (можлива кількість > 1)
            size = order.get("size") or ""
            if size and size != "-":
                base_item["size_title"] = size
            base_item["amount"] = amount
            products_payload.append(base_item)
    cod           = int(order["cod"])
    city_ref      = data.get("city_ref") or ""
    warehouse_ref = data.get("warehouse_ref") or ""
    city_name     = data.get("city_name") or order.get("city") or ""
    city_short    = data.get("city_short") or city_name.split(",")[0].strip()
    # warehouse_number — тільки цифри, ніякого тексту опису
    warehouse_num = data.get("warehouse_number") or ""
    try:
        warehouse_num = str(int("".join(filter(str.isdigit, str(warehouse_num))))) if warehouse_num else ""
    except Exception:
        warehouse_num = ""

    order_payload = {
        "name":             order["name"],
        "phone":            order["phone"],
        "products":         products_payload,
        "city":             city_short,        # коротка назва для тексту
        "warehouse_number": warehouse_num,     # тільки число
        "city_ref":         city_ref,          # UUID — МийДроп бере в першу чергу
        "warehouse_ref":    warehouse_ref,     # UUID — МийДроп бере в першу чергу
        "delivery_service": "nova_poshta",
        "delivery_payment": cod,
        "dropshipper_id":   int(order["ds_id"]) if order.get("ds_id") else None,
        "prepay_amount":    0 if cod > 0 else int(order.get("price") or 0),
    }
    log.info(f"МийДроп payload city='{city_short}' city_ref={city_ref[:8] if city_ref else '—'} wh_ref={warehouse_ref[:8] if warehouse_ref else '—'} wh_num='{warehouse_num}'")
    result, status = await api_create_order(order_payload)
    await notice.delete()
    if status in (200, 201):
        idx    = result.get("index") or result.get("id", "?")
        prepay = " (передплата)" if order["cod"] == 0 else ""
        names  = "\n".join(f"📦 {p.get('title') or p.get('name','?')}" for p in products_list)
        await cb.message.answer(
            f"✅ <b>Замовлення #{idx} створено!</b>\n\n{names}\n"
            f"👤 {order['name']} · {order['phone']}\n"
            f"🏙 {order['city']}, відд. {order['warehouse']}\n"
            f"💰 {int(order['cod'])} грн{prepay} · Дропшипер ID {order['ds_id']}\n\n"
            "Надсилай наступне замовлення!", parse_mode="HTML"
        )
    else:
        err = result.get("message") or result.get("error") or json.dumps(result, ensure_ascii=False)
        await cb.message.answer(f"❌ <b>Помилка МійДроп:</b>\n<code>{err}</code>", parse_mode="HTML")
    await state.clear()


@dp.callback_query(Order.final_confirm, F.data == "final_no")
async def final_cancel(cb: types.CallbackQuery, state: FSMContext):
    await cb.message.edit_reply_markup()
    await state.clear()
    await cb.message.answer("❌ Скасовано.")


# ══════════════════════════════════════════════
# Документ XLSX
# ══════════════════════════════════════════════
@dp.message(F.document)
async def handle_document(msg: types.Message, state: FSMContext):
    global _photo_catalog
    doc      = msg.document
    filename = doc.file_name or ""
    mime     = doc.mime_type or ""
    if not (filename.endswith('.xlsx') or filename.endswith('.zip') or 'spreadsheet' in mime):
        await msg.answer("📎 Надішли XLSX або ZIP файл.")
        return
    notice = await msg.answer("⏳ Обробляю файл...")
    try:
        file = await bot.get_file(doc.file_id)
        url  = f"https://api.telegram.org/file/bot{TELEGRAM_TOKEN}/{file.file_path}"
        async with aiohttp.ClientSession() as s:
            async with s.get(url) as r:
                file_bytes = await r.read()
        if filename.endswith('.zip'):
            import zipfile
            with zipfile.ZipFile(io.BytesIO(file_bytes)) as zf:
                xlsx_names = [n for n in zf.namelist() if n.endswith('.xlsx')]
                if not xlsx_names:
                    await notice.edit_text("❌ В ZIP немає XLSX.")
                    return
                xlsx_bytes = zf.read(xlsx_names[0])
        else:
            xlsx_bytes = file_bytes
        catalog = build_catalog_from_xlsx(xlsx_bytes)
        _photo_catalog = [{"name": c["name"], "sku": c["sku"], "photo_url": ""} for c in catalog]
        await notice.edit_text(f"✅ <b>Каталог оновлено! {len(_photo_catalog)} товарів.</b>", parse_mode="HTML")
    except Exception as e:
        await notice.edit_text(f"❌ Помилка: {e}")


# ══════════════════════════════════════════════
# Запуск
# ══════════════════════════════════════════════
async def main():
    await init_db()
    await load_dossiers_cache()
    catalog = await build_api_catalog_index()
    log.info(f"Каталог: {len(catalog)} товарів")
    if not _dossier_cache:
        log.warning("⚠️ Досьє не знайдені! Запусти: python generate_dossiers.py")
    log.info("Бот запускається...")
    await dp.start_polling(bot, skip_updates=True)


if __name__ == "__main__":
    asyncio.run(main())
