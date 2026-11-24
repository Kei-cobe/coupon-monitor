#!/usr/bin/env python3
"""手机端优惠券与奶茶/甜点活动监控器（仅使用 Python 标准库）。"""

from __future__ import annotations

import argparse
import base64
import concurrent.futures
import hashlib
import html
import http.client
import json
import os
import re
import smtplib
import socket
import sqlite3
import ssl
import sys
import threading
import time
import urllib.error
import urllib.parse
import urllib.request
import xml.etree.ElementTree as ET
from dataclasses import dataclass
from datetime import date, datetime, timedelta, timezone
from email.message import EmailMessage
from email.utils import parsedate_to_datetime
from html.parser import HTMLParser
from pathlib import Path
from typing import Any, Iterable

UTC = timezone.utc
CATEGORY_LABELS = {
    "free": "免单/免费",
    "bogo": "买一送一",
    "second_half": "第二杯半价",
    "big_coupon": "大额券",
    "low_price": "个位数低价",
    "collab": "联名/联动",
    "coupon": "优惠券/红包",
}
STATUS_LABELS = {
    "active": "进行中",
    "upcoming": "即将开始",
    "expired": "已结束",
    "unknown": "日期待核验",
}
HIGH_VALUE = {"free", "bogo", "second_half", "big_coupon", "low_price", "collab"}
TRACKING_KEYS = {
    "from", "from_source", "share_source", "share_token", "spm", "scm",
    "ref", "source", "timestamp", "sign", "signature", "_t",
}


def utc_now() -> datetime:
    return datetime.now(UTC).replace(microsecond=0)


def isoformat(value: datetime) -> str:
    if value.tzinfo is None:
        value = value.replace(tzinfo=UTC)
    return value.astimezone(UTC).isoformat()


def parse_datetime(value: str | None) -> datetime | None:
    if not value:
        return None
    try:
        parsed = datetime.fromisoformat(value.replace("Z", "+00:00"))
        return parsed.replace(tzinfo=parsed.tzinfo or UTC).astimezone(UTC)
    except (TypeError, ValueError):
        return None


class _TextParser(HTMLParser):
    def __init__(self) -> None:
        super().__init__()
        self.parts: list[str] = []

    def handle_data(self, data: str) -> None:
        self.parts.append(data)


def plain_text(value: str | None) -> str:
    parser = _TextParser()
    parser.feed(value or "")
    parser.close()
    return re.sub(r"\s+", " ", html.unescape(" ".join(parser.parts))).strip()


def clean_url(value: str) -> str:
    """清理分享追踪参数，并尝试还原 Bing 跳转链接。"""
    value = html.unescape((value or "").strip())
    if not value:
        return ""
    try:
        parsed = urllib.parse.urlsplit(value)
        host = (parsed.hostname or "").lower()
        query = urllib.parse.parse_qsl(parsed.query, keep_blank_values=True)
        if host.endswith("bing.com") and parsed.path.startswith("/ck/"):
            encoded = dict(query).get("u", "")
            if encoded.startswith("a1"):
                payload = encoded[2:]
                payload += "=" * (-len(payload) % 4)
                try:
                    decoded = base64.urlsafe_b64decode(payload).decode("utf-8")
                    if decoded.startswith(("http://", "https://")):
                        return clean_url(decoded)
                except (ValueError, UnicodeDecodeError):
                    pass
        kept = [
            (key, val) for key, val in query
            if not key.lower().startswith("utm_") and key.lower() not in TRACKING_KEYS
        ]
        netloc = parsed.netloc.lower()
        return urllib.parse.urlunsplit((
            parsed.scheme.lower(), netloc, parsed.path,
            urllib.parse.urlencode(sorted(kept), doseq=True), "",
        ))
    except (ValueError, UnicodeError):
        return value


def parse_rss(payload: bytes) -> list[dict[str, str]]:
    root = ET.fromstring(payload)
    results: list[dict[str, str]] = []
    for node in root.findall(".//item"):
        def field(name: str) -> str:
            child = node.find(name)
            return "" if child is None or child.text is None else child.text.strip()

        results.append({
            "title": plain_text(field("title")),
            "link": clean_url(field("link")),
            "summary": plain_text(field("description")),
            "published": field("pubDate"),
        })
    return results


def published_datetime(value: str) -> datetime | None:
    if not value:
        return None
    try:
        parsed = parsedate_to_datetime(value)
        return parsed.replace(tzinfo=parsed.tzinfo or UTC).astimezone(UTC)
    except (TypeError, ValueError, OverflowError):
        return parse_datetime(value)


def _valid_date(year: int, month: int, day: int) -> date | None:
    try:
        return date(year, month, day)
    except ValueError:
        return None


def extract_dates(text: str, now: datetime) -> tuple[date | None, date | None]:
    """提取中文/数字日期；不把价格后的“元”误识别为日期。"""
    pattern = re.compile(
        r"(?:(?P<year>20\d{2})\s*(?:年|[-/.])\s*)?"
        r"(?P<month>\d{1,2})\s*(?:月|[-/.])\s*(?P<day>\d{1,2})\s*日?"
    )
    found: list[tuple[date, bool, re.Match[str]]] = []
    today = now.astimezone().date()
    for match in pattern.finditer(text):
        if text[match.end():match.end() + 1] == "元" or text[max(0, match.start() - 1):match.start()] in {"¥", "￥"}:
            continue
        month, day = int(match.group("month")), int(match.group("day"))
        explicit_year = match.group("year") is not None
        year = int(match.group("year") or today.year)
        parsed = _valid_date(year, month, day)
        if not parsed:
            continue
        if not explicit_year and parsed < today - timedelta(days=180):
            parsed = date(year + 1, month, day)
        found.append((parsed, explicit_year, match))

    if not found:
        return None, None
    if len(found) >= 2:
        start, end = found[0][0], found[1][0]
        if end < start and not found[1][1]:
            try:
                end = date(end.year + 1, end.month, end.day)
            except ValueError:
                end = date(end.year + 1, end.month, 28)
        return (start, end) if start <= end else (end, start)

    only, _, match = found[0]
    before = text[max(0, match.start() - 10):match.start()]
    after = text[match.end():match.end() + 10]
    if re.search(r"截止|截至|结束|到期|至\s*$|到\s*$", before):
        return None, only
    if re.search(r"开始|开启|上线|发售|上市|起\s*$|自\s*$|从\s*$", before) or re.search(
        r"开始|开启|上线|发售|上市", after
    ):
        return only, None
    return (only, None) if only >= today else (None, only)


def activity_status(start: date | None, end: date | None, now: datetime) -> str:
    today = now.astimezone().date()
    if start and today < start:
        return "upcoming"
    if end and today > end:
        return "expired"
    if start or end:
        return "active"
    return "unknown"


def coupon_amount(text: str) -> float | None:
    values: list[float] = []
    patterns = [
        r"满\s*\d+(?:\.\d+)?\s*减\s*(\d+(?:\.\d+)?)\s*元?",
        r"(?:立减|减|抵扣)\s*(\d+(?:\.\d+)?)\s*元",
        r"(\d+(?:\.\d+)?)\s*元(?:无门槛)?(?:优惠券|券|红包|代金券)",
    ]
    for pattern in patterns:
        values.extend(float(value) for value in re.findall(pattern, text))
    return max(values) if values else None


def low_price(text: str) -> float | None:
    prices: list[float] = []
    pattern = re.compile(
        r"(?P<prefix>到手价?|售价|仅需|只要|每杯|单价|秒杀价|低价)?\s*"
        r"(?P<amount>\d+(?:\.\d+)?)\s*元"
        r"(?P<suffix>/杯|一杯|起|购|秒杀|喝|吃)?"
    )
    for match in pattern.finditer(text):
        prefix, suffix = match.group("prefix"), match.group("suffix")
        raw = match.group("amount")
        if not prefix and not suffix and "." not in raw:
            continue
        before = text[max(0, match.start() - 3):match.start()]
        after = text[match.end():match.end() + 3]
        if re.search(r"券|红包|立减|抵扣", after) or re.search(r"满|减|领", before):
            continue
        value = float(raw)
        if 0 < value < 10000:
            prices.append(value)
    return min(prices) if prices else None


def collaboration(text: str, names: Iterable[str]) -> str:
    partners: list[str] = []
    patterns = [
        r"(?:与|和|携手)\s*([^，。；;！!？?\s]{2,24})(?:联名|联动|合作|推出)",
        r"(?:×|x|X)\s*([^，。；;！!？?\s]{2,24})",
    ]
    for name in names:
        if name:
            patterns.append(
                re.escape(name) + r"\s*(?:联名|联动)\s*([^，。；;！!？?\s]{2,24})"
            )
    ignored = {"活动", "新品", "周边", "套餐", "系列", "官宣", "合作"}
    for pattern in patterns:
        for value in re.findall(pattern, text):
            value = value.strip("《》<>：:，,。 ")
            if value and value not in ignored and value not in partners:
                partners.append(value)
    return "、".join(partners[:2])


def extract_claims(text: str) -> str:
    """从原文提取可执行的领取线索：搜索口令、兑换码、活动入口。"""
    claims: list[str] = []

    def add(value: str) -> None:
        value = value.strip(" ，。；;、")
        if value and value not in claims and len(claims) < 3:
            claims.append(value)

    search_pattern = re.compile(
        r"(?P<app>淘宝闪购|淘宝|天猫|京东秒送|京东|美团外卖|美团|饿了么|拼多多|抖音|大众点评|口碑)?"
        r"\s*(?:APP|App|app|小程序|客户端)?\s*(?:内|里|中|首页)?\s*"
        r"(?:搜索|搜|输入|搜一搜)\s*[【\[“\"']?(?P<code>[A-Za-z0-9一-龥]{2,24})[】\]”\"']?"
    )
    for match in search_pattern.finditer(text):
        code = match.group("code").strip("【】[]“”\"'")
        if code in {"活动", "优惠券", "红包", "领券", "免单", "外卖", "奶茶"}:
            continue
        app = match.group("app") or ""
        add(f"{app + ' ' if app else ''}搜索【{code}】")

    for match in re.finditer(
        r"(?:口令|邀请码|兑换码|优惠码|密令)\s*(?:是|为|[:：])?\s*[【\[“\"']?([A-Za-z0-9￥$一-龥]{3,24})[】\]”\"']?",
        text,
    ):
        add(f"口令/兑换码：{match.group(1)}")

    for match in re.finditer(
        r"(?:活动入口|领取入口|领券入口|抽奖入口|参与入口)\s*(?:是|为|[:：])?\s*[【\[“\"']?([^，。；;！!？?\s】\]”\"']{2,40})",
        text,
    ):
        add(f"活动入口：{match.group(1)}")
    return "；".join(claims)


def sanitize_dates(start: date | None, end: date | None, published: datetime | None, now: datetime) -> tuple[date | None, date | None]:
    """剔除不合理日期：超过一年后的日期，以及老文章里被错误顺延到来年的日期。"""
    today = now.astimezone().date()
    horizon = today + timedelta(days=366)
    if start and start > horizon:
        start = None
    if end and end > horizon:
        end = None
    if published:
        limit = published.astimezone().date() + timedelta(days=400)
        if start and start > limit:
            start = None
        if end and end > limit:
            end = None
    return start, end


def is_navigation_page(title: str, link: str) -> bool:
    """过滤站点导航页、频道首页等不含具体活动的页面。"""
    if title.count("_") >= 2 or title.count(" | ") >= 2:
        return True
    path = urllib.parse.urlsplit(link).path
    if path in {"", "/"} and not re.search(r"\d", title):
        return True
    return bool(re.search(r"(首页|官网|官方网站|频道页)$", title) and len(title) < 30)


@dataclass
class Activity:
    fingerprint: str
    kind: str
    target: str
    title: str
    summary: str
    link: str
    categories: list[str]
    amount: float | None
    price: float | None
    start_date: date | None
    end_date: date | None
    collab: str
    source: str
    status: str
    official: bool
    published_at: datetime | None
    score: int
    first_seen: datetime
    is_new: bool = False
    claim: str = ""


def activity_score(categories: list[str], status: str, official: bool, published: datetime | None, now: datetime) -> int:
    if status == "expired":
        return -100
    score = {"active": 50, "upcoming": 30, "unknown": 5}.get(status, 0)
    score += sum({
        "free": 90, "bogo": 70, "second_half": 55, "big_coupon": 60,
        "low_price": 50, "collab": 45, "coupon": 20,
    }.get(category, 0) for category in categories)
    if official:
        score += 20
    if published and timedelta(0) <= now - published <= timedelta(days=3):
        score += 10
    return score


def make_activity(raw: dict[str, str], kind: str, target: dict[str, Any], settings: dict[str, Any], now: datetime) -> Activity | None:
    title, summary = raw.get("title", ""), raw.get("summary", "")
    link = clean_url(raw.get("link", ""))
    text = f"{title} {summary}"
    names = [target["name"], *target.get("aliases", [])]
    if not title or not any(name.lower() in text.lower() for name in names):
        return None

    categories: list[str] = []
    if re.search(r"免单|0\s*元|免费喝|免费领|免费吃", text):
        categories.append("free")
    if re.search(r"买一\s*[送赠]\s*一|买\s*1\s*[送赠]\s*1", text, re.I):
        categories.append("bogo")
    if re.search(r"第[二2]杯半价|第[二2]件半价", text):
        categories.append("second_half")
    if re.search(r"联名|联动|跨界合作|携手.*(?:合作|推出)|\s[xX×]\s", text):
        categories.append("collab")
    amount = coupon_amount(text)
    if amount is not None and amount >= float(settings.get("big_coupon_threshold", 10)):
        categories.append("big_coupon")
    price = low_price(text)
    if price is not None and price < float(settings.get("low_price_threshold", 10)):
        categories.append("low_price")
    if amount is not None or re.search(r"优惠券|领券|红包|满\s*\d+\s*减|立减", text):
        categories.append("coupon")
    categories = list(dict.fromkeys(categories))
    if not categories:
        return None

    published = published_datetime(raw.get("published", ""))
    claim = extract_claims(text)
    start, end = sanitize_dates(*extract_dates(text, now), published, now)
    status = activity_status(start, end, now)
    today = now.astimezone().date()
    still_valid = bool(end and end >= today)
    evergreen = bool(claim) and (end is None or still_valid)
    if status == "expired":
        return None
    if published and now - published > timedelta(days=1) and not evergreen and not still_valid:
        return None
    if is_navigation_page(title, link):
        return None
    specific = bool(claim or amount is not None or price is not None or start or end)
    if not specific and set(categories) <= {"coupon"}:
        return None
    source = (urllib.parse.urlsplit(link).hostname or "未知来源").lower()
    official_domains = [domain.lower() for domain in target.get("official_domains", [])]
    official = any(source == domain or source.endswith("." + domain) for domain in official_domains)
    if not official and source in {"weibo.com", "www.weibo.com", "mp.weixin.qq.com"}:
        official = "官方" in title and target["name"] in title
    stable = link or re.sub(r"\s+", "", f"{title}|{start or ''}")
    fingerprint = hashlib.sha256(f"{kind}|{target['name']}|{stable}".encode("utf-8")).hexdigest()
    return Activity(
        fingerprint=fingerprint, kind=kind, target=target["name"], title=title,
        summary=summary, link=link, categories=categories, amount=amount, price=price,
        start_date=start, end_date=end, collab=collaboration(text, names) if "collab" in categories else "",
        source=source, status=status, official=official, published_at=published,
        score=activity_score(categories, status, official, published, now),
        first_seen=now, claim=claim,
    )


class CouponMonitor:
    def __init__(self, config: dict[str, Any], db_path: str | Path) -> None:
        self.config = config
        self.settings = config.get("settings", {})
        self.db_path = Path(db_path).expanduser().resolve()
        self.db_path.parent.mkdir(parents=True, exist_ok=True)
        self.db = sqlite3.connect(self.db_path)
        self.db.row_factory = sqlite3.Row
        self.item_scopes: dict[str, set[str]] = {}
        self._lock = threading.Lock()
        self.db.executescript("""
            CREATE TABLE IF NOT EXISTS items (
                fingerprint TEXT PRIMARY KEY,
                kind TEXT NOT NULL,
                target TEXT NOT NULL,
                title TEXT NOT NULL,
                summary TEXT NOT NULL,
                link TEXT NOT NULL,
                categories TEXT NOT NULL,
                amount REAL,
                price REAL,
                start_date TEXT,
                end_date TEXT,
                collab TEXT NOT NULL,
                source TEXT NOT NULL,
                status TEXT NOT NULL,
                official INTEGER NOT NULL,
                published_at TEXT,
                score INTEGER NOT NULL,
                first_seen TEXT NOT NULL,
                last_seen TEXT NOT NULL,
                notified_at TEXT
            );
            CREATE INDEX IF NOT EXISTS idx_items_target ON items(kind, target);
            CREATE TABLE IF NOT EXISTS runs (
                id INTEGER PRIMARY KEY AUTOINCREMENT,
                mode TEXT NOT NULL,
                started_at TEXT NOT NULL,
                finished_at TEXT NOT NULL,
                new_count INTEGER NOT NULL,
                errors TEXT NOT NULL
            );
        """)
        self.db.commit()

    def close(self) -> None:
        self.db.close()

    def __enter__(self) -> "CouponMonitor":
        return self

    def __exit__(self, exc_type: Any, exc: Any, traceback: Any) -> None:
        self.close()

    def _request(self, url: str, data: bytes | None = None, headers: dict[str, str] | None = None) -> bytes:
        timeout = float(self.settings.get("timeout_seconds", 15))
        retries = int(self.settings.get("request_retries", 2))
        backoff = float(self.settings.get("retry_backoff_seconds", 0.8))
        request_headers = {"User-Agent": "CouponMonitor/1.0 (Python stdlib; personal activity reader)"}
        request_headers.update(headers or {})
        last_error: Exception | None = None
        for attempt in range(retries + 1):
            request = urllib.request.Request(url, data=data, headers=request_headers)
            try:
                with urllib.request.urlopen(request, timeout=timeout) as response:
                    return response.read()
            except (
                urllib.error.URLError, urllib.error.HTTPError, socket.timeout,
                TimeoutError, http.client.HTTPException, ssl.SSLError,
            ) as exc:
                last_error = exc
                if attempt < retries:
                    time.sleep(backoff * (2 ** attempt))
        raise RuntimeError(f"请求失败：{last_error}")

    def search(self, query: str) -> list[dict[str, str]]:
        """优先使用配置的中文搜索 API；未配置时使用免密钥的 Bing RSS。"""
        api_key = os.environ.get("BOCHA_API_KEY", "").strip()
        if api_key:
            return self.search_bocha(query, api_key)
        base = self.settings.get("search_rss_url", "https://www.bing.com/search?format=rss&q=")
        return parse_rss(self._request(base + urllib.parse.quote(query)))

    def search_bocha(self, query: str, api_key: str) -> list[dict[str, str]]:
        payload = json.dumps({
            "query": query, "summary": True, "count": 10,
            "freshness": self.settings.get("freshness", "oneDay"),
        }).encode("utf-8")
        raw = self._request(
            "https://api.bochaai.com/v1/web-search", data=payload,
            headers={"Authorization": f"Bearer {api_key}", "Content-Type": "application/json"},
        )
        try:
            body = json.loads(raw.decode("utf-8"))
            pages = body["data"]["webPages"]["value"]
        except (UnicodeDecodeError, json.JSONDecodeError, KeyError, TypeError) as exc:
            raise ValueError(f"搜索 API 返回格式异常：{exc}") from exc
        results: list[dict[str, str]] = []
        for page in pages:
            if not isinstance(page, dict):
                continue
            results.append({
                "title": plain_text(page.get("name", "")),
                "link": clean_url(page.get("url", "")),
                "summary": plain_text(page.get("summary") or page.get("snippet") or ""),
                "published": str(page.get("datePublished") or ""),
            })
        return results

    def save_item(self, item: Activity, now: datetime) -> bool:
        exists = self.db.execute(
            "SELECT 1 FROM items WHERE fingerprint = ?", (item.fingerprint,)
        ).fetchone()
        values = (
            item.kind, item.target, item.title, item.summary, item.link,
            json.dumps(item.categories, ensure_ascii=False), item.amount, item.price,
            item.start_date.isoformat() if item.start_date else None,
            item.end_date.isoformat() if item.end_date else None,
            item.collab, item.source, item.status, int(item.official),
            isoformat(item.published_at) if item.published_at else None,
            item.score, isoformat(now), item.fingerprint,
        )
        if exists:
            self.db.execute("""
                UPDATE items SET kind=?, target=?, title=?, summary=?, link=?, categories=?,
                    amount=?, price=?, start_date=?, end_date=?, collab=?, source=?, status=?,
                    official=?, published_at=?, score=?, last_seen=? WHERE fingerprint=?
            """, values)
        else:
            self.db.execute("""
                INSERT INTO items (
                    kind, target, title, summary, link, categories, amount, price,
                    start_date, end_date, collab, source, status, official, published_at,
                    score, last_seen, fingerprint, first_seen
                ) VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?)
            """, values[:-1] + (item.fingerprint, isoformat(now)))
        self.db.commit()
        return not exists

    def remember_scope(self, item: Activity, kind: str, target: dict[str, Any], category: str | None) -> None:
        if kind != "coupons":
            return
        scopes = self.item_scopes.setdefault(item.fingerprint, set())
        if category:
            scopes.add(category)
        else:
            scopes.update(target.get("categories") or ["other"])

    def search_target(self, kind: str, target: dict[str, Any], now: datetime,
                      category: str | None = None) -> tuple[list[Activity], list[str]]:
        # 目标名放在查询首位：Bing RSS 只按首个词检索，OR 表达式会被截断。
        expression = target["name"]
        if kind == "coupons" and category:
            query_terms = self.settings.get("category_queries", {}).get(category) or self.settings.get("platform_queries", [])
        else:
            query_terms = self.settings.get(
                "platform_queries" if kind == "coupons" else "brand_queries", []
            )
        query_terms = list(query_terms)
        # 追加小红书、微博、抖音、公众号等来源，按目标名与日期轮换，控制请求量。
        sites = self.settings.get("social_sites") or []
        social_count = min(int(self.settings.get("social_queries_per_target", 0)), len(sites))
        if sites and social_count > 0:
            rotation = (sum(ord(char) for char in target["name"]) + now.timetuple().tm_yday) % len(sites)
            for step in range(social_count):
                site = sites[(rotation + step) % len(sites)]
                query_terms.append(f"(优惠 OR 免单 OR 买一送一 OR 联名) site:{site}")
        found: dict[str, Activity] = {}
        errors: list[str] = []
        delay = float(self.settings.get("request_delay_seconds", 0.35))
        for index, term in enumerate(query_terms):
            query = f"{expression} {term}"
            try:
                for raw in self.search(query):
                    item = make_activity(raw, kind, target, self.settings, now)
                    if item:
                        with self._lock:
                            self.remember_scope(item, kind, target, category)
                            old = found.get(item.fingerprint)
                            if not old or item.score > old.score:
                                was_new = old.is_new if old else False
                                item.is_new = self.save_item(item, now) or was_new
                                found[item.fingerprint] = item
                            elif old:
                                self.save_item(item, now)
            except (RuntimeError, ET.ParseError, ValueError) as exc:
                errors.append(f"{target['name']}：{exc}")
            if index + 1 < len(query_terms):
                time.sleep(delay)
        return list(found.values()), errors

    def last_run(self, kind: str) -> datetime | None:
        row = self.db.execute(
            "SELECT finished_at FROM runs WHERE mode = ? ORDER BY id DESC LIMIT 1", (kind,)
        ).fetchone()
        return parse_datetime(row["finished_at"]) if row else None

    def is_due(self, kind: str, now: datetime) -> bool:
        previous = self.last_run(kind)
        if not previous:
            return True
        key = "coupon_interval_seconds" if kind == "coupons" else "brand_interval_seconds"
        default = 3600 if kind == "coupons" else 86400
        return now >= previous + timedelta(seconds=int(self.settings.get(key, default)))

    def execute(self, mode: str = "all", force: bool = False) -> None:
        now = utc_now()
        if mode in ("delivery", "groupbuy", "other"):
            self.run_kind("coupons", now, category=mode)
            return
        kinds = ["coupons", "brands"] if mode == "all" else [mode]
        for kind in kinds:
            if not force and not self.is_due(kind, now):
                previous = self.last_run(kind)
                key = "coupon_interval_seconds" if kind == "coupons" else "brand_interval_seconds"
                default = 3600 if kind == "coupons" else 86400
                next_time = previous + timedelta(seconds=int(self.settings.get(key, default))) if previous else now
                print(f"[跳过] {self.kind_label(kind)}尚未到检查时间；下次 {self.display_time(next_time)}")
                continue
            self.run_kind(kind, now)

    @staticmethod
    def kind_label(kind: str) -> str:
        return "平台优惠券" if kind == "coupons" else "奶茶/咖啡/甜点活动"

    def social_queries(self, target: dict[str, Any], index: int) -> list[str]:
        """为每个目标补充小红书、微博、抖音、公众号等来源，按日期轮换控制请求量。"""
        sites = self.settings.get("social_sites") or []
        count = int(self.settings.get("social_queries_per_target", 0))
        if not sites or count <= 0:
            return []
        rotation = (index + utc_now().timetuple().tm_yday) % len(sites)
        picked = [sites[(rotation + step) % len(sites)] for step in range(min(count, len(sites)))]
        return [f'{target["name"]} (优惠 OR 免单 OR 买一送一 OR 联名) site:{site}' for site in picked]

    def remember_scope(self, item: Activity, kind: str, target: dict[str, Any], category: str | None) -> None:
        if kind != "coupons":
            return
        scopes = self.item_scopes.setdefault(item.fingerprint, set())
        if category:
            scopes.add(category)
        else:
            scopes.update(target.get("categories") or ["other"])

    def run_kind(self, kind: str, now: datetime | None = None, category: str | None = None) -> None:
        now = now or utc_now()
        started = now
        config_key = "platforms" if kind == "coupons" else "brands"
        targets = [target for target in self.config.get(config_key, []) if target.get("enabled", True)]
        if kind == "coupons" and category:
            targets = [t for t in targets if category in (t.get("categories") or ["other"])]
        label = self.kind_label(kind) + (f"/{category}" if category else "")
        print(f"\n=== 开始检查{label}，共 {len(targets)} 个目标 ===")
        print("提示：公开搜索仅提供线索，不保证全量或实时；领取前请在官方 App/小程序复核。")
        all_items: dict[str, Activity] = {}
        errors: list[str] = []
        workers = max(1, int(self.settings.get("search_workers", 4)))
        done = 0

        def work(target: dict[str, Any]) -> tuple[list[Activity], list[str], str]:
            try:
                items, target_errors = self.search_target(kind, target, now, category=category)
                return items, target_errors, ""
            except Exception as exc:  # 隔离单个配置/数据源异常，保留其他结果
                return [], [], f"{target.get('name', '未知目标')}：{exc}"

        with concurrent.futures.ThreadPoolExecutor(max_workers=workers) as pool:
            for found_items, target_errors, failure in pool.map(work, targets):
                done += 1
                with self._lock:
                    print(f"\r检索 {done}/{len(targets)}", end="", flush=True)
                    if failure:
                        errors.append(failure)
                    errors.extend(target_errors)
                    for item in found_items:
                        old = all_items.get(item.fingerprint)
                        if not old or item.score > old.score:
                            all_items[item.fingerprint] = item
                        elif item.is_new:
                            old.is_new = True
        print("\r" + " " * 60 + "\r", end="")
        items = sorted(
            all_items.values(),
            key=lambda item: (item.score, isoformat(item.published_at or item.first_seen)),
            reverse=True,
        )
        self.display_items(items)
        new_items = [item for item in items if item.is_new]
        notification_errors = self.notify_new(new_items)
        errors.extend(notification_errors)
        finished = utc_now()
        self.db.execute(
            "INSERT INTO runs(mode, started_at, finished_at, new_count, errors) VALUES (?, ?, ?, ?, ?)",
            (kind, isoformat(started), isoformat(finished), len(new_items), json.dumps(errors, ensure_ascii=False)),
        )
        self.db.commit()
        print(f"[完成] 本次相关线索 {len(items)} 条，新记录 {len(new_items)} 条，错误 {len(errors)} 个。")
        for error in errors[:8]:
            print(f"  [错误] {error}")
        if len(errors) > 8:
            print(f"  其余 {len(errors) - 8} 个错误已写入执行记录。")
        self.print_claim_guides(kind, items)

    @staticmethod
    def display_time(value: datetime | None) -> str:
        if not value:
            return "未知"
        return value.astimezone().strftime("%Y-%m-%d %H:%M:%S %Z")

    def display_items(self, items: list[Activity]) -> None:
        if not items:
            print("未发现符合条件的公开活动线索。可稍后强制重试，或直接查看官方入口。")
            return
        limit = int(self.settings.get("console_limit", 30))
        print(f"\n--- 推荐线索（按活动状态、优惠力度、官方来源与新鲜度排序）---")
        for index, item in enumerate(items[:limit], 1):
            labels = [STATUS_LABELS[item.status]] + [CATEGORY_LABELS[c] for c in item.categories]
            print(f"{index}. [{' / '.join(labels)}] {item.target}｜{item.title}")
            details: list[str] = []
            if item.amount is not None:
                details.append(f"券额/减额约 {item.amount:g} 元")
            if item.price is not None:
                details.append(f"低价约 {item.price:g} 元")
            if item.start_date or item.end_date:
                details.append(f"日期 {item.start_date or '待确认'} 至 {item.end_date or '待确认'}")
            if item.collab:
                details.append(f"联动方线索：{item.collab}")
            if item.claim:
                details.append(f"领取线索：{item.claim}")
            details.append(f"来源：{item.source}{'（官方域名）' if item.official else '（第三方，需核验）'}")
            print("   " + "；".join(details))
            if item.summary:
                print("   摘要：" + item.summary[:180])
            if item.link:
                print("   链接：" + item.link)
        if len(items) > limit:
            print(f"另有 {len(items) - limit} 条已保存，可用 --history {len(items)} 查看。")

    def print_claim_guides(self, kind: str, items: list[Activity]) -> None:
        if not items:
            if kind != "coupons":
                return
            print("\n--- 官方领取入口（未发现活动线索时的兜底入口，均需手动领取）---")
            for platform in self.config.get("platforms", []):
                if platform.get("enabled", True):
                    print(f"【{platform['name']}】{platform.get('app_path', '以官方 App 为准')}")
                    print(f"  官网：{platform.get('official_url', '请使用官方 App')}")
            return
        print("\n--- 领取与核验方式 ---")
        if kind == "coupons":
            by_name = {platform["name"]: platform for platform in self.config.get("platforms", [])}
            for name in sorted({item.target for item in items}):
                platform = by_name[name]
                print(f"【{name}】需手动领取：未接入平台官方授权自动领取接口。")
                print(f"入口：{platform.get('app_path', '以官方 App 当前页面为准')}")
                print(f"官网：{platform.get('official_url', '请使用官方 App')}")
                for step_number, step in enumerate(platform.get("claim_steps", []), 1):
                    print(f"  {step_number}. {step}")
        else:
            print("1. 打开对应品牌官方 App 或微信/支付宝官方小程序，并确认账号、城市和门店。")
            print("2. 在首页活动区、会员中心或“我的—优惠券/卡券”查找同名活动，按页面要求领取或下单。")
            print("3. 下单前核对有效期、适用门店、套餐/周边库存、联名时间与使用门槛；第三方消息不要直接付款。")

    def notify_new(self, items: list[Activity]) -> list[str]:
        valuable = [item for item in items if item.status != "expired" and HIGH_VALUE.intersection(item.categories)]
        if not valuable:
            return []
        sendkey = os.environ.get("SERVERCHAN_SENDKEY", "").strip()
        smtp_host = os.environ.get("SMTP_HOST", "").strip()
        if not sendkey and not smtp_host:
            print("[通知] 未配置 Server 酱或 SMTP；结果已保存到本地。")
            return []
        title = f"优惠监控：{len(valuable)} 条新高价值活动线索"
        lines = ["公开搜索线索，领取前请通过官方渠道核验。", ""]
        for item in valuable[:12]:
            labels = "/".join(CATEGORY_LABELS[c] for c in item.categories if c in HIGH_VALUE)
            lines.append(f"【{item.target}｜{STATUS_LABELS[item.status]}｜{labels}】{item.title}")
            if item.collab:
                lines.append(f"联动方：{item.collab}")
            lines.append(item.link or item.source)
            lines.append("")
        content = "\n".join(lines)
        errors: list[str] = []
        succeeded = False
        if sendkey:
            try:
                self.send_serverchan(sendkey, title, content)
                succeeded = True
                print("[通知] Server 酱推送成功。")
            except Exception as exc:
                errors.append(f"Server 酱通知：{exc}")
        if smtp_host:
            try:
                self.send_email(title, content)
                succeeded = True
                print("[通知] 邮件发送成功。")
            except Exception as exc:
                errors.append(f"邮件通知：{exc}")
        if succeeded:
            now = isoformat(utc_now())
            self.db.executemany(
                "UPDATE items SET notified_at = ? WHERE fingerprint = ?",
                [(now, item.fingerprint) for item in valuable],
            )
            self.db.commit()
        return errors

    def send_serverchan(self, sendkey: str, title: str, content: str) -> None:
        key = urllib.parse.quote(sendkey, safe="")
        data = urllib.parse.urlencode({"title": title, "desp": content}).encode("utf-8")
        response = self._request(f"https://sctapi.ftqq.com/{key}.send", data=data)
        try:
            result = json.loads(response.decode("utf-8"))
            if result.get("code") not in (None, 0):
                raise RuntimeError(result.get("message") or "Server 酱返回错误")
        except (UnicodeDecodeError, json.JSONDecodeError):
            pass

    def send_email(self, title: str, content: str) -> None:
        host = os.environ["SMTP_HOST"].strip()
        port = int(os.environ.get("SMTP_PORT", "465"))
        user = os.environ.get("SMTP_USER", "").strip()
        password = os.environ.get("SMTP_PASSWORD", "")
        recipients = [value.strip() for value in os.environ.get("SMTP_TO", "").split(",") if value.strip()]
        if not recipients or not user:
            raise RuntimeError("SMTP_HOST 已配置，但 SMTP_USER 或 SMTP_TO 缺失")
        message = EmailMessage()
        message["Subject"] = title
        message["From"] = user
        message["To"] = ", ".join(recipients)
        message.set_content(content)
        if port == 465:
            client: smtplib.SMTP = smtplib.SMTP_SSL(host, port, timeout=20)
        else:
            client = smtplib.SMTP(host, port, timeout=20)
        with client:
            if port != 465 and os.environ.get("SMTP_STARTTLS", "1") != "0":
                client.starttls()
            client.login(user, password)
            client.send_message(message)

    def show_history(self, limit: int = 20) -> None:
        rows = self.db.execute("SELECT * FROM items ORDER BY last_seen DESC LIMIT ?", (limit,)).fetchall()
        if not rows:
            print("暂无活动记录。")
            return
        print(f"\n--- 最近 {len(rows)} 条活动记录（均需按有效期与官方页面复核）---")
        for index, row in enumerate(rows, 1):
            categories = json.loads(row["categories"])
            labels = [STATUS_LABELS.get(row["status"], row["status"])] + [
                CATEGORY_LABELS.get(category, category) for category in categories
            ]
            print(f"{index}. [{' / '.join(labels)}] {row['target']}｜{row['title']}")
            print(f"   {row['start_date'] or '日期待定'} 至 {row['end_date'] or '日期待定'}；{row['source']}；{row['link']}")
            if row["collab"]:
                print(f"   联动方线索：{row['collab']}")

    def show_runs(self, limit: int = 20) -> None:
        rows = self.db.execute("SELECT * FROM runs ORDER BY id DESC LIMIT ?", (limit,)).fetchall()
        if not rows:
            print("暂无执行记录。")
            return
        print(f"\n--- 最近 {len(rows)} 次执行 ---")
        for row in rows:
            errors = json.loads(row["errors"])
            print(
                f"#{row['id']} {self.kind_label(row['mode'])}｜{self.display_time(parse_datetime(row['started_at']))}"
                f"｜新增 {row['new_count']}｜错误 {len(errors)}"
            )
            for error in errors[:3]:
                print(f"   {error}")


def load_config(path: str | Path) -> dict[str, Any]:
    with Path(path).expanduser().open("r", encoding="utf-8") as handle:
        config = json.load(handle)
    if not isinstance(config.get("platforms"), list) or not isinstance(config.get("brands"), list):
        raise ValueError("config.json 必须包含 platforms 和 brands 数组")
    return config


def interactive_menu(monitor: CouponMonitor) -> None:
    while True:
        print("""
========== 手机优惠监控 ==========
1. 立即强制搜索全部
2. 立即强制搜索平台优惠券
3. 立即强制搜索奶茶/甜点活动
4. 按配置间隔持续监控
5. 查看活动历史
6. 查看执行记录
0. 退出
=================================""")
        try:
            choice = input("请选择：").strip()
        except (EOFError, KeyboardInterrupt):
            print()
            return
        try:
            if choice == "1":
                monitor.execute("all", force=True)
            elif choice == "2":
                monitor.execute("coupons", force=True)
            elif choice == "3":
                monitor.execute("brands", force=True)
            elif choice == "4":
                run_loop(monitor)
            elif choice == "5":
                monitor.show_history(int(input("显示条数（建议 20）：") or "20"))
            elif choice == "6":
                monitor.show_runs(int(input("显示条数（建议 20）：") or "20"))
            elif choice == "0":
                return
            else:
                print("无效选项。")
        except (ValueError, EOFError, KeyboardInterrupt) as exc:
            if isinstance(exc, ValueError):
                print("请输入有效数字。")
            else:
                print("\n已返回菜单。")


def run_loop(monitor: CouponMonitor) -> None:
    poll = max(5, int(monitor.settings.get("scheduler_poll_seconds", 60)))
    print(f"进入持续监控，每 {poll} 秒检查是否到期；按 Ctrl+C 停止。请允许终端在后台运行并关闭电池限制。")
    try:
        while True:
            monitor.execute("all", force=False)
            time.sleep(poll)
    except KeyboardInterrupt:
        print("\n已停止持续监控。")


def build_parser() -> argparse.ArgumentParser:
    script_dir = Path(__file__).resolve().parent
    parser = argparse.ArgumentParser(description="优惠券、奶茶/咖啡/甜点活动与联动监控")
    action = parser.add_mutually_exclusive_group()
    action.add_argument("--once", action="store_true", help="执行一次；仅运行已到期间隔的任务")
    action.add_argument("--loop", action="store_true", help="常驻运行，按间隔检查")
    parser.add_argument("--force", action="store_true", help="忽略间隔，强制搜索；不会重复通知旧活动")
    parser.add_argument("--mode", choices=("all", "coupons", "brands", "delivery", "groupbuy", "other"), default="all", help="搜索范围")
    parser.add_argument("--interval", type=int, help="覆盖平台券检查间隔（秒，默认 3600）")
    parser.add_argument("--brand-interval", type=int, help="覆盖品牌检查间隔（秒，默认 86400）")
    parser.add_argument("--history", nargs="?", const=20, type=int, help="查看活动历史，可选条数")
    parser.add_argument("--runs", nargs="?", const=20, type=int, help="查看执行记录，可选条数")
    parser.add_argument("--web", action="store_true", help="启动本地网页控制台")
    parser.add_argument("--host", default="127.0.0.1", help="网页控制台监听地址，默认仅本机")
    parser.add_argument("--port", type=int, default=8000, help="网页控制台端口，默认 8000")
    parser.add_argument("--auth", help="网页登录口令，格式 用户名:密码；公网访问时必填")
    parser.add_argument("--config", default=str(script_dir / "config.json"), help="配置文件路径")
    parser.add_argument("--db", default=str(script_dir / "monitor.db"), help="SQLite 数据库路径")
    parser.add_argument("--export", metavar="JSON路径", help="运行后把当前有效线索导出为 JSON（供静态网页读取）")
    parser.add_argument("--export-dir", metavar="目录", help="按分类导出最新结果、历史库和清单到该目录")
    return parser


def export_results(monitor: CouponMonitor, config: dict[str, Any], path: str) -> dict[str, Any]:
    """把有效线索导出为静态网页可读取的 JSON。"""
    target = Path(path).expanduser()
    target.parent.mkdir(parents=True, exist_ok=True)
    rows = monitor.db.execute(
        "SELECT * FROM items WHERE status IN ('active', 'upcoming', 'unknown') "
        "ORDER BY score DESC, last_seen DESC LIMIT 300"
    ).fetchall()
    items: list[dict[str, Any]] = []
    for row in rows:
        data = dict(row)
        try:
            categories = json.loads(data["categories"])
        except (TypeError, json.JSONDecodeError):
            categories = []
        items.append({
            "kind": data["kind"],
            "target": data["target"],
            "title": data["title"],
            "summary": data["summary"],
            "link": data["link"],
            "categories": categories,
            "amount": data["amount"],
            "price": data["price"],
            "start_date": data["start_date"],
            "end_date": data["end_date"],
            "collab": data["collab"],
            "source": data["source"],
            "status": data["status"],
            "official": bool(data["official"]),
        })
    guides = {
        platform["name"]: {
            "app_path": platform.get("app_path", ""),
            "official_url": platform.get("official_url", ""),
            "claim_steps": platform.get("claim_steps", []),
        }
        for platform in config.get("platforms", [])
        if platform.get("enabled", True)
    }
    payload = {
        "generated_at": utc_now().isoformat(),
        "count": len(items),
        "items": items,
        "guides": guides,
    }
    target.write_text(json.dumps(payload, ensure_ascii=False, indent=2), encoding="utf-8")
    print(f"已导出 {len(items)} 条线索到 {target}")
    return payload


BUCKET_LABELS = {
    "delivery": "外卖券",
    "groupbuy": "团购券",
    "other": "其他优惠",
    "brand_coupon": "奶茶优惠券",
    "brand_activity": "奶茶优惠活动",
    "brand_collab": "奶茶联动",
}
PLATFORM_BUCKETS = ("delivery", "groupbuy", "other")
BRAND_BUCKETS = ("brand_coupon", "brand_activity", "brand_collab")


def brand_buckets(categories: list[str]) -> list[str]:
    cats = set(categories or [])
    buckets: list[str] = []
    if "collab" in cats:
        buckets.append("brand_collab")
    if cats & {"coupon", "big_coupon"}:
        buckets.append("brand_coupon")
    if cats & {"bogo", "second_half", "free", "low_price"}:
        buckets.append("brand_activity")
    return buckets or ["brand_activity"]


def searched_buckets(mode: str) -> list[str]:
    if mode in PLATFORM_BUCKETS:
        return [mode]
    if mode == "coupons":
        return list(PLATFORM_BUCKETS)
    if mode == "brands":
        return list(BRAND_BUCKETS)
    return list(PLATFORM_BUCKETS) + list(BRAND_BUCKETS)


def export_bundle(monitor: CouponMonitor, config: dict[str, Any], data_dir: str, mode: str) -> dict[str, Any]:
    """按六个分类导出最新结果，并维护可回看的历史库。"""
    directory = Path(data_dir).expanduser()
    directory.mkdir(parents=True, exist_ok=True)
    now = utc_now()
    now_text = isoformat(now)
    buckets_searched = searched_buckets(mode)
    guides = {
        platform["name"]: {
            "app_path": platform.get("app_path", ""),
            "official_url": platform.get("official_url", ""),
            "claim_steps": platform.get("claim_steps", []),
        }
        for platform in config.get("platforms", [])
        if platform.get("enabled", True)
    }
    rows = monitor.db.execute("SELECT * FROM items ORDER BY score DESC, last_seen DESC").fetchall()
    latest: dict[str, list[dict[str, Any]]] = {bucket: [] for bucket in buckets_searched}
    found: list[dict[str, Any]] = []
    for row in rows:
        data = dict(row)
        try:
            categories = json.loads(data["categories"])
        except (TypeError, json.JSONDecodeError):
            categories = []
        item = {
            "fingerprint": data["fingerprint"],
            "kind": data["kind"], "target": data["target"], "title": data["title"],
            "summary": data["summary"], "link": data["link"], "categories": categories,
            "amount": data["amount"], "price": data["price"],
            "start_date": data["start_date"], "end_date": data["end_date"],
            "collab": data["collab"], "source": data["source"],
            "status": data["status"], "official": bool(data["official"]),
            "claim": extract_claims(f"{data['title']} {data['summary']}"),
        }
        item["evergreen"] = bool(item["claim"]) and (
            not data["end_date"] or data["end_date"] >= now.astimezone().date().isoformat()
        )
        if data["kind"] == "coupons":
            buckets = sorted(monitor.item_scopes.get(data["fingerprint"]) or []) or ["other"]
        else:
            buckets = brand_buckets(categories)
        item["buckets"] = buckets
        found.append(item)
        if data["status"] not in ("active", "upcoming", "unknown"):
            continue
        for bucket in buckets:
            if bucket in latest:
                latest[bucket].append(item)

    for bucket, items in latest.items():
        payload = {
            "bucket": bucket, "label": BUCKET_LABELS[bucket], "generated_at": now_text,
            "count": len(items), "items": items[:200], "guides": guides,
        }
        (directory / f"{bucket}.json").write_text(
            json.dumps(payload, ensure_ascii=False, indent=2), encoding="utf-8"
        )

    history_path = directory / "history.json"
    history: dict[str, Any] = {"items": []}
    if history_path.exists():
        try:
            history = json.loads(history_path.read_text(encoding="utf-8"))
        except (OSError, json.JSONDecodeError):
            history = {"items": []}
    merged = {
        entry.get("fingerprint"): entry
        for entry in history.get("items", [])
        if isinstance(entry, dict) and entry.get("fingerprint")
    }
    for item in found:
        fingerprint = item["fingerprint"]
        old = merged.get(fingerprint)
        if old:
            old.update({key: value for key, value in item.items() if key != "buckets"})
            old["buckets"] = sorted(set(old.get("buckets", [])) | set(item["buckets"]))
            old["last_seen"] = now_text
        else:
            entry = dict(item)
            entry["first_seen"] = now_text
            entry["last_seen"] = now_text
            merged[fingerprint] = entry
    retention_hours = int(config.get("settings", {}).get("retention_hours", 24))
    cutoff = now - timedelta(hours=retention_hours)
    today_text = now.astimezone().date().isoformat()
    kept: list[dict[str, Any]] = []
    for entry in merged.values():
        try:
            seen = parse_datetime(entry.get("last_seen") or "")
        except (TypeError, ValueError):
            seen = None
        if not seen or seen < cutoff:
            if not entry.get("evergreen"):
                continue
        end_date = entry.get("end_date") or ""
        if end_date and end_date < today_text and not entry.get("evergreen"):
            continue
        kept.append(entry)
    kept.sort(key=lambda entry: entry.get("last_seen") or "", reverse=True)
    kept = kept[:500]
    history_path.write_text(
        json.dumps({"updated_at": now_text, "count": len(kept), "items": kept}, ensure_ascii=False, indent=2),
        encoding="utf-8",
    )

    # 分类文件直接展示“最近 24 小时记录 + 长期有效线索”，不再单独区分回看视图。
    latest = {bucket: [] for bucket in BUCKET_LABELS}
    for entry in kept:
        if entry.get("status") not in ("active", "upcoming", "unknown"):
            continue
        for bucket in entry.get("buckets", []):
            if bucket in latest:
                latest[bucket].append(entry)
    for bucket, items in latest.items():
        items.sort(key=lambda entry: entry.get("last_seen") or "", reverse=True)
        payload = {
            "bucket": bucket, "label": BUCKET_LABELS[bucket], "generated_at": now_text,
            "count": len(items), "items": items[:200], "guides": guides,
            "retention_hours": retention_hours,
        }
        (directory / f"{bucket}.json").write_text(
            json.dumps(payload, ensure_ascii=False, indent=2), encoding="utf-8"
        )

    manifest_path = directory / "manifest.json"
    manifest: dict[str, Any] = {"categories": {}}
    if manifest_path.exists():
        try:
            manifest = json.loads(manifest_path.read_text(encoding="utf-8"))
        except (OSError, json.JSONDecodeError):
            manifest = {"categories": {}}
    manifest.setdefault("categories", {})
    for bucket, items in latest.items():
        previous = manifest["categories"].get(bucket, {})
        manifest["categories"][bucket] = {
            "label": BUCKET_LABELS[bucket],
            "updated_at": now_text if bucket in buckets_searched else previous.get("updated_at", now_text),
            "count": len(items),
        }
    manifest["generated_at"] = now_text
    manifest["history_count"] = len(kept)
    manifest["retention_hours"] = retention_hours
    manifest_path.write_text(json.dumps(manifest, ensure_ascii=False, indent=2), encoding="utf-8")
    print("已导出分类记录：" + "，".join(f"{BUCKET_LABELS[b]} {len(v)} 条" for b, v in latest.items()))
    print(f"记录库 {len(kept)} 条：仅保留最近 {retention_hours} 小时，长期有效的领取口令/入口除外。")
    return manifest


def main(argv: list[str] | None = None) -> int:
    parser = build_parser()
    args = parser.parse_args(argv)
    if args.interval is not None and args.interval < 60:
        parser.error("--interval 不能小于 60 秒")
    if args.brand_interval is not None and args.brand_interval < 60:
        parser.error("--brand-interval 不能小于 60 秒")
    if not 1 <= args.port <= 65535:
        parser.error("--port 必须在 1-65535 之间")
    if args.auth is not None:
        user, sep, password = args.auth.partition(":")
        if not sep or not user or not password:
            parser.error("--auth 格式应为 用户名:密码，且两部分都不能为空")
    try:
        config = load_config(args.config)
        if args.interval is not None:
            config.setdefault("settings", {})["coupon_interval_seconds"] = args.interval
        if args.brand_interval is not None:
            config.setdefault("settings", {})["brand_interval_seconds"] = args.brand_interval
        if args.web:
            from web_console import serve
            return serve(config, args.db, args.host, args.port, args.auth)
        monitor = CouponMonitor(config, args.db)
    except (OSError, ValueError, json.JSONDecodeError, sqlite3.Error) as exc:
        print(f"启动失败：{exc}", file=sys.stderr)
        return 2

    with monitor:
        if args.history is not None:
            monitor.show_history(max(1, args.history))
            return 0
        if args.runs is not None:
            monitor.show_runs(max(1, args.runs))
            return 0
        try:
            if args.loop:
                run_loop(monitor)
            elif args.once or args.force:
                monitor.execute(args.mode, force=args.force)
                if args.export:
                    export_results(monitor, config, args.export)
                if args.export_dir:
                    export_bundle(monitor, config, args.export_dir, args.mode)
            else:
                interactive_menu(monitor)
        except KeyboardInterrupt:
            print("\n已停止。")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
