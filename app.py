"""가장 빨리 도착하는 길찾기의 화면(명세 §6 ~ §8).

실행: `python app.py` (실행기가 밝은 테마와 회색 기본 색을 붙여 `streamlit run` 을 새 프로세스로 띄운다, §8.2).
`streamlit run app.py` 로 직접 띄울 때는 `--theme.base=light --theme.primaryColor=#52514e` 를 붙인다.
화면 검사: `python app.py --uitest` (§8.7, §9.9).

화면은 엔진 결과를 그대로 보여 준다. 화면이 하는 계산은 형식 변환, 정렬된 결과의 걸러 보기, 표시용 좌표 변환,
입력 변환(마감 시계 시각을 t 로)뿐이다(§6.1). 엔진 함수는 늘 모듈 속성으로 부른다(`ce.run_engine(...)`, §8.1).
"""

from __future__ import annotations

import contextlib
import dataclasses
import datetime
import html
import io
import json
import math
import os
import re
import sqlite3
import subprocess
import sys
import tempfile
import time
import traceback
import unicodedata
from pathlib import Path
from typing import Any, Callable, Iterable, Iterator, Mapping, MutableMapping, Sequence

_APP_DIR = Path(__file__).resolve().parent
if str(_APP_DIR) not in sys.path:
    sys.path.insert(0, str(_APP_DIR))

import altair as alt  # noqa: E402
import folium  # noqa: E402
from folium.template import Template  # noqa: E402
import pandas as pd  # noqa: E402
import streamlit as st  # noqa: E402
from pydantic import TypeAdapter  # noqa: E402
from streamlit import runtime  # noqa: E402

if __name__ == "__main__" and not runtime.exists():
    # 실행기와 화면 검사(`python app.py`, `--uitest`): 실행 맥락 밖에서 캐시 장식자를 만들 때의 안내
    # ("No runtime found", "missing ScriptRunContext")를 숨긴다. 화면은 새 프로세스가 띄우므로 그쪽 로그는 그대로다.
    # 검사 중에는 AppTest 가 실행마다 로그 수준을 되돌리므로 `_quiet` 가 다시 낮춘다.
    from streamlit import config as _streamlit_config, logger as _streamlit_logger

    _streamlit_config.get_config_options()  # 설정을 먼저 읽는다(처음 읽을 때 로그 수준을 설정값으로 되돌리므로)
    _streamlit_logger.set_log_level("error")

from streamlit_folium import st_folium  # noqa: E402

import core_engine as ce  # noqa: E402
from models_and_config import (  # noqa: E402
    DEFAULT_TARGETS_JSON,
    PARAM_RANGES,
    WALK_SPEED_PRESETS,
    WEIGHT_PRESETS,
    ApiSourceStatus,
    BusRouteType,
    CollectTargets,
    DataMode,
    DayType,
    EdgeKind,
    EngineConfig,
    EngineOutput,
    EngineStatus,
    FullVehiclePolicy,
    Grade,
    ItineraryResult,
    LegKind,
    Mode,
    NodeType,
    OriginKind,
    OriginState,
    ProbMethod,
    Query,
    RankCriterion,
    ReasonCode,
    RouteStatus,
    RunTimeSource,
    Scenario,
    SearchRun,
    SignalSource,
    SignalState,
    SourceKind,
    SourceState,
    StationUse,
    TimeSource,
    TrainChoice,
    TravelMode,
    WaitRule,
    WarningCode,
)

# ===== U1. 설정과 디자인 토큰 =====

THEME_FLAGS = ("--theme.base=light", "--theme.primaryColor=#52514e")
LIVE_MIN_REFRESH_S = 30  # "지금 다시 조회"를 다시 누를 수 있기까지의 초(§6.3)
MAP_MAX_PRUNED_MARKERS = 500  # "타원 밖 노드" 레이어에 그리는 표지의 최대 수(§6.3)
KAKAO_SESSION_CALL_LIMIT = 50  # 세션마다 카카오 호출 수 한도(§5.4)
DATA_DIR_ENV = "MOBILITY_ROUTER_DATA_DIR"  # 데이터 폴더 환경변수(§8.2)
LIVE_CACHE_TTL_S = 60  # 같은 조건의 실시간 조회를 다시 부르지 않는 시간(§8.4 의 cached_live)
KST = datetime.timezone(datetime.timedelta(hours=9), "KST")
SECONDS_PER_DAY = 86_400
# 화면 폭(§6.1). Streamlit 1.67 기본 사이드바 300 px(내용 240 px)에서는 데이터 모드·출발·걷는 속도 단추가 두 줄로 접혀(10단계
# 화면 확인: 단추 폭 273, 371, 276 px) 처음 폭을 340 px 로 둔다. 그만큼 본문이 좁아지지 않게 넓은 배치의 본문 양옆 여백
# (Streamlit 기본 5rem = 80 px, 화면 864 px 이상)을 48 px 로 줄인다. 본문 폭 = 화면 - 사이드바 - 2 × 여백(1440 에서 1,004 px).
SIDEBAR_WIDTH_PX = 340
REFERENCE_VIEWPORT_PX = 1440  # §6.1 의 1440 × 900
MAIN_SIDE_PADDING_PX = 48  # 넓은 배치에서 본문 한쪽 여백
WIDE_PADDING_MIN_VIEWPORT_PX = 864  # Streamlit 1.67 이 넓은 여백을 쓰는 화면 폭(736 + 2 × (80 - 16))
ORIGIN_KIND_LABEL = "출발"  # 출발 종류 구간 선택의 라벨. 단추가 넷이면 page_css 가 2 × 2 격자로 놓는다
THEME_SEEN_KEY = "theme_seen"  # 세션의 첫 실행이 지났는지(theme_tokens, §7.2)
# 지금 위치에서 출발(§6.8). 위치 단추는 페이지 문서에서 도는 사용자 컴포넌트(st.components.v2, §8.5)라 브라우저 위치를 받을 수 있다.
GPS_COMPONENT_NAME = "mr_gps"
GPS_COMPONENT_KEY = "gps_locate"
GPS_BUTTON_LABEL = "지금 위치에서 출발"
GPS_BUSY_LABEL = "위치를 찾는 중입니다"
GPS_PRIVACY_NOTE = "기기 위치는 이 계산에만 쓰고 파일에 남기지 않습니다."
GPS_ORIGIN_NAME = "지금 위치"  # 지금 위치로 정한 출발의 이름(머리말, 사이드바, 지도 표지)
GPS_TIMEOUT_MS = 15_000  # getCurrentPosition 의 timeout
GPS_MAX_AGE_MS = 30_000  # getCurrentPosition 의 maximumAge: 이만큼 안에 잰 위치는 다시 재지 않고 쓴다
GPS_ACCURACY_WARN_M = 100.0  # 정확도(반경)가 이보다 크면 알린다. 트인 곳의 스마트폰 GPS 는 보통 반경 4.9 m 안(gps.gov)
_GPS_ICON = (
    '<svg viewBox="0 0 24 24" width="18" height="18" aria-hidden="true" focusable="false">'
    '<circle cx="12" cy="12" r="7" fill="none" stroke="currentColor" stroke-width="2"/>'
    '<circle cx="12" cy="12" r="2.5" fill="currentColor"/>'
    '<path d="M12 2v3 M12 19v3 M2 12h3 M19 12h3" stroke="currentColor" stroke-width="2" stroke-linecap="round"/></svg>'
)
GPS_HTML = f'<button type="button" class="mr-gps">{_GPS_ICON}<span class="mr-gps-text">{html.escape(GPS_BUTTON_LABEL)}</span></button>'
# 테마 변수(§8.5)로 Streamlit 1.67 기본(secondary) 단추와 같은 모양을 만든다(§6.8). 바탕은 사이드바 바탕의 HSL 명도를
# 2.5 올린 색(기본 단추의 규칙), 마우스를 올리거나 키보드 초점이면 글자색을 섞은 옅은 바탕(밝은 화면 6 %, 어두운 화면 12 %),
# 누르는 동안 10 %·20 %, 키보드 초점에는 주 색 50 % 의 0.2rem 고리다. 상대 색(`hsl(from …)`)이나 `light-dark()` 를 모르는
# 브라우저는 앞 줄의 값을 쓴다. 기다리는 동안은 `aria-busy` 로 흐리게 한다(`disabled` 는 초점을 잃게 해서 쓰지 않는다).
GPS_CSS = """
.mr-gps { display: flex; align-items: center; justify-content: center; gap: 0.5rem; width: 100%; min-height: 2.5rem; margin: 0;
  padding: 0.25rem 0.75rem; box-sizing: border-box; border: 1px solid var(--st-border-color); border-radius: var(--st-button-radius);
  background: var(--st-background-color); background: hsl(from var(--st-background-color) h s calc(l + 2.5));
  color: var(--st-text-color); font-family: var(--st-font); font-size: 1rem; line-height: 1.6; cursor: pointer; }
.mr-gps:hover:not([aria-busy="true"]), .mr-gps:focus-visible {
  background: color-mix(in srgb, var(--st-text-color) 8%, transparent);
  background: light-dark(color-mix(in srgb, var(--st-text-color) 6%, transparent),
                         color-mix(in srgb, var(--st-text-color) 12%, transparent)); }
.mr-gps:active:not([aria-busy="true"]) {
  background: color-mix(in srgb, var(--st-text-color) 14%, transparent);
  background: light-dark(color-mix(in srgb, var(--st-text-color) 10%, transparent),
                         color-mix(in srgb, var(--st-text-color) 20%, transparent)); }
.mr-gps:focus { outline: none; }
.mr-gps:focus-visible { box-shadow: 0 0 0 0.2rem color-mix(in srgb, var(--st-primary-color) 50%, transparent); }
.mr-gps[aria-busy="true"] { cursor: progress; opacity: 0.6; }
.mr-gps svg { flex: none; }
"""
# 단추를 누른 때에만 위치를 요청한다. 결과는 트리거 "fix" 로 보낸다: {lat, lon, accuracy} 또는 {error}(§6.8).
GPS_JS = """
export default function (component) {
  const { data, parentElement, setTriggerValue } = component;
  const button = parentElement.querySelector("button.mr-gps");
  const text = parentElement.querySelector(".mr-gps-text");
  if (!button || !text || !data) {
    return;
  }
  const idle = () => {
    delete button.dataset.busy;
    button.removeAttribute("aria-busy");
    button.removeAttribute("aria-disabled");
    text.textContent = data.label;
  };
  button.title = data.title;
  if (button.dataset.busy !== "1") {
    idle();
  }
  button.onclick = () => {
    if (button.dataset.busy === "1") {
      return;
    }
    if (!window.isSecureContext) {
      setTriggerValue("fix", { error: "INSECURE" });
      return;
    }
    if (!("geolocation" in navigator)) {
      setTriggerValue("fix", { error: "UNSUPPORTED" });
      return;
    }
    button.dataset.busy = "1";
    button.setAttribute("aria-busy", "true");
    button.setAttribute("aria-disabled", "true");
    text.textContent = data.busy_label;
    navigator.geolocation.getCurrentPosition(
      (position) => {
        idle();
        setTriggerValue("fix", {
          lat: position.coords.latitude, lon: position.coords.longitude, accuracy: position.coords.accuracy,
        });
      },
      (error) => {
        idle();
        const codes = { 1: "PERMISSION_DENIED", 2: "POSITION_UNAVAILABLE", 3: "TIMEOUT" };
        setTriggerValue("fix", { error: codes[error.code] || "POSITION_UNAVAILABLE" });
      },
      { enableHighAccuracy: true, timeout: data.timeout_ms, maximumAge: data.max_age_ms },
    );
  };
}
"""

# 간단히 보기(§6.9). 처음 화면은 소비자용 간단히 보기이고, 지금까지의 분석 화면은 자세히 보기다.
VIEW_NAMES: Mapping[str, str] = {"SIMPLE": "간단히", "DETAIL": "자세히"}
VIEW_LABEL = "화면"  # 보기 바꾸기 구간 선택의 라벨(숨김, aria-label 로 남는다)
DETAIL_BUTTON_LABEL = "자세한 분석 보기"
TRIP_EDIT_LABEL = "출발·목적지 바꾸기"
TRIP_SIDEBAR_NOTE = "출발과 목적지, 도착해야 하는 시각은 본문의 출발·도착 상자에서 고릅니다."
NAIVE_EASY_NOTE = ("기존 길찾기 방식은 신호를 기다리지 않고 보통 걸음으로 가장 짧은 길을 걸어, "
                   "정류장에 닿는 순간 떠나는 차도 탈 수 있다고 보고 계산합니다.")
NO_PLAN_EASY_TEXT = "계획대로 갈 수 있는 경로가 없습니다. 자세히 보기에서 걸러진 경로와 사유를 볼 수 있습니다."
WARNINGS_EASY_TEXT = "계산 경고 {n}건은 자세히 보기에서 볼 수 있습니다."
SIMPLE_MAP_HEIGHT_PX = 380  # 간단히 보기 지도 높이
SIMPLE_ALT_MAX = 3  # "다른 경로"의 최대 수
WALK_EASY_LABEL = "내 걸음 빠르기"  # 간단히 보기의 걷는 속도(22단계, 답 카드 바로 아래)
MODES_EASY_LABEL = "타는 것"  # 간단히 보기의 수단 켜기(24단계, 내 걸음 빠르기 아래)
WALK_ONLY_TEXT = "걷기만으로 찾습니다"
DEPART_NOW_LABEL = "지금"  # 출발 늦추기 막대의 0(26단계)
TOGGLE_OFF_RING_PX = 1.5  # 꺼진 토글 테두리 두께(25단계, page_css)
DEADLINE_EASY_LABEL = "도착해야 하는 시각 정하기"  # 간단히 보기의 마감 켜기(19단계)
LEAVE_SCAN_MAX_S = 600  # 출발 여유를 찾는 가장 긴 늦춤(초, 19단계)
LEAVE_ORIGIN_KINDS = (OriginKind.AT_NODE, OriginKind.AT_POINT)  # 출발 여유를 보이는 출발(차량 안 출발은 늦출 수 없다)
SIDE_MORE_LABEL = "경로 고르는 기준과 세부 설정"  # 간단히 보기 사이드바의 접힘(§6.9, 17단계)
BACK_TO_BEST_LABEL = "추천 경로로 돌아가기"
ALT_PICK_LABEL = "이 경로 보기"
SIMPLE_MAP_PAD_PX = 36  # 지도 맞춤 여백의 최솟값
SIMPLE_MAP_SPAN_PX = 200  # 여백 안쪽 길이의 어림(라벨 여백 계산, §6.9 의 근거)
SIMPLE_MAP_LABEL_GAP_PX = 6  # 라벨 알약과 지도 가장자리의 최소 간격(19단계 LabelFit)
SIMPLE_MAP_FOOT_PX = 24  # 아래 여백에 더하는 축척·출처 줄
SIMPLE_MAP_MAX_ZOOM = 17  # 라벨 맞춤이 키울 수 있는 가장 큰 확대 단계(19단계)
SIMPLE_MAP_BADGE_PX = 22  # 간단히 보기 지도의 단계 번호 표지 지름(19단계): 쉬운 단계 목록의 번호와 같은 수
SIMPLE_ROUTE_LAYER = "추천 경로"
SIMPLE_ENDS_LAYER = "출발·도착"

# §7.2 의 색 토큰. CSS, Folium, Altair 가 모두 이 값을 쓴다. `bg` 는 차트의 평균 점 테두리(바탕색, §7.4)다.
TOKENS_LIGHT: Mapping[str, str] = {
    "ink": "#0b0b0b",
    "ink2": "#52514e",
    "muted": "#898781",
    "grid": "#e1e0d9",
    "baseline": "#c3c2b7",
    "border": "rgba(11,11,11,0.10)",
    "safe": "#0ca30c",
    "risky": "#fab219",
    "ghost": "#d03b3b",
    "bus": "#2a78d6",
    "subway": "#eb6834",
    "bike": "#1baf7a",
    "bg": "#ffffff",
}
# 지도의 바탕 타일은 테마와 상관없이 밝다(§7.7). 지도 표지와 선의 중립 색은 이 키들의 밝은 토큰 값을 쓰고, 수단·등급 색만 테마를 따른다.
MAP_NEUTRAL_TOKENS: tuple[str, ...] = ("ink", "ink2", "muted", "grid", "baseline", "border", "bg")
TOKENS_DARK: Mapping[str, str] = {
    "ink": "#f0efec",
    "ink2": "#c3c2b7",
    "muted": "#898781",
    "grid": "#2c2c2a",
    "baseline": "#383835",
    "border": "rgba(255,255,255,0.10)",
    "safe": "#0ca30c",
    "risky": "#fab219",
    "ghost": "#d03b3b",
    "bus": "#3987e5",
    "subway": "#d95926",
    "bike": "#199e70",
    "bg": "#0e1117",
}


def theme_tokens() -> Mapping[str, str]:
    """테마가 "dark" 일 때만 어두운 토큰. 테스트 환경처럼 알 수 없으면 밝은 토큰(§7.2).
    테마는 `st.context.theme.type` 으로 알되, 세션의 첫 실행에서는 이 값이 앱 테마가 아니라 브라우저의 색 설정을 따르므로
    (Streamlit 1.67, 10단계 확인) 서버 설정 `theme.base` (실행기의 `--theme.base=light`, 사용자가 붙인 `--theme.base=dark`)가
    있으면 첫 실행은 그 값을 쓴다. 설정이 없으면 앱이 브라우저 색 설정을 따르므로 첫 실행의 값도 맞다."""
    try:
        kind = getattr(getattr(st.context, "theme", None), "type", None)
        base = st.get_option("theme.base")
        state = st.session_state
        if not state.get(THEME_SEEN_KEY) and base in ("light", "dark"):
            kind = base
        state[THEME_SEEN_KEY] = True
    except Exception:  # noqa: BLE001 - 실행 맥락 밖에서는 테마를 알 수 없다
        kind = None
    return TOKENS_DARK if kind == "dark" else TOKENS_LIGHT


def page_css(tokens: Mapping[str, str]) -> str:
    """직접 만드는 HTML 부품(§7.5)의 CSS. 글자색은 상속하고 배경은 반투명 틴트라 두 테마에서 읽힌다(§7.1, §7.7)."""
    variables = "\n".join(f"  --mr-{name}: {value};" for name, value in tokens.items())
    return f"""<style>
:root {{
{variables}
}}
[data-testid="stMainBlockContainer"] {{ padding-top: 2.2rem; padding-bottom: 2rem; }}
[data-testid="stSidebarContent"] [data-testid="stCaptionContainer"] {{ line-height: 1.45; }}
@media (min-width: {WIDE_PADDING_MIN_VIEWPORT_PX}px) {{ [data-testid="stMainBlockContainer"] {{
  padding-left: {MAIN_SIDE_PADDING_PX}px; padding-right: {MAIN_SIDE_PADDING_PX}px; }} }}
[data-testid="stSidebarContent"] button[data-variant="segmented_control"] {{ padding-left: 12px; padding-right: 12px; }}
[data-testid="stSidebarContent"] [role="radiogroup"][aria-label="{ORIGIN_KIND_LABEL}"]:has(> button:nth-child(4)) {{
  display: grid; grid-template-columns: repeat(2, minmax(0, 1fr)); }}
[data-testid="stSidebarContent"] [role="radiogroup"][aria-label="{ORIGIN_KIND_LABEL}"]:has(> button:nth-child(4)) > button:nth-child(odd) {{
  border-top-left-radius: 0.5rem; border-bottom-left-radius: 0.5rem; }}
[data-testid="stSidebarContent"] [role="radiogroup"][aria-label="{ORIGIN_KIND_LABEL}"]:has(> button:nth-child(4)) > button:nth-child(even) {{
  border-top-right-radius: 0.5rem; border-bottom-right-radius: 0.5rem; }}
.mr-num {{ font-variant-numeric: tabular-nums; }}
.st-key-mr_trip button[data-variant="segmented_control"] {{ padding-left: 12px; padding-right: 12px; }}
.st-key-mr_trip [role="radiogroup"][aria-label="{ORIGIN_KIND_LABEL}"]:has(> button:nth-child(4)) {{
  display: grid; grid-template-columns: repeat(2, minmax(0, 1fr)); }}
.st-key-mr_trip [role="radiogroup"][aria-label="{ORIGIN_KIND_LABEL}"]:has(> button:nth-child(4)) > button:nth-child(odd) {{
  border-top-left-radius: 0.5rem; border-bottom-left-radius: 0.5rem; }}
.st-key-mr_trip [role="radiogroup"][aria-label="{ORIGIN_KIND_LABEL}"]:has(> button:nth-child(4)) > button:nth-child(even) {{
  border-top-right-radius: 0.5rem; border-bottom-right-radius: 0.5rem; }}
.mr-trip {{ display: grid; gap: 4px; font-size: 1rem; line-height: 1.45; }}
.mr-trip > div {{ display: flex; gap: 10px; align-items: baseline; }}
.mr-trip .mr-tk {{ flex: none; font-size: 0.8rem; font-weight: 700; padding: 0 8px; border-radius: 999px; color: var(--mr-bg);
  background: var(--mr-ink2); line-height: 1.6; }}
.mr-trip .mr-tk.d {{ background: var(--mr-ink); }}
.mr-answer {{ --c: var(--mr-muted); border: 1px solid color-mix(in srgb, var(--c) 45%, transparent); border-left: 5px solid var(--c);
  border-radius: 10px; padding: 14px 18px; background: color-mix(in srgb, var(--c) 7%, transparent); margin: 2px 0 10px 0; }}
.mr-answer.safe {{ --c: var(--mr-safe); }}
.mr-answer.risky {{ --c: var(--mr-risky); }}
.mr-answer.ghost {{ --c: var(--mr-ghost); }}
.mr-answer .mr-ahead {{ display: flex; justify-content: space-between; align-items: center; font-size: 0.85rem; color: var(--mr-ink2); }}
.mr-answer .mr-atitle {{ font-size: 1.2rem; font-weight: 700; line-height: 1.4; margin: 4px 0 2px 0; }}
.mr-answer .mr-abig {{ display: flex; flex-wrap: wrap; align-items: baseline; gap: 4px 14px; margin: 2px 0 6px 0; }}
.mr-answer .mr-amin {{ font-size: 2.1rem; font-weight: 800; line-height: 1.15; letter-spacing: -0.01em; }}
.mr-answer .mr-aspan {{ font-size: 1.1rem; font-weight: 600; }}
.mr-answer .mr-arow {{ line-height: 1.55; }}
.mr-answer .mr-afacts {{ color: var(--mr-ink2); font-size: 0.9rem; }}
.mr-caution {{ --c: var(--mr-muted); border: 1px solid color-mix(in srgb, var(--c) 45%, transparent); border-left: 5px solid var(--c);
  border-radius: 10px; padding: 12px 16px; margin: 0 0 12px 0; background: color-mix(in srgb, var(--c) 8%, transparent); line-height: 1.6; }}
.mr-caution.ghost {{ --c: var(--mr-ghost); }}
.mr-caution.warn {{ --c: var(--mr-risky); }}
.mr-caution .mr-chead {{ display: flex; gap: 8px; align-items: flex-start; font-weight: 700; margin-bottom: 4px; line-height: 1.45; }}
.mr-caution .mr-csym {{ margin-top: 2px; width: 18px; height: 18px; border-radius: 50%; background: var(--c); color: #ffffff; font-size: 12px; font-weight: 800;
  display: inline-flex; align-items: center; justify-content: center; flex: none; }}
.mr-caution.warn .mr-csym {{ color: #0b0b0b; }}
.mr-caution p {{ margin: 0 0 2px 0; }}
.mr-caution .mr-cnote {{ margin-top: 6px; font-size: 0.85rem; color: var(--mr-ink2); }}
.mr-guide {{ --c: var(--mr-safe); border: 1px solid color-mix(in srgb, var(--c) 45%, transparent); border-left: 5px solid var(--c);
  border-radius: 10px; padding: 12px 16px; margin: 0 0 8px 0; background: color-mix(in srgb, var(--c) 8%, transparent); line-height: 1.6; }}
.mr-guide.ghost {{ --c: var(--mr-ghost); }}
.mr-guide.warn {{ --c: var(--mr-risky); }}
.mr-guide .mr-ghead {{ font-weight: 700; margin-bottom: 2px; }}
.mr-guide p {{ margin: 0 0 2px 0; }}
.mr-guide .mr-gnote {{ margin-top: 6px; font-size: 0.85rem; color: var(--mr-ink2); }}
.mr-easy {{ margin-top: 2px; }}
.mr-easy li {{ margin-bottom: 10px; }}
.mr-easy .mr-n {{ width: 24px; height: 24px; font-size: 12px; margin-top: 0; }}
.mr-easy .mr-main {{ font-weight: 600; }}
.mr-alts-h {{ font-weight: 700; margin: 8px 0 4px 0; }}
.mr-cmp-cols, .mr-cmp-v {{ display: grid; grid-template-columns: minmax(4.5em, 1fr) minmax(4.5em, 1fr) minmax(5.5em, 1fr); gap: 0 8px; }}
.mr-cmp-cols {{ font-size: 0.75rem; color: var(--mr-ink2); padding: 0 10px 2px 10px; }}
.mr-cmp {{ border: 1px solid var(--mr-border); border-radius: 8px; padding: 8px 10px; margin: 6px 0 4px 0; }}
.mr-cmp.rec {{ border: 2px solid var(--mr-safe); }}
.mr-cmp .mr-cmp-t {{ font-weight: 600; line-height: 1.45; display: flex; flex-wrap: wrap; gap: 4px 8px; align-items: center; }}
.mr-cmp .mr-cmp-name {{ word-break: keep-all; }}
.mr-cmp .mr-cmp-common {{ font-weight: 400; color: var(--mr-ink2); }}
.mr-cmp .mr-badge, .mr-cmp .mr-tag {{ font-weight: 400; font-size: 0.75rem; }}
.mr-cmp .mr-tag {{ border: 1px solid var(--mr-ink2); border-radius: 999px; padding: 0 6px; }}
.mr-cmp .mr-tag.rec {{ border-color: var(--mr-safe); }}
.mr-cmp .mr-cmp-v {{ font-size: 1.05rem; font-weight: 700; margin-top: 4px; }}
.mr-cmp .mr-cmp-note {{ font-size: 0.85rem; line-height: 1.45; margin-top: 4px; word-break: keep-all; }}
.mr-cmp .mr-cmp-note.lead {{ font-weight: 700; }}
.mr-cmp-foot {{ font-size: 0.8rem; color: var(--mr-ink2); line-height: 1.45; margin-top: 6px; word-break: keep-all; }}
.mr-aleave .mr-al {{ display: block; }}
.mr-alt {{ border-top: 1px solid var(--mr-border); padding-top: 8px; }}
.mr-alt .mr-alt-t {{ font-weight: 600; line-height: 1.45; display: flex; flex-wrap: wrap; gap: 4px 8px; align-items: center; }}
.mr-alt .mr-alt-t .mr-badge {{ font-weight: 400; font-size: 0.75rem; }}
.mr-alt .mr-tag {{ font-weight: 400; font-size: 0.75rem; border: 1px solid var(--mr-ink2); border-radius: 999px; padding: 0 6px; }}
.mr-alt .mr-alt-s {{ font-size: 0.9rem; color: var(--mr-ink2); line-height: 1.45; }}
.mr-alt .mr-alt-n {{ font-size: 0.8rem; color: var(--mr-ink2); line-height: 1.45; }}
.st-key-mr_alts {{ gap: 2px; }}
.st-key-mr_alts button p {{ font-size: 0.85rem; }}
.mr-answer .mr-anext {{ font-weight: 600; margin: 2px 0 4px 0; }}
.mr-answer .mr-anext .mr-nb {{ white-space: nowrap; }}
.st-key-mr_trip {{ gap: 0.5rem; }}
.mr-backup {{ margin-top: 4px; padding: 4px 0 4px 10px; border-left: 3px solid var(--mr-border); font-size: 0.85rem; line-height: 1.5; }}
.mr-backup .mr-nb {{ white-space: nowrap; }}
/* 꺼진 토글의 테두리(25단계): Streamlit 의 꺼진 바탕은 화면 바탕과 대비가 1.5:1 이 안 돼 "꺼짐"이 보이지 않는다. 대비 3:1 이 넘는 muted 로 테두리 */
[data-testid="stCheckbox"] label:has(input[role="switch"]:not(:checked)) > span + div {{ box-shadow: inset 0 0 0 {TOGGLE_OFF_RING_PX}px var(--mr-muted); }}
.mr-ctl-label {{ font-size: 0.875rem; margin: 0 0 -0.5rem 0; line-height: 1.6; }}
.mr-answer .mr-aleave {{ margin: 0 0 4px 0; padding: 6px 10px; border-radius: 8px; line-height: 1.5;
  background: color-mix(in srgb, var(--mr-ink) 5%, transparent); }}
.mr-answer .mr-aleave .mr-nb {{ white-space: nowrap; }}
@media (max-width: 640px) {{ [data-testid="stMainBlockContainer"] h1 {{ font-size: 1.75rem; }} }}
@media (max-width: 640px) {{
  .stApp:has(.st-key-mr_trip) [data-testid="stHeader"] {{ height: 3rem !important; min-height: 0 !important; }}
  [data-testid="stMainBlockContainer"]:has(.st-key-mr_trip) h1 {{ font-size: 1.5rem; padding-top: 0.9rem; padding-bottom: 0; }}
  .mr-answer {{ padding: 10px 14px; }}
}}
[data-testid="stMainBlockContainer"]:has(.st-key-mr_trip),
[data-testid="stMainBlockContainer"]:has(.st-key-mr_trip) * {{ word-break: keep-all; overflow-wrap: break-word; }}
.mr-chips {{ display: flex; flex-wrap: wrap; gap: 6px; align-items: center; margin: 0 0 4px 0; }}
.mr-chip {{ display: inline-flex; align-items: center; gap: 6px; padding: 2px 10px; border-radius: 999px;
  border: 1px solid var(--mr-border); background: color-mix(in srgb, currentColor 4%, transparent);
  font-size: 0.85rem; line-height: 1.5; font-variant-numeric: tabular-nums; white-space: nowrap; }}
.mr-chip.warn {{ border-color: color-mix(in srgb, var(--mr-risky) 60%, transparent);
  background: color-mix(in srgb, var(--mr-risky) 14%, transparent); }}
.mr-chip .mr-dot {{ width: 14px; height: 14px; border-radius: 50%; background: var(--mr-risky); color: #0b0b0b;
  font-size: 10px; font-weight: 700; display: inline-flex; align-items: center; justify-content: center; }}
.mr-desc {{ font-size: 1rem; margin: 2px 0 8px 0; }}
.mr-desc .mr-num {{ font-weight: 600; }}
.mr-badge {{ --c: var(--mr-muted); display: inline-flex; align-items: center; gap: 6px; padding: 1px 10px 1px 6px;
  border-radius: 999px; border: 1px solid color-mix(in srgb, var(--c) 50%, transparent);
  background: color-mix(in srgb, var(--c) 12%, transparent); font-size: 0.85rem; line-height: 1.5; white-space: nowrap; }}
.mr-badge .mr-sym {{ width: 16px; height: 16px; border-radius: 50%; background: var(--c); color: #ffffff; font-size: 10px;
  font-weight: 700; display: inline-flex; align-items: center; justify-content: center; flex: none; }}
.mr-badge.safe, .mr-badge.ok {{ --c: var(--mr-safe); }}
.mr-badge.risky {{ --c: var(--mr-risky); }}
.mr-badge.risky .mr-sym {{ color: #0b0b0b; }}
.mr-badge.ghost, .mr-badge.fail {{ --c: var(--mr-ghost); }}
.mr-badge.skip {{ --c: var(--mr-muted); }}
.mr-compare {{ margin: 4px 0 12px 0; }}
.mr-cards {{ display: grid; grid-template-columns: 1fr 1fr; gap: 12px; }}
@media (max-width: 760px) {{ .mr-cards {{ grid-template-columns: 1fr; }} }}
.mr-card {{ --c: var(--mr-muted); border: 1px solid var(--mr-border); border-radius: 8px; padding: 14px 18px; }}
.mr-card.app {{ border-left: 4px solid var(--c); background: color-mix(in srgb, var(--c) 7%, transparent); }}
.mr-card.app.safe {{ --c: var(--mr-safe); }}
.mr-card.app.risky {{ --c: var(--mr-risky); }}
.mr-card.app.ghost, .mr-card.none {{ --c: var(--mr-ghost); }}
.mr-card.none {{ border: 1px solid var(--mr-ghost); }}
.mr-card.naive.pruned {{ border-left: 4px solid var(--mr-ghost); }}
.mr-card .mr-head {{ font-size: 0.8rem; opacity: 0.7; }}
.mr-card .mr-title {{ font-size: 1.25rem; font-weight: 700; line-height: 1.4; margin: 2px 0 4px 0; }}
.mr-card .mr-badgerow {{ display: flex; flex-wrap: wrap; gap: 6px; align-items: center; margin-bottom: 6px; font-size: 0.85rem; }}
.mr-card .mr-row {{ line-height: 1.6; }}
.mr-card .mr-label {{ color: var(--mr-ink2); }}
.mr-card .mr-note {{ color: var(--mr-ink2); font-size: 0.85rem; }}
.mr-card .mr-faint {{ opacity: 0.75; }}
.mr-card .mr-msg {{ line-height: 1.6; }}
.mr-conclusion {{ margin-top: 10px; font-size: 1rem; line-height: 1.6; }}
.mr-conclusion p {{ margin: 0 0 2px 0; }}
.mr-state {{ border: 1px solid var(--mr-border); border-radius: 8px; padding: 14px 18px; margin: 4px 0 12px 0; line-height: 1.6; }}
.mr-state.ghost {{ border-color: color-mix(in srgb, var(--mr-ghost) 60%, transparent); border-left: 4px solid var(--mr-ghost);
  background: color-mix(in srgb, var(--mr-ghost) 7%, transparent); }}
.mr-tl {{ margin: 6px 0 2px 0; }}
.mr-tl .mr-bar {{ display: flex; gap: 2px; height: 22px; }}
.mr-tl .mr-seg {{ min-width: 3px; border-radius: 4px; color: #ffffff; font-size: 0.7rem; line-height: 22px; text-align: center;
  overflow: hidden; white-space: nowrap; box-sizing: border-box; }}
.mr-k-walk {{ background: var(--mr-muted); }}
.mr-k-signal_wait {{ background-color: color-mix(in srgb, var(--mr-muted) 25%, transparent);
  background-image: repeating-linear-gradient(135deg, var(--mr-muted) 0 1px, transparent 1px 4px); }}
.mr-k-bike_unlock, .mr-k-bike_dock {{ background: color-mix(in srgb, var(--mr-bike) 55%, transparent); }}
.mr-k-bike {{ background: var(--mr-bike); }}
.mr-k-bus {{ background: var(--mr-bus); }}
.mr-k-subway {{ background: var(--mr-subway); }}
.mr-k-stop_wait {{ background: transparent; border: 1px dashed var(--mr-muted); color: var(--mr-ink); }}
.mr-tl .mr-ends {{ display: flex; justify-content: space-between; font-size: 0.85rem; font-variant-numeric: tabular-nums;
  color: var(--mr-ink2); margin-top: 2px; }}
.mr-tl .mr-tlegend {{ display: flex; flex-wrap: wrap; gap: 4px 12px; font-size: 0.8rem; margin-top: 4px; font-variant-numeric: tabular-nums; }}
.mr-tl .mr-tlegend span.mr-sw {{ display: inline-block; width: 14px; height: 10px; border-radius: 2px; margin-right: 4px;
  vertical-align: -1px; box-sizing: border-box; }}
.mr-steps {{ list-style: none; padding: 0; margin: 8px 0 0 0; }}
.mr-steps li {{ display: flex; gap: 10px; align-items: flex-start; margin: 0 0 8px 0; }}
.mr-steps .mr-n {{ flex: none; width: 20px; height: 20px; border-radius: 50%; color: #ffffff; font-size: 11px; font-weight: 700;
  display: inline-flex; align-items: center; justify-content: center; margin-top: 2px; box-sizing: border-box; }}
.mr-steps .mr-n.walk, .mr-steps .mr-n.missed {{ background: transparent; border: 1.5px solid var(--mr-muted); color: inherit; }}
.mr-steps .mr-n.bike {{ background: var(--mr-bike); }}
.mr-steps .mr-n.bus {{ background: var(--mr-bus); }}
.mr-steps .mr-n.subway {{ background: var(--mr-subway); }}
.mr-steps .mr-n.arrive {{ background: var(--mr-ink); color: transparent; }}
.mr-steps .mr-main {{ font-size: 1rem; line-height: 1.5; }}
.mr-steps .mr-sub {{ font-size: 0.85rem; color: var(--mr-ink2); line-height: 1.5; }}
.mr-legend {{ display: flex; flex-wrap: wrap; gap: 4px 14px; font-size: 0.8rem; margin: 6px 0 2px 0; align-items: center; }}
.mr-legend .mr-li {{ display: inline-flex; align-items: center; gap: 5px; white-space: nowrap; }}
.mr-legend .mr-swl {{ display: inline-block; flex: none; width: 24px; height: 8px; }}
.mr-legend .mr-swd {{ display: inline-flex; flex: none; align-items: center; justify-content: center; box-sizing: border-box;
                      font-size: 9px; font-weight: 700; line-height: 1; }}
.mr-warnlist {{ margin: 0; padding-left: 1.1rem; font-size: 0.9rem; line-height: 1.6; }}
.mr-warnlist code {{ font-size: 0.8rem; }}
.mr-chiprow {{ display: flex; flex-wrap: wrap; gap: 6px; align-items: center; margin: 2px 0 8px 0; }}
.mr-callout {{ --c: var(--mr-muted); border: 1px solid color-mix(in srgb, var(--c) 45%, transparent); border-left: 4px solid var(--c);
  border-radius: 8px; padding: 10px 14px; margin: 4px 0 10px 0; line-height: 1.6;
  background: color-mix(in srgb, var(--c) 8%, transparent); }}
.mr-callout.ghost {{ --c: var(--mr-ghost); }}
.mr-callout.warn {{ --c: var(--mr-risky); }}
.mr-callout p {{ margin: 0 0 2px 0; }}
.mr-bhead {{ display: flex; flex-wrap: wrap; gap: 8px; align-items: center; margin: 18px 0 4px 0; }}
.mr-bhead .mr-bt {{ font-size: 1.05rem; font-weight: 600; line-height: 1.5; }}
.mr-verdict {{ line-height: 1.6; margin: 6px 0 4px 0; }}
.mr-verdict p {{ margin: 0 0 2px 0; }}
.mr-notes {{ margin: 0; padding-left: 1.1rem; font-size: 0.9rem; line-height: 1.6; }}
.mr-alegend {{ display: flex; flex-wrap: wrap; gap: 4px 16px; font-size: 0.8rem; margin: 4px 0 0 0; align-items: center; }}
.mr-alegend .mr-li {{ display: inline-flex; align-items: center; gap: 6px; white-space: nowrap; }}
.mr-alegend .mr-am {{ display: inline-block; flex: none; box-sizing: border-box; }}
.mr-alegend .mr-am.mean {{ width: 8px; height: 8px; border-radius: 50%; background: var(--mr-ink); }}
.mr-alegend .mr-am.mid {{ width: 2px; height: 12px; background: var(--mr-ink2); }}
.mr-alegend .mr-am.range {{ width: 18px; height: 2px; background: var(--mr-ink2); }}
.mr-alegend .mr-am.promise {{ font-size: 13px; line-height: 1; font-weight: 700; color: var(--mr-muted); }}
.mr-stages .mr-slegend {{ display: flex; flex-wrap: wrap; gap: 4px 12px; font-size: 0.8rem; margin-top: 4px; font-variant-numeric: tabular-nums; }}
.mr-phase {{ max-width: 560px; margin: 8px 0 4px 0; }}
.mr-phase .mr-ph-head {{ font-size: 0.9rem; font-weight: 600; line-height: 1.5; margin-bottom: 2px; }}
.mr-phase .mr-ph-track {{ position: relative; padding-top: 20px; }}
.mr-phase .mr-ph-bar {{ display: flex; gap: 2px; height: 16px; }}
.mr-phase .mr-ph-bar > span {{ display: block; min-width: 2px; }}
.mr-phase .mr-ph-green {{ background: var(--mr-safe); border-radius: 4px 0 0 4px; }}
.mr-phase .mr-ph-red {{ background: var(--mr-ghost); border-radius: 0 4px 4px 0; }}
.mr-phase .mr-ph-hatch {{ flex: 1 1 auto; position: relative; border-radius: 4px;
  background-color: color-mix(in srgb, var(--mr-muted) 25%, transparent);
  background-image: repeating-linear-gradient(135deg, var(--mr-muted) 0 1px, transparent 1px 4px); }}
.mr-phase .mr-ph-edge {{ position: absolute; top: 0; bottom: 0; width: 1px; background: var(--mr-muted); }}
.mr-phase .mr-ph-tau {{ position: absolute; top: 16px; height: 24px; width: 2px; margin-left: -1px; background: var(--mr-ink); }}
.mr-phase .mr-ph-label {{ position: absolute; top: 0; font-size: 0.8rem; line-height: 16px; white-space: nowrap;
  font-variant-numeric: tabular-nums; }}
.mr-phase .mr-ph-ticks {{ position: relative; height: 18px; margin-top: 3px; font-size: 0.75rem; color: var(--mr-ink2);
  font-variant-numeric: tabular-nums; }}
.mr-phase .mr-ph-ticks span {{ position: absolute; top: 0; white-space: nowrap; }}
.mr-phase .mr-ph-note {{ font-size: 0.85rem; color: var(--mr-ink2); margin-top: 2px; font-variant-numeric: tabular-nums; }}
</style>"""


# ===== U2. 표시 도구 =====

_WEEKDAYS_KO = "월화수목금토일"


def _half(x: float) -> int:
    """화면의 반올림 $\\lfloor x + 0.5 \\rfloor$ (§6.5)."""
    return math.floor(x + 0.5)


def _fixed(x: float, digits: int) -> str:
    """소수 `digits` 자리 고정 표기. 반올림은 $\\lfloor x \\cdot 10^d + 0.5 \\rfloor$, 정수부는 천 단위 쉼표."""
    scale = 10**digits
    n = math.floor(x * scale + 0.5)
    sign = "-" if n < 0 else ""
    whole, frac = divmod(abs(n), scale)
    return f"{sign}{whole:,}" + (f".{frac:0{digits}d}" if digits else "")


def fmt_clock(clock_s: float, t_s: float) -> str:
    """시계 시각 "HH:MM:SS". $v = \\lfloor c_0 + t + 0.5 \\rfloor$ 가 86,400 이상이면 " (다음 날)"을 붙인다."""
    v = _half(clock_s + t_s)
    day = v % SECONDS_PER_DAY
    text = f"{day // 3600:02d}:{day % 3600 // 60:02d}:{day % 60:02d}"
    return f"{text} (다음 날)" if v >= SECONDS_PER_DAY else text


def fmt_dur(s: float) -> str:
    """시간: 60초 미만이면 "{v}초", 아니면 "{분}분 {초 두 자리}초"(분은 59 를 넘을 수 있다)."""
    v = _half(s)
    if v < 60:
        return f"{v}초"
    return f"{v // 60}분 {v % 60:02d}초"


def fmt_delta_dur(s: float) -> str:
    """시간 변화량: ASCII "+" 나 "-" 로 시작한다. 반올림한 값이 0 이면 "0초"."""
    v = _half(s)
    if v == 0:
        return "0초"
    return ("+" if v > 0 else "-") + fmt_dur(abs(v))


def fmt_date(iso: str) -> str:
    """날짜 "YYYY-MM-DD(요일)"."""
    day = datetime.date.fromisoformat(iso)
    return f"{day.isoformat()}({_WEEKDAYS_KO[day.weekday()]})"


def fmt_won(krw: float) -> str:
    return f"{_half(krw):,}원"


def fmt_delta_won(krw: float) -> str:
    """요금 변화량: "-500원", "+1,000원". 반올림한 값이 0 이면 "변동 없음"."""
    v = _half(krw)
    if v == 0:
        return "변동 없음"
    return f"{'+' if v > 0 else '-'}{abs(v):,}원"


def fmt_pct(p: float) -> str:
    return f"{100 * p:.1f}%"


def fmt_dist(m: float) -> str:
    """거리: 반올림한 m 가 1,000 미만이면 "{m} m", 아니면 km 를 소수 둘째 자리로."""
    v = _half(m)
    if v < 1000:
        return f"{v} m"
    return f"{_fixed(m / 1000.0, 2)} km"


def fmt_speed(mps: float) -> str:
    return f"{_fixed(mps, 2)} m/s"


def fmt_mult(x: float) -> str:
    return f"{_fixed(x, 2)}배"


def fmt_rate(per_hour: float) -> str:
    return f"{_fixed(per_hour, 1)}건/시"


def _clock_or_dash(clock_s: float, t_s: float | None) -> str:
    return "-" if t_s is None else fmt_clock(clock_s, t_s)


def _kst_clock(unix_s: float) -> str:
    return datetime.datetime.fromtimestamp(unix_s, KST).strftime("%H:%M:%S")


def esc(text: Any) -> str:
    """데이터에서 온 글자를 HTML 에 넣을 때(§7.5)."""
    return html.escape(str(text), quote=True)


_MD_SPECIAL = set("\\`*_{}[]<>#|~$")


def md_escape(text: str) -> str:
    """데이터에서 온 글자를 마크다운 라벨(라디오 선택지)에 넣을 때 특수 문자를 글자 그대로 보이게 한다."""
    return "".join(f"\\{ch}" if ch in _MD_SPECIAL else ch for ch in str(text))


# --- 이름표 (§6.5) ---

ORIGIN_CHOICE_NAMES: Mapping[str, str] = {"PLACE": "장소", "POINT": "지도에서", "TRAIN": "지금 탄 열차", "BUS": "지금 탄 버스"}
ORIGIN_KIND_TO_CHOICE: Mapping[OriginKind, str] = {
    OriginKind.AT_NODE: "PLACE", OriginKind.AT_POINT: "POINT", OriginKind.ON_TRAIN: "TRAIN", OriginKind.ON_BUS: "BUS",
}
DEST_CHOICE_NAMES: Mapping[str, str] = {"PLACE": "장소", "POINT": "지도에서"}
MAP_PICK_NAMES: Mapping[str, str] = {"ORIGIN": "출발", "DESTINATION": "목적지"}
# 지금 위치의 안내 문구(§6.8)
GPS_ERROR_TEXTS: Mapping[str, str] = {
    "PERMISSION_DENIED": "위치 권한이 없어 지금 위치를 받지 못했습니다. 브라우저의 사이트 설정에서 위치를 허용한 뒤 다시 누르세요.",
    "POSITION_UNAVAILABLE": "기기가 지금 위치를 찾지 못했습니다. 잠시 뒤 다시 누르거나 지도에서 출발을 찍으세요.",
    "TIMEOUT": f"{GPS_TIMEOUT_MS // 1000}초 안에 위치를 받지 못했습니다. 다시 누르거나 지도에서 출발을 찍으세요.",
    "UNSUPPORTED": "이 브라우저는 위치 기능을 지원하지 않습니다. 지도에서 출발을 찍으세요.",
    "INSECURE": "브라우저는 https 주소나 이 컴퓨터의 localhost 주소에서만 위치를 줍니다. 지금 주소에서는 지도에서 출발을 찍으세요.",
    "BAD_FIX": "받은 위치 값이 올바르지 않습니다. 다시 누르거나 지도에서 출발을 찍으세요.",
}
GPS_VIRTUAL_PREFIX = "지금 시나리오는 가상 노선이라 지금 위치를 출발로 쓰지 않습니다. "
GPS_OTHER_TEXT = "지금 위치는 다른 시나리오의 지역 안입니다. 아래에서 고르면 그 시나리오로 바꿔 지금 위치에서 출발합니다."
GPS_SWITCH_LABEL = "바꿔 출발: {label}"


def gps_outside_text(nearest: tuple[str, str, float] | None) -> str:
    """OUTSIDE 문구(§6.8). `nearest` 는 가장 가까운 곳의 (시나리오 표시 이름, 노드 이름, 거리 m), 가상이 아닌 시나리오가 없으면 None."""
    head, tail = "지금 위치는 데이터가 준비된 지역 밖입니다", " 지도에서 출발을 찍거나 장소를 고르세요."
    if nearest is None:
        return f"{head}.{tail}"
    label, name, distance = nearest
    return f"{head}(가장 가까운 곳: {label}, {name}까지 {fmt_dist(distance)}).{tail}"


def gps_accuracy_text(accuracy_m: float) -> str:
    return f"위치 정확도가 ±{fmt_dist(accuracy_m)}입니다. 실제 위치와 다르면 지도를 눌러 고쳐 찍으세요."


def gps_point_line(gps: Mapping[str, float]) -> str:
    """사이드바 "지도에서" 아래의 첫 줄: "지금 위치 {위도}, {경도} · 정확도 ±{거리}" (§6.8)."""
    return f"{GPS_ORIGIN_NAME} {gps['lat']:.5f}, {gps['lon']:.5f} · 정확도 ±{fmt_dist(gps['accuracy_m'])}"
RUN_NAMES: Mapping[SearchRun, str] = {
    SearchRun.FULL: "기본 탐색", SearchRun.NO_BIKE: "따릉이 없이", SearchRun.BUS_ONLY: "버스만", SearchRun.SUBWAY_ONLY: "지하철만",
    SearchRun.SLOW: "느린 걸음 기준", SearchRun.AVERSE: "신호 피하기", SearchRun.NAIVE: "기존 앱 방식",
}
WAIT_RULE_NAMES: Mapping[WaitRule, str] = {WaitRule.EXPECTED: "평균 대기", WaitRule.WORST: "가장 긴 대기", WaitRule.NONE: "신호 무시"}
GRADE_NAMES: Mapping[Grade, str] = {Grade.SAFE: "안전", Grade.RISKY: "주의", Grade.GHOST: "유령"}
# 간단히 보기의 등급 말(32단계): 갈아탈 차를 탈 수 있는지를 소비자 말로
EASY_GRADE_NAMES: Mapping[Grade, str] = {Grade.SAFE: "여유 있음", Grade.RISKY: "빠듯함", Grade.GHOST: "놓치기 쉬움"}
STATUS_NAMES: Mapping[RouteStatus, str] = {RouteStatus.RANKED: "순위", RouteStatus.GHOST_PRUNED: "걸러짐"}
REASON_NAMES: Mapping[ReasonCode, str] = {
    ReasonCode.LAST_VEHICLE_RISK: "막차 위험", ReasonCode.LOW_PLAN_PROBABILITY: "확률 낮음", ReasonCode.UNREACHABLE: "도착 불가",
}
RANK_NAMES: Mapping[RankCriterion, str] = {
    RankCriterion.MEAN_ARRIVAL: "평균 도착", RankCriterion.P90_ARRIVAL: "90% 도착", RankCriterion.ON_TIME: "마감 확률",
    RankCriterion.UTILITY: "종합 점수",
}
RANK_CHOICE_NAMES: Mapping[str, str] = {
    "MEAN_ARRIVAL": "평균 도착이 이른 순", "P90_ARRIVAL": "90% 도착이 이른 순", "ON_TIME": "마감까지 도착할 확률이 높은 순",
    "UTILITY": "종합 점수 순",
}
RANK_HELP = (
    "평균 도착이 이른 순: 걷는 속도와 신호, 차를 놓칠 경우까지 넣은 도착 시각의 평균으로 정렬합니다. "
    "90% 도착이 이른 순: 열 번 가운데 아홉 번은 그보다 일찍 닿는 시각으로 정렬합니다. "
    "마감까지 도착할 확률이 높은 순: 도착 마감 시각까지 닿을 확률로 정렬합니다. "
    "종합 점수 순: 시간, 요금, 위험을 가중치로 더한 점수가 낮은 순입니다."
)
TIME_SOURCE_NAMES: Mapping[TimeSource, str] = {
    TimeSource.PREDICTED: "도착 예측", TimeSource.EXTENDED: "예측에 운행시간을 이음", TimeSource.HEADWAY: "배차 간격으로 이음",
    TimeSource.TIMETABLE: "시각표",
}
RUN_TIME_SOURCE_NAMES: Mapping[RunTimeSource, str] = {RunTimeSource.PREDICTION: "예측에서", RunTimeSource.DESIGN: "설계 속도"}
LEG_NAMES: Mapping[LegKind, str] = {
    LegKind.WALK: "걷기", LegKind.SIGNAL_WAIT: "신호 대기", LegKind.BIKE_UNLOCK: "대여", LegKind.BIKE: "따릉이",
    LegKind.BIKE_DOCK: "반납", LegKind.STOP_WAIT: "기다림", LegKind.BUS: "버스", LegKind.SUBWAY: "지하철",
}
STATION_USE_NAMES: Mapping[StationUse, str] = {
    StationUse.AVAILABLE: "빌릴 수 있음", StationUse.NO_BIKE: "자전거 없음", StationUse.LOW_P_BIKE: "남을 확률 낮음",
}
SIGNAL_STATE_NAMES: Mapping[SignalState, str] = {SignalState.GREEN: "녹색", SignalState.RED: "적색", SignalState.STOCHASTIC: "위상 모름"}
ROUTE_TYPE_NAMES: Mapping[BusRouteType, str] = {
    BusRouteType.TRUNK: "간선", BusRouteType.BRANCH: "지선", BusRouteType.CIRCULAR: "순환", BusRouteType.WIDE_AREA: "광역",
    BusRouteType.NIGHT: "심야", BusRouteType.VILLAGE: "마을",
}
PROB_METHOD_NAMES: Mapping[ProbMethod, str] = {
    ProbMethod.EXACT: "정확 계산", ProbMethod.QMC: "준난수", ProbMethod.DEGENERATE: "걷는 속도 변동 없음",
}
FARE_BREAK_NAMES: Mapping[str, str] = {
    "WINDOW": "환승 인정 시간 초과", "MAX_RIDES": "환승 횟수 초과", "SAME_LINE": "같은 노선 다시 탐",
    "SUBWAY_OUTSIDE": "지하철을 역 밖에서 갈아탐",
}
MODE_NAMES: Mapping[str, str] = {"SIMULATION": "시뮬레이션", "REPLAY": "기록 재생", "LIVE": "실시간"}
SOURCE_NAMES: Mapping[SourceKind, str] = {
    SourceKind.BUS_ARRIVAL: "버스 도착", SourceKind.BIKE: "따릉이", SourceKind.SIGNAL: "신호", SourceKind.SUBWAY_TIMETABLE: "지하철 시각표",
}
SOURCE_STATE_NAMES: Mapping[SourceState, str] = {SourceState.SUCCESS: "성공", SourceState.FAILED: "실패", SourceState.SKIPPED: "건너뜀"}
SIGNAL_SOURCE_NAMES: Mapping[SignalSource, str] = {SignalSource.DESIGN: "설계 현시", SignalSource.LEARNED: "기록 학습"}
DAY_TYPE_NAMES: Mapping[DayType, str] = {DayType.WEEKDAY: "평일", DayType.SATURDAY: "토요일", DayType.HOLIDAY: "일요일·공휴일"}
POINT_NAMES: Mapping[str, str] = {ce.ORIGIN_POINT_ID: "찍은 출발점", ce.DESTINATION_POINT_ID: "찍은 목적지"}
WEIGHT_CUSTOM = "직접 설정"
WALK_CUSTOM = "직접"
TRAVEL_MODE_NAMES: Mapping[TravelMode, str] = {TravelMode.BUS: "버스", TravelMode.SUBWAY: "지하철", TravelMode.BIKE: "따릉이"}
NODE_TYPE_NAMES: Mapping[NodeType, str] = {
    NodeType.PLACE: "장소", NodeType.INTERSECTION: "교차로", NodeType.WAYPOINT: "경유점", NodeType.BUS_STOP: "정류장",
    NodeType.SUBWAY_PLATFORM: "승강장", NodeType.STATION_HALL: "역 안", NodeType.STATION_EXIT: "역 출구",
    NodeType.BIKE_STATION: "대여소", NodeType.POINT: "찍은 점",
}
MODEL_KIND_NAMES: Mapping[str, str] = {"SIGNAL": "신호", "BIKE": "따릉이"}


def ride_name(ride) -> str:
    """탑승 노선 이름(§6.5): 버스는 "{노선 번호}번", 지하철은 `Ride.route_name`, 묶음 탑승(§1.7.4)은 `Ride.bundle_name`."""
    if ride.bundle:
        return ride.bundle_name
    return f"{ride.route_name}번" if ride.mode == TravelMode.BUS else ride.route_name


def vehicle_route(ride, trip_id: str, scenario: Scenario | None) -> str:
    """차량이 다니는 노선 ID 또는 패턴 ID. 묶음 탑승(§1.7.4)이면 묶음의 노선 가운데 그 차량의 노선이고, 아니면 탑승의 노선이다.
    버스 차량 ID 는 "{노선 ID}:{차량}" 이고(§1.7.1), 지하철 열차 ID 는 같은 호선·방향 안에서 겹치지 않는다(§1.7.2)."""
    if not ride.bundle:
        return ride.route_id
    ids = tuple(line.route_id for line in ride.bundle)
    if ride.mode == TravelMode.BUS:
        found = [route_id for route_id in ids if trip_id.startswith(f"{route_id}:")]
        return max(found, key=len) if found else ride.route_id
    for pattern in scenario.subway_patterns if scenario is not None else ():
        if pattern.id in ids and any(trip.id == trip_id for trip in pattern.trips):
            return pattern.id
    return ride.route_id


def vehicle_line_name(ride, route_id: str, trip_id: str, scenario: Scenario | None) -> str:
    """차량 노선 이름(§6.5 몇 번째 차): 버스는 "{BusLine.name}번", 지하철은 "{패턴 마지막 역 이름}행"이고 급행 열차면 앞에 "급행 ".
    시나리오 없이 부르면(`conclusion_lines` 의 기본값, §8.1) 지하철은 그 노선의 `BundleLine.route_name` 이다."""
    line = next((item for item in ride.bundle if item.route_id == route_id), None)
    name = line.route_name if line is not None else (ride.route_name if route_id == ride.route_id else route_id)
    if ride.mode == TravelMode.BUS:
        return f"{name}번"
    if scenario is not None:
        stations = {station.key: station.name for station in scenario.subway_stations}
        for pattern in scenario.subway_patterns:
            if pattern.id == route_id:
                express = any(trip.id == trip_id and trip.express for trip in pattern.trips)
                last = stations.get(pattern.station_keys[-1], pattern.station_keys[-1])
                return f"{'급행 ' if express else ''}{last}행"
    return name


def nth_vehicle(ride, option, scenario: Scenario | None) -> str:
    """몇 번째 차(§6.5): "{n}번째 차". 묶음 탑승의 문장에서는 앞에 차량 노선 이름을 붙인다(예 "가상8번 1번째 차")."""
    text = f"{option.ordinal}번째 차"
    if not ride.bundle:
        return text
    return f"{vehicle_line_name(ride, option.route_id, option.trip_id, scenario)} {text}"


def full_text(option) -> str:
    """만차 칸(§6.3 ② 탭의 2): 승차 순번의 시각 출처가 `PREDICTED` 가 아닌데 만차면 앞 정류장의 표시를 이어 쓴 것이다(§1.7.3)."""
    if not option.is_full:
        return "아니오"
    return "예" if option.time_source == TimeSource.PREDICTED else "예(앞 정류장 표시)"


def node_names(scenario: Scenario | None) -> dict[str, str]:
    """노드와 대여소 ID → 이름. 지도에서 찍은 점은 엔진이 붙이는 노드라 화면 이름을 따로 둔다."""
    names = dict(POINT_NAMES)
    if scenario is not None:
        names.update({node.id: node.name for node in scenario.nodes})
        names.update({station.id: station.name for station in scenario.bike_stations})
    return names


EARLIER_OK_TEXT = "더 일찍 닿으면 앞차를 타도 됩니다."  # 유령 환승 줄 끝(§6.9, 21단계)
EASY_STOP_SUFFIX = " 정류장"  # 간단히 보기의 버스 정류장 이름 뒤(§6.9, 20단계)


def easy_names(scenario: Scenario | None) -> dict[str, str]:
    """간단히 보기의 지점 이름(§6.9, 20단계): `node_names` 와 같되 버스 정류장 노드의 이름에 "정류장"도 "정류소"도 없으면 뒤에
    " 정류장"을 붙인다. 서울 정류장 이름은 "지하철2호선강남역", "신사역" 처럼 역 이름과 같아 지하철역으로 걸어가게 할 수 있다."""
    names = node_names(scenario)
    if scenario is not None:
        for node in scenario.nodes:
            if node.node_type == NodeType.BUS_STOP and "정류장" not in node.name and "정류소" not in node.name:
                names[node.id] = node.name + EASY_STOP_SUFFIX
    return names


def stop_number(node_id: str | None, scenario: Scenario | None) -> str | None:
    """정류장 번호(§6.9, 20단계): 버스 정류장 노드의 공식 번호(arsId)가 숫자 다섯 자리이면 그 번호, 아니면 None.
    서울 정류장 표지판에 적힌 번호라, 길 양쪽에 같은 이름의 정류장이 있어도 탈 쪽을 찾을 수 있다."""
    if scenario is None or not node_id:
        return None
    node = next((item for item in scenario.nodes if item.id == node_id), None)
    if node is None or node.node_type != NodeType.BUS_STOP or node.official_id is None:
        return None
    return node.official_id if re.fullmatch(r"[0-9]{5}", node.official_id) else None


def _items(output: EngineOutput) -> dict[str, ItineraryResult]:
    return {it.itinerary_id: it for it in output.itineraries}


def _vehicle(boarding, trip_id: str | None):
    if boarding is None or trip_id is None:
        return None
    return next((option for option in boarding.vehicles if option.trip_id == trip_id), None)


def _boardings(it: ItineraryResult) -> dict[int, Any]:
    return {boarding.ride_index: boarding for boarding in it.boardings}


def reason_text(code: ReasonCode | str, itinerary: ItineraryResult, output: EngineOutput, config: EngineConfig) -> str:
    """걸러진 사유 문장(§6.5). 값은 설정과 결과에서 채운다."""
    code = ReasonCode(code)
    threshold = fmt_pct(config.p_ghost)
    if code == ReasonCode.LAST_VEHICLE_RISK:
        boardings = itinerary.boardings
        boarding = next((b for b in boardings if not b.guided_found), boardings[-1] if boardings else None)
        if boarding is None:
            return f"막차까지 따져도 계획대로 탈 확률이 기준 {threshold}에 못 미칩니다."
        ride = next((r for r in itinerary.rides if r.index == boarding.ride_index), None)
        name = ride_name(ride) if ride is not None else "-"
        return (f"탑승 {boarding.ride_index}({name})에서 막차까지 따져도 계획대로 탈 확률이 {fmt_pct(boarding.q_joint)}로 "
                f"기준 {threshold}에 못 미칩니다.")
    if code == ReasonCode.LOW_PLAN_PROBABILITY:
        text = f"계획대로 갈 확률 {fmt_pct(itinerary.p_star)}가 기준 {threshold}에 못 미칩니다"
        if itinerary.p_bikes:
            p_bike = math.prod(itinerary.p_bikes)
            if itinerary.boardings:
                text += f"(자전거가 남아 있을 확률 {fmt_pct(p_bike)} × 차를 탈 확률 {fmt_pct(itinerary.boardings[-1].q_joint)})"
            else:
                text += f"(자전거가 남아 있을 확률 {fmt_pct(p_bike)})"
        return text + "."
    return "어떤 걸음 속도로도 도착하지 못합니다. 차를 놓치거나 자전거가 없을 때 걸을 길이 없습니다."


# --- 정보 배지와 등급 배지 (§7.5) ---

_GRADE_CLASS = {Grade.SAFE: ("safe", "✓"), Grade.RISKY: ("risky", "!"), Grade.GHOST: ("ghost", "✕")}


def badge_html(text: str, css: str, symbol: str) -> str:
    return f'<span class="mr-badge {css}"><span class="mr-sym">{esc(symbol)}</span>{esc(text)}</span>'


def grade_badge(grade: Grade, *, easy: bool = False) -> str:
    """등급 배지. `easy` 면 간단히 보기의 말(32단계 `EASY_GRADE_NAMES`)."""
    css, symbol = _GRADE_CLASS[Grade(grade)]
    return badge_html((EASY_GRADE_NAMES if easy else GRADE_NAMES)[Grade(grade)], css, symbol)


def source_badge(state: SourceState) -> str:
    css, symbol = {SourceState.SUCCESS: ("ok", "✓"), SourceState.FAILED: ("fail", "✕"), SourceState.SKIPPED: ("skip", "–")}[state]
    return badge_html(SOURCE_STATE_NAMES[state], css, symbol)


def chip_html(text: str, *, warn: bool = False, title: str | None = None) -> str:
    title_attr = f' title="{esc(title)}"' if title else ""
    dot = '<span class="mr-dot">!</span>' if warn else ""
    return f'<span class="mr-chip{" warn" if warn else ""}"{title_attr}>{dot}{esc(text)}</span>'


# --- 비교 패널과 결론 문장 (§6.3, §7.5 mr-compare) ---


def _row(label: str, value: str, note: str = "", *, faint: bool = False) -> str:
    note_html = f' <span class="mr-note">{esc(note)}</span>' if note else ""
    css = "mr-row mr-faint" if faint else "mr-row"
    return f'<div class="{css}"><span class="mr-label">{esc(label)}</span> <span class="mr-num">{esc(value)}</span>{note_html}</div>'


def _mean_p90_row(label: str, clock_s: float, mean_s: float | None, p90_s: float | None) -> str:
    return (f'<div class="mr-row"><span class="mr-label">{esc(label)}</span> <span class="mr-num">{esc(_clock_or_dash(clock_s, mean_s))}</span>'
            f' · <span class="mr-label">90%</span> <span class="mr-num">{esc(_clock_or_dash(clock_s, p90_s))}</span></div>')


def _naive_card(output: EngineOutput) -> str:
    cmp = output.comparison
    naive = _items(output).get(cmp.naive_best_id) if cmp.naive_best_id else None
    head = '<div class="mr-head">기존 앱 방식의 1위</div>'
    if naive is None:
        return f'<div class="mr-card naive">{head}<div class="mr-msg">기존 앱 방식으로는 경로를 찾지 못했습니다.</div></div>'
    pruned = cmp.naive_status == RouteStatus.GHOST_PRUNED
    badges = []
    if pruned:
        badges.append(badge_html("걸러짐", "ghost", "✕"))
        badges.extend(f"<span>{esc(REASON_NAMES[reason])}</span>" for reason in cmp.naive_reasons)
    else:
        badges.append(grade_badge(naive.grade))
    if naive.ghost_count:
        badges.append(badge_html(f"유령 환승 {naive.ghost_count}", "ghost", "✕"))
    c0 = output.clock_s
    promised = "약속 없음(탈 차량 없음)" if cmp.naive_promised_s is None else fmt_clock(c0, cmp.naive_promised_s)
    rows = (
        _row("약속 도착", promised, "기존 앱이 안내할 도착")
        + _mean_p90_row("이 앱이 계산한 평균 도착", c0, cmp.naive_mean_s, cmp.naive_p90_s)
        + _row("계획대로 갈 확률", "-" if cmp.naive_p_star is None else fmt_pct(cmp.naive_p_star))
    )
    css = "mr-card naive pruned" if pruned else "mr-card naive"
    return (f'<div class="{css}">{head}<div class="mr-title">{esc(naive.label)}</div>'
            f'<div class="mr-badgerow">{"".join(badges)}</div>{rows}</div>')


def _best_card(output: EngineOutput) -> str:
    best = _items(output).get(output.comparison.best_id) if output.comparison.best_id else None
    head = '<div class="mr-head">이 앱의 추천</div>'
    if best is None:
        return (f'<div class="mr-card app none">{head}<div class="mr-msg">계획대로 갈 수 있는 경로가 없습니다. '
                "걸러진 경로와 사유는 오른쪽 목록에 있습니다.</div></div>")
    c0 = output.clock_s
    grade_css = _GRADE_CLASS[best.grade][0]
    promised = "약속 없음(탈 차량 없음)" if best.naive_promised_s is None else fmt_clock(c0, best.naive_promised_s)
    rows = (
        _row("약속 도착", promised, "기존 앱 방식으로 보면", faint=True)
        + _mean_p90_row("평균 도착", c0, best.arrival.mean_s, best.arrival.p90_s)
        + _row("계획대로 갈 확률", fmt_pct(best.p_star))
    )
    return (f'<div class="mr-card app {grade_css}">{head}<div class="mr-title">{esc(best.label)}</div>'
            f'<div class="mr-badgerow">{grade_badge(best.grade)}</div>{rows}</div>')


def snap_failed_text(distance_m: float | None, config: EngineConfig) -> str:
    """찍은 점을 길에 붙이지 못했을 때의 카드 문장(§6.4)."""
    limit = fmt_dist(config.snap_max_m)
    if distance_m is None:
        return f"찍은 점을 길에 붙이지 못했습니다(최대 {limit}). 길 가까이를 다시 찍으세요."
    return f"찍은 점이 길에서 {fmt_dist(distance_m)} 떨어져 있습니다(최대 {limit}). 길 가까이를 다시 찍으세요."


def no_route_text(output: EngineOutput) -> str:
    return (f"경로가 없습니다. 세부 조건에서 탐색 타원 계수(지금 {_fixed(output.config.gamma, 2)})를 키우거나 "
            "수단을 켜 보세요.")


def compare_panel_html(output: EngineOutput, config: EngineConfig, scenario: Scenario | None = None, *,
                       snap_distance_m: float | None = None) -> str:
    """비교 패널 HTML(§6.3). 찍은 점을 붙이지 못했거나 경로가 없으면 패널 자리의 상태 카드(§6.4). `scenario` 는 결론 문장에 넘긴다."""
    if output.status == EngineStatus.SNAP_FAILED:
        return f'<div class="mr-state ghost">{esc(snap_failed_text(snap_distance_m, config))}</div>'
    if output.status == EngineStatus.NO_ROUTE:
        return f'<div class="mr-state">{esc(no_route_text(output))}</div>'
    lines = "".join(f"<p>{esc(line)}</p>" for line in conclusion_lines(output, config, scenario))
    return (f'<div class="mr-compare"><div class="mr-cards">{_naive_card(output)}{_best_card(output)}</div>'
            f'<div class="mr-conclusion">{lines}</div></div>')


def _first_ghost(it: ItineraryResult, scenario: Scenario | None) -> tuple[str, float, str | None] | None:
    """첫 유령 환승의 (탑승 노선 이름, 기존 앱 차량의 탈 확률, 안내 차량의 몇 번째 차). 몇 번째 차는 `nth_vehicle` 의 글이다."""
    rides = {ride.index: ride for ride in it.rides}
    for boarding in it.boardings:
        if not boarding.ghost or boarding.p_catch_naive is None:
            continue
        ride = rides.get(boarding.ride_index)
        guided = _vehicle(boarding, boarding.guided_trip_id)
        nth = None if guided is None else (nth_vehicle(ride, guided, scenario) if ride is not None else f"{guided.ordinal}번째 차")
        return (ride_name(ride) if ride else "-", boarding.p_catch_naive, nth)
    return None


def _late_text(late_s: float | None) -> str:
    if late_s is None:
        return "-"
    v = _half(late_s)
    if v > 0:
        return f"{fmt_dur(v)} 늦음"
    if v < 0:
        return f"{fmt_dur(-v)} 이름"
    return "약속과 같음"


def _criterion_comparison(criterion: RankCriterion, best: ItineraryResult, naive: ItineraryResult | None,
                          output: EngineOutput) -> str | None:
    cmp = output.comparison
    if criterion == RankCriterion.P90_ARRIVAL and best.arrival.p90_s is not None and cmp.naive_p90_s is not None:
        return f"90% 도착이 {fmt_dur(cmp.naive_p90_s - best.arrival.p90_s)} 이릅니다"
    if criterion == RankCriterion.ON_TIME and best.arrival.p_on_time is not None and naive is not None \
            and naive.arrival.p_on_time is not None:
        return f"마감까지 도착할 확률이 {fmt_pct(best.arrival.p_on_time)}로 {fmt_pct(naive.arrival.p_on_time)}보다 높습니다"
    if criterion == RankCriterion.UTILITY and best.utility is not None:
        if naive is not None and naive.utility is not None:
            return f"종합 점수가 {_fixed(best.utility.total, 3)}로 {_fixed(naive.utility.total, 3)}보다 낮습니다"
        return f"종합 점수가 {_fixed(best.utility.total, 3)}로 가장 낮습니다"
    return None


def _recommend_line(output: EngineOutput, best: ItineraryResult, naive: ItineraryResult | None) -> str:
    cmp = output.comparison
    c0 = output.clock_s
    mean = _clock_or_dash(c0, best.arrival.mean_s)
    saving = cmp.saving_s
    if saving is None or naive is None:
        return f"이 앱의 추천은 평균 {mean}에 도착합니다."
    if _half(saving) > 0:
        return f"이 앱의 추천은 평균 {mean}에 도착해 {fmt_dur(saving)} 줄입니다."
    criterion = output.config.rank_criterion
    if criterion == RankCriterion.MEAN_ARRIVAL:
        return f"이 앱의 추천은 평균 {mean}에 도착해 기존 앱 방식의 1위와 평균 도착이 같습니다."
    comparison = _criterion_comparison(criterion, best, naive, output)
    late = f"평균 도착은 {fmt_dur(-saving)} 늦지만" if _half(saving) < 0 else "평균 도착은 같지만"
    if comparison is None:
        return f"이 앱의 추천은 {RANK_NAMES[criterion]} 기준으로 골랐습니다."
    return f"이 앱의 추천은 {RANK_NAMES[criterion]} 기준이라 {late} {comparison}."


def conclusion_lines(output: EngineOutput, config: EngineConfig, scenario: Scenario | None = None) -> tuple[str, ...]:
    """비교 패널 아래 결론 문장(§6.3). 시나리오별 문구를 적어 두지 않고 결과에서 만든다. `scenario` 는 묶음 탑승의 차량 노선
    이름(§6.5)에 쓰고, 화면은 지금 시나리오를 넘긴다(§8.1)."""
    cmp = output.comparison
    items = _items(output)
    naive = items.get(cmp.naive_best_id) if cmp.naive_best_id else None
    best = items.get(cmp.best_id) if cmp.best_id else None
    c0 = output.clock_s
    if cmp.same and best is not None:
        lines = ["기존 앱 방식의 1위와 이 앱의 추천이 같은 경로입니다."]
        ghost = _first_ghost(best, scenario)
        if ghost is not None:
            name, p_naive, nth = ghost
            guided = f"{nth}를" if nth is not None else "다른 차를"
            lines.append(f"다만 기존 앱이 안내하는 {name} 차량은 탈 확률이 {fmt_pct(p_naive)}라, 이 앱은 {guided} 안내합니다.")
        return tuple(lines)
    lines: list[str] = []
    if naive is not None:
        promised = cmp.naive_promised_s
        if cmp.naive_status == RouteStatus.GHOST_PRUNED:
            reason = reason_text(cmp.naive_reasons[0], naive, output, config) if cmp.naive_reasons else ""
            if promised is not None:
                lines.append(f"기존 앱 방식의 1위는 {fmt_clock(c0, promised)} 도착을 약속하지만 걸러졌습니다: {reason}")
            else:
                lines.append(f"기존 앱 방식의 1위는 걸러졌습니다: {reason}")
        elif promised is not None and cmp.naive_mean_s is not None:
            lines.append(f"기존 앱 방식의 1위는 {fmt_clock(c0, promised)} 도착을 약속하지만, 이 앱이 계산한 평균 도착은 "
                         f"{fmt_clock(c0, cmp.naive_mean_s)}({_late_text(cmp.late_vs_promise_s)})입니다.")
    if best is not None:
        lines.append(_recommend_line(output, best, naive))
    return tuple(lines)


# --- KPI (§6.3) ---


@dataclasses.dataclass(frozen=True)
class KpiTile:
    label: str
    value: str
    delta: str | None
    delta_color: str
    delta_arrow: str
    help: str | None = None


def kpi_tiles(output: EngineOutput | None, config: EngineConfig) -> tuple[KpiTile, ...]:
    """KPI 네 타일. 값은 최선 여정, 변화량은 기존 방식 1위와의 차이. 최선 여정이 없으면 "-"(§6.3)."""
    prob_help = ("모든 탑승에서 안내한 차(또는 그보다 이른 차)를 타고, 따릉이 대여소에 자전거가 남아 있을 확률입니다. "
                 f"걷는 속도의 개인차와 위상을 모르는 신호를 넣었고, 승차 여유 {config.safety_buffer_s:g}초를 두었습니다.")
    labels = ("평균 도착", "90% 도착", "계획대로 갈 확률", "요금")
    items = _items(output) if output is not None else {}
    best = items.get(output.best_id) if output is not None and output.best_id else None
    if output is None or best is None:
        return tuple(KpiTile(label, "-", None, "off", "off", prob_help if i == 2 else None) for i, label in enumerate(labels))
    cmp = output.comparison
    naive = items.get(cmp.naive_best_id) if cmp.naive_best_id else None
    differ = naive is not None and not cmp.same
    c0 = output.clock_s

    def time_tile(label: str, mine: float | None, theirs: float | None) -> KpiTile:
        delta = fmt_delta_dur(mine - theirs) if differ and mine is not None and theirs is not None else None
        return KpiTile(label, _clock_or_dash(c0, mine), delta, "inverse", "auto")

    tiles = [
        time_tile(labels[0], best.arrival.mean_s, naive.arrival.mean_s if naive else None),
        time_tile(labels[1], best.arrival.p90_s, naive.arrival.p90_s if naive else None),
    ]
    if output.query.deadline_s is not None and best.arrival.p_on_time is not None:
        tiles.append(KpiTile(labels[2], fmt_pct(best.p_star), f"마감까지 도착할 확률 {fmt_pct(best.arrival.p_on_time)}", "off", "off",
                             prob_help))
    else:
        tiles.append(KpiTile(labels[2], fmt_pct(best.p_star), None, "off", "off", prob_help))
    if naive is None:
        tiles.append(KpiTile(labels[3], fmt_won(best.fare.total_krw), None, "off", "off"))
    elif naive.plan_missed_last and not cmp.same:
        tiles.append(KpiTile(labels[3], fmt_won(best.fare.total_krw), FARE_MISSED_NOTE, "off", "off"))
    else:
        diff = 0 if cmp.same else best.fare.total_krw - naive.fare.total_krw
        text = fmt_delta_won(diff)
        if text == "변동 없음":
            tiles.append(KpiTile(labels[3], fmt_won(best.fare.total_krw), text, "off", "off"))
        else:
            tiles.append(KpiTile(labels[3], fmt_won(best.fare.total_krw), text, "inverse", "auto"))
    return tuple(tiles)


# --- 경로 목록 (§6.3) ---


@dataclasses.dataclass(frozen=True)
class RouteEntry:
    itinerary_id: str
    label: str  # 라디오 선택지(마크다운)
    caption: str


FARE_MISSED_NOTE = "막차 놓쳐 비교 없음"  # 기존 방식 1위의 계획이 막차를 놓친 때 요금 KPI 의 변화량 자리(§6.3)
FARE_MISSED_SUFFIX = " (막차 놓쳐 걷기)"  # 계획이 막차를 놓친 여정의 요금 뒤에 붙인다(§6.3, §1.5 (1))


def fare_text(it: ItineraryResult) -> str:
    """경로 목록과 다른 경로의 요금(§6.3): 계획이 막차를 놓친 여정은 놓친 탑승부터 요금에 넣지 않으므로(§1.5 (1)) 그 사실을 붙인다."""
    return fmt_won(it.fare.total_krw) + (FARE_MISSED_SUFFIX if it.plan_missed_last else "")


def route_caption(it: ItineraryResult, output: EngineOutput) -> str:
    c0 = output.clock_s
    parts = [
        f"평균 {_clock_or_dash(c0, it.arrival.mean_s)}",
        f"90% {_clock_or_dash(c0, it.arrival.p90_s)}",
        f"확률 {fmt_pct(it.p_star)} {GRADE_NAMES[it.grade]}",
        fare_text(it),
        f"걷기 {fmt_dist(it.walk_distance_m)}",
    ]
    if it.itinerary_id == output.comparison.naive_best_id:
        parts.append("기존 앱 1위")
    if it.ghost_count:
        parts.append(f"유령 환승 {it.ghost_count}")
    if it.status == RouteStatus.GHOST_PRUNED:
        parts.extend(REASON_NAMES[reason] for reason in it.reasons)
    if output.query.deadline_s is not None:
        parts.append("마감 확률 -" if it.arrival.p_on_time is None else f"마감 확률 {fmt_pct(it.arrival.p_on_time)}")
    return " · ".join(parts)


def route_entries(output: EngineOutput, show_variants: bool) -> tuple[RouteEntry, ...]:
    """경로 목록의 라디오 선택지: 대표 여정을 순위대로, 켜면 그 아래 다른 걷는 길, 맨 아래 걸러진 여정(평균 도착 순)."""
    items = _items(output)
    entries: list[RouteEntry] = []
    for rep_id in output.ranking:
        it = items[rep_id]
        entries.append(RouteEntry(rep_id, f"**{it.rank}위** {md_escape(it.label)}", route_caption(it, output)))
        if show_variants:
            for variant_id in it.variant_ids:
                variant = items[variant_id]
                entries.append(RouteEntry(variant_id, f"↳ 다른 걷는 길 · 걷기 {fmt_dist(variant.walk_distance_m)}",
                                          route_caption(variant, output)))
    for pruned_id in output.pruned_ids:
        it = items[pruned_id]
        entries.append(RouteEntry(pruned_id, f"✕ {md_escape(it.label)} (걸러짐)", route_caption(it, output)))
    return tuple(entries)


def default_selection(output: EngineOutput) -> str | None:
    """기본 선택(§6.4): 최선 여정, 없으면 기존 방식 1위, 그것도 없으면 목록의 첫 여정."""
    if output.best_id:
        return output.best_id
    if output.comparison.naive_best_id:
        return output.comparison.naive_best_id
    for candidate in (*output.ranking, *output.pruned_ids, *(it.itinerary_id for it in output.itineraries)):
        return candidate
    return None


# --- 시간 막대 (§7.5 mr-tl) ---

_LEG_ORDER = (LegKind.WALK, LegKind.SIGNAL_WAIT, LegKind.BIKE_UNLOCK, LegKind.BIKE, LegKind.BIKE_DOCK, LegKind.STOP_WAIT,
              LegKind.BUS, LegKind.SUBWAY)


def _vehicle_origin(it: ItineraryResult) -> bool:
    return bool(it.rides) and it.rides[0].board_index is None


def timeline_html(itinerary: ItineraryResult, clock_s: float) -> str:
    """고른 여정의 계획(`legs`)을 시간 비례 막대로(§7.5). 구간 폭이 전체의 15% 이상일 때만 안에 글자를 둔다."""
    legs = itinerary.legs
    if not legs:
        return '<div class="mr-tl"><div class="mr-ends"><span>계획한 구간이 없습니다.</span></div></div>'
    durations = [max(0.0, leg.end_s - leg.start_s) for leg in legs]
    total = sum(durations) or 1.0
    segments = []
    for leg, duration in zip(legs, durations):
        name = LEG_NAMES[leg.kind]
        moving = leg.kind in (LegKind.BUS, LegKind.SUBWAY)
        title = f"{name}({leg.label}) {fmt_dur(duration)}" if moving else f"{name} {fmt_dur(duration)}"
        inner = (esc(leg.label) if moving else esc(fmt_dur(duration))) if duration / total >= 0.15 else ""
        segments.append(f'<div class="mr-seg mr-k-{leg.kind.value.lower()}" style="flex: {duration:.3f} 1 0px" '
                        f'title="{esc(title)}">{inner}</div>')
    start_word = "하차" if _vehicle_origin(itinerary) else "출발"
    end_s = itinerary.plan_arrival_s if itinerary.plan_arrival_s is not None else legs[-1].end_s
    totals: dict[LegKind, float] = {}
    for leg, duration in zip(legs, durations):
        totals[leg.kind] = totals.get(leg.kind, 0.0) + duration
    legend = "".join(
        f'<span><span class="mr-sw mr-k-{kind.value.lower()}"></span>{esc(LEG_NAMES[kind])} {esc(fmt_dur(totals[kind]))}</span>'
        for kind in _LEG_ORDER if kind in totals
    )
    return (f'<div class="mr-tl"><div class="mr-bar">{"".join(segments)}</div>'
            f'<div class="mr-ends"><span>{esc(fmt_clock(clock_s, legs[0].start_s))} {start_word}</span>'
            f'<span>{esc(fmt_clock(clock_s, end_s))} 도착(계획)</span></div>'
            f'<div class="mr-tlegend">{legend}</div></div>')


# --- 여정 안내 (§6.3, §7.5 mr-steps) ---


@dataclasses.dataclass(frozen=True)
class GuideStep:
    kind: str  # walk, bike, bus, subway, missed, arrive
    main: str
    subs: tuple[str, ...] = ()
    ghost: bool = False
    at: str = ""  # 쉬운 단계의 때(§6.9 지금 할 일): 타기는 "HH:MM 출발", 지금 탄 차의 내리기는 "HH:MM 도착"
    backup: tuple[str, ...] = ()  # 놓쳤을 때(§6.9 놓치면, 19단계): 타기는 탈 확률과 다음 차, 따릉이는 자전거가 없을 때
    spot: str = ""  # 간단히 보기 지도의 번호 표지 자리(§6.9, 19단계): 타기는 승차 지점, 지금 탄 차의 내리기는 하차 지점, 따릉이는 대여소


def guide_steps(itinerary: ItineraryResult, output: EngineOutput, scenario: Scenario | None, config: EngineConfig) -> tuple[GuideStep, ...]:
    """여정 안내의 단계(§6.3): 이동과 탑승을 차례로, 마지막은 도착. 계획이 막차를 놓친 탑승은 대체 보행 한 줄로 바꾸고 멈춘다."""
    names = node_names(scenario)
    c0 = output.clock_s
    moves = {move.index: move for move in itinerary.moves}
    boardings = _boardings(itinerary)
    destination_id = output.destination_node_id or (itinerary.moves[-1].to_id if itinerary.moves else "")
    dest_name = names.get(destination_id, destination_id)
    steps: list[GuideStep] = []
    missed = False
    for k in range(len(itinerary.rides) + 1):
        move = moves.get(k)
        if move is not None:
            step = _move_step(move, names)
            if step is not None:
                steps.append(step)
        if k == len(itinerary.rides):
            break
        ride = itinerary.rides[k]
        if itinerary.plan_missed_last and ride.plan_dep_s is None and ride.board_index is not None:
            fallback = ride.fallback
            text = f"{ride_name(ride)} 막차를 놓쳐 {names.get(ride.board_node_id or '', ride.board_node_id)}에서 {dest_name}까지 걷습니다"
            if fallback is not None:
                text += f" · {fmt_dist(fallback.distance_m)} · {fmt_dur(fallback.t_end_s - fallback.t_start_s)}"
            steps.append(GuideStep("missed", text))
            missed = True
            break
        steps.append(_ride_step(ride, boardings.get(ride.index), names, c0, scenario))
    del missed
    steps.append(GuideStep("arrive", f"도착 {dest_name} · 평균 {_clock_or_dash(c0, itinerary.arrival.mean_s)}, "
                                     f"90% {_clock_or_dash(c0, itinerary.arrival.p90_s)}"))
    return tuple(steps)


def _move_step(move, names: Mapping[str, str]) -> GuideStep | None:
    if move.bike is not None:
        bike = move.bike
        text = (f"따릉이: {names.get(bike.pick_id, bike.pick_id)}까지 걷기 {fmt_dist(bike.walk_in.distance_m)} → 대여 → "
                f"{names.get(bike.drop_id, bike.drop_id)}까지 {fmt_dist(bike.ride.distance_m)} 주행 → 반납 → "
                f"{names.get(move.to_id, move.to_id)}까지 걷기 {fmt_dist(bike.walk_out.distance_m)} · "
                f"모두 {fmt_dur(move.t_end_s - move.t_start_s)} · 자전거가 남아 있을 확률 {fmt_pct(bike.p_bike)}")
        return GuideStep("bike", text)
    walk = move.walk
    if walk is None or (not walk.edge_ids and walk.distance_m <= 0):
        return None
    text = f"걷기 {fmt_dist(walk.distance_m)} · {fmt_dur(walk.t_end_s - walk.t_start_s)} → {names.get(move.to_id, move.to_id)}"
    if walk.events:
        text += f" (신호 {len(walk.events)}개, 대기 {fmt_dur(walk.wait_s)})"
    return GuideStep("walk", text)


def _ride_step(ride, boarding, names: Mapping[str, str], c0: float, scenario: Scenario | None) -> GuideStep:
    """탑승 한 단계(§6.3 여정 안내). 묶음 탑승이면 "{탑승 노선 이름} 가운데 {차량 노선 이름} {n}번째 차" 로 시작하고 둘째 줄에
    묶음 안내를 둔다. "{n}번째 차" 는 모두 `nth_vehicle` 로 적는다(§6.5)."""
    kind = "bus" if ride.mode == TravelMode.BUS else "subway"
    alight = names.get(ride.alight_node_id, ride.alight_node_id)
    if ride.board_index is None:
        guided = _vehicle(boarding, boarding.guided_trip_id) if boarding is not None else None
        arrival = ride.plan_arr_s if ride.plan_arr_s is not None else (guided.alight_arr_s if guided else None)
        return GuideStep(kind, f"지금 탄 차량 · {alight} {_clock_or_dash(c0, arrival)} 하차")
    board = names.get(ride.board_node_id or "", ride.board_node_id or "-")
    guided = _vehicle(boarding, boarding.guided_trip_id) if boarding is not None else None
    if guided is not None:
        joiner = " 가운데 " if ride.bundle else " "
        text = (f"{ride_name(ride)}{joiner}{nth_vehicle(ride, guided, scenario)} · {board} {fmt_clock(c0, guided.dep_s)} → {alight} "
                f"{fmt_clock(c0, guided.alight_arr_s)} · 탈 확률 {fmt_pct(guided.p_catch)}")
    else:
        text = (f"{ride_name(ride)} · {board} {_clock_or_dash(c0, ride.plan_dep_s)} → {alight} "
                f"{_clock_or_dash(c0, ride.plan_arr_s)}")
    if ride.plan_wait_s is not None and _half(ride.plan_wait_s) > 0:
        text += f" · {fmt_dur(ride.plan_wait_s)} 기다림"
    subs: list[str] = []
    if ride.bundle:
        subs.append(f"{ride_name(ride)} 가운데 하차 정류장에 먼저 닿는 차를 탑니다.")
    ghost = bool(boarding is not None and boarding.ghost)
    if ghost and boarding.p_catch_naive is not None:
        naive = _vehicle(boarding, boarding.naive_trip_id)
        which = f"{nth_vehicle(ride, naive, scenario)}를" if naive is not None else "다른 차를"
        subs.append(f"기존 앱은 {which} 안내하지만 탈 확률이 {fmt_pct(boarding.p_catch_naive)}입니다(유령 환승).")
    if boarding is not None and ride.plan_trip_id is not None and ride.plan_trip_id != boarding.guided_trip_id:
        plan = _vehicle(boarding, ride.plan_trip_id)
        if plan is not None:
            subs.append(f"평소 속도로 걸으면 {nth_vehicle(ride, plan, scenario)}도 탈 수 있습니다(탈 확률 {fmt_pct(plan.p_catch)}).")
    return GuideStep(kind, text, tuple(subs), ghost)


def guide_lines(itinerary: ItineraryResult, output: EngineOutput, scenario: Scenario | None, config: EngineConfig) -> tuple[str, ...]:
    """여정 안내의 문장. 단계마다 한 항목이고 둘째 줄(유령 환승, 평소 속도의 차)은 줄바꿈으로 잇는다."""
    return tuple("\n".join((step.main, *step.subs)) for step in guide_steps(itinerary, output, scenario, config))


def guide_html(itinerary: ItineraryResult, output: EngineOutput, scenario: Scenario | None, config: EngineConfig) -> str:
    items = []
    for number, step in enumerate(guide_steps(itinerary, output, scenario, config), start=1):
        badge = badge_html("유령 환승", "ghost", "✕") + " " if step.ghost else ""
        label = "" if step.kind == "arrive" else str(number)
        subs = "".join(f'<div class="mr-sub">{esc(sub)}</div>' for sub in step.subs)
        items.append(f'<li><span class="mr-n {step.kind}">{label}</span><div><div class="mr-main">{badge}{esc(step.main)}</div>'
                     f"{subs}</div></li>")
    return f'<ol class="mr-steps">{"".join(items)}</ol>'


# --- 간단히 보기 (§6.9) ---
#
# 휴대폰 한 화면에서 언제 도착하는지, 무엇을 타는지, 걷기·타기 단계, 쉬운 말 주의를 보인다. 값은 엔진 결과의 최선 여정과
# 비교 패널이고 형식만 바꾼다(§6.1). 시각은 분까지, 차이는 분 단위다.

_KO_COUNTS = ("", "한", "두", "세", "네", "다섯", "여섯", "일곱", "여덟", "아홉")


def minute_of(seconds: float, rounding: str = "nearest") -> int:
    """초를 분으로(§6.9): nearest 는 ⌊x + 0.5⌋, floor 는 ⌊x⌋, ceil 은 ⌈x⌉ (x = 초 / 60. 부동소수 오차 1e-9 분은 무시)."""
    x = seconds / 60.0
    if rounding == "floor":
        return math.floor(x + 1e-9)
    if rounding == "ceil":
        return math.ceil(x - 1e-9)
    return math.floor(x + 0.5)


def fmt_hm(clock_s: float, t_s: float, rounding: str = "nearest") -> str:
    """시계 시각을 분까지 "HH:MM" (§6.9). 24시를 넘으면 " (다음 날)"."""
    minutes = minute_of(clock_s + t_s, rounding)
    text = f"{(minutes // 60) % 24:02d}:{minutes % 60:02d}"
    return f"{text} (다음 날)" if minutes >= 1440 else text


def fmt_minutes(n: int) -> str:
    """분 수(§6.9): 1 미만 "1분 미만", 60 미만 "{n}분", 아니면 "{h}시간" 또는 "{h}시간 {m}분"."""
    if n < 1:
        return "1분 미만"
    if n < 60:
        return f"{n}분"
    hours, rest = divmod(n, 60)
    return f"{hours}시간" if rest == 0 else f"{hours}시간 {rest}분"


def miss_text(p: float, verb: str) -> str:
    """놓치는 횟수(§6.9): n = ⌊10(1 − p) + 0.5⌋. 10 이면 "거의 매번 {verb}", 0 이면 "드물게 {verb}", 아니면 "열 번 중 {n} 번은 {verb}"."""
    n = math.floor(10.0 * (1.0 - p) + 0.5)
    if n >= 10:
        return f"거의 매번 {verb}"
    if n <= 0:
        return f"드물게 {verb}"
    return f"열 번 중 {_KO_COUNTS[n]} 번은 {verb}"


WALK_EASY_CAPTION = "걷는 속도 {v} 기준으로 계획하고, 조금 빠르거나 느리게 걸어도 탈 수 있는지 함께 따집니다."
FAST_WALK_PRESET = "빠르게"  # 빠른 걸음(28단계): 걸음 빠르기 프리셋의 "빠르게"


def catch_text(p: float, p_safe: float, fast: bool = False) -> str:
    """탈 수 있나(§6.9 결정 문장, 28단계): p ≥ p_safe 면 "탈 수 있습니다", 아니고 빠른 걸음 판정이 참이면
    "빠른 걸음이면 탈 수 있습니다", 아니면 "놓칠 수 있습니다". 확률 숫자는 간단히 보기에 적지 않는다."""
    if p >= p_safe:
        return "탈 수 있습니다"
    if fast:
        return "빠른 걸음이면 탈 수 있습니다"
    return "놓칠 수 있습니다"


def fast_config(config: EngineConfig) -> EngineConfig | None:
    """빠른 걸음 설정(28단계): 걷는 속도가 "빠르게" 프리셋보다 느리면 그 속도로 바꾼 설정, 아니면 None."""
    fast = float(WALK_SPEED_PRESETS[FAST_WALK_PRESET])
    if config.v_walk_mps >= fast:
        return None
    return config.model_copy(update={"v_walk_mps": fast})


def same_routes(output: EngineOutput | None, it: ItineraryResult) -> list[ItineraryResult]:
    """다른 결과에서 같은 경로(28단계): 탑승마다 `ride_sig` 가 모두 같은 여정들(순위 차례, 그다음 나머지 차례).
    탑승이 없는 여정은 따릉이 사용 여부까지 같아야 한다."""
    if output is None or output.status != EngineStatus.OK:
        return []
    want = [ride_sig(ride) for ride in it.rides]
    items = _items(output)
    order = [items[rid] for rid in output.ranking if rid in items]
    order += [x for x in output.itineraries if x.itinerary_id not in output.ranking]
    return [cand for cand in order if [ride_sig(ride) for ride in cand.rides] == want
            and (want or _bike_used(cand) == _bike_used(it))]


def fast_catch(it: ItineraryResult, ride_index: int, option, fast_output: EngineOutput | None, p_safe: float) -> bool:
    """빠른 걸음이면 탈 수 있나(28단계): 빠른 걸음 결과의 같은 경로들 가운데 하나라도, 같은 탑승의 안내 차량 u 가 `option` 보다
    늦게 떠나지 않고 그 탑승의 p_conditional(앞 탑승을 계획대로 했을 때 u 나 그 앞차를 탈 확률)이 p_safe 이상이면 참."""
    if option is None:
        return False
    for twin in same_routes(fast_output, it):
        boarding = _boardings(twin).get(ride_index)
        u = _vehicle(boarding, boarding.guided_trip_id) if boarding is not None else None
        if u is not None and u.dep_s <= option.dep_s + 1e-9 and boarding.p_conditional >= p_safe:
            return True
    return False


def fast_map(it: ItineraryResult, output: EngineOutput, fast_output: EngineOutput | None) -> dict[int, bool]:
    """타기 단계마다 빠른 걸음 판정(28단계): {탑승 순번: fast_catch(안내 차량)}."""
    result = {}
    for boarding in it.boardings:
        option = _vehicle(boarding, boarding.guided_trip_id)
        result[boarding.ride_index] = fast_catch(it, boarding.ride_index, option, fast_output, output.config.p_safe)
    return result


def josa(word: str, with_final: str, without_final: str) -> str:
    """조사 고르기(§6.9): 낱말의 마지막 글자가 받침 있는 한글 음절이면 `with_final`, 아니면 `without_final`."""
    last = word[-1:] or " "
    if "가" <= last <= "힣" and (ord(last) - 0xAC00) % 28:
        return with_final
    return without_final


def easy_vehicle(ride, option, scenario: Scenario | None, c0: float, particle: tuple[str, str] = ("", "")) -> str:
    """쉬운 말의 차량(§6.9): "{노선}({HH:MM} 출발){조사}". 막차면 노선 뒤에 " 막차", 지하철은 " 열차". 출발 시각은 분 아래를 버린다.
    조사는 괄호 앞 낱말에 맞춘다(`particle` = (받침 있을 때, 없을 때))."""
    name = vehicle_line_name(ride, option.route_id, option.trip_id, scenario) if ride.bundle else ride_name(ride)
    if option.is_last:
        name += " 막차"
    elif ride.mode == TravelMode.SUBWAY:
        name += " 열차"
    return f"{name}({fmt_hm(c0, option.dep_s, 'floor')} 출발){josa(name, *particle)}"


def deadline_clock(c0: float, deadline_s: float) -> str:
    """답 카드의 마감 시각(19단계): 정각 분이면 "HH:MM", 아니면 "HH:MM:SS" (마감보다 이르거나 늦게 적지 않는다)."""
    total = c0 + deadline_s
    return fmt_hm(c0, deadline_s) if abs(total - 60.0 * round(total / 60.0)) < 1e-6 else fmt_clock(c0, deadline_s)


def trip_minutes(c0: float, t_s: float) -> int:
    """기준 시각(분 아래 버림)부터 도착(분 반올림)까지의 분: 화면의 두 시각의 차와 같다(§6.9)."""
    return minute_of(c0 + t_s) - minute_of(c0, "floor")


@dataclasses.dataclass(frozen=True)
class EasyAnswer:
    head: str
    title: str
    grade: Grade
    minutes: str
    span: str
    rows: tuple[str, ...]
    facts: str


def _first_board(it: ItineraryResult) -> str | None:
    return next((ride.board_node_id for ride in it.rides if ride.board_node_id), None)


def _shown_id(output: EngineOutput, shown_id: str | None) -> str | None:
    return shown_id if shown_id is not None and shown_id in _items(output) else output.comparison.best_id


def _alt_ids(output: EngineOutput, shown_id: str | None) -> list[str]:
    """다른 경로 줄의 여정(§6.9): [최선] + 순위(최선 제외)에서 보는 경로를 뺀 앞의 `SIMPLE_ALT_MAX` 개."""
    best_id = output.comparison.best_id
    shown = _shown_id(output, shown_id)
    pool = ([best_id] if best_id else []) + [rep for rep in output.ranking if rep != best_id]
    return [rep for rep in pool if rep != shown][:SIMPLE_ALT_MAX]


def easy_title(it: ItineraryResult, shown_ids: Sequence[str], output: EngineOutput, scenario: Scenario | None) -> str:
    """같은 이름의 경로(§6.9): 함께 보이는 여정에 이름이 같은 것이 있으면 첫 승차 지점을 붙인다."""
    items = _items(output)
    same = sum(1 for rid in shown_ids if rid in items and items[rid].label == it.label)
    board = _first_board(it)
    if same >= 2 and board is not None:
        return f"{it.label} · {node_names(scenario).get(board, board)} 승차"  # 20단계: 제목은 노드 이름 그대로
    return it.label


def easy_answer(output: EngineOutput, scenario: Scenario | None = None, shown_id: str | None = None) -> EasyAnswer | None:
    """답 카드(§6.9): 보는 경로(None 이면 최선 여정). 최선 여정이 없으면 None."""
    items = _items(output)
    best = items.get(output.comparison.best_id) if output.comparison.best_id else None
    if best is None:
        return None
    shown = items[_shown_id(output, shown_id)]
    picked = shown.itinerary_id != best.itinerary_id
    c0 = output.clock_s
    arrival = shown.arrival
    start = fmt_hm(c0, 0.0, "floor")
    if arrival.mean_s is None:
        minutes, span = "-", f"{start} 출발"
    else:
        minutes, span = fmt_minutes(trip_minutes(c0, arrival.mean_s)), f"{start} → {fmt_hm(c0, arrival.mean_s)} 도착"
    if arrival.p90_s is None:
        p90 = "도착하지 못할 수 있습니다."
    else:
        p90 = f"늦어도 {fmt_hm(c0, arrival.p90_s, 'ceil')}에는 도착합니다."
    rows = [p90]
    if output.query.deadline_s is not None and arrival.p_on_time is not None:
        late = "늦지 않습니다" if arrival.p_on_time >= DEADLINE_SURE_P else "늦을 수 있습니다"
        rows.append(f"{deadline_clock(c0, output.query.deadline_s)}까지 {late}.")
    if picked and shown.arrival.mean_s is not None and best.arrival.mean_s is not None:
        n = minute_of(c0 + shown.arrival.mean_s) - minute_of(c0 + best.arrival.mean_s)  # 화면에 보인 두 도착 시각의 차
        if n >= 1:
            rows.append(f"추천 경로보다 평균 약 {fmt_minutes(n)} 늦게 도착합니다.")
        elif n <= -1:
            rows.append(f"추천 경로보다 평균 약 {fmt_minutes(-n)} 일찍 도착합니다.")
        else:
            rows.append("추천 경로와 평균 도착이 1분도 차이 나지 않습니다.")
    facts = f"{fmt_won(shown.fare.total_krw)} · 걷기 {fmt_dist(shown.walk_distance_m)}"
    criterion = effective_criterion(output)
    if picked:
        head = "고른 경로"
    else:
        head = "추천 경로" if criterion == RankCriterion.MEAN_ARRIVAL else f"추천 경로 · {RANK_NAMES[criterion]} 기준"
    title = easy_title(shown, [shown.itinerary_id, *_alt_ids(output, shown.itinerary_id)], output, scenario)
    return EasyAnswer(head, title, shown.grade, minutes, span, tuple(rows), facts)


def _nowrap_parens(text: str) -> str:
    """괄호 안의 때("(19:24 출발)")는 줄을 나누지 않는다(§7.5 `mr-anext`, 18단계)."""
    return re.sub(r"\(([^()]*)\)", r'<span class="mr-nb">(\1)</span>', text)


def _step_text(step: GuideStep) -> str:
    return f"{step.main} ({step.at})" if step.at else step.main


def easy_next(itinerary: ItineraryResult, output: EngineOutput, scenario: Scenario | None) -> str | None:
    """지금 할 일(§6.9): 쉬운 단계의 첫 행동. 첫 단계가 걷기이거나 지금 탄 차에서 내리기이면(19단계) 다음 단계까지 잇는다."""
    steps = easy_steps(itinerary, output, scenario)
    first = steps[0]
    if first.kind == "arrive":
        return None
    alight_first = first.kind in ("bus", "subway") and first.main.endswith("에서 내리기")  # 지금 탄 차에서 내리기(19단계)
    if (first.kind == "walk" or alight_first) and len(steps) > 1 and steps[1].kind != "arrive":
        return f"지금 할 일: {_step_text(first)}, 이어서 {_step_text(steps[1])}"
    return f"지금 할 일: {_step_text(first)}"


def josa_ro(word: str) -> str:
    """조사 "로/으로"(19단계): 마지막 글자가 받침 있는 한글 음절이고 그 받침이 ㄹ 이 아니면 "으로", 아니면 "로"."""
    last = word[-1:] or " "
    final = (ord(last) - 0xAC00) % 28 if "가" <= last <= "힣" else 0
    return "으로" if final not in (0, 8) else "로"


def easy_leave(output: EngineOutput, later: Iterable[tuple[int, EngineOutput | None]]) -> str | None:
    """출발 여유(§6.9, 19단계): 출발을 늦춘 결과 `later` ((늦춘 초 d, 그 결과), d 오름차순)를 차례로 보며 추천 경로의 평균 도착
    시각(분)이 지금 출발의 것보다 늦어지는 첫 d 를 찾는다. 늦춘 결과가 없거나(차 없음) 최선 여정·평균이 없으면 그 d 에서 멈춘다.
    지금 출발에 최선 여정이나 평균이 없거나 `later` 가 비면 None."""
    items = _items(output)
    best = items.get(output.comparison.best_id) if output.comparison.best_id else None
    if best is None or best.arrival.mean_s is None:
        return None
    c0 = output.clock_s
    base_minute = minute_of(c0 + best.arrival.mean_s)
    base_text = fmt_hm(c0, best.arrival.mean_s)
    last_ok = 0
    seen = False
    for d, out in later:
        seen = True
        when = fmt_hm(c0, float(d), "floor")
        head = (f"{fmt_hm(c0, float(last_ok), 'floor')}까지 나서도 {base_text} 도착은 같고, " if last_ok
                else f"지금 나서면 {base_text} 도착, ")
        top = None
        if out is not None and out.status == EngineStatus.OK and out.comparison.best_id:
            top = _items(out).get(out.comparison.best_id)
        if top is None or top.arrival.mean_s is None:
            return f"{head}{when}에 나서면 갈 수 있는 경로가 없습니다."
        if minute_of(out.clock_s + top.arrival.mean_s) > base_minute:
            route = "" if top.label == best.label else f"{top.label}{josa_ro(top.label)} "
            return f"{head}{when}에 나서면 {route}{fmt_hm(out.clock_s, top.arrival.mean_s)} 도착입니다."
        last_ok = d
    if not seen:
        return None
    return f"{fmt_hm(c0, float(last_ok), 'floor')}까지 나서도 {base_text} 도착은 같습니다."


DEADLINE_SURE_P = 0.9  # 마감(23·28단계): 마감 확률이 이 이상이면 "늦지 않습니다"


def easy_deadline_leave(output: EngineOutput, later: Iterable[tuple[int, EngineOutput | None]],
                        scenario: Scenario | None = None) -> str | None:
    """마감 여유(§6.9, 23단계): 도착해야 하는 시각이 있을 때 출발 여유 대신 "늦어도 언제 나서면 열 번 중 아홉 번 맞추나"를 답한다.
    지금 출발의 최선 여정 마감 확률이 `DEADLINE_SURE_P` 미만이면 늦는다는 문장이고, 순위의 다른 여정 가운데 기준 이상인 것이 있으면
    평균이 가장 이른 것(같으면 순위 차례)을 함께 권한다. 아니면 `later` 를 차례로 보며 최선 여정의 마감 확률이 기준 이상인 마지막 d 를
    찾는다(결과가 없거나 OK 가 아니거나 최선·마감 확률이 없거나 기준 미만이면 멈춘다).
    마감이 없거나 최선 여정·마감 확률이 없거나 `later` 가 비면 None."""
    deadline = output.query.deadline_s
    items = _items(output)
    best = items.get(output.comparison.best_id) if output.comparison.best_id else None
    if deadline is None or best is None or best.arrival.p_on_time is None:
        return None
    c0 = output.clock_s
    target = deadline_clock(c0, deadline)
    if best.arrival.p_on_time < DEADLINE_SURE_P:
        sure = [items[rid] for rid in output.ranking if rid != best.itinerary_id and rid in items
                and items[rid].arrival.p_on_time is not None and items[rid].arrival.p_on_time >= DEADLINE_SURE_P
                and items[rid].arrival.mean_s is not None]
        if not sure:
            return f"지금 나서도 {target}까지 늦을 수 있습니다."
        alt = min(sure, key=lambda it: it.arrival.mean_s)  # min 은 같은 값이면 앞(순위 차례)을 고른다
        name = easy_title(alt, [best.itinerary_id, alt.itinerary_id], output, scenario)
        return (f"추천 경로로는 {target}까지 늦을 수 있습니다. "
                f"{name}{josa_ro(name)} 가면 늦지 않습니다.")
    last_ok = 0
    seen = False
    stopped = False
    for d, out in later:
        seen = True
        top = None
        if out is not None and out.status == EngineStatus.OK and out.comparison.best_id:
            top = _items(out).get(out.comparison.best_id)
        if top is None or top.arrival.p_on_time is None or top.arrival.p_on_time < DEADLINE_SURE_P:
            stopped = True
            break
        last_ok = d
    if not seen:
        return None
    if not stopped:
        return f"{fmt_hm(c0, float(last_ok), 'floor')}에 나서도 {target}까지 늦지 않습니다."
    if last_ok == 0:
        return f"{target}까지 늦지 않으려면 지금 나서야 합니다."
    return f"{target}까지 늦지 않으려면 늦어도 {fmt_hm(c0, float(last_ok), 'floor')}에는 나서세요."


def leave_query(query: Query, d_s: float) -> Query:
    """출발을 d 초 더 늦춘 질의(19단계): 마감은 같은 시계 시각이므로 남은 시간 $t_{dl} - d$ 이고, 0 이하이면 마감 없음(`deadline_t` 와 같다)."""
    if query.deadline_s is None:
        return query
    left = query.deadline_s - float(d_s)
    return query.model_copy(update={"deadline_s": left if left > 0 else None})


def leave_runs(p: "Prepared") -> Iterator[tuple[int, EngineOutput | None]]:
    """출발 여유의 늦춘 결과(19단계): d = 간격, 2·간격, … `LEAVE_SCAN_MAX_S` 까지(늦춘 합이 `depart_offset_max_s` 를 넘지 않게).
    결과는 화면과 같은 `cached_run` 으로 얻고, 기록 재생은 기준 시각 + 늦춘 합으로 다시 만든 재생을 넘긴다(§8.4)."""
    if p.config is None or p.query is None:
        return
    step = int(PARAM_RANGES["depart_offset_s"][2])
    limit = int(p.ctx.data_config.depart_offset_max_s)
    dconf_json = p.ctx.data_config.model_dump_json()
    for d in range(step, LEAVE_SCAN_MAX_S + 1, step):
        dt = p.dt_s + d
        if dt > limit:
            return
        shifted_json, sources_json = "", p.sources_json
        if p.mode == DataMode.REPLAY.value and p.replay_at is not None:
            shifted_json, sources_json = cached_replay(p.scenario_json, p.replay_at + dt, dconf_json, p.ctx.models_key)
        output_json, _ = cached_run(p.base_json, shifted_json, dt, leave_query(p.query, d).model_dump_json(),
                                    p.config.model_dump_json(), sources_json)
        yield d, (output_object(output_json) if output_json else None)


def easy_answer_html(output: EngineOutput, scenario: Scenario | None, shown_id: str | None = None,
                     leave: str | None = None) -> str:
    answer = easy_answer(output, scenario, shown_id)
    if answer is None:
        return f'<div class="mr-state ghost">{esc(NO_PLAN_EASY_TEXT)}</div>'
    css = _GRADE_CLASS[answer.grade][0]
    nxt = easy_next(_items(output)[_shown_id(output, shown_id)], output, scenario)
    shown_rows = answer.rows
    if leave and output.query.deadline_s is not None:  # 28단계: 마감 여유 줄이 이미 늦는지 말한다
        target = f"{deadline_clock(output.clock_s, output.query.deadline_s)}까지 "
        shown_rows = tuple(row for row in shown_rows if not row.startswith(target))
    # 32단계: 시각을 쓰임새로 묶는다. 경로를 고르는 줄(분·도착·늦어도·요금), 지금 할 일, 출발을 늦추면(두 줄, 안내 시작 바로 위)
    rows = "".join(f'<div class="mr-arow">{esc(row)}</div>' for row in shown_rows)
    rows += f'<div class="mr-arow mr-afacts">{esc(answer.facts)}</div>'
    if nxt:
        rows += f'<div class="mr-arow mr-anext">{_nowrap_parens(esc(nxt))}</div>'
    if leave:  # 출발을 늦추면 어떻게 되나: 두 시각 비교, 안내 시작 단추 바로 위
        rows += f'<div class="mr-arow mr-aleave">{_leave_lines(leave)}</div>'
    return (f'<div class="mr-answer {css}"><div class="mr-ahead"><span>{esc(answer.head)}</span>'
            f'{grade_badge(answer.grade, easy=True)}</div>'
            f'<div class="mr-atitle">{esc(answer.title)}</div>'
            f'<div class="mr-abig"><span class="mr-amin mr-num">{esc(answer.minutes)}</span>'
            f'<span class="mr-aspan mr-num">{esc(answer.span)}</span></div>{rows}</div>')


def _leave_lines(leave: str) -> str:
    """출발 여유 문장(32단계)을 두 시각 비교로 위아래에 맞춘다: 첫 ", " 에서 나눠 줄마다 한 덩이. 글(textContent)은 그대로다."""
    head, sep, tail = leave.partition(", ")
    if not sep:
        return esc(leave)
    return f'<span class="mr-al">{esc(head + sep)}</span><span class="mr-al">{esc(tail)}</span>'


def _ghost_boarding(it: ItineraryResult):
    """첫 유령 환승의 (탑승, 평가). 없으면 None."""
    rides = {ride.index: ride for ride in it.rides}
    for boarding in it.boardings:
        if boarding.ghost and boarding.p_catch_naive is not None and boarding.ride_index in rides:
            return rides[boarding.ride_index], boarding
    return None


@dataclasses.dataclass(frozen=True)
class EasyCaution:
    tone: str  # ghost, warn, plain
    head: str
    lines: tuple[str, ...]


def easy_caution(output: EngineOutput, scenario: Scenario | None) -> EasyCaution | None:
    """주의 카드(§6.9). 최선이나 기존 방식 1위가 없으면 None."""
    cmp = output.comparison
    items = _items(output)
    best = items.get(cmp.best_id) if cmp.best_id else None
    naive = items.get(cmp.naive_best_id) if cmp.naive_best_id else None
    if best is None or naive is None:
        return None
    c0 = output.clock_s
    ghost = _ghost_boarding(naive)
    promised = cmp.naive_promised_s
    lines = ["탈 차가 없어 도착 시각을 안내하지 못합니다." if promised is None else f"{fmt_hm(c0, promised)} 도착이라고 안내합니다."]
    if ghost is not None:
        ride, boarding = ghost
        option = _vehicle(boarding, boarding.naive_trip_id)
        which = easy_vehicle(ride, option, scenario, c0, ("은", "는")) if option is not None else f"{ride_name(ride)} 차는"
        lines.append(f"하지만 타라는 {which} 놓치기 쉽습니다.")
    if cmp.same:
        if ghost is not None:
            ride, boarding = ghost
            guided = _vehicle(boarding, boarding.guided_trip_id)
            if guided is not None:
                lines.append(f"이 앱은 {easy_vehicle(ride, guided, scenario, c0, ('을', '를'))} 안내합니다.")
        return EasyCaution("warn" if ghost is not None else "plain", "기존 길찾기 방식의 1위도 이 경로입니다", tuple(lines))
    pruned = cmp.naive_status == RouteStatus.GHOST_PRUNED
    if ghost is None and pruned:
        if ReasonCode.UNREACHABLE in cmp.naive_reasons:
            lines.append("하지만 차를 놓치면 걸어서 갈 길이 없습니다.")
        else:
            lines.append("하지만 그대로는 계획대로 가기 어렵습니다.")
    if cmp.naive_mean_s is not None:
        head = f"이 앱이 계산한 평균 도착은 {fmt_hm(c0, cmp.naive_mean_s)}"
        saving = cmp.saving_s
        n = None if saving is None else minute_of(saving)
        if n is None:
            lines.append(f"{head}입니다.")
        elif n >= 1:
            lines.append(f"{head}이고, 추천 경로보다 약 {fmt_minutes(n)} 늦습니다.")
        elif n <= -1:
            lines.append(f"{head}이고, 추천 경로보다 약 {fmt_minutes(-n)} 이릅니다.")
            criterion = effective_criterion(output)
            if pruned:
                lines.append("계획대로 가지 못할 위험이 커서 추천에서 뺐습니다.")
            elif criterion == RankCriterion.MEAN_ARRIVAL:
                lines.append("추천 경로가 더 확실하게 도착합니다.")
            else:
                lines.append(f"추천 경로는 {RANK_NAMES[criterion]} 기준으로 골랐습니다.")
        else:
            lines.append(f"{head}이고, 추천 경로와 평균 도착이 1분도 차이 나지 않습니다.")
    tone = "ghost" if pruned else ("warn" if ghost is not None else "plain")
    return EasyCaution(tone, f"기존 길찾기 방식의 1위: {naive.label}", tuple(lines))


def caution_html(output: EngineOutput, scenario: Scenario | None) -> str:
    caution = easy_caution(output, scenario)
    if caution is None:
        return ""
    body = " ".join(esc(line) for line in caution.lines)
    return (f'<div class="mr-caution {caution.tone}"><div class="mr-chead"><span class="mr-csym">!</span>'
            f'<span>{esc(caution.head)}</span></div><p>{body}</p><p class="mr-cnote">{esc(NAIVE_EASY_NOTE)}</p></div>')


def _easy_walk(path, to_name: str, events: int = 0) -> GuideStep | None:
    if path is None or (not path.edge_ids and path.distance_m <= 0):
        return None
    sub = f"{fmt_minutes(minute_of(path.t_end_s - path.t_start_s))} · {fmt_dist(path.distance_m)}"
    if events:
        sub += f" · 신호 {events}개"
    return GuideStep("walk", f"{to_name}까지 걷기", (sub,))


def easy_steps(itinerary: ItineraryResult, output: EngineOutput, scenario: Scenario | None,
               fast: Mapping[int, bool] | None = None) -> tuple[GuideStep, ...]:
    """쉬운 말 단계(§6.9): 걷기, 따릉이(대여소까지 걷기 · 타기 · 내려 걷기), 타기, 내리기, 도착. 이름은 `easy_names`(20단계).
    `fast` 는 탑승 순번마다 빠른 걸음 판정(28단계, `fast_map`). 없으면 모두 거짓."""
    names = easy_names(scenario)
    p_safe = output.config.p_safe
    fast = fast or {}
    c0 = output.clock_s
    moves = {move.index: move for move in itinerary.moves}
    boardings = _boardings(itinerary)
    destination_id = output.destination_node_id or (itinerary.moves[-1].to_id if itinerary.moves else "")
    dest_name = names.get(destination_id, destination_id)
    steps: list[GuideStep] = []
    for k in range(len(itinerary.rides) + 1):
        move = moves.get(k)
        if move is not None:
            if move.bike is not None:
                bike = move.bike
                pick, drop = names.get(bike.pick_id, bike.pick_id), names.get(bike.drop_id, bike.drop_id)
                step = _easy_walk(bike.walk_in, pick, len(bike.walk_in.events))
                if step is not None:
                    steps.append(step)
                ride_s = bike.walk_out.t_start_s - bike.walk_in.t_end_s
                steps.append(GuideStep("bike", f"따릉이 타기: {pick} → {drop}",
                                       (f"{fmt_minutes(minute_of(ride_s))} · {fmt_dist(bike.ride.distance_m)} · 빌리고 반납하는 시간 포함",
                                        "자전거를 빌릴 수 있습니다" if bike.p_bike >= p_safe
                                        else "자전거가 없을 수 있습니다"),
                                       backup=bike_backup(bike, short_stop_name(move.to_id, scenario)), spot=bike.pick_id))
                step = _easy_walk(bike.walk_out, names.get(move.to_id, move.to_id), len(bike.walk_out.events))
                if step is not None:
                    steps.append(step)
            elif move.walk is not None:
                step = _easy_walk(move.walk, names.get(move.to_id, move.to_id), len(move.walk.events))
                if step is not None:
                    steps.append(step)
        if k == len(itinerary.rides):
            break
        ride = itinerary.rides[k]
        kind = "bus" if ride.mode == TravelMode.BUS else "subway"
        alight = names.get(ride.alight_node_id, ride.alight_node_id)
        if itinerary.plan_missed_last and ride.plan_dep_s is None and ride.board_index is not None:
            board = names.get(ride.board_node_id or "", ride.board_node_id or "-")
            subs = ()
            if ride.fallback is not None:
                subs = (f"{fmt_minutes(minute_of(ride.fallback.t_end_s - ride.fallback.t_start_s))} · "
                        f"{fmt_dist(ride.fallback.distance_m)}",)
            steps.append(GuideStep("missed", f"{ride_name(ride)} 막차를 놓쳐 {board}에서 {dest_name}까지 걷기", subs,
                                   spot=ride.board_node_id or ""))
            break
        boarding = boardings.get(ride.index)
        guided = _vehicle(boarding, boarding.guided_trip_id) if boarding is not None else None
        if ride.board_index is None:
            arrival = ride.plan_arr_s if ride.plan_arr_s is not None else (guided.alight_arr_s if guided else None)
            vehicle = "열차" if ride.mode == TravelMode.SUBWAY else "버스"
            when = "-" if arrival is None else fmt_hm(c0, arrival)
            steps.append(GuideStep(kind, f"{alight}에서 내리기", (f"지금 탄 {vehicle} · {when} 도착",),
                                   at="" if arrival is None else f"{when} 도착", spot=ride.alight_node_id))
            continue
        board = names.get(ride.board_node_id or "", ride.board_node_id or "-")
        if guided is not None:
            dep, arr = guided.dep_s, guided.alight_arr_s
            line = vehicle_line_name(ride, guided.route_id, guided.trip_id, scenario) + " · " if ride.bundle else ""
        else:
            dep, arr, line = ride.plan_dep_s, ride.plan_arr_s, ""
        dep_text = "-" if dep is None else fmt_hm(c0, dep, "floor")
        arr_text = "-" if arr is None else fmt_hm(c0, arr)
        subs = [f"{line}{board} {dep_text} 출발 → {alight} {arr_text} 하차"]
        number = stop_number(ride.board_node_id, scenario)
        if number is not None:  # 20단계
            subs.append(f"정류장 번호 {number}")
        if ride.bundle:
            subs.append(f"{ride_name(ride)} 가운데 {alight}에 먼저 닿는 차를 타면 됩니다.")
        ghost = bool(boarding is not None and boarding.ghost and boarding.p_catch_naive is not None)
        if ghost:
            naive_vehicle = _vehicle(boarding, boarding.naive_trip_id)
            which = easy_vehicle(ride, naive_vehicle, scenario, c0, ("은", "는")) if naive_vehicle is not None else "앞차는"
            line = f"{which} 놓치기 쉬워 이 차를 안내합니다."
            if naive_vehicle is not None and guided is not None and naive_vehicle.alight_arr_s <= guided.alight_arr_s:
                line += " " + EARLIER_OK_TEXT  # 21단계: 앞차에 닿으면 그 차가 더 빠르다
            subs.append(line)
        steps.append(GuideStep(kind, f"{ride_name(ride)} 타기", tuple(subs), ghost, "" if dep is None else f"{dep_text} 출발",
                               ride_backup(ride, boarding, scenario, c0, short_stop_name(ride.board_node_id or "-", scenario),
                                           short_stop_name(ride.alight_node_id, scenario), dest_name, p_safe,
                                           bool(fast.get(ride.index))), ride.board_node_id or ""))
    arrival = itinerary.arrival.mean_s
    steps.append(GuideStep("arrive", f"{dest_name} 도착", () if arrival is None else (f"평균 {fmt_hm(c0, arrival)} 도착",)))
    return tuple(steps)


def _walk_text(path) -> str:
    return f"{fmt_minutes(minute_of(path.t_end_s - path.t_start_s))} · {fmt_dist(path.distance_m)}"


def ride_backup(ride, boarding, scenario: Scenario | None, c0: float, board: str, alight: str, dest_name: str,
                p_safe: float = 0.75, fast: bool = False) -> tuple[str, ...]:
    """타기 단계의 놓치면 줄(§6.9, 19·28단계). 안내 차량이 없으면 빈 튜플. `board`, `alight` 는 짧은 지점 이름(`short_stop_name`).
    1. "이 차는 {catch_text(p_conditional, p_safe, fast)}." (앞 탑승을 계획대로 했을 때 안내 차량이나 그 앞차를 탈 확률).
    2. 안내 차량이 막차이면 대체 보행으로, 아니면 차량 목록에서 안내 차량 다음의(출발이 더 늦은) 첫 차로 적는다."""
    guided = _vehicle(boarding, boarding.guided_trip_id) if boarding is not None else None
    if guided is None:
        return ()
    lines = [f"이 차는 {catch_text(boarding.p_conditional, p_safe, fast)}."]
    if guided.is_last:
        if ride.fallback is not None:
            lines.append(f"막차입니다. 놓치면 {board}에서 {dest_name}까지 걸어야 합니다({_walk_text(ride.fallback)}).")
        else:
            lines.append("막차입니다. 놓치면 이 노선으로는 갈 수 없습니다.")
        return tuple(lines)
    order = list(boarding.vehicles)
    after = order[order.index(guided) + 1:]
    nxt = next((option for option in after if option.dep_s > guided.dep_s), None)
    if nxt is not None:
        n = minute_of(c0 + nxt.alight_arr_s) - minute_of(c0 + guided.alight_arr_s)
        if n >= 1:
            lines.append(f"놓치면 {next_vehicle_text(ride, nxt, scenario, c0, ('을', '를'))} 타면 되고, {alight}에서 약 "
                         f"{fmt_minutes(n)} 늦게 내립니다.")
        else:
            lines.append(f"놓치면 {next_vehicle_text(ride, nxt, scenario, c0, ('을', '를'))} 타도 {alight}에서 내리는 시각은 같습니다.")
    return tuple(lines)


def next_vehicle_text(ride, option, scenario: Scenario | None, c0: float, particle: tuple[str, str] = ("", "")) -> str:
    """놓치면 줄의 뒤차(§6.9, 19단계): 묶음 탑승이면 노선이 다를 수 있어 `easy_vehicle`, 아니면 "막차"(뒤차가 막차) 또는
    "다음 열차"/"다음 버스" 에 "({HH:MM} 출발)" 과 조사. 노선은 단계 제목이 이미 말한다."""
    if ride.bundle:
        return easy_vehicle(ride, option, scenario, c0, particle)
    word = "막차" if option.is_last else ("다음 열차" if ride.mode == TravelMode.SUBWAY else "다음 버스")
    return f"{word}({fmt_hm(c0, option.dep_s, 'floor')} 출발){josa(word, *particle)}"


def bike_backup(bike, to_name: str) -> tuple[str, ...]:
    """따릉이 타기 단계의 놓치면 줄(§6.9, 19단계): 대여소에서 그 이동의 도착점(짧은 지점 이름)까지 걷는 대체 보행."""
    if bike.fallback is None:
        return ()
    return (f"자전거가 없으면 {to_name}까지 걸어야 합니다({_walk_text(bike.fallback)}).",)


def easy_steps_html(itinerary: ItineraryResult, output: EngineOutput, scenario: Scenario | None,
                    fast: Mapping[int, bool] | None = None) -> str:
    items = []
    for number, step in enumerate(easy_steps(itinerary, output, scenario, fast), start=1):
        label = "" if step.kind == "arrive" else str(number)
        subs = "".join(f'<div class="mr-sub">{esc(sub)}</div>' for sub in step.subs)
        if step.backup:
            subs += ('<div class="mr-backup">' + "".join(f'<div>{_nowrap_parens(esc(line))}</div>' for line in step.backup)
                     + "</div>")
        items.append(f'<li><span class="mr-n {step.kind}">{label}</span><div><div class="mr-main">{esc(step.main)}</div>'
                     f"{subs}</div></li>")
    return f'<ol class="mr-easy mr-steps">{"".join(items)}</ol>'


@dataclasses.dataclass(frozen=True)
class EasyAlternative:
    title: str
    grade: Grade
    detail: str
    itinerary_id: str = ""
    recommended: bool = False
    note: str = ""


def easy_alternatives(output: EngineOutput, scenario: Scenario | None, shown_id: str | None = None) -> tuple[EasyAlternative, ...]:
    """다른 경로(§6.9): [최선] + 순위에서 보는 경로를 뺀 대표 여정 `SIMPLE_ALT_MAX` 개까지."""
    items = _items(output)
    names = easy_names(scenario)
    c0 = output.clock_s
    shown = _shown_id(output, shown_id)
    ids = _alt_ids(output, shown_id)
    visible = [shown, *ids] if shown else ids
    naive_id = output.comparison.naive_best_id
    rows = []
    for rep_id in ids:
        it = items[rep_id]
        title = easy_title(it, visible, output, scenario)
        parts = []
        if it.arrival.mean_s is not None:
            parts.append(f"{fmt_minutes(trip_minutes(c0, it.arrival.mean_s))} · {fmt_hm(c0, it.arrival.mean_s)} 도착")
        parts.append(fare_text(it))
        board = _first_board(it)
        if board is not None and title == it.label:
            parts.append(f"{names.get(board, board)}에서 승차")
        note = ""
        if rep_id == naive_id:
            parts.append("기존 길찾기 방식의 1위")
            naive = items.get(naive_id)
            ghost = _ghost_boarding(naive) if naive is not None else None
            if ghost is not None:
                note = "기존 길찾기 방식이 타라는 차는 놓치기 쉬워, 이 앱은 탈 수 있는 차로 다시 계산했습니다."
        rows.append(EasyAlternative(title, it.grade, " · ".join(parts), rep_id, rep_id == output.comparison.best_id, note))
    return tuple(rows)


ALTS_HEAD_HTML = '<div class="mr-alts-h">다른 경로</div>'

COMPARE_HEAD = "경로 비교"
COMPARE_COLS = ("걸리는 시간", "도착", "요금")
COMPARE_HEAD_HTML = (f'<div class="mr-alts-h">{COMPARE_HEAD}</div><div class="mr-cmp-cols" aria-hidden="true">'
                     + "".join(f"<span>{name}</span>" for name in COMPARE_COLS) + "</div>")


@dataclasses.dataclass(frozen=True)
class CompareRow:
    """경로 비교 표의 한 줄(§6.9, 32단계). 세 값(분, 도착, 요금)은 모든 줄에서 같은 칸·같은 글자 크기다."""
    itinerary_id: str
    common: str  # 모든 줄이 같은 앞부분("지하철 2호선 → 지하철 9호선 → "), 없으면 ""
    tail: str  # 줄마다 다른 뒷부분
    grade: Grade
    minutes: str
    arrive: str
    fare: str
    recommended: bool  # 이 앱의 추천(최선)
    shown: bool  # 지금 위에서 보는 경로
    naive: bool  # 기존 길찾기 방식의 1위
    pickable: bool  # "이 경로 보기" 단추를 두나(걸러진 경로는 안내할 수 없어 두지 않는다)
    notes: tuple[str, ...] = ()


def _compare_ids(output: EngineOutput) -> list[str]:
    """표의 여정: 최선, 기존 방식 1위(최선과 다르면 바로 아래에: 추천 줄과 도착을 맞대어 보게), 순위의 다른 대표(최대 `SIMPLE_ALT_MAX` 개)."""
    best_id = output.comparison.best_id
    naive_id = output.comparison.naive_best_id
    head = [best_id] if best_id else []
    if naive_id and naive_id in _items(output) and naive_id not in head:
        head.append(naive_id)
    return head + [rep for rep in output.ranking if rep not in head][:SIMPLE_ALT_MAX]


def naive_notes(output: EngineOutput, scenario: Scenario | None) -> tuple[str, ...]:
    """기존 방식 1위 줄에 붙이는 설명(32단계): 기존 앱이 안내하는 도착과 이 앱이 계산한 도착, 놓치기 쉬운 차."""
    cmp = output.comparison
    naive = _items(output).get(cmp.naive_best_id) if cmp.naive_best_id else None
    if naive is None:
        return ()
    c0 = output.clock_s
    lines = []
    promised = cmp.naive_promised_s
    if cmp.same:
        lines.append("기존 길찾기 앱도 이 경로를 1위로 안내합니다.")
    if promised is None:
        lines.append("기존 길찾기 앱은 탈 차가 없어 도착 시각을 안내하지 못합니다.")
    elif cmp.naive_mean_s is not None and not cmp.same:
        said, real = fmt_hm(c0, promised), fmt_hm(c0, cmp.naive_mean_s)
        late = minute_of(c0 + cmp.naive_mean_s) - minute_of(c0 + promised)  # 33단계: 보이는 두 시각(분 단위)의 차
        lines.append(f"기존 길찾기 앱 안내 {said} 도착 → 이 앱 계산 {real} 도착" + (f" ({late}분 늦음)" if late >= 1 else ""))
    else:
        lines.append(f"기존 길찾기 앱 안내 {fmt_hm(c0, promised)} 도착")
    ghost = _ghost_boarding(naive)
    if ghost is not None:
        ride, boarding = ghost
        option = _vehicle(boarding, boarding.naive_trip_id)
        which = easy_vehicle(ride, option, scenario, c0, ("은", "는")) if option is not None else f"{ride_name(ride)} 차는"
        lines.append(f"기존 앱이 타라는 {which} 놓치기 쉽습니다.")
        if cmp.same:
            guided = _vehicle(boarding, boarding.guided_trip_id)
            if guided is not None:
                lines.append(f"이 앱은 {easy_vehicle(ride, guided, scenario, c0, ('을', '를'))} 안내합니다.")
    elif cmp.naive_status == RouteStatus.GHOST_PRUNED:
        lines.append("차를 놓치면 걸어서 갈 길이 없습니다." if ReasonCode.UNREACHABLE in cmp.naive_reasons
                     else "그대로는 계획대로 가기 어렵습니다.")
    return tuple(lines)


def compare_rows(output: EngineOutput, scenario: Scenario | None, shown_id: str | None = None) -> tuple[CompareRow, ...]:
    """경로 비교 표(§6.9, 32단계): 최선이 맨 위, 기존 방식 1위는 그 줄에 설명을 붙인다. 최선이 없으면 빈 튜플."""
    items = _items(output)
    if output.comparison.best_id not in items:
        return ()
    ids = _compare_ids(output)
    shown = _shown_id(output, shown_id)
    titles = [easy_title(items[rid], ids, output, scenario) for rid in ids]
    parts = [title.split(" → ") for title in titles]
    common_n = 0
    if len(parts) >= 2:
        while all(len(part) > common_n + 1 and part[common_n] == parts[0][common_n] for part in parts):
            common_n += 1
    c0 = output.clock_s
    naive_id = output.comparison.naive_best_id
    notes = naive_notes(output, scenario)
    rows = []
    for rid, part in zip(ids, parts):
        it = items[rid]
        mean = it.arrival.mean_s
        common = " → ".join(part[:common_n]) + " → " if common_n else ""
        # 35단계: 기존 방식 1위 줄의 배지는 기존 앱이 타라는 차 기준. 그 차가 놓치기 쉬우면 "놓치기 쉬움"(설명 줄과 같은 말)
        grade = Grade.GHOST if rid == naive_id and _ghost_boarding(it) is not None else it.grade
        rows.append(CompareRow(
            rid, common, " → ".join(part[common_n:]), grade,
            "-" if mean is None else fmt_minutes(trip_minutes(c0, mean)), "-" if mean is None else fmt_hm(c0, mean),
            fare_text(it), rid == output.comparison.best_id, rid == shown, rid == naive_id,
            it.status == RouteStatus.RANKED, notes if rid == naive_id else ()))
    return tuple(rows)


def compare_row_html(row: CompareRow) -> str:
    tags = []
    if row.recommended:
        tags.append('<span class="mr-tag rec">앱 추천</span>')
    if row.naive:
        tags.append('<span class="mr-tag">기존 앱 1위</span>')
    if row.shown:
        tags.append('<span class="mr-tag">보는 중</span>')
    name = (f'<span class="mr-cmp-common">{esc(row.common)}</span>' if row.common else "") + f'<span>{esc(row.tail)}</span>'
    notes = "".join(f'<div class="mr-cmp-note{" lead" if n == 0 and row.naive else ""}">{esc(line)}</div>' for n, line in enumerate(row.notes))
    css = " ".join(c for c in ("mr-cmp", "rec" if row.recommended else "", "naive" if row.naive else "") if c)
    return (f'<div class="{css}"><div class="mr-cmp-t"><span class="mr-cmp-name">{name}</span>'
            f'{grade_badge(row.grade, easy=True)}{"".join(tags)}</div>'
            f'<div class="mr-cmp-v mr-num"><span>{esc(row.minutes)}</span><span>{esc(row.arrive)}</span>'
            f'<span>{esc(row.fare)}</span></div>{notes}</div>')


def easy_alternative_html(row: EasyAlternative) -> str:
    tag = '<span class="mr-tag">앱 추천</span>' if row.recommended else ""
    note = f'<div class="mr-alt-n">{esc(row.note)}</div>' if row.note else ""
    return (f'<div class="mr-alt"><div class="mr-alt-t"><span>{esc(row.title)}</span>{grade_badge(row.grade)}{tag}</div>'
            f'<div class="mr-alt-s mr-num">{esc(row.detail)}</div>{note}</div>')


def trip_html(origin_text: str, dest_text: str) -> str:
    return (f'<div class="mr-trip"><div><span class="mr-tk o">출발</span><span class="mr-tv">{esc(origin_text)}</span></div>'
            f'<div><span class="mr-tk d">도착</span><span class="mr-tv">{esc(dest_text)}</span></div></div>')


# --- 지도 범례 (§7.5 mr-legend) ---
# st.html 은 넣은 HTML 을 걸러 svg 요소를 지운다(streamlit 1.67 의 브라우저 화면에서 확인). 그래서 견본은 CSS 배경과 테두리로 그린다.


def _line_swatch(color: str, *, width: float = 3, style: str = "solid") -> str:
    """24 × 8 px 선 견본. style: solid(실선), double(가운데 흰 줄), dots(둥근 점선 1·5), dash(파선 5·4), dashdot(일점쇄선 7·3·2·3)."""
    c = color
    band = f"center / 22px {width:g}px no-repeat"
    background = {
        "solid": f"linear-gradient({c}, {c}) {band}",
        "double": f"linear-gradient(#ffffff, #ffffff) center / 22px 1.2px no-repeat, linear-gradient({c}, {c}) {band}",
        "dots": f"radial-gradient(circle at 3px 50%, {c} {width / 2:g}px, transparent {width / 2 + 0.3:g}px) 1px 50% / 6px 100% repeat-x",
        "dash": f"repeating-linear-gradient(90deg, {c} 0 5px, transparent 5px 9px) {band}",
        "dashdot": f"repeating-linear-gradient(90deg, {c} 0 7px, transparent 7px 10px, {c} 10px 12px, transparent 12px 15px) {band}",
    }[style]
    return f'<span class="mr-swl" style="background: {esc(background)}" aria-hidden="true"></span>'


def _dot_swatch(fill: str, *, stroke: str = "#ffffff", dashed: bool = False, square: bool = False, text: str = "",
                text_color: str = "#ffffff", size: int = 12) -> str:
    """표지 견본: 지름(정류장은 한 변) size px, 테두리 1.5 px(감응 신호와 남을 확률 낮은 대여소는 점선), 가운데 글자."""
    style = (f"width: {size}px; height: {size}px; background: {fill}; border: 1.5px {'dashed' if dashed else 'solid'} {stroke}; "
             f"border-radius: {'3px' if square else '50%'}; color: {text_color}")
    return f'<span class="mr-swd" style="{esc(style)}" aria-hidden="true">{esc(text)}</span>'


def legend_html(tokens: Mapping[str, str], *, kakao: bool = False) -> str:
    """지도 범례(§7.5): 견본은 실제 선 모양(실선, 이중선, 점선, 파선, 일점쇄선)과 표지 모양을 그린다."""
    t = tokens
    entries = [
        (_line_swatch(t["bus"], width=4), "버스"),
        (_line_swatch(t["subway"], width=5, style="double"), "지하철"),
        (_line_swatch(t["bike"], width=3.5), "따릉이"),
        (_line_swatch(t["ink2"], width=3, style="dots"), "도보"),
        (_line_swatch(t["muted"], width=3, style="dash"), "기존 앱 방식 1위"),
    ]
    if kakao:
        entries.append((_line_swatch(t["ink"], width=2, style="dashdot"), "카카오 도보 경로(비교)"))
    entries += [
        (_dot_swatch(t["safe"]), "녹색 신호"),
        (_dot_swatch(t["ghost"]), "적색 신호"),
        (_dot_swatch(t["muted"]), "미개방 신호"),
        (_dot_swatch(t["muted"], dashed=True), "감응 신호"),
        (_dot_swatch(t["bus"], square=True), "정류장"),
        (_dot_swatch(t["subway"]), "승강장"),
        (_dot_swatch(t["bike"], text="3", size=14), "대여소(빌릴 수 있음)"),
        (_dot_swatch("#ffffff", stroke=t["bike"], text="0", text_color=t["bike"], size=14), "대여소(자전거 없음)"),
        (_dot_swatch("#ffffff", stroke=t["bike"], dashed=True, text="1", text_color=t["bike"], size=14), "대여소(남을 확률 낮음)"),
        (_dot_swatch(t["ink"], size=12), "출발·도착"),
        (_dot_swatch(t["ghost"], text="✕", size=14), "유령 환승 표지"),
        (_dot_swatch("#ffffff", stroke=t["ink2"], text="1", text_color=t["ink"], size=14), "탐색 라운드(숫자)"),
    ]
    return '<div class="mr-legend">' + "".join(f'<span class="mr-li">{swatch}{esc(text)}</span>' for swatch, text in entries) + "</div>"


# ===== U3. 상태와 데이터 준비 =====

DEADLINE_PAST_LIMIT_S = 43_200  # 마감까지 남은 시간이 이보다 길면 이미 지난 마감으로 본다(§6.4)
STORE_FILE = "records.sqlite"
TARGETS_FILE = "collect_targets.json"
MODEL_FILES = ("signal_model.json", "bike_model.json")
_UTF8_BOM = b"\xef\xbb\xbf"
_SOURCES_ADAPTER: TypeAdapter = TypeAdapter(tuple[ApiSourceStatus, ...])
_TRAINS_ADAPTER: TypeAdapter = TypeAdapter(tuple[TrainChoice, ...])
_COLLECTED_SOURCES = (SourceKind.BUS_ARRIVAL, SourceKind.BIKE, SourceKind.SIGNAL)

# 이번 실행에서 실시간 조회를 실제로 한 시각. Streamlit 은 실행마다 스크립트를 새로 실행하므로 이 목록은 실행마다 비어서
# 시작하고, `cached_live` 의 본문이 실제로 실행될 때만(캐시에서 꺼내면 실행되지 않는다) 시각이 들어간다(§8.4).
_LIVE_FETCHES: list[float] = []

# 시나리오를 바꾸면 그 시나리오의 기본 질의로 돌아가는 키(§6.3, §8.3).
QUERY_KEYS: tuple[str, ...] = (
    "origin_kind", "origin_place", "origin_point", "train_station", "train_key", "bus_line", "bus_stop_index",
    "bus_vehicle", "prior_km", "dest_kind", "dest_place", "dest_point", "map_pick", "last_map_click",
    "use_deadline", "deadline_time", "selected_id", "last_default_id", "origin_gps", "gps_note",
)
# 조건에 따라 그리는 위젯. 그리지 않은 실행에서 값이 지워지므로 `keep_` 보존 키에 복사해 둔다(§8.3).
KEEP_KEYS: tuple[str, ...] = (
    "replay_window", "replay_date", "replay_time", "origin_place", "train_station", "train_key", "bus_line",
    "bus_stop_index", "bus_vehicle", "prior_km", "dest_place", "map_pick", "deadline_time", "weight_preset", "w_time",
    "w_cost", "w_risk", "v_walk", "selected_id", "show_variants", "trace_run", "trace_line",
)


def setting_defaults() -> dict[str, Any]:
    """조건 위젯의 기본값(§8.3). 값은 `EngineConfig` 기본값과 프리셋 표에서 읽는다(코드에 숫자를 적지 않는다)."""
    config = EngineConfig()
    walk = next((name for name, value in WALK_SPEED_PRESETS.items() if value == config.v_walk_mps), WALK_CUSTOM)
    return {
        "depart_offset_s": 0,
        "rank_criterion": config.rank_criterion.value,
        "weight_preset": next(iter(WEIGHT_PRESETS)),
        "w_time": config.w_time,
        "w_cost": config.w_cost,
        "w_risk": config.w_risk,
        "walk_preset": walk,
        "v_walk": config.v_walk_mps,
        "use_bus": TravelMode.BUS in config.modes_enabled,
        "use_subway": TravelMode.SUBWAY in config.modes_enabled,
        "use_bike": TravelMode.BIKE in config.modes_enabled,
        "max_rides": config.max_rides,
        "climate_card": config.climate_card,
        "bike_mileage": config.bike_mileage,
        "gamma": config.gamma,
        "safety_buffer": config.safety_buffer_s,
        "v_pm": config.v_pm_mps,
        "max_bike_legs": config.max_bike_legs,
        "full_skip": config.full_vehicle_policy == FullVehiclePolicy.SKIP,
        "k_pm": config.k_pm,
        "show_variants": False,
    }


APP_TITLE = "가장 빨리 도착하는 길찾기"
APP_SUBTITLE = "놓치기 쉬운 환승을 걸러 실제로 가장 빨리 닿는 길"  # 휴대폰에서 한 줄(§6.5)

SESSION_DEFAULTS: Mapping[str, Any] = {
    "data_mode": DataMode.SIMULATION.value,
    "view_mode": "SIMPLE",
    "live_refresh": 0,
    "live_fetched_at": None,
    "kakao_results": {},
    "kakao_calls": 0,
}


def keep_key(key: str) -> str:
    return f"keep_{key}"


def remember(key: str) -> None:
    """위젯의 `on_change`: 값을 보존 키에 복사한다(§8.3)."""
    st.session_state[keep_key(key)] = st.session_state.get(key)


def restore(state: MutableMapping[str, Any], key: str, default: Any) -> None:
    """위젯을 그리기 전에: 보존 키가 있으면 그 값으로, 위젯 키도 없으면 기본값으로 둔다."""
    keep = keep_key(key)
    if keep in state:
        state[key] = state[keep]
    elif key not in state:
        state[key] = default


def store_value(state: MutableMapping[str, Any], key: str, value: Any) -> None:
    """위젯을 그리기 전에 값을 바꾼다. 보존 키가 있는 위젯이면 보존 키도 함께 바꾼다."""
    state[key] = value
    if key in KEEP_KEYS:
        state[keep_key(key)] = value


def sync_keep(state: MutableMapping[str, Any], key: str) -> None:
    """위젯을 그린 뒤 보존 키를 지금 값에 맞춘다."""
    state[keep_key(key)] = state.get(key)


def drop_keys(state: MutableMapping[str, Any], keys: Iterable[str]) -> None:
    for key in keys:
        for name in (key, keep_key(key)):
            if name in state:
                del state[name]


def _on_scenario_change() -> None:
    """시나리오를 바꾸면 출발, 목적지, 마감, 선택이 그 시나리오의 기본 질의로 돌아가고 카카오 비교 결과를 지운다(§6.3).
    재생 구간, 날짜, 시각과 출발 늦추기를 포함한 조건은 그대로 둔다."""
    state = st.session_state
    drop_keys(state, QUERY_KEYS)
    state["kakao_results"] = {}


def _on_mode_change() -> None:
    st.session_state["kakao_results"] = {}


def _on_reset() -> None:
    """"기본값으로 되돌리기"(§6.3): 시나리오, 데이터 모드, 재생 날짜와 시각은 두고 나머지를 기본값으로 둔다.
    `live_refresh`, `live_fetched_at`, `kakao_calls` 는 조건이 아니라 사용 기록이라(조회 간격과 호출 한도를 지키려고) 두고,
    카카오 비교 결과도 여정 ID 로 찾는 결과라 그대로 둔다."""
    state = st.session_state
    defaults = setting_defaults()
    drop_keys(state, (*QUERY_KEYS, *defaults, "guide"))  # 안내도 끝낸다(§6.10)
    for key, value in defaults.items():
        state[key] = value


def _on_train_station_change() -> None:
    remember("train_station")
    drop_keys(st.session_state, ("train_key",))


def _on_bus_line_change() -> None:
    remember("bus_line")
    drop_keys(st.session_state, ("bus_stop_index", "bus_vehicle"))


def _on_bus_stop_change() -> None:
    remember("bus_stop_index")
    drop_keys(st.session_state, ("bus_vehicle",))


def _on_window_change(info: Mapping[str, tuple[datetime.date, datetime.time]]) -> None:
    """기록 구간을 고르면 날짜를 그 날짜로, 시각을 첫 조회 + 2 × 조회 주기(분 단위 올림)로 둔다(§6.3)."""
    state = st.session_state
    remember("replay_window")
    value = state.get("replay_window")
    if value in info:
        day, clock = info[value]
        store_value(state, "replay_date", day)
        store_value(state, "replay_time", clock)


def _on_live_refresh() -> None:
    st.session_state["live_refresh"] = int(st.session_state.get("live_refresh", 0)) + 1


def _on_apply_bike_speed(v_pm: float, k_pm: float) -> None:
    st.session_state["v_pm"] = v_pm
    st.session_state["k_pm"] = k_pm


def _on_gps_fix() -> None:
    """위치 단추의 트리거 콜백: 받은 값을 두기만 하고, 판정은 다음 실행의 `process_gps` 가 한다(§6.8)."""
    value = st.session_state.get(GPS_COMPONENT_KEY)
    fix = value.get("fix") if isinstance(value, Mapping) else None
    if fix is not None:
        st.session_state["gps_pending"] = fix


def _on_gps_switch(scenario_id: str) -> None:
    """"바꿔 출발"(§6.8): 시나리오 선택 상자를 바꿀 때처럼 질의 키를 지우고, 그 시나리오에서 지금 위치로 출발한다."""
    state = st.session_state
    note = state.get("gps_note")
    fix = note.get("fix") if isinstance(note, Mapping) else None
    drop_keys(state, QUERY_KEYS)
    state["kakao_results"] = {}
    if isinstance(fix, Mapping):
        state["scenario_id"] = scenario_id
        apply_gps_result(state, {"kind": "HERE", "fix": fix})


def _on_origin_kind_change() -> None:
    drop_keys(st.session_state, ("gps_note",))


def first_example(state: MutableMapping[str, Any], scenario: Scenario) -> None:
    """첫 화면(§6.3 30단계): 시나리오에 예시 경로가 있으면 첫 예시의 출발·목적지 장소를 둔다. 없으면 아무것도 바꾸지 않는다."""
    if not scenario.examples:
        return
    name_of = {place.node_id: place.name for place in scenario.places}
    example = scenario.examples[0]
    for key, value in (("origin_kind", "PLACE"), ("origin_place", name_of[example.origin_node_id]),
                       ("dest_kind", "PLACE"), ("dest_place", name_of[example.destination_node_id])):
        store_value(state, key, value)


def _on_example(origin_place: str, dest_place: str) -> None:
    """예시 경로 버튼(§6.3): 출발·목적지를 그 예시의 장소로 두고 고른 여정과 지금 위치를 지운다. 다른 조건은 그대로다.
    간단히 보기의 접힘 "출발·목적지 바꾸기"는 닫는다(§6.9 19단계): 둘 다 정해졌으니 답 카드가 바로 보이게."""
    state = st.session_state
    state["trip_edit"] = False
    store_value(state, "origin_kind", "PLACE")
    store_value(state, "origin_place", origin_place)
    store_value(state, "dest_kind", "PLACE")
    store_value(state, "dest_place", dest_place)
    drop_keys(state, ("selected_id", "last_default_id", "origin_gps", "gps_note"))


def effective_mode(selected: str, has_records: bool, has_key: bool) -> tuple[str, str | None]:
    """실제 데이터 모드와 대체 사유(§6.4). 쓸 수 없는 모드를 고르면 시뮬레이션으로 계산한다."""
    if selected == DataMode.REPLAY.value and not has_records:
        return DataMode.SIMULATION.value, "기록 재생 불가"
    if selected == DataMode.LIVE.value and not has_key:
        return DataMode.SIMULATION.value, "실시간 불가"
    return selected, None


def deadline_t(deadline_clock_s: float, c0_s: float) -> float | None:
    """마감 시계 시각을 $t$ 로: $t_{dl} = (\\text{마감 시계 초} - c_0') \\bmod 86{,}400$. 43,200 초를 넘거나 0 이면 None(§6.4)."""
    t = (float(deadline_clock_s) - float(c0_s)) % SECONDS_PER_DAY
    if t <= 0 or t > DEADLINE_PAST_LIMIT_S:
        return None
    return t


def apply_map_click(state: MutableMapping[str, Any], clicked: Mapping[str, Any] | None) -> bool:
    """지도에서 누른 좌표를 출발이나 목적지로 둔다(§6.4). 직전에 처리한 좌표와 같으면 무시한다. 상태가 바뀌면 참."""
    if not clicked:
        return False
    lat, lng = clicked.get("lat"), clicked.get("lng")
    if lat is None or lng is None:
        return False
    origin_point = state.get("origin_kind") == "POINT"
    dest_point = state.get("dest_kind") == "POINT"
    if not origin_point and not dest_point:
        return False
    if origin_point and dest_point:
        target = state.get("map_pick") or "ORIGIN"
    else:
        target = "ORIGIN" if origin_point else "DESTINATION"
    point = {"lat": float(lat), "lng": float(lng)}
    if state.get("last_map_click") == point:
        return False
    state["origin_point" if target == "ORIGIN" else "dest_point"] = (point["lat"], point["lng"])
    state["last_map_click"] = point
    return True


# --- 지금 위치에서 출발 (§6.8) ---


@dataclasses.dataclass(frozen=True)
class _GpsRegion:
    """목록의 시나리오 하나에서 본 위치: 가장 가까운 지상 노드까지의 거리와 그 노드 이름, 가상 여부, 지역 안인지."""

    distance_m: float
    order: int
    scenario_id: str
    label: str
    node_name: str
    virtual: bool
    inside: bool


def gps_virtual(scenario: Scenario) -> bool:
    """버스 노선 가운데 실제 노선이 아닌 것이 하나라도 있으면 가상 시나리오다(골든과 그 변형, 합성 기록 세계, §6.8)."""
    return any(not line.real_route for line in scenario.bus_lines)


def _gps_number(value: Any) -> float | None:
    if isinstance(value, bool) or not isinstance(value, (int, float)):
        return None
    number = float(value)
    return number if math.isfinite(number) else None


def _gps_error(code: str) -> dict[str, Any]:
    return {"kind": "ERROR", "code": code, "text": GPS_ERROR_TEXTS[code], "fix": None, "choices": []}


def locate_fix(fix: Any, current_id: str, listed: Sequence[tuple[str, str, Scenario]], config: EngineConfig) -> dict[str, Any]:
    """브라우저가 준 위치가 어느 시나리오의 지역인지 판정한다(§6.8). 순수 함수.

    지역 안은 가장 가까운 지상 노드까지 `snap_max_m` 이하(엔진이 그 점을 붙이는 조건)이고, 가상 시나리오는 지역으로 치지 않는다.
    지금 시나리오의 지역이면 HERE, 다른 시나리오들의 지역이면 OTHER (거리, 목록 순서), 아니면 OUTSIDE (가장 가까운 곳을 적는다).
    """
    if not isinstance(fix, Mapping):
        return _gps_error("BAD_FIX")
    if "error" in fix:
        code = fix["error"]
        return _gps_error(code if isinstance(code, str) and code in GPS_ERROR_TEXTS else "BAD_FIX")
    lat, lon, accuracy = (_gps_number(fix.get(name)) for name in ("lat", "lon", "accuracy"))
    if lat is None or lon is None or accuracy is None or not (-90.0 <= lat <= 90.0 and -180.0 <= lon <= 180.0) or accuracy < 0:
        return _gps_error("BAD_FIX")
    point = {"lat": lat, "lon": lon, "accuracy_m": accuracy}
    regions: list[_GpsRegion] = []
    for order, (scenario_id, label, scenario) in enumerate(listed):
        found = nearest_ground(scenario, lat, lon, ce.ORIGIN_POINT_ID, config)
        if found is None:
            continue
        node_id, distance = found
        regions.append(_GpsRegion(distance, order, scenario_id, label, node_names(scenario).get(node_id, node_id),
                                  gps_virtual(scenario), distance <= config.snap_max_m))
    current = next((region for region in regions if region.scenario_id == current_id), None)
    if current is not None and current.inside and not current.virtual:
        return {"kind": "HERE", "code": None, "text": "", "fix": point, "choices": []}
    prefix = GPS_VIRTUAL_PREFIX if current is not None and current.inside and current.virtual else ""
    real = sorted((region for region in regions if not region.virtual), key=lambda region: (region.distance_m, region.order))
    choices = [(region.scenario_id, region.label) for region in real if region.inside and region.scenario_id != current_id]
    if choices:
        return {"kind": "OTHER", "code": None, "text": prefix + GPS_OTHER_TEXT, "fix": point, "choices": choices}
    nearest = (real[0].label, real[0].node_name, real[0].distance_m) if real else None
    return {"kind": "OUTSIDE", "code": None, "text": prefix + gps_outside_text(nearest), "fix": point, "choices": []}


def apply_gps_result(state: MutableMapping[str, Any], result: Mapping[str, Any]) -> None:
    """`locate_fix` 의 결과로 상태를 바꾼다(§6.8). 순수 함수: 넘겨받은 상태 사전만 고친다.
    HERE 면 출발을 그 점으로, 그 밖에는 안내 `gps_note` 만 둔다(OTHER 만 바꿔 출발에 쓸 위치를 함께 둔다)."""
    if result["kind"] == "HERE":
        fix = result["fix"]
        state["origin_kind"] = "POINT"
        state["origin_point"] = (fix["lat"], fix["lon"])
        state["origin_gps"] = dict(fix)
        drop_keys(state, ("gps_note",))
        return
    note: dict[str, Any] = {"kind": result["kind"], "code": result["code"], "text": result["text"]}
    if result["kind"] == "OTHER":
        note["choices"] = list(result["choices"])
        note["fix"] = dict(result["fix"])
    state["gps_note"] = note


def gps_origin(state: Mapping[str, Any]) -> Mapping[str, float] | None:
    """지금 위치로 정한 출발이면 그 위치 {"lat", "lon", "accuracy_m"}, 아니면 None. `origin_gps` 가 `origin_point` 와 같을 때만이다."""
    gps, point = state.get("origin_gps"), state.get("origin_point")
    if not isinstance(gps, Mapping) or point is None:
        return None
    return gps if (gps.get("lat"), gps.get("lon")) == (float(point[0]), float(point[1])) else None


def process_gps(state: MutableMapping[str, Any], ctx: DataContext, scenario_id: str) -> None:
    """위치 단추가 둔 값을 판정해 상태를 바꾸고, 지도 누르기로 바뀐 출발에서는 지금 위치를 지운다(§6.8). 출발 위젯 앞에서 부른다."""
    if "gps_pending" in state:
        fix = state["gps_pending"]
        del state["gps_pending"]
        listed = [(entry_id, label, scenario_object(entry_json)) for entry_id, label, entry_json in ctx.entries]
        apply_gps_result(state, locate_fix(fix, scenario_id, listed, ctx.data_config))
    if "origin_gps" in state and gps_origin(state) is None:
        drop_keys(state, ("origin_gps",))


# --- 데이터 폴더, 키, 수집 대상, 기록 요약, 모델 (§8.2, §8.4) ---


def data_folder() -> Path:
    """환경변수 `MOBILITY_ROUTER_DATA_DIR` 가 있으면 그 폴더, 없으면 app.py 옆의 `data/`(§8.2)."""
    value = (os.environ.get(DATA_DIR_ENV) or "").strip()
    return Path(value).expanduser().resolve() if value else _APP_DIR / "data"


def files_key(paths: Iterable[Path]) -> str:
    """파일들의 (이름, 수정 시각, 크기) 목록. 캐시 함수가 파일이 바뀐 것을 알아채는 키다."""
    rows = []
    for path in paths:
        try:
            info = path.stat()
        except OSError:
            continue
        rows.append((path.name, info.st_mtime_ns, info.st_size))
    return json.dumps(rows)


def key_presence() -> dict[str, bool]:
    """키 환경변수가 있는지(값은 읽어 두지 않는다, §5.5). 이름은 `EngineConfig` 의 환경변수 이름 필드에서 읽는다."""
    config = EngineConfig()
    names = (config.env_seoul_key, config.env_data_go_kr_key, config.env_kakao_key, config.env_tdata_key)
    return {name: bool((os.environ.get(name) or "").strip()) for name in names}


def load_targets(folder: Path) -> tuple[CollectTargets, bool]:
    """데이터 폴더의 수집 대상 파일. 없거나 읽지 못하면 기본 대상에서 휴일을 뺀 값(명령줄과 같은 규칙)."""
    path = folder / TARGETS_FILE
    try:
        raw = path.read_bytes()
    except OSError:
        raw = None
    if raw is not None:
        if raw.startswith(_UTF8_BOM):
            raw = raw[len(_UTF8_BOM):]
        try:
            return CollectTargets.model_validate_json(raw), True
        except ValueError:
            pass
    default = CollectTargets.model_validate_json(DEFAULT_TARGETS_JSON)
    return default.model_copy(update={"holidays": ()}), False


@st.cache_data(show_spinner=False)
def cached_scenarios(data_dir: str, scenario_files_key: str) -> tuple[tuple[tuple[str, str, str], ...], tuple[str, ...]]:
    """((시나리오 ID, 표시 이름, JSON), ...)과 읽지 못한 파일 이름들(§6.3, §8.4). 손으로 만든 시나리오(ID 순), 골든,
    데이터 폴더의 `scenarios/*.json` (생성 명세 `*.spec.json` 제외, ID 순) 차례다. ID 가 앞과 겹치는 파일도 읽지 못한 파일이다."""
    entries: list[tuple[str, str, str]] = []
    seen: set[str] = set()
    hand = ce.build_scenarios()
    for scenario_id in sorted(hand):
        scenario = hand[scenario_id]
        entries.append((scenario.id, scenario.title, scenario.model_dump_json()))
        seen.add(scenario.id)
    golden = ce.golden_scenario()
    entries.append((golden.id, f"{golden.title} (검산용)", golden.model_dump_json()))
    seen.add(golden.id)
    folder = Path(data_dir) / "scenarios"
    loaded: list[tuple[Scenario, str]] = []
    bad: list[str] = []
    if folder.is_dir():
        for path in sorted(folder.glob("*.json")):
            if path.name.endswith(".spec.json"):
                continue
            try:
                loaded.append((ce.load_scenario_json(path), path.name))
            except (OSError, ValueError, UnicodeDecodeError):
                bad.append(path.name)
    for scenario, name in sorted(loaded, key=lambda item: (item[0].id, item[1])):
        if scenario.id in seen:
            bad.append(name)
            continue
        seen.add(scenario.id)
        entries.append((scenario.id, f"{scenario.title} (생성)", scenario.model_dump_json()))
    return tuple(entries), tuple(sorted(bad))


@st.cache_resource(show_spinner=False, max_entries=2)
def cached_models(data_dir: str, model_files_key: str):
    """`load_models(data_dir)`. 키는 모델 파일들의 (이름, 수정 시각, 크기)라 `--fit` 뒤에 새로 읽는다. 읽기 전용으로만 쓴다."""
    del model_files_key
    return ce.load_models(data_dir)


@st.cache_data(ttl=LIVE_CACHE_TTL_S, show_spinner=False)
def cached_record_summary(store_path: str, targets_key: str) -> str:
    """`record_summary` 의 JSON. 수집 중에도 60초마다 새로 읽는다. 저장소가 없거나 열 수 없으면 빈 문자열."""
    path = Path(store_path)
    if not path.is_file():
        return ""
    targets = CollectTargets.model_validate_json(targets_key)
    try:
        with ce.RecordStore(path, read_only=True) as store:
            summary = ce.record_summary(store, targets)
    except (sqlite3.Error, OSError, ValueError):
        return ""
    return json.dumps(dataclasses.asdict(summary), ensure_ascii=False)


@st.cache_resource(show_spinner=False, max_entries=16)
def scenario_object(scenario_json: str) -> Scenario:
    """캐시 키로 쓰는 시나리오 JSON 을 객체로(같은 JSON 은 한 번만 읽는다). 객체는 고치지 않는다."""
    return Scenario.model_validate_json(scenario_json)


@st.cache_resource(show_spinner=False, max_entries=16)
def shifted_object(base_json: str, dt_s: int) -> Scenario:
    """시뮬레이션과 실시간의 늦춘 시나리오 `advance_clock(base, dt_s)` (`cached_run` 안의 계산과 같다)."""
    base = scenario_object(base_json)
    return ce.advance_clock(base, float(dt_s), EngineConfig()) if dt_s else base


@st.cache_resource(show_spinner=False, max_entries=16)
def output_object(output_json: str) -> EngineOutput:
    return EngineOutput.model_validate_json(output_json)


@st.cache_data(show_spinner="기록에서 시나리오를 만드는 중입니다", max_entries=128)
def cached_replay(scenario_json: str, at_unix_s: int, config_json: str, models_key: str) -> tuple[str, str]:
    """`replay_scenario` 결과 (시나리오 JSON, 원천 상태 JSON). 기록 저장소는 읽기 전용으로 열고 닫는다(§8.4)."""
    config = EngineConfig.model_validate_json(config_json)
    models = cached_models(config.data_dir, models_key)
    with ce.RecordStore(Path(config.data_dir) / STORE_FILE, read_only=True) as store:
        scenario, sources = ce.replay_scenario(scenario_object(scenario_json), store, models, float(at_unix_s), config)
    return scenario.model_dump_json(), _SOURCES_ADAPTER.dump_json(tuple(sources)).decode("utf-8")


@st.cache_data(ttl=LIVE_CACHE_TTL_S, show_spinner="실시간 값을 불러오는 중입니다")
def cached_live(scenario_json: str, config_json: str, models_key: str, refresh: int) -> tuple[str, str]:
    """`apply_live_overrides` 결과 (시나리오 JSON, 원천 상태 JSON). `refresh` 는 "지금 다시 조회"가 올리는 번호(§8.4)."""
    del refresh
    config = EngineConfig.model_validate_json(config_json)
    models = cached_models(config.data_dir, models_key)
    scenario, sources = ce.apply_live_overrides(scenario_object(scenario_json), config, models=models)
    _LIVE_FETCHES.append(time.time())
    return scenario.model_dump_json(), _SOURCES_ADAPTER.dump_json(tuple(sources)).decode("utf-8")


@st.cache_data(show_spinner=False, max_entries=64)
def cached_train_candidates(base_json: str, station_key: str, config_json: str) -> str:
    """`train_candidates(base, station_key, config)` 의 JSON(§4.10)."""
    config = EngineConfig.model_validate_json(config_json)
    choices = ce.train_candidates(scenario_object(base_json), station_key, config)
    return _TRAINS_ADAPTER.dump_json(choices).decode("utf-8")


def _bus_vehicle_rows(line, clock_s: float, config: EngineConfig) -> dict[str, list[list[Any]]]:
    trips = ce.build_bus_trips(line, clock_s, config)
    if not trips.usable:
        return {}
    prefix = f"{line.id}:"
    result: dict[str, list[list[Any]]] = {}
    for index in range(trips.n_stops):
        rows: list[list[Any]] = []
        for ordinal, (trip_id, t_s, _) in enumerate(ce.stop_vehicle_order(trips, index), start=1):
            row = trips.row_of(trip_id)
            vehicle = trip_id[len(prefix):] if trip_id.startswith(prefix) else trip_id
            text = "배차 간격으로 이은 차" if row is not None and row >= trips.n_known else f"차량 {vehicle}"
            if row is not None and trips.last[row]:
                text += " (막차)"
            rows.append([trip_id, ordinal, t_s, text])
        if rows:
            result[str(index)] = rows
    return result


@st.cache_data(show_spinner=False, max_entries=64)
def cached_bus_vehicles(base_json: str, line_id: str, config_json: str) -> str:
    """`build_bus_trips(그 노선, base.clock_s, config)` 의 차량 가운데 순번마다 시각이 0 이상인 차량을 시각 순으로 담은 JSON
    (순번 → [(차량 ID, 몇 번째, 시각, 차량 표시)]). 화면은 이 값으로 "지금 탄 버스"의 선택지를 만든다(§8.4)."""
    base = scenario_object(base_json)
    line = next((item for item in base.bus_lines if item.id == line_id), None)
    if line is None:
        return "{}"
    return json.dumps(_bus_vehicle_rows(line, base.clock_s, EngineConfig.model_validate_json(config_json)), ensure_ascii=False)


@st.cache_data(show_spinner=False, max_entries=64)
def cached_bus_line_ids(base_json: str, config_json: str) -> tuple[str, ...]:
    """"지금 탄 버스"에 쓸 수 있는 노선: 차량 시각을 만들 수 있고 시각이 0 이상인 차량이 있는 노선, ID 순(§6.4)."""
    base = scenario_object(base_json)
    config = EngineConfig.model_validate_json(config_json)
    return tuple(sorted(line.id for line in base.bus_lines if _bus_vehicle_rows(line, base.clock_s, config)))


@st.cache_data(show_spinner="경로를 계산하는 중입니다", max_entries=256)
def cached_run(base_json: str, shifted_json: str, dt_s: int, query_json: str, config_json: str,
               sources_json: str) -> tuple[str, str]:
    """늦춘 시나리오는 `shifted_json` 이 비면 `advance_clock(base, dt_s)`, 아니면 그 시나리오.
    q = `shift_origin(base, shifted, query, dt_s, config)`. q 가 None 이면 ("", ""),
    아니면 (`run_engine(shifted, q, config, sources)` 의 JSON, q 의 JSON)(§8.4)."""
    config = EngineConfig.model_validate_json(config_json)
    base = scenario_object(base_json)
    shifted = scenario_object(shifted_json) if shifted_json else shifted_object(base_json, dt_s)
    query = Query.model_validate_json(query_json)
    moved = ce.shift_origin(base, shifted, query, float(dt_s), config)
    if moved is None:
        return "", ""
    sources = _SOURCES_ADAPTER.validate_json(sources_json) if sources_json else ()
    output = ce.run_engine(shifted, moved, config, sources)
    return output.model_dump_json(), moved.model_dump_json()


def parse_sources(sources_json: str) -> tuple[ApiSourceStatus, ...]:
    return tuple(_SOURCES_ADAPTER.validate_json(sources_json)) if sources_json else ()


@dataclasses.dataclass(frozen=True)
class DataContext:
    """한 번의 실행에서 읽은 데이터 폴더의 상태(§8.4 의 1 ~ 2)."""

    folder: Path
    entries: tuple[tuple[str, str, str], ...]
    bad_files: tuple[str, ...]
    keys: Mapping[str, bool]
    targets: CollectTargets
    targets_found: bool
    summary: Mapping[str, Any] | None
    models: Any
    models_key: str

    @property
    def store_path(self) -> Path:
        return self.folder / STORE_FILE

    @property
    def has_records(self) -> bool:
        return self.summary is not None and sum(int(item["polls"]) for item in self.summary["sources"]) > 0

    @property
    def has_live_key(self) -> bool:
        """실시간 조회를 할 수 있는 키(열린데이터광장 또는 공공데이터포털). 카카오 키만으로는 받을 원천이 없다."""
        config = EngineConfig()
        return bool(self.keys.get(config.env_seoul_key) or self.keys.get(config.env_data_go_kr_key))

    @property
    def data_config(self) -> EngineConfig:
        """기록 재생, 실시간, 후보 계산에 쓰는 설정: 데이터 폴더와 휴일만 넣는다(화면 조건이 바뀌어도 다시 만들지 않으려고)."""
        return EngineConfig(data_dir=str(self.folder), holidays=tuple(self.targets.holidays))


def load_context() -> DataContext:
    folder = data_folder()
    scenario_paths = sorted((folder / "scenarios").glob("*.json")) if (folder / "scenarios").is_dir() else []
    entries, bad = cached_scenarios(str(folder), files_key(scenario_paths))
    targets, found = load_targets(folder)
    summary_json = cached_record_summary(str(folder / STORE_FILE), targets.model_dump_json())
    models_key = files_key(folder / name for name in MODEL_FILES)
    models = cached_models(str(folder), models_key)
    return DataContext(folder, entries, bad, key_presence(), targets, found,
                       json.loads(summary_json) if summary_json else None, models, models_key)


# --- 위젯 값 → 설정과 질의 ---


def weights_of(state: Mapping[str, Any]) -> tuple[float, float, float]:
    preset = state.get("weight_preset")
    if preset == WEIGHT_CUSTOM:
        return (round(float(state.get("w_time", 0.0)), 6), round(float(state.get("w_cost", 0.0)), 6),
                round(float(state.get("w_risk", 0.0)), 6))
    return tuple(WEIGHT_PRESETS.get(preset, next(iter(WEIGHT_PRESETS.values()))))


def walk_speed_of(state: Mapping[str, Any]) -> float:
    preset = state.get("walk_preset")
    if preset == WALK_CUSTOM:
        return round(float(state.get("v_walk", EngineConfig().v_walk_mps)), 6)
    return float(WALK_SPEED_PRESETS.get(preset, EngineConfig().v_walk_mps))


def build_run_config(state: Mapping[str, Any], ctx: DataContext) -> EngineConfig | str:
    """위젯 값으로 만든 엔진 설정. 바꾼 필드만 기본값과 다르다. 만들 수 없으면 이유 문장(§8.4 의 4).
    순위 기준이 종합 점수가 아니면 가중치는 결과에 쓰이지 않으므로 기본값으로 둔다(쓰이지 않는 값 때문에 다시 계산하지 않게)."""
    defaults = EngineConfig()
    criterion = RankCriterion(state.get("rank_criterion") or defaults.rank_criterion)
    weights = weights_of(state) if criterion == RankCriterion.UTILITY else (defaults.w_time, defaults.w_cost, defaults.w_risk)
    if sum(weights) <= 0:
        return "가중치가 모두 0이라 종합 점수를 계산할 수 없습니다. 하나 이상을 0보다 크게 두세요."
    modes = tuple(mode for mode, key in ((TravelMode.BUS, "use_bus"), (TravelMode.SUBWAY, "use_subway"),
                                         (TravelMode.BIKE, "use_bike")) if state.get(key))
    return EngineConfig(
        data_dir=str(ctx.folder),
        holidays=tuple(ctx.targets.holidays),
        rank_criterion=criterion,
        w_time=weights[0],
        w_cost=weights[1],
        w_risk=weights[2],
        v_walk_mps=walk_speed_of(state),
        modes_enabled=modes,
        max_rides=int(state.get("max_rides", defaults.max_rides)),
        climate_card=bool(state.get("climate_card")),
        bike_mileage=bool(state.get("bike_mileage")),
        gamma=round(float(state.get("gamma", defaults.gamma)), 6),
        safety_buffer_s=round(float(state.get("safety_buffer", defaults.safety_buffer_s)), 6),
        v_pm_mps=round(float(state.get("v_pm", defaults.v_pm_mps)), 6),
        max_bike_legs=int(state.get("max_bike_legs", defaults.max_bike_legs)),
        full_vehicle_policy=FullVehiclePolicy.SKIP if state.get("full_skip") else FullVehiclePolicy.IGNORE,
        k_pm=float(state.get("k_pm", defaults.k_pm)),
    )


def split_train_key(value: str) -> tuple[str, str, int] | None:
    """"{패턴 ID}|{열차 ID}|{순번}" → (패턴 ID, 열차 ID, 순번)."""
    try:
        pattern_id, rest = value.split("|", 1)
        trip_id, index = rest.rsplit("|", 1)
        return pattern_id, trip_id, int(index)
    except (AttributeError, ValueError):
        return None


def train_key_of(pattern_id: str, trip_id: str, index: int) -> str:
    return f"{pattern_id}|{trip_id}|{index}"


def build_query(state: Mapping[str, Any], scenario: Scenario, deadline_s: float | None) -> Query | str:
    """위젯 값으로 만든 질의. 엔진을 부를 수 없으면 안내 문장(§6.4)."""
    places = {place.name: place.node_id for place in scenario.places}
    kind = state.get("origin_kind")
    prior_m = round(float(state.get("prior_km") or 0.0) * 1000.0, 1)
    if kind == "POINT":
        point = state.get("origin_point")
        if point is None:
            return "지도를 눌러 출발을 정하세요."
        origin = OriginState(kind=OriginKind.AT_POINT, lat=float(point[0]), lon=float(point[1]))
    elif kind == "TRAIN":
        parts = split_train_key(state.get("train_key") or "")
        if parts is None:
            return "탄 열차를 고르세요."
        origin = OriginState(kind=OriginKind.ON_TRAIN, pattern_id=parts[0], trip_id=parts[1], next_index=parts[2],
                             prior_distance_m=prior_m)
    elif kind == "BUS":
        if state.get("bus_line") is None or state.get("bus_vehicle") is None or state.get("bus_stop_index") is None:
            return "탄 버스를 고르세요."
        origin = OriginState(kind=OriginKind.ON_BUS, line_id=state["bus_line"], trip_id=state["bus_vehicle"],
                             next_index=int(state["bus_stop_index"]), prior_distance_m=prior_m)
    else:
        node_id = places.get(state.get("origin_place"))
        if node_id is None:
            return "출발 장소를 고르세요."
        origin = OriginState(kind=OriginKind.AT_NODE, node_id=node_id)
    if state.get("dest_kind") == "POINT":
        point = state.get("dest_point")
        if point is None:
            return "지도를 눌러 목적지를 정하세요."
        destination = {"destination_lat": float(point[0]), "destination_lon": float(point[1])}
    else:
        node_id = places.get(state.get("dest_place"))
        if node_id is None:
            return "목적지 장소를 고르세요."
        if origin.kind == OriginKind.AT_NODE and origin.node_id == node_id:
            return "출발과 목적지가 같은 장소입니다. 다른 장소를 고르세요."
        destination = {"destination_node_id": node_id}
    return Query(origin=origin, deadline_s=deadline_s, **destination)


def query_defaults(scenario: Scenario) -> dict[str, Any]:
    """시나리오 기본 질의에서 정하는 출발·목적지 위젯의 기본값(§8.3). 열차·버스 선택은 후보를 구한 뒤 정한다."""
    query = scenario.default_query
    places = scenario.places
    place_of = {place.node_id: place.name for place in places}
    first = places[0].name if places else None
    second = places[1].name if len(places) > 1 else first
    origin = query.origin if query is not None else None
    dest_place = place_of.get(query.destination_node_id, second) if query is not None and query.destination_node_id else second
    # 기본 출발이 장소가 아니면(열차·버스·점) 출발을 "장소"로 돌렸을 때 목적지와 다른 첫 장소에서 출발한다
    origin_place = (place_of.get(origin.node_id, first) if origin is not None and origin.kind == OriginKind.AT_NODE
                    else next((place.name for place in places if place.name != dest_place), first))
    defaults: dict[str, Any] = {
        "origin_kind": ORIGIN_KIND_TO_CHOICE[origin.kind] if origin is not None else "PLACE",
        "origin_place": origin_place,
        "origin_point": (origin.lat, origin.lon) if origin is not None and origin.kind == OriginKind.AT_POINT else None,
        "prior_km": round(origin.prior_distance_m / 1000.0, 3) if origin is not None else 0.0,
        "dest_kind": "POINT" if query is not None and query.destination_node_id is None else "PLACE",
        "dest_place": dest_place,
        "dest_point": ((query.destination_lat, query.destination_lon)
                       if query is not None and query.destination_lat is not None else None),
        "map_pick": "ORIGIN",
        "last_map_click": None,
        "use_deadline": query is not None and query.deadline_s is not None,
        "selected_id": None,
        "last_default_id": None,
    }
    return defaults


def default_deadline_time(c0_s: float, query: Query | None) -> datetime.time:
    """마감 시각 기본값: 기본 질의에 마감이 있으면 그 시각, 없으면 기준 시각 + 30분의 분 단위 내림(§6.3)."""
    if query is not None and query.deadline_s is not None:
        value = _half(c0_s + query.deadline_s) % SECONDS_PER_DAY
    else:
        value = (math.floor(c0_s + 1800.0) // 60 * 60) % SECONDS_PER_DAY
    return datetime.time(value // 3600, value % 3600 // 60, value % 60)


def clock_seconds(value: datetime.time) -> int:
    return value.hour * 3600 + value.minute * 60 + value.second


def replay_unix(day: datetime.date, clock: datetime.time) -> int:
    return int(datetime.datetime.combine(day, clock.replace(tzinfo=None), tzinfo=KST).timestamp())


def window_options(summary: Mapping[str, Any]) -> tuple[list[str], dict[str, str], dict[str, tuple[datetime.date, datetime.time]]]:
    """기록 구간 선택지(최근 것부터), 표시 문구, 고르면 둘 (날짜, 시각)(§6.3)."""
    periods = [float(item["period_s"]) for item in summary["sources"]]
    period = max(periods) if periods else 0.0
    windows = sorted(summary["windows"], key=lambda item: (item["first_unix"], item["date"], item["window"]), reverse=True)
    values: list[str] = []
    labels: dict[str, str] = {}
    info: dict[str, tuple[datetime.date, datetime.time]] = {}
    for item in windows:
        value = f"{item['date']}|{item['window']}"
        if value in labels:
            continue
        first = datetime.datetime.fromtimestamp(item["first_unix"], KST)
        last = datetime.datetime.fromtimestamp(item["last_unix"], KST)
        labels[value] = (f"{fmt_date(item['date'])} {item['window']} {first:%H:%M} ~ {last:%H:%M} · "
                         f"조회 {int(item['polls']):,}회")
        start = math.ceil((item["first_unix"] + 2.0 * period) / 60.0) * 60
        moment = datetime.datetime.fromtimestamp(start, KST)
        info[value] = (datetime.date.fromisoformat(item["date"]), moment.time().replace(second=0, microsecond=0))
        values.append(value)
    return values, labels, info


def replay_gap(sources: Sequence[ApiSourceStatus]) -> bool:
    """재생 시각 앞뒤에 기록이 없음: 수집하는 원천(버스 도착, 따릉이, 신호)이 모두 건너뜀이고 `REPLAY_DATA_GAP` 이 있다(§6.4)."""
    collected = [item for item in sources if item.source in _COLLECTED_SOURCES]
    if not collected or any(item.state != SourceState.SKIPPED for item in collected):
        return False
    return any(issue.code == WarningCode.REPLAY_DATA_GAP for item in collected for issue in item.issues)


def source_state(sources: Sequence[ApiSourceStatus], kind: SourceKind) -> SourceState | None:
    states = [item.state for item in sources if item.source == kind]
    if not states:
        return None
    if SourceState.FAILED in states:
        return SourceState.FAILED
    if SourceState.SKIPPED in states and SourceState.SUCCESS not in states:
        return SourceState.SKIPPED
    return SourceState.SUCCESS


def served_stations(scenario: Scenario) -> list[tuple[str, str]]:
    """정차 패턴이 지나는 역 (역 키, 표시 "{역 이름} ({호선들})"), 역 키 순(§6.3)."""
    names = {station.key: station.name for station in scenario.subway_stations}
    lines: dict[str, list[str]] = {}
    for pattern in scenario.subway_patterns:
        for key in pattern.station_keys:
            served = lines.setdefault(key, [])
            if pattern.line not in served:
                served.append(pattern.line)
    return [(key, f"{names.get(key, key)} ({', '.join(lines[key])})") for key in sorted(lines)]


def train_label(choice: TrainChoice) -> str:
    text = f"{choice.clock_label} 도착 · {choice.line} {choice.direction} · {choice.destination}행 · {choice.train_no}"
    return f"급행 · {text}" if choice.express else text


def train_number(scenario: Scenario, pattern_id: str, trip_id: str) -> str:
    for pattern in scenario.subway_patterns:
        if pattern.id == pattern_id:
            for trip in pattern.trips:
                if trip.id == trip_id:
                    return trip.train_no
    return trip_id


def vehicle_text(trip_id: str, line_id: str) -> str:
    """버스 차량 ID 의 표시(§6.5): 합성 차량은 "배차 간격으로 이은 차", 그 밖은 "차량 {차량 ID}"."""
    prefix = f"{line_id}:"
    vehicle = trip_id[len(prefix):] if trip_id.startswith(prefix) else trip_id
    return "배차 간격으로 이은 차" if vehicle.startswith("+") else f"차량 {vehicle}"


def nearest_ground(scenario: Scenario, lat: float, lon: float, role: str, config: EngineConfig) -> tuple[str, float] | None:
    """찍은 점에서 가장 가까운 지상 노드와 거리. 엔진의 공개 함수 `snap_point` 를 거리 한도 없이 불러 붙일 노드를 얻는다."""
    unlimited = config.model_copy(update={"snap_max_m": 1e12})
    try:
        snapped = ce.snap_point(scenario, lat, lon, role, unlimited)
    except ValueError:
        return None
    if snapped is None:
        return None
    joined, distance = snapped
    edge = joined.edges[-1]
    node_id = edge.target if role == ce.ORIGIN_POINT_ID else edge.source
    return node_id, distance


# --- 카카오 도보 경로 비교 (§8.4, 9단계) ---
# 카카오 응답과 거기서 나온 값은 `st.session_state["kakao_results"]` 에만 둔다. 캐시 함수의 인자나 반환값, 파일, 엔진 결과에
# 넣지 않는다(§5.4).

_STATION_EDGE_KINDS = (EdgeKind.STATION_PASSAGE, EdgeKind.STAIRS)
_SNAP_EDGES = {"origin": "__snap_origin__", "destination": "__snap_destination__"}
KAKAO_STATE_ORDER = ("RATE_LIMITED", "FAILED", "NO_KEY", "OK")  # 전체 상태는 단위 상태 가운데 이 순서로 먼저 나오는 것


@dataclasses.dataclass(frozen=True)
class KakaoUnit:
    """비교 단위 하나(§8.4 의 1 ~ 3): 역 안 엣지를 잘라 낸 경로의 노드와 엣지, 시작·끝 좌표, 화면 이름."""

    name: str
    node_ids: tuple[str, ...]
    edge_ids: tuple[str, ...]
    start: tuple[float, float]
    end: tuple[float, float]


def _trim_station_edges(path, kinds: Mapping[str, EdgeKind]) -> tuple[tuple[str, ...], tuple[str, ...]] | None:
    """경로의 맨 앞과 맨 뒤에 이어지는 역 안 엣지(STATION_PASSAGE, STAIRS)를 잘라 낸다. 남는 엣지가 없으면 None."""
    edges, nodes = list(path.edge_ids), list(path.node_ids)
    if not edges or len(nodes) != len(edges) + 1:
        return None
    first, last = 0, len(edges)
    while first < last and kinds.get(edges[first]) in _STATION_EDGE_KINDS:
        first += 1
    while last > first and kinds.get(edges[last - 1]) in _STATION_EDGE_KINDS:
        last -= 1
    if first >= last:
        return None
    return tuple(nodes[first:last + 1]), tuple(edges[first:last])


def _point_coords(scenario: Scenario, query: Query | None) -> dict[str, tuple[float, float]]:
    """노드와 대여소의 좌표. 지도에서 찍은 점(POINT)은 질의의 좌표다(§8.4 의 3)."""
    coords = {node.id: (node.lat, node.lon) for node in (*scenario.nodes, *scenario.bike_stations)}
    if query is not None:
        if query.origin.kind == OriginKind.AT_POINT and query.origin.lat is not None and query.origin.lon is not None:
            coords[ce.ORIGIN_POINT_ID] = (query.origin.lat, query.origin.lon)
        if query.destination_lat is not None and query.destination_lon is not None:
            coords[ce.DESTINATION_POINT_ID] = (query.destination_lat, query.destination_lon)
    return coords


def kakao_units(itinerary: ItineraryResult, scenario: Scenario, query: Query | None) -> tuple[KakaoUnit, ...]:
    """고른 여정의 비교 단위(§8.4 의 1 ~ 3): 따릉이 없는 이동의 걷기 경로 하나, 따릉이 이동의 ① 과 ⑤. 역 안 엣지를 잘라 내고
    남는 엣지가 없는 단위는 뺀다. 이름은 "이동 {k}: {시작} → {끝}" (따릉이는 "이동 {k} ①: …", "이동 {k} ⑤: …")."""
    names = node_names(scenario)
    kinds = {edge.id: edge.kind for edge in scenario.edges}
    coords = _point_coords(scenario, query)
    units: list[KakaoUnit] = []
    for move in itinerary.moves:
        number = move.index + 1
        if move.bike is not None:
            parts = ((move.bike.walk_in, f"이동 {number} ①"), (move.bike.walk_out, f"이동 {number} ⑤"))
        elif move.walk is not None:
            parts = ((move.walk, f"이동 {number}"),)
        else:
            parts = ()
        for path, prefix in parts:
            trimmed = _trim_station_edges(path, kinds)
            if trimmed is None:
                continue
            node_ids, edge_ids = trimmed
            start, end = coords.get(node_ids[0]), coords.get(node_ids[-1])
            if start is None or end is None:
                continue
            name = f"{prefix}: {names.get(node_ids[0], node_ids[0])} → {names.get(node_ids[-1], node_ids[-1])}"
            units.append(KakaoUnit(name, node_ids, edge_ids, start, end))
    return tuple(units)


def kakao_our_distance(unit: KakaoUnit, scenario: Scenario, graph: Any, config: EngineConfig) -> float:
    """우리 최단거리 L(§8.4 의 4): 남은 경로 양 끝의 붙이기(SNAP) 엣지 길이와, 그 둘을 뺀 첫 노드에서 마지막 노드까지의
    최단거리 경로 길이의 합."""
    nodes, edges = list(unit.node_ids), list(unit.edge_ids)
    snapped = 0.0
    if edges and edges[0] == _SNAP_EDGES["origin"]:
        snap = ce.snap_point(scenario, unit.start[0], unit.start[1], ce.ORIGIN_POINT_ID, config)
        snapped += snap[1] if snap is not None else 0.0
        nodes, edges = nodes[1:], edges[1:]
    if edges and edges[-1] == _SNAP_EDGES["destination"]:
        snap = ce.snap_point(scenario, unit.end[0], unit.end[1], ce.DESTINATION_POINT_ID, config)
        snapped += snap[1] if snap is not None else 0.0
        nodes, edges = nodes[:-1], edges[:-1]
    if not nodes or nodes[0] == nodes[-1]:
        return snapped
    hops = ce.shortest_distance_path(graph, nodes[0], nodes[-1], Mode.WALK)
    if hops is None:  # 단위 경로가 그래프 안에 있으므로 일어나지 않지만, 그때는 단위 경로의 길이를 쓴다
        return snapped + sum(graph.lengths.get(edge_id, 0.0) for edge_id in edges)
    return snapped + sum(hop.length_m for hop in hops)


def _kakao_row(unit: KakaoUnit, ours_m: float, result: Any | None) -> dict[str, Any]:
    if result is None:  # 앞 단위가 RATE_LIMITED 라 부르지 않은 단위
        return {"name": unit.name, "ours_m": ours_m, "state": "RATE_LIMITED", "basic": None, "shortest": None, "ratio": None,
                "warn": False, "coords": ()}
    basic, shortest = result.basic, result.shortest
    return {
        "name": unit.name,
        "ours_m": ours_m,
        "state": result.state,
        "basic": None if basic is None else (float(basic.distance_m), float(basic.time_s)),
        "shortest": None if shortest is None else (float(shortest.distance_m), float(shortest.time_s)),
        "ratio": result.shortest_diff_ratio,
        "warn": bool(result.warn),
        "coords": () if shortest is None else tuple((float(lat), float(lon)) for lat, lon in shortest.coords),
    }


def _on_kakao_compare(scenario_id: str, itinerary: ItineraryResult, scenario: Scenario, query: Query | None,
                      config: EngineConfig) -> None:
    """"카카오 도보 경로와 비교" 버튼의 콜백(§8.4): 단위마다 `ce.kakao_walk_compare` 를 차례로 부르고, RATE_LIMITED 가 나오면
    남은 단위는 부르지 않는다. 결과는 `kakao_results[(시나리오 키, 여정 ID)]` 에, 보낸 요청 수는 `kakao_calls` 에 더한다."""
    state = st.session_state
    units = kakao_units(itinerary, scenario, query)
    if not units:
        return
    graph = ce.build_graph(scenario, frozenset(node.id for node in (*scenario.nodes, *scenario.bike_stations)), config)
    rows: list[dict[str, Any]] = []
    calls = 0
    limited = False
    for unit in units:
        ours = kakao_our_distance(unit, scenario, graph, config)
        if limited:
            rows.append(_kakao_row(unit, ours, None))
            continue
        result = ce.kakao_walk_compare(unit.start, unit.end, ours, config)
        calls += int(result.calls)
        limited = result.state == "RATE_LIMITED"
        rows.append(_kakao_row(unit, ours, result))
    overall = next(name for name in KAKAO_STATE_ORDER if any(row["state"] == name for row in rows))
    results = dict(state.get("kakao_results") or {})
    results[(scenario_id, itinerary.itinerary_id)] = {"state": overall, "units": rows}
    state["kakao_results"] = results
    state["kakao_calls"] = int(state.get("kakao_calls", 0) or 0) + calls


# ===== U4. 사이드바 =====


@dataclasses.dataclass
class Prepared:
    """사이드바가 정한 이번 실행의 입력(§8.4 의 3 ~ 6). 본문은 이 값과 엔진 결과만 그린다."""

    ctx: DataContext
    scenario_id: str
    scenario_json: str
    scenario: Scenario
    selected_mode: str
    mode: str
    fallback: str | None
    base_json: str
    base: Scenario
    base_sources: tuple[ApiSourceStatus, ...]
    shifted_json: str
    sources_json: str
    sources: tuple[ApiSourceStatus, ...]
    dt_s: int
    display: Scenario  # 엔진에 넘기는(늦춘) 시나리오
    block: str | None = None
    config: EngineConfig | None = None
    query: Query | None = None
    pick: tuple[str, tuple[float, float, str] | None, tuple[float, float, str] | None] | None = None
    replay_at: int | None = None  # 기록 재생의 기준 시각(유닉스 초), 출발 여유 계산이 늦춘 재생을 다시 만든다(19단계)


def _clip_to_range(value: float, name: str) -> float:
    """`PARAM_RANGES` 의 범위 안으로 자르고 간격에 맞춰 반올림한다(§6.3 의 "학습한 따릉이 속도 적용")."""
    low, high, step = PARAM_RANGES[name]
    clipped = min(max(float(value), low), high)
    snapped = low + round((clipped - low) / step) * step
    return round(min(max(snapped, low), high), 6)


def _required_guard(state: MutableMapping[str, Any], key: str, options: Sequence[str], default: str) -> None:
    """`required=True` 구간 선택의 값이 None 이거나 선택지에 없으면 기본값으로 둔다(§8.3)."""
    if state.get(key) not in options:
        value = default if default in options else options[0]
        store_value(state, key, value)


def sidebar_scenario(ctx: DataContext) -> tuple[str, str]:
    state = st.session_state
    ids = [entry[0] for entry in ctx.entries]
    labels = {entry[0]: entry[1] for entry in ctx.entries}
    jsons = {entry[0]: entry[2] for entry in ctx.entries}
    if state.get("scenario_id") not in ids:
        drop_keys(state, QUERY_KEYS)
        state["scenario_id"] = ids[0]
    st.selectbox("시나리오", ids, key="scenario_id", format_func=labels.get, on_change=_on_scenario_change)
    if ctx.bad_files:
        st.caption(f"읽지 못한 시나리오 파일 {len(ctx.bad_files)}개: {', '.join(ctx.bad_files)}")
    scenario_id = state["scenario_id"]
    return scenario_id, jsons[scenario_id]


def sidebar_mode(ctx: DataContext) -> tuple[str, str, str | None]:
    state = st.session_state
    options = [mode.value for mode in DataMode]
    _required_guard(state, "data_mode", options, SESSION_DEFAULTS["data_mode"])
    st.segmented_control(
        "데이터 모드", options, key="data_mode", required=True, format_func=MODE_NAMES.get, on_change=_on_mode_change,
        help="버스 도착 예측, 신호, 자전거 수를 어디서 가져올지 고릅니다. 지하철은 어느 모드든 시각표대로 다닌다고 봅니다.",
    )
    replay_note = "쓸 수 있음" if ctx.has_records else "기록 저장소가 없거나 비었음"
    live_note = "쓸 수 있음" if ctx.has_live_key else "키 없음"
    st.caption(f"기록 재생: {replay_note} · 실시간: {live_note}")
    selected = state["data_mode"]
    mode, fallback = effective_mode(selected, ctx.has_records, ctx.has_live_key)
    return selected, mode, fallback


def sidebar_replay(ctx: DataContext) -> int:
    """기록 구간, 재생 날짜, 재생 시각(§6.3). 재생 시각의 유닉스 초를 돌려준다."""
    state = st.session_state
    summary = ctx.summary or {}
    values, labels, info = window_options(summary)
    dates = [datetime.date.fromisoformat(item[0]) for item in summary.get("dates", [])]
    low, high = (min(dates), max(dates)) if dates else (None, None)
    if values:
        restore(state, "replay_window", values[0])
        if state.get("replay_window") not in values:
            store_value(state, "replay_window", values[0])
        st.selectbox("기록 구간", values, key="replay_window", format_func=labels.get, on_change=_on_window_change,
                     kwargs={"info": info})
        sync_keep(state, "replay_window")
        default_day, default_clock = info[state["replay_window"]]
    else:
        last = max((float(item["last_unix"]) for item in summary.get("sources", [])), default=time.time())
        moment = datetime.datetime.fromtimestamp(last, KST)
        default_day, default_clock = moment.date(), moment.time().replace(second=0, microsecond=0)
    restore(state, "replay_date", default_day)
    if low is not None and not low <= state["replay_date"] <= high:
        store_value(state, "replay_date", min(max(state["replay_date"], low), high))
    st.date_input("재생 날짜", key="replay_date", min_value=low, max_value=high, format="YYYY-MM-DD",
                  on_change=remember, args=("replay_date",))
    sync_keep(state, "replay_date")
    restore(state, "replay_time", default_clock)
    st.time_input("재생 시각", key="replay_time", step=60, on_change=remember, args=("replay_time",))
    sync_keep(state, "replay_time")
    return replay_unix(state["replay_date"], state["replay_time"])


def sidebar_live() -> None:
    state = st.session_state
    fetched = state.get("live_fetched_at")
    wait = fetched is not None and time.time() - float(fetched) < LIVE_MIN_REFRESH_S
    st.button("지금 다시 조회", key="live_refresh_button", on_click=_on_live_refresh, disabled=wait,
              help=f"마지막 조회 뒤 {LIVE_MIN_REFRESH_S}초가 지나야 다시 부를 수 있습니다.")
    if fetched is not None:
        st.caption(f"마지막 조회 {_kst_clock(float(fetched))} · 같은 조건은 {LIVE_CACHE_TTL_S}초 동안 다시 부르지 않습니다")


def _place_names(scenario: Scenario) -> list[str]:
    return [place.name for place in scenario.places]


def _point_lines(scenario: Scenario, point: tuple[float, float] | None, role: str, config: EngineConfig,
                 gps: Mapping[str, float] | None = None) -> list[str]:
    """"지도에서" 아래의 줄. 지금 위치로 정한 점이면 첫 줄이 위치와 정확도다(§6.8)."""
    if point is None:
        return ["아직 찍지 않았습니다"]
    lines = [gps_point_line(gps) if gps is not None else f"찍은 점 {point[0]:.5f}, {point[1]:.5f}"]
    nearest = nearest_ground(scenario, float(point[0]), float(point[1]), role, config)
    if nearest is not None:
        names = node_names(scenario)
        lines.append(f"가장 가까운 {names.get(nearest[0], nearest[0])}까지 {fmt_dist(nearest[1])}")
    return lines


def _default_origin(scenario: Scenario) -> OriginState | None:
    return scenario.default_query.origin if scenario.default_query is not None else None


def sidebar_train(p: Prepared) -> str | None:
    """"지금 탄 열차": 다음에 설 역과 탄 열차(§6.3). 후보가 없으면 엔진을 부르지 않을 이유를 돌려준다."""
    state = st.session_state
    dconf = p.ctx.data_config
    stations = served_stations(p.base)
    keys = [key for key, _ in stations]
    labels = dict(stations)
    origin = _default_origin(p.scenario)
    default_station = keys[0]
    if origin is not None and origin.kind == OriginKind.ON_TRAIN:
        pattern = next((item for item in p.scenario.subway_patterns if item.id == origin.pattern_id), None)
        if pattern is not None and pattern.station_keys[origin.next_index] in keys:
            default_station = pattern.station_keys[origin.next_index]
    restore(state, "train_station", default_station)
    if state.get("train_station") not in keys:
        store_value(state, "train_station", default_station)
    st.selectbox("다음에 설 역", keys, key="train_station", format_func=labels.get, on_change=_on_train_station_change)
    sync_keep(state, "train_station")
    choices = _TRAINS_ADAPTER.validate_json(cached_train_candidates(p.base_json, state["train_station"], dconf.model_dump_json()))
    values = [train_key_of(choice.pattern_id, choice.trip_id, choice.index) for choice in choices]
    if not values:
        state["train_key"] = None
        st.selectbox("탄 열차", [], key="train_key", disabled=True)
        reason = f"기준 시각부터 {_half(dconf.train_lookahead_s / 60.0)}분 안에 이 역에 닿는 열차가 없습니다."
        st.caption(reason)
        return reason
    texts = {value: train_label(choice) for value, choice in zip(values, choices)}
    default_key = values[0]
    if origin is not None and origin.kind == OriginKind.ON_TRAIN:
        candidate = train_key_of(origin.pattern_id, origin.trip_id, origin.next_index)
        if candidate in values:
            default_key = candidate
    restore(state, "train_key", default_key)
    notice = None
    if state.get("train_key") not in values:
        old = split_train_key(state.get("train_key") or "")
        store_value(state, "train_key", values[0])
        if old is not None:
            notice = f"고른 열차({train_number(p.base, old[0], old[1])})가 지금 후보에 없어 첫 열차로 바꿨습니다."
    st.selectbox("탄 열차", values, key="train_key", format_func=texts.get, on_change=remember, args=("train_key",))
    sync_keep(state, "train_key")
    if notice:
        st.info(notice)
    return None


def sidebar_bus(p: Prepared, line_ids: Sequence[str]) -> str | None:
    """"지금 탄 버스": 노선, 다음에 설 정류장, 탄 버스(§6.3)."""
    state = st.session_state
    dconf = p.ctx.data_config
    lines = {line.id: line for line in p.base.bus_lines}
    names = node_names(p.base)
    origin = _default_origin(p.scenario)
    on_bus = origin is not None and origin.kind == OriginKind.ON_BUS
    default_line = origin.line_id if on_bus and origin.line_id in line_ids else line_ids[0]
    restore(state, "bus_line", default_line)
    if state.get("bus_line") not in line_ids:
        store_value(state, "bus_line", default_line)
    st.selectbox("노선", list(line_ids), key="bus_line", on_change=_on_bus_line_change,
                 format_func=lambda line_id: f"{lines[line_id].name} ({ROUTE_TYPE_NAMES[lines[line_id].route_type]})")
    sync_keep(state, "bus_line")
    line = lines[state["bus_line"]]
    indices = list(range(len(line.stop_ids)))
    default_index = origin.next_index if on_bus and origin.line_id == line.id and origin.next_index in indices else 0
    restore(state, "bus_stop_index", default_index)
    if state.get("bus_stop_index") not in indices:
        store_value(state, "bus_stop_index", default_index)
    st.selectbox("다음에 설 정류장", indices, key="bus_stop_index", on_change=_on_bus_stop_change,
                 format_func=lambda j: f"{j + 1}. {names.get(line.stop_ids[j], line.stop_ids[j])}")
    sync_keep(state, "bus_stop_index")
    index = int(state["bus_stop_index"])
    rows = json.loads(cached_bus_vehicles(p.base_json, line.id, dconf.model_dump_json())).get(str(index), [])
    if not rows:
        state["bus_vehicle"] = None
        st.selectbox("탄 버스", [], key="bus_vehicle", disabled=True)
        reason = "이 정류장에 닿는 차가 없습니다. 다른 정류장을 고르세요."
        st.caption(reason)
        return reason
    values = [row[0] for row in rows]
    texts = {row[0]: f"{row[1]}번째 차 · {fmt_clock(p.base.clock_s, row[2])} 도착 · {row[3]}" for row in rows}
    default_vehicle = values[0]
    if on_bus and origin.line_id == line.id and origin.next_index == index and origin.trip_id in values:
        default_vehicle = origin.trip_id
    restore(state, "bus_vehicle", default_vehicle)
    notice = None
    if state.get("bus_vehicle") not in values:
        old = state.get("bus_vehicle")
        store_value(state, "bus_vehicle", values[0])
        if old:
            notice = f"고른 버스({vehicle_text(old, line.id)})가 지금 후보에 없어 첫 차로 바꿨습니다."
    st.selectbox("탄 버스", values, key="bus_vehicle", format_func=texts.get, on_change=remember, args=("bus_vehicle",))
    sync_keep(state, "bus_vehicle")
    if notice:
        st.info(notice)
    return None


EXAMPLES_LABEL = "예시 경로"


def trip_examples(scenario: Scenario) -> None:
    """예시 경로 버튼(§6.3). 시나리오에 `examples` 가 있을 때만 출발 묶음 바로 위에 그린다."""
    if not scenario.examples:
        return
    name_of = {place.node_id: place.name for place in scenario.places}
    st.caption(EXAMPLES_LABEL)
    for number, example in enumerate(scenario.examples, start=1):
        st.button(example.name, key=f"example_{number}", help=example.note, width="stretch", on_click=_on_example,
                  args=(name_of[example.origin_node_id], name_of[example.destination_node_id]))


def sidebar_origin(p: Prepared, defaults: Mapping[str, Any], with_gps: bool = True) -> str | None:
    """출발(§6.3). 엔진을 부르지 않을 이유가 있으면 그 문장을 돌려준다. `with_gps` 가 거짓이면 위치 단추와 지금 위치의
    개인정보 문장·정확도 경고를 그리지 않는다(간단히 보기는 이것들을 상자의 접힘 위에 그린다, §6.9)."""
    state = st.session_state
    dconf = p.ctx.data_config
    line_ids = cached_bus_line_ids(p.base_json, dconf.model_dump_json())
    timetable_skipped = p.mode != DataMode.SIMULATION.value and \
        source_state(p.base_sources, SourceKind.SUBWAY_TIMETABLE) == SourceState.SKIPPED
    options = ["PLACE", "POINT"]
    if p.base.subway_patterns and not timetable_skipped:
        options.append("TRAIN")
    if line_ids:
        options.append("BUS")
    _required_guard(state, "origin_kind", options, defaults["origin_kind"])
    st.segmented_control(ORIGIN_KIND_LABEL, options, key="origin_kind", required=True, format_func=ORIGIN_CHOICE_NAMES.get,
                         on_change=_on_origin_kind_change)
    if with_gps:
        sidebar_gps()
    kind = state["origin_kind"]
    block = None
    if kind == "PLACE":
        names = _place_names(p.base)
        restore(state, "origin_place", defaults["origin_place"])
        if state.get("origin_place") not in names:
            store_value(state, "origin_place", defaults["origin_place"] if defaults["origin_place"] in names else names[0])
        st.selectbox("출발 장소", names, key="origin_place", on_change=remember, args=("origin_place",))
        sync_keep(state, "origin_place")
    elif kind == "POINT":
        st.caption("지도를 누르면 그 점을 출발로 씁니다.")
        fix = gps_origin(state)
        for line in _point_lines(p.display, state.get("origin_point"), ce.ORIGIN_POINT_ID, dconf, fix):
            st.caption(line)
        if with_gps:
            gps_feedback(fix)
    elif kind == "TRAIN":
        block = sidebar_train(p)
    else:
        block = sidebar_bus(p, line_ids)
    if kind in ("TRAIN", "BUS"):
        low, high, step = PARAM_RANGES["prior_distance_km"]
        restore(state, "prior_km", defaults["prior_km"])
        state["prior_km"] = min(max(float(state["prior_km"] or 0.0), low), high)
        st.number_input("이미 탄 거리(km)", min_value=low, max_value=high, step=step, format="%.1f", key="prior_km",
                        on_change=remember, args=("prior_km",), help="요금의 거리비례 추가요금 계산에 씁니다.")
        sync_keep(state, "prior_km")
    return block


def gps_button() -> Callable[..., Any]:
    """위치 단추 컴포넌트(§8.5). 모듈을 불러올 때 등록하면 실행 맥락 밖에서 경고가 남으므로 그릴 때 등록한다."""
    return st.components.v2.component(GPS_COMPONENT_NAME, html=GPS_HTML, css=GPS_CSS, js=GPS_JS)


def sidebar_gps() -> None:
    """출발 구간 선택 아래의 위치 단추와 위치 결과의 안내, "바꿔 출발" 단추(§6.8)."""
    state = st.session_state
    data = {"label": GPS_BUTTON_LABEL, "busy_label": GPS_BUSY_LABEL, "title": GPS_PRIVACY_NOTE,
            "timeout_ms": GPS_TIMEOUT_MS, "max_age_ms": GPS_MAX_AGE_MS}
    gps_button()(key=GPS_COMPONENT_KEY, data=data, on_fix_change=_on_gps_fix)
    note = state.get("gps_note")
    if not isinstance(note, Mapping):
        return
    if note.get("kind") == "OTHER":
        st.info(note["text"])
        for scenario_id, label in note.get("choices", ()):
            st.button(GPS_SWITCH_LABEL.format(label=label), key=f"gps_switch_{scenario_id}", on_click=_on_gps_switch,
                      args=(scenario_id,), width="stretch")
    else:
        st.warning(note["text"])


def gps_feedback(fix: Mapping[str, float] | None) -> None:
    """지금 위치로 정한 출발이면 개인정보 문장과, 정확도 반경이 크면 경고(§6.8). 간단히 보기에서는 상자의 위치 단추 아래(§6.9)."""
    if fix is None:
        return
    st.caption(GPS_PRIVACY_NOTE)
    if fix["accuracy_m"] > GPS_ACCURACY_WARN_M:
        st.warning(gps_accuracy_text(fix["accuracy_m"]))


def sidebar_destination(p: Prepared, defaults: Mapping[str, Any]) -> None:
    state = st.session_state
    options = list(DEST_CHOICE_NAMES)
    _required_guard(state, "dest_kind", options, defaults["dest_kind"])
    st.segmented_control("목적지", options, key="dest_kind", required=True, format_func=DEST_CHOICE_NAMES.get)
    if state["dest_kind"] == "PLACE":
        names = _place_names(p.base)
        restore(state, "dest_place", defaults["dest_place"])
        if state.get("dest_place") not in names:
            store_value(state, "dest_place", defaults["dest_place"] if defaults["dest_place"] in names else names[-1])
        st.selectbox("목적지 장소", names, key="dest_place", on_change=remember, args=("dest_place",))
        sync_keep(state, "dest_place")
    else:
        st.caption("지도를 누르면 그 점을 목적지로 씁니다.")
        for line in _point_lines(p.display, state.get("dest_point"), ce.DESTINATION_POINT_ID, p.ctx.data_config):
            st.caption(line)
    if state.get("origin_kind") == "POINT" and state["dest_kind"] == "POINT":
        restore(state, "map_pick", "ORIGIN")
        _required_guard(state, "map_pick", list(MAP_PICK_NAMES), "ORIGIN")
        st.segmented_control("지도를 누르면", list(MAP_PICK_NAMES), key="map_pick", required=True,
                             format_func=MAP_PICK_NAMES.get, on_change=remember, args=("map_pick",))
        sync_keep(state, "map_pick")


_DEPART_HELP = {
    DataMode.SIMULATION.value: "지금 값을 그만큼 옮겨 계산합니다. 신호 위상, 버스 예측, 열차 시각이 함께 움직입니다.",
    DataMode.REPLAY.value: "재생 시각을 그만큼 뒤로 옮겨 기록에서 다시 만듭니다.",
    DataMode.LIVE.value: "지금 받은 예측을 그만큼 옮긴 계산입니다.",
}


def depart_label(clock_s: float, dt_s: int) -> str:
    """출발 늦추기 막대의 글자(§6.3, 26단계): 0 이면 "지금", 아니면 "{나설 시각} ({분}분 뒤)". 초 단위 글자("300초")를 쓰지 않는다."""
    return DEPART_NOW_LABEL if dt_s == 0 else f"{fmt_hm(clock_s, dt_s, 'floor')} ({dt_s // 60}분 뒤)"


def sidebar_depart(p: Prepared) -> None:
    state = st.session_state
    help_text = _DEPART_HELP[p.mode]
    if state.get("origin_kind") in ("TRAIN", "BUS"):
        help_text += " 같은 역(정류장)에 그만큼 늦게 닿는 차를 탄 것으로 바꿔 계산합니다."
    step = int(PARAM_RANGES["depart_offset_s"][2])
    options = list(range(0, int(p.ctx.data_config.depart_offset_max_s) + 1, step))
    clock = p.base.clock_s
    st.select_slider("출발 늦추기", options, key="depart_offset_s", format_func=lambda d: depart_label(clock, d), help=help_text)
    dt = int(state["depart_offset_s"])
    st.caption("지금 출발" if dt == 0 else f"{dt // 60}분 뒤 출발 ({fmt_clock(p.base.clock_s, dt)})")


def sidebar_deadline(p: Prepared, label: str = "도착 마감 시각") -> float | None:
    """도착 마감(§6.3). 엔진에 넘길 $t$ (없으면 None)를 돌려준다. `label` 은 켜기 단추의 글(간단히 보기는 `DEADLINE_EASY_LABEL`)."""
    state = st.session_state
    st.toggle(label, key="use_deadline")
    if not state.get("use_deadline"):
        return None
    restore(state, "deadline_time", default_deadline_time(p.base.clock_s, p.scenario.default_query))
    if state.get("deadline_time") is None:
        store_value(state, "deadline_time", default_deadline_time(p.base.clock_s, p.scenario.default_query))
    st.time_input("마감 시각", key="deadline_time", step=1, on_change=remember, args=("deadline_time",))
    sync_keep(state, "deadline_time")
    t_s = deadline_t(clock_seconds(state["deadline_time"]), p.display.clock_s)
    if t_s is None:
        st.caption("마감 시각이 이미 지났습니다")
    return t_s


def weight_text(weights: tuple[float, float, float]) -> str:
    total = sum(weights)
    if total <= 0:
        return "가중치가 모두 0이라 종합 점수를 계산할 수 없습니다. 하나 이상을 0보다 크게 두세요."
    parts = (f"{name} {_fixed(100.0 * value / total, 0)}%" for name, value in zip(("시간", "요금", "위험"), weights))
    return " · ".join(parts)


def sidebar_rank(deadline_s: float | None) -> None:
    state = st.session_state
    defaults = setting_defaults()
    options = [criterion.value for criterion in RankCriterion]
    if state.get("rank_criterion") not in options:
        state["rank_criterion"] = defaults["rank_criterion"]
    st.selectbox("순위 기준", options, key="rank_criterion", format_func=RANK_CHOICE_NAMES.get, help=RANK_HELP)
    if state["rank_criterion"] == RankCriterion.ON_TIME.value and deadline_s is None:
        st.caption(f"마감 시각을 켜면 그 기준으로 정렬합니다. 지금은 {RANK_NAMES[RankCriterion.MEAN_ARRIVAL]} 순입니다.")
    if state["rank_criterion"] != RankCriterion.UTILITY.value:
        return
    presets = [*WEIGHT_PRESETS, WEIGHT_CUSTOM]
    restore(state, "weight_preset", defaults["weight_preset"])
    _required_guard(state, "weight_preset", presets, defaults["weight_preset"])
    st.segmented_control("가중치", presets, key="weight_preset", required=True, on_change=remember, args=("weight_preset",))
    sync_keep(state, "weight_preset")
    if state["weight_preset"] == WEIGHT_CUSTOM:
        for key, label in (("w_time", "시간"), ("w_cost", "요금"), ("w_risk", "위험")):
            low, high, step = PARAM_RANGES[key]
            restore(state, key, defaults[key])
            st.slider(label, low, high, step=step, key=key, on_change=remember, args=(key,))
            sync_keep(state, key)
    st.caption(weight_text(weights_of(state)))


def sidebar_walk(label: str = "걷는 속도") -> None:
    """걷는 속도(§6.3). 간단히 보기는 답 카드 바로 아래에 `WALK_EASY_LABEL` 로 그린다(§6.9, 22단계). 키와 동작은 같다."""
    state = st.session_state
    defaults = setting_defaults()
    presets = [*WALK_SPEED_PRESETS, WALK_CUSTOM]
    _required_guard(state, "walk_preset", presets, defaults["walk_preset"])
    st.segmented_control(label, presets, key="walk_preset", required=True)
    if state["walk_preset"] == WALK_CUSTOM:
        low, high, step = PARAM_RANGES["v_walk_mps"]
        restore(state, "v_walk", defaults["v_walk"])
        st.slider("걷는 속도(m/s)", low, high, step=step, key="v_walk", on_change=remember, args=("v_walk",))
        sync_keep(state, "v_walk")
    if label == WALK_EASY_LABEL:  # 간단히 보기(28단계): 확률·백분율 없이
        st.caption(WALK_EASY_CAPTION.format(v=fmt_speed(walk_speed_of(state))))
        return
    k_move = EngineConfig().k_move
    st.caption(f"보통 사람의 걷는 속도 {fmt_speed(walk_speed_of(state))} 기준으로 계획하고, 사람마다 속도가 "
               f"±{k_move * 100:g}% 정도 다르다고 보고 확률을 계산합니다.")


def sidebar_mode_toggles(label: str | None = None) -> None:
    """수단 켜기(§6.3). 간단히 보기는 내 걸음 빠르기 아래에 `MODES_EASY_LABEL` 을 달아 그린다(§6.9, 24단계). 키와 동작은 같다."""
    state = st.session_state
    with st.container(gap="small"):  # 이름표와 토글 사이를 위젯 이름표 간격으로
        if label is not None:
            st.html(f'<p class="mr-ctl-label">{esc(label)}</p>')
        with st.container(horizontal=True, gap="medium"):
            st.toggle("버스", key="use_bus")
            st.toggle("지하철", key="use_subway")
            st.toggle("따릉이", key="use_bike")
    if not (state.get("use_bus") or state.get("use_subway") or state.get("use_bike")):
        st.caption(WALK_ONLY_TEXT)


def sidebar_modes(toggles: bool = True) -> None:
    if toggles:  # 간단히 보기는 본문에 그린다(§6.9, 24단계)
        sidebar_mode_toggles()
    low, high, step = PARAM_RANGES["max_rides"]
    st.slider("최대 탑승 수", low, high, step=step, key="max_rides", help="지금 탄 차량도 셉니다.")


def sidebar_fare() -> None:
    notes = ce.fare_notes(EngineConfig())
    for key, label in (("climate_card", "기후동행카드 단기권 보유"), ("bike_mileage", "따릉이 환승 마일리지 적용")):
        help_text = " ".join(note for note in notes if f"'{label}'" in note) or None
        st.toggle(label, key=key, help=help_text)


def sidebar_details() -> None:
    with st.expander("세부 조건"):
        low, high, step = PARAM_RANGES["gamma"]
        st.slider("탐색 타원 계수", low, high, step=step, key="gamma", format="%.2f",
                  help="출발과 목적지를 두 초점으로 하는 타원 안의 길만 탐색합니다. 키우면 더 돌아가는 길까지 봅니다.")
        low, high, step = PARAM_RANGES["safety_buffer_s"]
        st.slider("승차 여유(초)", low, high, step=step, key="safety_buffer", format="%.0f",
                  help="차가 정류장을 떠나기 이만큼 전에 닿아야 탈 수 있다고 봅니다.")
        low, high, step = PARAM_RANGES["v_pm_mps"]
        st.slider("따릉이 속도(m/s)", low, high, step=step, key="v_pm", format="%.1f",
                  help="따릉이를 평소처럼 탈 때의 주행 속도입니다.")
        low, high, step = PARAM_RANGES["max_bike_legs"]
        st.slider("따릉이 최대 대여 횟수", low, high, step=step, key="max_bike_legs",
                  help="한 여정에서 따릉이를 빌리는 최대 횟수입니다. 0이면 따릉이를 쓰지 않습니다.")
        st.toggle("만차 표시 차량은 타지 않기", key="full_skip", help="만차 표시의 뜻이 확인되기 전에는 끄세요")


def store_line(summary: Mapping[str, Any] | None, store_path: Path, now: float) -> str:
    """"원천과 학습 모델"의 기록 저장소 한 줄(§6.3)."""
    if summary is None:
        return "기록 저장소 없음"
    size = f"{_fixed(int(summary['size_bytes']) / 1_000_000.0, 1)} MB"
    dates = [item[0] for item in summary.get("dates", [])]
    sources = summary.get("sources", [])
    if not dates or not sources:
        return f"기록 저장소 {size} · 조회 기록 없음"
    period = max(float(item["period_s"]) for item in sources)
    last = max(float(item["last_unix"]) for item in sources)
    status = "수집 중" if now - last <= 2.0 * period else "멈춤"
    return f"기록 저장소 {size} · {fmt_date(dates[0])} ~ {fmt_date(dates[-1])} · {status}"


def timetable_line(scenario: Scenario, folder: Path) -> str:
    codes = sorted({station.line_key(line) for station in scenario.subway_stations for line, _ in station.platforms})
    if not codes:
        return "시각표: 이 시나리오에는 지하철역이 없습니다"
    found = sum(1 for code in codes if (folder / "timetables" / f"{code}.csv").is_file())
    return f"시각표: 시나리오 역 {len(codes)}개 가운데 {found}개"


def sidebar_sources(ctx: DataContext, scenario: Scenario) -> None:
    config = EngineConfig()
    with st.expander("원천과 학습 모델"):
        present = ("감지됨", "없음")
        keys = " · ".join(
            f"{name} {present[0] if ctx.keys.get(env) else present[1]}"
            for name, env in (("열린데이터광장", config.env_seoul_key), ("공공데이터포털", config.env_data_go_kr_key),
                              ("카카오", config.env_kakao_key), ("서울 신호", config.env_tdata_key))
        )
        st.caption(f"키: {keys}")
        st.caption(store_line(ctx.summary, ctx.store_path, time.time()))
        st.caption(timetable_line(scenario, ctx.folder))
        models = ctx.models
        signal = "있음" if models is not None and models.signal is not None else "없음"
        bike = "있음" if models is not None and models.bike is not None else "없음"
        st.caption(f"모델: 신호 {signal} · 따릉이 {bike}")
        st.caption("자세한 내용은 본문의 ⑦ 데이터·기록 탭에 있습니다.")
        speed = models.bike.speed if models is not None and models.bike is not None else None
        kwargs = None
        if speed is not None:
            kwargs = {"v_pm": _clip_to_range(speed.median_mps, "v_pm_mps"), "k_pm": float(speed.k)}
        st.button("학습한 따릉이 속도 적용", key="apply_bike_speed", disabled=speed is None, on_click=_on_apply_bike_speed,
                  kwargs=kwargs or {"v_pm": config.v_pm_mps, "k_pm": config.k_pm},
                  help="따릉이 대여 이력에서 배운 주행 속도 중앙값과 개인차를 세부 조건에 넣습니다.")


def init_session(ctx: DataContext) -> None:
    """세션 상태의 기본값(§8.3). 위젯 기본값은 상태에 먼저 넣고 위젯에는 key 만 준다."""
    state = st.session_state
    for key, value in SESSION_DEFAULTS.items():
        if key not in state:
            state[key] = dict(value) if isinstance(value, dict) else value
    if "scenario_id" not in state:
        state["scenario_id"] = ctx.entries[0][0]
        if state.get("view_mode") != "DETAIL":  # 간단히 보기 첫 화면은 첫 시나리오의 첫 예시 경로로 연다(§6.3 30단계)
            first_example(state, scenario_object(ctx.entries[0][2]))
    for key, value in setting_defaults().items():
        if key in KEEP_KEYS:
            continue
        if key not in state:
            state[key] = value


def init_query_state(defaults: Mapping[str, Any]) -> None:
    """위젯이 아닌 질의 키와 늘 그리는 위젯의 기본값. 조건부 위젯은 그리기 직전에 `restore` 로 정한다."""
    state = st.session_state
    for key in ("origin_point", "dest_point", "last_map_click", "selected_id", "last_default_id", "use_deadline"):
        if key not in state and keep_key(key) not in state:
            state[key] = defaults[key]


def scenario_story(scenario: Scenario, state: Mapping[str, Any], *, simple: bool) -> str:
    """사이드바의 시나리오 설명(32단계). 시나리오 설명은 기본 질의(지금 탄 열차 등)의 이야기라, 간단히 보기에서는 지금 출발·목적지가
    예시 경로와 같으면 그 예시의 설명을, 아니면 아무것도 보이지 않는다(본문 경로와 맞지 않는 설명을 보이지 않게). 자세히 보기는 그대로."""
    if not simple:
        return scenario.description
    if state.get("origin_kind") != "PLACE" or state.get("dest_kind") != "PLACE":
        return ""
    name_of = {place.node_id: place.name for place in scenario.places}
    for example in scenario.examples:
        if (name_of.get(example.origin_node_id), name_of.get(example.destination_node_id)) == (
                state.get("origin_place"), state.get("dest_place")):
            return f"{example.name}. {example.note}"
    return ""


def render_sidebar(ctx: DataContext, trip: Any = None) -> Prepared:
    """사이드바를 위에서 아래로 그리며 이번 실행의 시나리오, 모드, 질의, 설정을 정한다(§6.3, §8.4 의 1 ~ 6)."""
    state = st.session_state
    with st.sidebar:
        scenario_id, scenario_json = sidebar_scenario(ctx)
        scenario = scenario_object(scenario_json)
        story = scenario_story(scenario, state, simple=trip is not None)
        if story:
            st.caption(story)
        note_slot = st.empty()
        selected, mode, fallback = sidebar_mode(ctx)
        if mode == DataMode.SIMULATION.value:
            note_slot.caption(scenario.simulated_time_note)
        dconf_json = ctx.data_config.model_dump_json()
        dt_s = int(state.get("depart_offset_s") or 0)
        guide = state.get("guide") if trip is not None else None  # 안내 중이면 지난 시간으로 시계를 옮긴다(§6.10)
        if not (isinstance(guide, Mapping) and guide.get("scenario_id") == scenario_id and guide.get("mode") == mode):
            guide = None
        if mode != DataMode.REPLAY.value:
            dt_s = guide_clock(guide, mode, None, dt_s)[1]
        base_json, shifted_json, sources_json, base_sources_json = scenario_json, "", "", ""
        if mode == DataMode.REPLAY.value:
            at = sidebar_replay(ctx)
            at, dt_s = guide_clock(guide, mode, at, dt_s)
            base_json, base_sources_json = cached_replay(scenario_json, at, dconf_json, ctx.models_key)
            if dt_s:
                shifted_json, sources_json = cached_replay(scenario_json, at + dt_s, dconf_json, ctx.models_key)
            else:
                shifted_json, sources_json = base_json, base_sources_json
            if replay_gap(parse_sources(base_sources_json)):
                st.warning("이 시각 앞뒤에 기록이 없습니다. 기록 구간에서 고르세요.")
        elif mode == DataMode.LIVE.value:
            base_json, sources_json = cached_live(scenario_json, dconf_json, ctx.models_key, int(state.get("live_refresh", 0)))
            base_sources_json = sources_json
            if _LIVE_FETCHES:
                state["live_fetched_at"] = _LIVE_FETCHES[-1]
            sidebar_live()
        elif selected == DataMode.REPLAY.value:
            st.caption("기록이 없습니다")
        if guide is not None and mode == DataMode.SIMULATION.value:
            base_json = guide_sim_base(scenario_json, guide)
        base = scenario_object(base_json)
        display = scenario_object(shifted_json) if shifted_json else shifted_object(base_json, dt_s)
        p = Prepared(ctx, scenario_id, scenario_json, scenario, selected, mode, fallback, base_json, base,
                     parse_sources(base_sources_json), shifted_json, sources_json, parse_sources(sources_json), dt_s, display)
        if mode == DataMode.REPLAY.value:
            p.replay_at = at
        defaults = query_defaults(scenario)
        init_query_state(defaults)
        if guide is not None:
            guide_follow_vehicle(state, p.base, ctx.data_config)
        process_gps(state, ctx, scenario_id)
        st.divider()
        if trip is None:
            trip_examples(p.base)
            block = sidebar_origin(p, defaults)
            sidebar_destination(p, defaults)
        else:
            st.caption(TRIP_SIDEBAR_NOTE)
            with trip:
                sidebar_gps()
                feedback = st.empty()  # 개인정보 문장과 정확도 경고의 자리: 출발 종류는 접힘 안의 가드를 거친 값으로 본다
                with st.expander(TRIP_EDIT_LABEL, key="trip_edit", on_change="rerun"):
                    trip_examples(p.base)
                    block = sidebar_origin(p, defaults, with_gps=False)
                    sidebar_destination(p, defaults)
                fix = gps_origin(state) if state.get("origin_kind") == "POINT" else None
                if fix is not None:
                    with feedback.container():
                        gps_feedback(fix)
        st.divider()
        sidebar_depart(p)
        if trip is None:
            deadline_s = sidebar_deadline(p)
        else:  # 간단히 보기는 도착해야 하는 시각을 출발·도착 상자에 둔다(§6.9, 19단계). 키와 동작은 같다
            with trip:
                deadline_s = sidebar_deadline(p, DEADLINE_EASY_LABEL)
        st.divider()
        # 간단히 보기는 분석용 조절을 접힘 안에 둔다(§6.9, 17단계). 접혀도 위젯은 그려지므로 값과 키는 같다.
        with st.expander(SIDE_MORE_LABEL, key="side_more", on_change="rerun") if trip is not None else contextlib.nullcontext():
            sidebar_rank(deadline_s)
            if trip is None:  # 간단히 보기는 답 카드 아래에 그린다(§6.9, 22단계)
                sidebar_walk()
                st.divider()
            sidebar_modes(toggles=trip is None)
            sidebar_fare()
            sidebar_details()
            sidebar_sources(ctx, scenario)
            st.button("기본값으로 되돌리기", key="reset_button", on_click=_on_reset, width="stretch")
    config = build_run_config(state, ctx)
    if isinstance(config, str):
        block = block or config
        config = None
    else:
        p.config = config
    if block is None:
        query = build_query(state, base, deadline_s)
        if isinstance(query, str):
            block = query
        else:
            p.query = query
    p.block = block
    p.pick = map_pick_of(state, base)
    return p


def map_pick_of(state: Mapping[str, Any], scenario: Scenario):
    """지도 누르기를 기다리면 (대상, 출발 표지, 목적지 표지), 아니면 None(§8.1 의 `build_map` 인자)."""
    origin_point = state.get("origin_kind") == "POINT"
    dest_point = state.get("dest_kind") == "POINT"
    if not origin_point and not dest_point:
        return None
    if origin_point and dest_point:
        target = state.get("map_pick") or "ORIGIN"
    else:
        target = "ORIGIN" if origin_point else "DESTINATION"
    nodes = {node.id: node for node in scenario.nodes}
    places = {place.name: place.node_id for place in scenario.places}

    def marker(kind: str, point_key: str, place_key: str, name: str):
        if state.get(kind) == "POINT":
            point = state.get(point_key)
            return None if point is None else (float(point[0]), float(point[1]), name)
        if state.get(kind) == "PLACE":
            node = nodes.get(places.get(state.get(place_key), ""))
            return None if node is None else (node.lat, node.lon, state.get(place_key))
        return None

    origin_name = GPS_ORIGIN_NAME if gps_origin(state) is not None else POINT_NAMES[ce.ORIGIN_POINT_ID]
    return (target, marker("origin_kind", "origin_point", "origin_place", origin_name),
            marker("dest_kind", "dest_point", "dest_place", POINT_NAMES[ce.DESTINATION_POINT_ID]))


# ===== U5. 머리말, 비교 패널, KPI, 바닥글 =====

FOOTER_TEXT = "데이터: 서울 열린데이터광장, 공공데이터포털, © OpenStreetMap 기여자(ODbL)"
MAP_NOTE = "지도 타일 © OpenStreetMap 기여자 · 지도 표시는 인터넷 연결이 필요합니다"
MAP_SIMPLE_NOTE = "지도의 번호는 단계의 번호입니다. "  # 32단계, 33단계: 표지 옆에 노선 이름을 붙여 짧게
KAKAO_NOTE = " · 경로 비교: 카카오"
KPI_DELTA_NOTE = "기존 1위 대비"  # KPI 변화량 설명(§6.3). 1440 px 화면의 타일 폭에서 잘리지 않는 길이


def _earliest_observed(sources: Sequence[ApiSourceStatus]) -> str | None:
    """버스 도착, 따릉이, 신호 가운데 성공한 원천의 가장 이른 관측 시각(지하철 시각표 파일의 시각은 쓰지 않는다, §6.3)."""
    moments = []
    for item in sources:
        if item.source in _COLLECTED_SOURCES and item.state == SourceState.SUCCESS and item.observed_at:
            try:
                moments.append(datetime.datetime.fromisoformat(item.observed_at))
            except ValueError:
                continue
    if not moments:
        return None
    return min(moments).astimezone(KST).strftime("%H:%M:%S")


def mode_chip(p: Prepared) -> tuple[str, str | None]:
    """머리말의 모드와 시각 배지 (문구, 도움말)(§6.3)."""
    help_text = None
    if p.mode == DataMode.REPLAY.value:
        text = p.base.record_note or MODE_NAMES[p.mode]
    elif p.mode == DataMode.LIVE.value:
        observed = _earliest_observed(p.sources)
        text = f"실시간 · {observed} 조회" if observed else "실시간"
    else:
        text = "시뮬레이션 값" + (f" ({p.fallback})" if p.fallback else "")
        help_text = p.scenario.simulated_time_note
    if p.dt_s:
        text += f" · {p.dt_s // 60}분 뒤 출발"
        if p.mode == DataMode.LIVE.value:
            text += " (받은 값을 옮김)"
    return text, help_text


def header_chips(p: Prepared, output: EngineOutput | None) -> list[str]:
    text, help_text = mode_chip(p)
    chips = [chip_html(text, title=help_text)]
    if p.mode != DataMode.SIMULATION.value:
        states = {item.state for item in p.sources}
        if SourceState.FAILED in states:
            chips.append(chip_html("원천 일부 실패", warn=True))
        elif SourceState.SKIPPED in states:
            chips.append(chip_html("원천 일부 건너뜀", warn=True))
    if output is None:
        return chips
    codes = {warning.code for warning in output.warnings}
    if WarningCode.STALE_PREDICTION in codes:
        lines = {line.id: line for line in p.display.bus_lines}
        ages = [lines[ref].prediction_age_s for warning in output.warnings if warning.code == WarningCode.STALE_PREDICTION
                for ref in warning.ref_ids if ref in lines and lines[ref].prediction_age_s is not None]
        if ages:
            chips.append(chip_html(f"버스 예측 {_half(max(ages)) // 60}분 전 값", warn=True))
    if WarningCode.DAYTYPE_NOT_LEARNED in codes:
        chips.append(chip_html(f"{DAY_TYPE_NAMES[output.day_type]}: 학습값 없음", warn=True))
    return chips


def _distance_segments(output: EngineOutput, scenario: Scenario) -> list[str]:
    stations = {station.key: station.name for station in scenario.subway_stations}
    for station in scenario.subway_stations:
        for _, code in station.line_keys:
            stations.setdefault(code, station.name)
    rows = []
    for warning in output.warnings:
        if warning.code != WarningCode.UNVERIFIED_DISTANCE:
            continue
        if len(warning.ref_ids) == 3:
            pattern_id, a, b = warning.ref_ids
            rows.append(f"{stations.get(a, a)} → {stations.get(b, b)} ({pattern_id})")
        else:
            rows.append(warning.message)
    return rows


def _origin_display(p: Prepared, state: Mapping[str, Any], output: EngineOutput | None, moved: Query | None,
                    simple: bool = False) -> str:
    """출발 표시(§6.3). `simple` 이면(간단히 보기의 출발·도착 상자, 19단계) 열차 번호를 빼고 다음 역(정류장) 도착을 분으로 적는다."""
    kind = state.get("origin_kind")
    query = moved or p.query
    scenario = p.display if moved is not None else p.base
    names = node_names(scenario)
    if kind == "PLACE":
        return str(state.get("origin_place"))
    if kind == "POINT":
        point = state.get("origin_point")
        if point is None:
            return "지도에서(아직 찍지 않았습니다)"
        nearest = nearest_ground(p.display, float(point[0]), float(point[1]), ce.ORIGIN_POINT_ID, p.ctx.data_config)
        label = GPS_ORIGIN_NAME if gps_origin(state) is not None else "지도에서 찍은 점"
        if nearest is None:
            return label
        near_names = easy_names(scenario) if simple else names  # 20단계: 간단히 보기는 정류장 이름
        return f"{label}(가장 가까운 {near_names.get(nearest[0], nearest[0])}까지 {fmt_dist(nearest[1])})"
    origin = query.origin if query is not None else None
    if kind == "TRAIN" and origin is not None and origin.kind == OriginKind.ON_TRAIN:
        pattern = next((item for item in scenario.subway_patterns if item.id == origin.pattern_id), None)
        trip = next((item for item in pattern.trips if item.id == origin.trip_id), None) if pattern else None
        if pattern is not None and trip is not None:
            stations = {station.key: station.name for station in scenario.subway_stations}
            key = pattern.station_keys[origin.next_index]
            if simple:
                return (f"{pattern.line} {pattern.direction} 열차 안 · 다음 역 {stations.get(key, key)} "
                        f"{fmt_hm(scenario.clock_s, trip.arr_s[origin.next_index])} 도착")
            return (f"{pattern.line} {pattern.direction} {trip.train_no} 열차 안, 다음 역 {stations.get(key, key)} "
                    f"{fmt_clock(scenario.clock_s, trip.arr_s[origin.next_index])}")
    if kind == "BUS" and origin is not None and origin.kind == OriginKind.ON_BUS:
        line = next((item for item in scenario.bus_lines if item.id == origin.line_id), None)
        if line is not None:
            config = output.config if output is not None else p.ctx.data_config
            trips = ce.build_bus_trips(line, scenario.clock_s, config)
            row = trips.row_of(origin.trip_id)
            stop = line.stop_ids[origin.next_index]
            if row is not None:
                arrival = trips.times(row)[origin.next_index]
                if simple:
                    when = "-" if arrival is None else f"{fmt_hm(scenario.clock_s, arrival)} 도착"
                    return f"{line.name}번 버스 안 · 다음 정류장 {names.get(stop, stop)} {when}"
                return (f"{line.name}번 버스 안, 다음 정류장 {names.get(stop, stop)} "
                        f"{_clock_or_dash(scenario.clock_s, arrival)}")
    return ORIGIN_CHOICE_NAMES.get(kind, "-")


def _dest_display(p: Prepared, state: Mapping[str, Any], simple: bool = False) -> str:
    if state.get("dest_kind") == "PLACE":
        return str(state.get("dest_place"))
    point = state.get("dest_point")
    if point is None:
        return "지도에서(아직 찍지 않았습니다)"
    nearest = nearest_ground(p.display, float(point[0]), float(point[1]), ce.DESTINATION_POINT_ID, p.ctx.data_config)
    if nearest is None:
        return "지도에서 찍은 점"
    names = easy_names(p.display) if simple else node_names(p.display)  # 20단계
    return f"지도에서 찍은 점(가장 가까운 {names.get(nearest[0], nearest[0])}까지 {fmt_dist(nearest[1])})"


def description_line(p: Prepared, state: Mapping[str, Any], output: EngineOutput | None, moved: Query | None) -> str:
    """한 줄 설명(§6.3): "출발: {출발 표시} · 기준 시각 {HH:MM:SS} · 목적지: {목적지 표시}". 기준 시각은 늦춘 $c_0$ 다."""
    c0 = output.clock_s if output is not None else p.display.clock_s
    return (f"출발: {_origin_display(p, state, output, moved)} · 기준 시각 {fmt_clock(c0, 0.0)} · "
            f"목적지: {_dest_display(p, state)}")


def fallback_message(p: Prepared) -> str | None:
    if p.fallback is None:
        return None
    if p.selected_mode == DataMode.REPLAY.value:
        return f"기록 재생을 할 수 없습니다: {p.ctx.store_path}에 기록이 없습니다. 시뮬레이션 값으로 보여 줍니다."
    return "실시간 조회를 할 수 없습니다: 키가 없습니다. 시뮬레이션 값으로 보여 줍니다."


def render_header(p: Prepared, output: EngineOutput | None, moved: Query | None, simple: bool = False) -> None:
    state = st.session_state
    st.title(APP_TITLE)
    st.caption(APP_SUBTITLE)
    popovers: list[tuple[str, str | None, list[str]]] = []
    if output is not None and output.unverified_node_ids:
        names = node_names(p.display)
        popovers.append((f"미검증 좌표 {len(output.unverified_node_ids)}개", "좌표 근거를 확인하지 않은 노드와 대여소입니다.",
                         [f"{names.get(node_id, node_id)} ({node_id})" for node_id in output.unverified_node_ids]))
    if output is not None:
        segments = _distance_segments(output, p.display)
        if segments:
            popovers.append((f"역간 거리 미확인 {len(segments)}구간", "요금의 탑승 거리에만 쓰입니다(시각에는 쓰지 않습니다).",
                             segments))
    if simple:
        popovers = []
    with st.container(horizontal=True, vertical_alignment="center", gap="small"):
        if simple:  # 34단계: 소개 페이지로 돌아가기
            st.button(INTRO_BACK, key="to_intro", type="tertiary", icon=":material/arrow_back:", on_click=_go_intro)
        render_view_switch()
        st.html(f'<div class="mr-chips">{"".join(header_chips(p, output))}</div>', width="content")
        for label, help_text, rows in popovers:
            with st.popover(label, help=help_text):
                st.markdown("\n".join(f"- {md_escape(row)}" for row in rows))
    if not simple:
        st.html(f'<div class="mr-desc">{esc(description_line(p, state, output, moved))}</div>')
    message = fallback_message(p)
    if message:
        st.warning(message)


def snap_distance(p: Prepared, output: EngineOutput) -> float | None:
    """붙이지 못한 찍은 점에서 가장 가까운 지상 노드까지의 거리(§6.4 의 SNAP_FAILED 카드)."""
    if output.status != EngineStatus.SNAP_FAILED:
        return None
    query = output.query
    points = []
    if query.origin.kind == OriginKind.AT_POINT:
        points.append((ce.ORIGIN_POINT_ID, query.origin.lat, query.origin.lon))
    if query.destination_lat is not None:
        points.append((ce.DESTINATION_POINT_ID, query.destination_lat, query.destination_lon))
    for role, lat, lon in points:
        nearest = nearest_ground(p.display, float(lat), float(lon), role, output.config)
        if nearest is not None and nearest[1] > output.config.snap_max_m:
            return nearest[1]
    return None


def render_kpi(output: EngineOutput, config: EngineConfig) -> None:
    columns = st.columns(4)
    for index, (column, tile) in enumerate(zip(columns, kpi_tiles(output, config))):
        comparison = tile.delta is not None and index != 2
        with column:
            st.metric(tile.label, tile.value, tile.delta, delta_color=tile.delta_color, help=tile.help, border=True,
                      height="stretch", delta_arrow=tile.delta_arrow,
                      delta_description=KPI_DELTA_NOTE if comparison else None)


def render_warnings(output: EngineOutput) -> None:
    if not output.warnings:
        return
    with st.expander(f"엔진 경고 {len(output.warnings)}건"):
        items = "".join(f"<li><code>{esc(warning.code.value)}</code> {esc(warning.message)}</li>" for warning in output.warnings)
        st.html(f'<ul class="mr-warnlist">{items}</ul>')


def render_footer() -> None:
    calls = int(st.session_state.get("kakao_calls", 0) or 0)
    st.divider()
    st.caption(FOOTER_TEXT + (KAKAO_NOTE if calls > 0 else ""))


# ===== U6. 지도, 경로 목록, 시간 막대, 여정 안내 =====

_PANES = (("mr-ellipse", 380), ("mr-naive", 410), ("mr-route", 420), ("mr-kakao", 430))
_LINE_STYLE = {
    "bus": ("bus", 6, None),
    "subway": ("subway", 7, None),
    "bike": ("bike", 5, None),
    "walk": ("ink2", 4, "1 9"),
}


def _poly(group, locations: Sequence[tuple[float, float]], color: str, weight: float, *, pane: str,
          dash: str | None = None, tooltip: str | None = None, double: bool = False) -> None:
    """색 선 아래에 흰 테두리 선(두께 + 4, 불투명도 0.9)을 먼저 그린다(§7.6). 지하철은 위에 흰 선을 겹친 이중선."""
    points = [(float(lat), float(lon)) for lat, lon in locations]
    if len(points) < 2:
        return
    folium.PolyLine(points, color="#ffffff", weight=weight + 4, opacity=0.9, pane=pane, interactive=False).add_to(group)
    folium.PolyLine(points, color=color, weight=weight, opacity=1.0, dash_array=dash, pane=pane,
                    tooltip=folium.Tooltip(tooltip) if tooltip else None).add_to(group)
    if double:
        folium.PolyLine(points, color="#ffffff", weight=2, opacity=1.0, pane=pane, interactive=False).add_to(group)


def _icon(html_body: str, size: tuple[int, int], anchor: tuple[int, int]) -> folium.DivIcon:
    return folium.DivIcon(html=html_body, icon_size=size, icon_anchor=anchor, class_name="mr-map-icon")


def _circle_html(size: int, fill: str, border: str, *, text: str = "", text_color: str = "#ffffff", border_width: float = 2,
                 dashed: bool = False, font: int = 11, radius: str = "50%") -> str:
    style = (f"width:{size}px;height:{size}px;box-sizing:border-box;border-radius:{radius};background:{fill};"
             f"border:{border_width}px {'dashed' if dashed else 'solid'} {border};color:{text_color};font:700 {font}px/1 sans-serif;"
             "display:flex;align-items:center;justify-content:center;font-variant-numeric:tabular-nums;")
    return f'<div style="{style}">{esc(text)}</div>'


def _pill_html(text: str, *, fill: str, border: str, color: str, size: int = 11, weight: int = 600, below: bool = False) -> str:
    """알약 표지. 기본은 기준점을 아래 가운데로 두어 점 위에 뜬다(아이콘 크기 0 에서 자기 크기만큼 위로 옮긴다).
    below 면 점 아래 10 px 에 매단다(같은 점의 출발·도착 표지나 승차 라벨과 겹치지 않게)."""
    shift = "translate(-50%,10px)" if below else "translate(-50%,-100%)"
    style = (f"position:absolute;transform:{shift};white-space:nowrap;background:{fill};color:{color};"
             f"border:2px solid {border};border-radius:999px;padding:1px 8px;font:{weight} {size}px/1.5 sans-serif;"
             "box-shadow:0 1px 2px rgba(0,0,0,0.25);")
    return f'<div style="{style}">{esc(text)}</div>'


def _marker(group, location: tuple[float, float], icon: folium.DivIcon, tooltip: str | None = None, z: int = 0) -> None:
    kwargs: dict[str, Any] = {"z_index_offset": z} if z else {}
    folium.Marker((float(location[0]), float(location[1])), icon=icon, tooltip=folium.Tooltip(tooltip) if tooltip else None,
                  **kwargs).add_to(group)


def _ride_points(ride, scenario: Scenario, origin: OriginState | None, coords: Callable[[str], tuple[float, float] | None]):
    """탑승의 승차부터 하차까지 정류장·승강장 좌표열. 차량 안 출발의 첫 탑승은 다음에 설 정류장(역)부터."""
    if ride.mode == TravelMode.BUS:
        line = next((item for item in scenario.bus_lines if item.id == ride.route_id), None)
        stops = line.stop_ids if line is not None else ()
    else:
        pattern = next((item for item in scenario.subway_patterns if item.id == ride.route_id), None)
        stops = pattern.platform_ids if pattern is not None else ()
    start = ride.board_index
    if start is None:
        start = origin.next_index if origin is not None and origin.next_index is not None else ride.alight_index
    points = [coords(stop) for stop in stops[start:ride.alight_index + 1]]
    return [point for point in points if point is not None]


def _ride_tooltip(ride, names: Mapping[str, str]) -> str:
    board = names.get(ride.board_node_id or "", "지금 탄 차량") if ride.board_node_id else "지금 탄 차량"
    alight = names.get(ride.alight_node_id, ride.alight_node_id)
    text = f"{ride_name(ride)} · {board} → {alight}"
    if ride.plan_dep_s is not None and ride.plan_arr_s is not None:
        text += f" · {fmt_dur(ride.plan_arr_s - ride.plan_dep_s)}"
    return esc(text)


def _spot(location: tuple[float, float]) -> tuple[float, float]:
    """같은 점인지 견주는 열쇠(약 0.1 m 단위)."""
    return (round(float(location[0]), 6), round(float(location[1]), 6))


def _draw_itinerary(group, it: ItineraryResult, scenario: Scenario, origin: OriginState | None, coords, names, tokens,
                    *, naive: bool, labels: bool, ends_at: frozenset = frozenset()) -> list[str]:
    """여정의 이동 좌표열과 탑승 정류장 좌표열을 그린다. 그린 승하차 정류장 ID 를 돌려준다.
    승하차 라벨은 하차를 점 아래, 승차를 점 위에 둔다. 승차 점에 출발·도착 표지(점 위)가 있으면(`ends_at`) 승차도 아래에 둔다."""
    pane = "mr-naive" if naive else "mr-route"
    muted = tokens["muted"]

    def style(kind: str) -> tuple[str, float, str | None]:
        if naive:
            return muted, 4, "8 8"
        token, weight, dash = _LINE_STYLE[kind]
        return tokens[token], weight, dash

    def walk(path, title: str) -> None:
        if path is None:
            return
        color, weight, dash = style("walk")
        _poly(group, path.polyline, color, weight, pane=pane, dash=dash,
              tooltip=esc(f"{title} {fmt_dist(path.distance_m)} · {fmt_dur(path.t_end_s - path.t_start_s)}"))

    moves = {move.index: move for move in it.moves}
    stops: list[str] = []
    for k in range(len(it.rides) + 1):
        move = moves.get(k)
        if move is not None:
            if move.bike is not None:
                bike = move.bike
                walk(bike.walk_in, "걷기")
                color, weight, dash = style("bike")
                _poly(group, bike.ride.polyline, color, weight, pane=pane, dash=dash,
                      tooltip=esc(f"따릉이 {fmt_dist(bike.ride.distance_m)} · {fmt_dur(bike.ride.t_end_s - bike.ride.t_start_s)}"))
                walk(bike.walk_out, "걷기")
            else:
                walk(move.walk, "걷기")
        if k == len(it.rides):
            break
        ride = it.rides[k]
        if it.plan_missed_last and ride.plan_dep_s is None and ride.board_index is not None:
            walk(ride.fallback, f"{ride_name(ride)} 막차를 놓쳐 걷기")
            break
        points = _ride_points(ride, scenario, origin, coords)
        kind = "bus" if ride.mode == TravelMode.BUS else "subway"
        color, weight, dash = style(kind)
        _poly(group, points, color, weight, pane=pane, dash=dash, tooltip=_ride_tooltip(ride, names),
              double=(kind == "subway" and not naive))
        if labels and points:
            border = tokens[kind]
            if ride.board_node_id is not None:
                _marker(group, points[0], _icon(_pill_html(f"{ride_name(ride)} 승차", fill="#ffffff", border=border,
                                                           color="#0b0b0b", below=_spot(points[0]) in ends_at), (0, 0), (0, 0)),
                        z=500)
            _marker(group, points[-1], _icon(_pill_html(f"{names.get(ride.alight_node_id, ride.alight_node_id)} 하차",
                                                        fill="#ffffff", border=border, color="#0b0b0b", below=True), (0, 0), (0, 0)),
                    z=500)
        if ride.board_node_id:
            stops.append(ride.board_node_id)
        stops.append(ride.alight_node_id)
    return stops


def _stop_tooltips(scenario: Scenario, config: EngineConfig, names: Mapping[str, str]) -> dict[str, str]:
    """정류장마다 이름과 그 정류장에 오는 차량 1·2번째의 시각과 출처(§7.6)."""
    rows: dict[str, list[str]] = {}
    for line in scenario.bus_lines:
        trips = ce.build_bus_trips(line, scenario.clock_s, config)
        if not trips.usable:
            continue
        for index, stop_id in enumerate(line.stop_ids):
            order = ce.stop_vehicle_order(trips, index)[:2]
            if not order:
                continue
            parts = [f"{fmt_clock(scenario.clock_s, t_s)}({TIME_SOURCE_NAMES[source] if source else '-'})" for _, t_s, source in order]
            rows.setdefault(stop_id, []).append(f"{line.name}번 " + ", ".join(parts))
    return {stop_id: esc(names.get(stop_id, stop_id)) + "<br>" + "<br>".join(esc(row) for row in items)
            for stop_id, items in rows.items()}


def _platform_tooltips(scenario: Scenario, names: Mapping[str, str]) -> dict[str, str]:
    """승강장마다 역 이름, 호선, 다음 열차 시각(§7.6)."""
    station_of: dict[str, tuple[str, str]] = {}
    for station in scenario.subway_stations:
        for line, platform_id in station.platforms:
            station_of[platform_id] = (station.name, line)
    nexts: dict[str, float] = {}
    for pattern in scenario.subway_patterns:
        for index, platform_id in enumerate(pattern.platform_ids):
            times = [trip.arr_s[index] for trip in pattern.trips if trip.arr_s[index] >= 0]
            if times:
                nexts[platform_id] = min(min(times), nexts.get(platform_id, math.inf))
    result = {}
    for platform_id, (station, line) in station_of.items():
        upcoming = f"다음 열차 {fmt_clock(scenario.clock_s, nexts[platform_id])}" if platform_id in nexts else "다음 열차 없음"
        result[platform_id] = esc(f"{station} · {line} · {upcoming}")
    return result


def _bike_style(use: str, tokens: Mapping[str, str]) -> dict[str, Any]:
    bike = tokens["bike"]
    if use in ("PICK", "DROP"):
        return {"fill": bike, "border": "#ffffff", "text_color": "#ffffff", "border_width": 3}
    if use == StationUse.AVAILABLE.value:
        return {"fill": bike, "border": "#ffffff", "text_color": "#ffffff", "border_width": 1.5}
    if use == StationUse.NO_BIKE.value:
        return {"fill": "#ffffff", "border": bike, "text_color": bike, "border_width": 2}
    return {"fill": "#ffffff", "border": bike, "text_color": bike, "border_width": 2, "dashed": True}


def build_map(scenario: Scenario, output: EngineOutput | None, selected_id: str | None, kakao: Mapping[str, Any] | None = None,
              pick: tuple | None = None, *, tokens: Mapping[str, str] | None = None) -> folium.Map:
    """지도(§6.3, §7.6). Streamlit 없이 부를 수 있고 캐시하지 않는다(카카오 좌표가 들어갈 수 있다, §5.4).
    바탕 타일이 늘 밝으므로 중립 색은 밝은 토큰이고 수단·등급 색만 `tokens` 를 따른다(§7.7)."""
    t = {**dict(tokens or TOKENS_LIGHT), **{key: TOKENS_LIGHT[key] for key in MAP_NEUTRAL_TOKENS}}
    index = {node.id: node for node in scenario.nodes}
    index.update({station.id: station for station in scenario.bike_stations})
    names = node_names(scenario)
    points: dict[str, tuple[float, float]] = {}
    query = output.query if output is not None else None
    if query is not None:
        if query.origin.kind == OriginKind.AT_POINT:
            points[ce.ORIGIN_POINT_ID] = (query.origin.lat, query.origin.lon)
        if query.destination_lat is not None:
            points[ce.DESTINATION_POINT_ID] = (query.destination_lat, query.destination_lon)

    def coords(node_id: str) -> tuple[float, float] | None:
        node = index.get(node_id)
        return (node.lat, node.lon) if node is not None else points.get(node_id)

    fmap = folium.Map(location=tuple(scenario.map_center), zoom_start=scenario.map_zoom, tiles="OpenStreetMap",
                      control_scale=True)
    fmap.get_root().header.add_child(folium.Element(SCALE_METRIC_CSS))  # 축척은 미터만(§7.6, 18단계)
    for name, z_index in _PANES:
        folium.map.CustomPane(name, z_index=z_index, pointer_events=True).add_to(fmap)
    if pick is not None:
        fmap.get_root().header.add_child(folium.Element("<style>.leaflet-container { cursor: crosshair; }</style>"))
    items = _items(output) if output is not None else {}
    selected = items.get(selected_id) if selected_id else None
    config = output.config if output is not None else EngineConfig()
    origin = query.origin if query is not None else None
    route_stops: list[str] = []
    pick_ids: set[str] = set()
    drop_ids: set[str] = set()
    end_marks: list[tuple[str, tuple[float, float], str | None]] = []  # (라벨, 자리, 노드 ID): 출발·도착 표지
    if output is not None:
        for node_id, label in ((output.origin_node_id, "출발"), (output.destination_node_id, "도착")):
            location = coords(node_id) if node_id else None
            if location is None and label == "출발" and origin is not None and origin.kind in (OriginKind.ON_TRAIN, OriginKind.ON_BUS):
                ride = selected.rides[0] if selected is not None and selected.rides else None
                location = None if ride is None else (_ride_points(ride, scenario, origin, coords) or [None])[0]
            if location is not None:
                end_marks.append((label, location, node_id))

    if selected is not None:
        group = folium.FeatureGroup(name="선택한 여정", show=True).add_to(fmap)
        route_stops = _draw_itinerary(group, selected, scenario, origin, coords, names, t, naive=False, labels=True,
                                      ends_at=frozenset(_spot(location) for _, location, _ in end_marks))
        for move in selected.moves:
            if move.bike is not None:
                pick_ids.add(move.bike.pick_id)
                drop_ids.add(move.bike.drop_id)
    naive_id = output.comparison.naive_best_id if output is not None else None
    if naive_id and naive_id != selected_id and naive_id in items:
        naive = items[naive_id]
        group = folium.FeatureGroup(name="기존 앱 방식 1위", show=True).add_to(fmap)
        _draw_itinerary(group, naive, scenario, origin, coords, names, t, naive=True, labels=False)
        rides = {ride.index: ride for ride in naive.rides}
        for boarding in naive.boardings:
            ride = rides.get(boarding.ride_index)
            if boarding.ghost and ride is not None and ride.board_node_id and coords(ride.board_node_id):
                _marker(group, coords(ride.board_node_id), _icon(_circle_html(18, t["ghost"], "#ffffff", text="✕"), (18, 18), (9, 9)),
                        tooltip=esc(f"유령 환승: {ride_name(ride)} 기존 앱 차량을 탈 확률 "
                                    f"{fmt_pct(boarding.p_catch_naive or 0.0)}"), z=400)

    ends = folium.FeatureGroup(name="출발·도착", show=True)
    has_ends = False
    if output is not None:
        for label, location, node_id in end_marks:
            _marker(ends, location, _icon(_pill_html(label, fill=t["ink"], border="#ffffff", color="#ffffff", size=12, weight=700),
                                          (0, 0), (0, 0)), tooltip=esc(names.get(node_id or "", label)), z=1000)
            has_ends = True
            if node_id in points:
                nearest = nearest_ground(scenario, points[node_id][0], points[node_id][1], node_id, config)
                if nearest is not None and coords(nearest[0]) is not None:
                    folium.PolyLine([points[node_id], coords(nearest[0])], color=t["ink"], weight=1, dash_array="2 4",
                                    pane="mr-route").add_to(ends)
    elif pick is not None:
        for marker, label in ((pick[1], "출발"), (pick[2], "도착")):
            if marker is None:
                continue
            _marker(ends, (marker[0], marker[1]), _icon(_pill_html(label, fill=t["ink"], border="#ffffff", color="#ffffff", size=12,
                                                                   weight=700), (0, 0), (0, 0)), tooltip=esc(marker[2]), z=1000)
            has_ends = True
    if has_ends:
        ends.add_to(fmap)

    if output is not None and output.pruning is not None and len(output.pruning.polygon) >= 3:
        group = folium.FeatureGroup(name="탐색 타원", show=True).add_to(fmap)
        folium.Polygon(output.pruning.polygon, color=t["muted"], weight=1.5, dash_array="6 6", fill=True,
                       fill_color=t["muted"], fill_opacity=0.04, pane="mr-ellipse", interactive=False).add_to(group)

    stops_group = folium.FeatureGroup(name="정류장·역", show=True).add_to(fmap)
    stop_tips = _stop_tooltips(scenario, config, names)
    platform_tips = _platform_tooltips(scenario, names)
    highlighted = set(route_stops)
    for node in scenario.nodes:
        if node.node_type == NodeType.BUS_STOP:
            size = 18 if node.id in highlighted else 14
            _marker(stops_group, (node.lat, node.lon),
                    _icon(_circle_html(size, t["bus"], "#ffffff", radius="4px"), (size, size), (size // 2, size // 2)),
                    tooltip=stop_tips.get(node.id, esc(node.name)))
        elif node.node_type == NodeType.SUBWAY_PLATFORM:
            size = 18 if node.id in highlighted else 14
            _marker(stops_group, (node.lat, node.lon), _icon(_circle_html(size, t["subway"], "#ffffff"), (size, size),
                                                             (size // 2, size // 2)),
                    tooltip=platform_tips.get(node.id, esc(node.name)))

    bikes_group = folium.FeatureGroup(name="따릉이 대여소", show=True).add_to(fmap)
    statuses = {status.station_id: status for status in output.stations} if output is not None else {}
    for station in scenario.bike_stations:
        status = statuses.get(station.id)
        if station.id in pick_ids:
            use, use_name = "PICK", "이 여정의 대여소"
        elif station.id in drop_ids:
            use, use_name = "DROP", "이 여정의 반납소"
        elif status is not None:
            use, use_name = status.use.value, STATION_USE_NAMES[status.use]
        else:
            use = StationUse.AVAILABLE.value if station.bikes_available > 0 else StationUse.NO_BIKE.value
            use_name = STATION_USE_NAMES[StationUse(use)]
        bikes = status.bikes_available if status is not None else station.bikes_available
        if output is None:
            tip = f"{station.name} · 자전거 {bikes}대"
        else:
            rate = "-" if station.rental_rate_per_hour is None else fmt_rate(station.rental_rate_per_hour)
            p_bike = "-" if status is None or status.p_bike is None else fmt_pct(status.p_bike)
            tip = f"{station.name} · 자전거 {bikes}대 / 거치대 {station.rack_total} · 시간당 대여 {rate} · {use_name} · P_bike {p_bike}"
        _marker(bikes_group, (station.lat, station.lon),
                _icon(_circle_html(20, text=str(bikes), **_bike_style(use, t)), (20, 20), (10, 10)), tooltip=esc(tip))

    signals_group = folium.FeatureGroup(name="신호", show=True).add_to(fmap)
    by_node: dict[str, list] = {}
    for phase in scenario.signals:
        by_node.setdefault(phase.intersection_id, []).append(phase)
    for node_id, phases in by_node.items():
        location = coords(node_id)
        if location is None:
            continue
        for k, phase in enumerate(phases):
            if phase.actuated:
                style = {"fill": t["muted"], "border": "#ffffff", "dashed": True}
                state_name = SIGNAL_STATE_NAMES[SignalState.STOCHASTIC]
            elif ce.is_open_signal(phase):
                state = ce.signal_event(phase, 0.0, WaitRule.EXPECTED).state
                style = {"fill": t["safe"] if state == SignalState.GREEN else t["ghost"], "border": "#ffffff"}
                state_name = SIGNAL_STATE_NAMES[state]
            else:
                style = {"fill": t["muted"], "border": "#ffffff"}
                state_name = SIGNAL_STATE_NAMES[SignalState.STOCHASTIC]
            shift = round(14 * (k - (len(phases) - 1) / 2))
            source = SIGNAL_SOURCE_NAMES[phase.source] + (" · 감응" if phase.actuated else "")
            tip = (f"{names.get(node_id, node_id)} {phase.direction} · 주기 {phase.cycle_s:g}초 · {source} · "
                   f"기준 시각 {state_name}")
            _marker(signals_group, location, _icon(_circle_html(12, style["fill"], style["border"], dashed=style.get("dashed", False)),
                                                   (12, 12), (6 - shift, 6)), tooltip=esc(tip))

    if output is not None and output.pruning is not None:
        rounds = folium.FeatureGroup(name="탐색 라운드", show=False).add_to(fmap)
        for node_id, round_no, t_s in output.search.reach:
            location = coords(node_id)
            if location is None:
                continue
            _marker(rounds, location, _icon(_circle_html(16, "#ffffff", t["ink2"], text=str(round_no), text_color=t["ink"],
                                                         border_width=1), (16, 16), (8, 8)),
                    tooltip=esc(f"라운드 {round_no} · {fmt_clock(output.clock_s, t_s)}"))
        outside = [record for record in output.pruning_records if not record.kept]
        suffix = ""
        if len(outside) > MAP_MAX_PRUNED_MARKERS:
            outside = [record for record in outside if index.get(record.node_id) is None
                       or index[record.node_id].node_type != NodeType.WAYPOINT]
            suffix = " (경유점 생략)"
            if len(outside) > MAP_MAX_PRUNED_MARKERS:
                outside = sorted(outside, key=lambda record: record.node_id)[:MAP_MAX_PRUNED_MARKERS]
        pruned = folium.FeatureGroup(name=f"타원 밖 노드{suffix}", show=False).add_to(fmap)
        for record in outside:
            location = coords(record.node_id)
            if location is None:
                continue
            folium.CircleMarker(location, radius=4, color=t["muted"], weight=1.5, fill=False,
                                tooltip=folium.Tooltip(esc(names.get(record.node_id, record.node_id)))).add_to(pruned)

    if kakao:
        group = folium.FeatureGroup(name="카카오 도보 경로(비교)", show=True).add_to(fmap)
        for unit in kakao.get("units", ()):
            if unit.get("state") != "OK" or not unit.get("coords"):
                continue
            shortest = unit.get("shortest")
            tip = None
            if shortest:
                tip = esc(f"카카오 최단 도보 {fmt_dist(shortest[0])} · {fmt_dur(shortest[1])}")
            _poly(group, unit["coords"], t["ink"], 3, pane="mr-kakao", dash="10 6 2 6", tooltip=tip)

    folium.LayerControl(collapsed=True).add_to(fmap)
    bounds: list[tuple[float, float]] = []
    if output is not None and output.pruning_records:
        bounds = [coords(record.node_id) for record in output.pruning_records if record.kept]
        bounds += list(points.values())
    if pick is not None:
        bounds += [(marker[0], marker[1]) for marker in pick[1:] if marker is not None]
    bounds = [point for point in bounds if point is not None]
    if not bounds:
        bounds = [(node.lat, node.lon) for node in (*scenario.nodes, *scenario.bike_stations)]
    if bounds:
        lats = [point[0] for point in bounds]
        lons = [point[1] for point in bounds]
        fmap.fit_bounds([[min(lats), min(lons)], [max(lats), max(lons)]], padding=(24, 24))
    return fmap


_SIDE_SHIFT = {"up": "translate(-50%,calc(-100% - 7px))", "down": "translate(-50%,7px)",
               "left": "translate(calc(-100% - 9px),-50%)", "right": "translate(9px,-50%)"}


def _badge_html(number: str, fill: str, short: str = "") -> str:
    """간단히 보기 지도의 단계 번호 표지(§6.9, 19단계): 수단 색 원에 흰 번호, 흰 테두리 2 px. 쉬운 단계 목록의 번호와 같다.
    33단계: `short`(노선 이름, "2호선", "143·146·345번", "따릉이")가 있으면 원 오른쪽에 같은 색 알약으로 잇는다(번호가 노선으로
    읽히지 않게). 원의 가운데가 그 자리다."""
    size = SIMPLE_MAP_BADGE_PX
    style = (f"width:{size}px;height:{size}px;box-sizing:border-box;border-radius:50%;background:{fill};border:2px solid #ffffff;"
             "color:#ffffff;font:700 12px/1 sans-serif;display:flex;align-items:center;justify-content:center;"
             "font-variant-numeric:tabular-nums;box-shadow:0 1px 2px rgba(0,0,0,0.35);flex:none;")
    circle = f'<div style="{style}">{esc(number)}</div>'
    if not short:
        return f'<div class="mr-map-badge" style="{style}">{esc(number)}</div>'
    tag = (f"margin-left:-6px;padding:1px 8px 1px 9px;background:{fill};color:#ffffff;border:2px solid #ffffff;border-left:none;"
           "border-radius:0 999px 999px 0;font:600 12px/1.5 sans-serif;white-space:nowrap;box-shadow:0 1px 2px rgba(0,0,0,0.25);")
    return (f'<div class="mr-map-badge" style="display:flex;align-items:center;width:max-content;">{circle}'
            f'<span style="{tag}">{esc(short)}</span></div>')


def _side_pill_html(text: str, side: str, *, fill: str, border: str, color: str) -> str:
    """간단히 보기 지도의 라벨(§6.9): 점에서 `side` 쪽으로 떨어진 알약."""
    style = (f"position:absolute;transform:{_SIDE_SHIFT[side]};white-space:nowrap;background:{fill};color:{color};"
             f"border:2px solid {border};border-radius:999px;padding:1px 8px;font:600 12px/1.5 sans-serif;"
             "box-shadow:0 1px 2px rgba(0,0,0,0.25);")
    return f'<div style="{style}">{esc(text)}</div>'


SCALE_METRIC_CSS = "<style>.leaflet-control-scale-line + .leaflet-control-scale-line { display: none; }</style>"


class FitClamp(folium.MacroElement):
    """간단히 보기 지도의 맞춤 여백 줄이기(§6.9, 18단계): 지도 폭(높이)에서 두 여백을 빼고 남는 길이가
    `SIMPLE_MAP_SPAN_PX` 보다 작으면 그 축의 두 여백을 같은 비율로 줄여 남는 길이를 맞추고 다시 맞춘다.
    여백이 지도보다 크면 Leaflet 이 최대 확대로 가서 경로가 보이지 않기 때문이다(휴대폰의 E1)."""

    _template = Template("""
        {% macro script(this, kwargs) %}
            (function () {
                var m = {{ this._parent.get_name() }}, s = m.getSize(), span = {{ this.span }};
                var tl = {{ this.top_left }}, br = {{ this.bottom_right }}, k = [1, 1], need = false;
                [s.x, s.y].forEach(function (size, i) {
                    var room = Math.max(0, size - span), sum = tl[i] + br[i];
                    if (sum > room) { k[i] = sum > 0 ? room / sum : 1; need = true; }
                });
                if (need) {
                    m.fitBounds({{ this.bounds }}, {paddingTopLeft: [tl[0] * k[0], tl[1] * k[1]],
                                                    paddingBottomRight: [br[0] * k[0], br[1] * k[1]], animate: false});
                }
            })();
        {% endmacro %}
    """)

    def __init__(self, bounds: Sequence[Sequence[float]], top_left: Sequence[float], bottom_right: Sequence[float],
                 span: float) -> None:
        super().__init__()
        self._name = "FitClamp"
        self.bounds = json.dumps([list(map(float, point)) for point in bounds])
        self.top_left = json.dumps([float(v) for v in top_left])
        self.bottom_right = json.dumps([float(v) for v in bottom_right])
        self.span = float(span)


class LabelFit(folium.MacroElement):
    """간단히 보기 지도의 라벨 맞춤(§6.9, 19단계): 맞춤(`fit_bounds`, `FitClamp`) 뒤에 경로 경계와 표지의 어림 상자
    (출발·도착 알약과 단계 번호 표지의 화면 좌표 ± `label_extents`)를 모아, 지도 가장자리에서 `gap` px (아래는 축척·출처 줄
    `foot` px 를 더해) 안에 맞춘다. 들어오지 않거나 남는 자리가 있으면 상자의 가운데로 옮기고(`panBy`) 분수 확대 단계로 줄이거나
    키운다(한 번에 최대 한 단계, 최대 여덟 번, 가장 크게 `SIMPLE_MAP_MAX_ZOOM`). 비율은 축마다 (남는 길이 − 표지가 뻗는 몫) /
    점들의 퍼짐 × 0.98 이고(뻗는 몫 = 상자 − 퍼짐은 확대 단계가 바뀌어도 그대로라서), 그 몫이 남는 길이 이상이거나 퍼짐이 0 이면
    남는 길이 / 상자다. 다 들어오고 키울 비율이 2^0.05 미만이면 멈춘다. 앞선 맞춤의 확대 움직임이 아직 끝나지 않았으면 끝난 뒤
    (`zoomend`) 맞춘다(움직임이 끝날 때 Leaflet 이 움직임의 목표 확대 단계로 되돌리기 때문). 표지의 화면 요소를 재지 않고 좌표로
    계산한다(지도가 그려지는 중에는 표지 요소의 자리가 아직 옛 화면 기준일 수 있다). 지도가 아직 크기 없이 그려졌으면(열린 사이드바
    뒤 등) 크기가 생길 때(`resize`) 맞춘다. 비율이 0 이하이거나 수가 아니면 멈춘다. 표지 하나가 남는 길이보다 크면 셈에서 뺀다.
    맞추는 동안만 확대 단계 간격(`zoomSnap`)을 0 으로 둔다."""

    _template = Template("""
        {% macro script(this, kwargs) %}
            (function () {
                var m = {{ this._parent.get_name() }}, gap = {{ this.gap }}, foot = {{ this.foot }};
                var zmax = Math.min(m.getMaxZoom(), {{ this.zmax }});
                var geo = L.latLngBounds({{ this.bounds }}), labels = {{ this.labels }};
                function scale(room, box, geo) {  // 점들의 퍼짐만 늘고 줄며 알약이 뻗는 길이는 그대로다
                    var fixed = box - geo;
                    return geo > 0 && room > fixed ? 0.98 * (room - fixed) / geo : room / Math.max(1, box);
                }
                function fitLabels() {
                    if (m._animatingZoom) { m.once('zoomend', fitLabels); return; }  // 맞춤(fitBounds)의 확대 움직임이 끝난 뒤
                    var size = m.getSize();
                    if (size.x <= 2 * gap + 40 || size.y <= 2 * gap + foot + 40) { m.once('resize', fitLabels); return; }
                    var snap = m.options.zoomSnap;
                    m.options.zoomSnap = 0;
                    for (var i = 0; i < 8; i++) {
                        var s = m.getSize();
                        var a = m.latLngToContainerPoint(geo.getNorthWest()), b = m.latLngToContainerPoint(geo.getSouthEast());
                        var x0 = Math.min(a.x, b.x), y0 = Math.min(a.y, b.y), x1 = Math.max(a.x, b.x), y1 = Math.max(a.y, b.y);
                        var gx0 = x0, gy0 = y0, gx1 = x1, gy1 = y1;
                        labels.forEach(function (l) {
                            if (l[2] + l[3] > s.x - 2 * gap || l[4] + l[5] > s.y - 2 * gap - foot) { return; }
                            var p = m.latLngToContainerPoint([l[0], l[1]]);
                            gx0 = Math.min(gx0, p.x); gx1 = Math.max(gx1, p.x); gy0 = Math.min(gy0, p.y); gy1 = Math.max(gy1, p.y);
                            x0 = Math.min(x0, p.x - l[2]); x1 = Math.max(x1, p.x + l[3]);
                            y0 = Math.min(y0, p.y - l[4]); y1 = Math.max(y1, p.y + l[5]);
                        });
                        var inside = x0 >= gap && y0 >= gap && x1 <= s.x - gap && y1 <= s.y - gap - foot;
                        var k = Math.min(scale(s.x - 2 * gap, x1 - x0, gx1 - gx0), scale(s.y - 2 * gap - foot, y1 - y0, gy1 - gy0));
                        if (!(k > 0) || !isFinite(k)) { break; }
                        var dz = Math.log(k) / Math.LN2, z = m.getZoom();
                        if (inside && (dz < 0.05 || z >= zmax)) { break; }  // 다 들어오고 더 키울 자리가 없다
                        m.panBy([(x0 + x1) / 2 - s.x / 2, (y0 + y1) / 2 - (s.y - foot) / 2], {animate: false});
                        var next = Math.min(zmax, z + Math.max(-1, Math.min(1, dz)));
                        if (Math.abs(next - z) > 1e-6) { m.setZoom(next, {animate: false}); }
                    }
                    m.options.zoomSnap = snap;
                }
                fitLabels();
            })();
        {% endmacro %}
    """)

    def __init__(self, bounds: Sequence[Sequence[float]], labels: Sequence[tuple[tuple[float, float], str, str]], gap: float,
                 foot: float) -> None:
        super().__init__()
        self._name = "LabelFit"
        self.bounds = json.dumps([list(map(float, point)) for point in bounds])
        self.extents = [(float(location[0]), float(location[1]), *label_extents(text, side)) for location, text, side in labels]
        self.labels = json.dumps([list(row) for row in self.extents])
        self.gap = float(gap)
        self.foot = float(foot)
        self.zmax = float(SIMPLE_MAP_MAX_ZOOM)


class MobilePan(folium.MacroElement):
    """휴대폰에서는 한 손가락으로 끌어도 지도를 옮기지 않는다(§6.9): 쪽이 먼저 넘어가고, 두 손가락으로 확대·이동한다."""

    _template = Template("""
        {% macro script(this, kwargs) %}
            if (L.Browser.mobile) { {{ this._parent.get_name() }}.dragging.disable(); }
            {{ this._parent.get_name() }}.attributionControl.setPrefix(false);  // 좁은 지도에서 축척과 겹치지 않게(18단계). OSM 출처는 그대로
        {% endmacro %}
    """)


def short_stop_name(node_id: str, scenario: Scenario | None) -> str:
    """간단히 보기의 짧은 지점 이름(§6.9, 19단계, 놓치면 줄): 지하철 승강장이면 "{역 이름}역"(예: "봉은사역"),
    아니면 `easy_names` 의 이름(20단계, 버스 정류장은 " 정류장" 이 붙는다)."""
    stations = scenario.subway_stations if scenario is not None else ()
    station = next((item for item in stations if any(pid == node_id for _, pid in item.platforms)), None)
    if station is not None:
        return f"{station.name}역"
    return easy_names(scenario).get(node_id, node_id)


def pill_size(text: str) -> tuple[float, float]:
    """라벨 알약의 어림 크기(§6.9, px): 너비 = 20 + 글자마다 ASCII 7, 그 밖 12. 높이 22."""
    return 20.0 + sum(7.0 if ord(ch) < 128 else 12.0 for ch in text), 22.0


def label_extents(text: str, side: str) -> tuple[float, float, float, float]:
    """점에서 라벨이 뻗는 길이(왼쪽, 오른쪽, 위, 아래, px). 자리 "badge" 는 점 가운데의 단계 번호 표지(지름 `SIMPLE_MAP_BADGE_PX`)."""
    if side == "badge":
        r = SIMPLE_MAP_BADGE_PX / 2
        number, _, short = text.partition(" ")
        tail = pill_size(short)[0] - 3.0 if short else 0.0  # 33단계: 원 오른쪽의 노선 알약(왼쪽 6 px 는 원 밑에 겹친다)
        return r, r + tail, r, r
    w, h = pill_size(text)
    if side == "up":
        return w / 2, w / 2, 7.0 + h, 0.0
    if side == "down":
        return w / 2, w / 2, 0.0, 7.0 + h
    if side == "left":
        return 9.0 + w, 0.0, h / 2, h / 2
    return 0.0, 9.0 + w, h / 2, h / 2


def map_padding(bounds: Sequence[tuple[float, float]], labels: Sequence[tuple[tuple[float, float], str, str]]
                ) -> tuple[tuple[float, float], tuple[float, float]]:
    """간단히 보기 지도의 맞춤 여백(§6.9): ((왼쪽, 위), (오른쪽, 아래)) px. 라벨마다 그 쪽으로 뻗는 길이 + 4 에서
    가장자리까지의 몫(최대 ½) × `SIMPLE_MAP_SPAN_PX` 를 뺀 값과 `SIMPLE_MAP_PAD_PX` 가운데 큰 값이고, 아래는 축척·출처 줄
    `SIMPLE_MAP_FOOT_PX` 를 더한다."""
    lats = [point[0] for point in bounds]
    lons = [point[1] for point in bounds]
    lat_span, lon_span = max(lats) - min(lats), max(lons) - min(lons)
    left = right = top = bottom = float(SIMPLE_MAP_PAD_PX)
    for (lat, lon), text, side in labels:
        fx = (lon - min(lons)) / lon_span if lon_span > 0 else 0.5
        fy = (max(lats) - lat) / lat_span if lat_span > 0 else 0.5
        ext_l, ext_r, ext_u, ext_d = label_extents(text, side)
        left = max(left, ext_l + 4 - min(fx, 0.5) * SIMPLE_MAP_SPAN_PX)
        right = max(right, ext_r + 4 - min(1 - fx, 0.5) * SIMPLE_MAP_SPAN_PX)
        top = max(top, ext_u + 4 - min(fy, 0.5) * SIMPLE_MAP_SPAN_PX)
        bottom = max(bottom, ext_d + 4 - min(1 - fy, 0.5) * SIMPLE_MAP_SPAN_PX)
    return (round(left), round(top)), (round(right), round(bottom + SIMPLE_MAP_FOOT_PX))


def label_sides(points: Sequence[tuple[float, float]]) -> list[str]:
    """라벨 자리(§6.9): 점마다 가장 가까운 다른 점의 반대쪽. 남북 차가 동서 차보다 크면(같으면) 위·아래, 아니면 왼쪽·오른쪽.
    거리는 위도 1도 = 111,195 m, 경도 1도 = 111,195 · cos(위도) m 로 잰다. 점이 하나면 위."""
    sides = []
    for i, (lat, lon) in enumerate(points):
        best = None
        for j, (lat2, lon2) in enumerate(points):
            if i == j:
                continue
            dy = (lat2 - lat) * 111_195.0
            dx = (lon2 - lon) * 111_195.0 * math.cos(math.radians(lat))
            d = math.hypot(dx, dy)
            if best is None or d < best[0]:
                best = (d, dx, dy)
        if best is None or best[0] == 0.0:
            sides.append("up")
        elif abs(best[2]) >= abs(best[1]):
            sides.append("down" if best[2] > 0 else "up")
        else:
            sides.append("left" if best[1] > 0 else "right")
    return sides


def map_short(step: GuideStep) -> str:
    """지도 표지 옆 노선 이름(33단계): 타기는 단계 글의 첫 낱말("2호선", "143·146·345번"), 따릉이는 "따릉이",
    지금 탄 차에서 내리기는 "내리기". 그 밖은 빈 글자."""
    if step.kind == "bike":
        return "따릉이"
    if step.kind in ("bus", "subway"):
        return "내리기" if step.main.endswith("내리기") else step.main.split(" ")[0]
    return ""


def build_simple_map(scenario: Scenario, output: EngineOutput | None, best_id: str | None, pick: tuple | None = None, *,
                     tokens: Mapping[str, str] | None = None) -> folium.Map:
    """간단히 보기 지도(§6.9): 추천 경로와 출발·도착만. 레이어 선택 창이 없고, 라벨은 이웃 점의 반대쪽에 둔다."""
    t = {**dict(tokens or TOKENS_LIGHT), **{key: TOKENS_LIGHT[key] for key in MAP_NEUTRAL_TOKENS}}
    index = {node.id: node for node in scenario.nodes}
    index.update({station.id: station for station in scenario.bike_stations})
    names = node_names(scenario)
    points: dict[str, tuple[float, float]] = {}
    query = output.query if output is not None else None
    if query is not None:
        if query.origin.kind == OriginKind.AT_POINT:
            points[ce.ORIGIN_POINT_ID] = (query.origin.lat, query.origin.lon)
        if query.destination_lat is not None:
            points[ce.DESTINATION_POINT_ID] = (query.destination_lat, query.destination_lon)

    def coords(node_id: str) -> tuple[float, float] | None:
        node = index.get(node_id)
        return (node.lat, node.lon) if node is not None else points.get(node_id)

    fmap = folium.Map(location=tuple(scenario.map_center), zoom_start=scenario.map_zoom, tiles="OpenStreetMap", control_scale=True,
                      zoom_control=False)
    MobilePan().add_to(fmap)
    fmap.get_root().header.add_child(folium.Element(SCALE_METRIC_CSS))  # 축척은 미터만(§7.6, 18단계)
    for name, z_index in _PANES:
        folium.map.CustomPane(name, z_index=z_index, pointer_events=True).add_to(fmap)
    if pick is not None:
        fmap.get_root().header.add_child(folium.Element("<style>.leaflet-container { cursor: crosshair; }</style>"))
    best = _items(output).get(best_id) if output is not None and best_id else None
    origin = query.origin if query is not None else None
    labels: list[tuple[tuple[float, float], str]] = []  # 출발·도착 알약 (자리, 글자)
    badges: list[tuple[tuple[float, float], str, str, str]] = []  # 단계 번호 표지 (자리, 번호, 채움, 노선 이름)
    placed: list[tuple[tuple[float, float], str, str]] = []
    bounds: list[tuple[float, float]] = []
    if best is not None:
        group = folium.FeatureGroup(name=SIMPLE_ROUTE_LAYER, show=True).add_to(fmap)
        _draw_itinerary(group, best, scenario, origin, coords, names, t, naive=False, labels=False)
        moves = {move.index: move for move in best.moves}
        for k in range(len(best.rides) + 1):
            move = moves.get(k)
            if move is not None:
                paths = (move.bike.walk_in, move.bike.ride, move.bike.walk_out) if move.bike is not None else (move.walk,)
                bounds += [tuple(point) for path in paths if path is not None for point in path.polyline]
            if k == len(best.rides):
                break
            ride = best.rides[k]
            if best.plan_missed_last and ride.plan_dep_s is None and ride.board_index is not None:
                if ride.fallback is not None:
                    bounds += [tuple(point) for point in ride.fallback.polyline]
                break
            bounds += _ride_points(ride, scenario, origin, coords)
    ends: list[tuple[tuple[float, float], str]] = []
    if output is not None:
        for node_id, word in ((output.origin_node_id, "출발"), (output.destination_node_id, "도착")):
            location = coords(node_id) if node_id else None
            if location is None and word == "출발" and origin is not None and origin.kind in (OriginKind.ON_TRAIN, OriginKind.ON_BUS):
                ride = best.rides[0] if best is not None and best.rides else None
                location = None if ride is None else (_ride_points(ride, scenario, origin, coords) or [None])[0]
            if location is not None:
                ends.append((location, word))
    if not ends and pick is not None:  # 엔진을 부르지 않았거나 찍은 점을 길에 붙이지 못함: 지도 누르기의 표지
        ends = [((marker[0], marker[1]), word) for marker, word in ((pick[1], "출발"), (pick[2], "도착")) if marker is not None]
    if ends:
        group = folium.FeatureGroup(name=SIMPLE_ENDS_LAYER, show=True).add_to(fmap)
        for location, word in ends:
            _marker(group, location, _icon(_circle_html(12, t["ink"], "#ffffff"), (12, 12), (6, 6)), z=900)
        labels = list(ends)
        bounds += [location for location, _ in ends]
    if best is not None and output is not None:
        end_spots = {_spot(location) for location, _ in ends}
        fills = {"bus": t["bus"], "subway": t["subway"], "bike": t["bike"]}
        for number, step in enumerate(easy_steps(best, output, scenario), start=1):
            location = coords(step.spot) if step.spot else None
            if location is not None and _spot(location) not in end_spots:  # 출발·도착 자리는 그 알약이 말한다
                badges.append((location, str(number), fills.get(step.kind, t["ink"]), map_short(step)))
    holder = next((child for child in fmap._children.values() if isinstance(child, folium.FeatureGroup)), None)
    if labels:
        merged: dict[tuple[float, float], list] = {}
        for location, text in labels:
            entry = merged.setdefault(_spot(location), [location, []])
            if text not in entry[1]:
                entry[1].append(text)
        entries = list(merged.values())
        sides = label_sides([entry[0] for entry in entries] + [location for location, _, _, _ in badges])[:len(entries)]
        placed = [(entry[0], " · ".join(entry[1]), side) for entry, side in zip(entries, sides)]
        for location, text, side in placed:
            _marker(holder, location, _icon(_side_pill_html(text, side, fill=t["ink"], border="#ffffff", color="#ffffff"),
                                            (0, 0), (0, 0)), z=1000)
    for location, number, fill, short in badges:
        size = SIMPLE_MAP_BADGE_PX
        _marker(holder, location, _icon(_badge_html(number, fill, short), (size, size), (size // 2, size // 2)), z=950)
    placed = placed + [(location, f"{number} {short}".strip(), "badge") for location, number, _, short in badges]
    if pick is not None:
        bounds += [(marker[0], marker[1]) for marker in pick[1:] if marker is not None]
    bounds = [point for point in bounds if point is not None]
    if not bounds:
        bounds = [(node.lat, node.lon) for node in (*scenario.nodes, *scenario.bike_stations)]
    lats = [point[0] for point in bounds]
    lons = [point[1] for point in bounds]
    top_left, bottom_right = map_padding(bounds, placed)
    fit = [[min(lats), min(lons)], [max(lats), max(lons)]]
    first_fit = folium.map.FitBounds(fit, padding_top_left=top_left, padding_bottom_right=bottom_right)
    first_fit.options["animate"] = False  # 움직임이 끝날 때 Leaflet 이 목표 단계로 되돌려 라벨 맞춤을 지우지 않게(19단계)
    first_fit.add_to(fmap)
    FitClamp(fit, top_left, bottom_right, SIMPLE_MAP_SPAN_PX).add_to(fmap)
    LabelFit(fit, placed, SIMPLE_MAP_LABEL_GAP_PX, SIMPLE_MAP_FOOT_PX).add_to(fmap)
    return fmap

def feature_groups(fmap: folium.Map) -> dict[str, folium.FeatureGroup]:
    """지도의 이름 있는 레이어(화면 검사가 읽는다)."""
    return {child.layer_name: child for child in fmap._children.values() if isinstance(child, folium.FeatureGroup)}


# --- 경로 목록 ---


def _on_variants_change() -> None:
    """"다른 걷는 길도 보기"를 끌 때 고른 여정이 다른 걷는 길이면 그 대표로 옮긴다(라디오 선택지에 있어야 하므로)."""
    state = st.session_state
    remember("show_variants")
    if not state.get("show_variants"):
        representative = (state.get("_variant_reps") or {}).get(state.get("selected_id"))
        if representative:
            store_value(state, "selected_id", representative)


def adjust_selection(state: MutableMapping[str, Any], output: EngineOutput) -> str | None:
    """다시 계산했을 때의 선택(§6.4): 직전 기본값이었으면 새 기본값으로, 고른 여정이 남아 있으면 유지, 없으면 기본값.
    고른 여정이 다른 걷는 길이면 "다른 걷는 길도 보기"를 켠다."""
    restore(state, "selected_id", None)
    restore(state, "show_variants", False)
    choices = {entry.itinerary_id for entry in route_entries(output, True)}
    new_default = default_selection(output)
    current = state.get("selected_id")
    if current is None or current == state.get("last_default_id") or current not in choices:
        current = new_default
    variants = {variant: rep for rep in output.ranking for variant in _items(output)[rep].variant_ids}
    state["_variant_reps"] = variants
    if current in variants and not state.get("show_variants"):
        store_value(state, "show_variants", True)
    store_value(state, "selected_id", current)
    state["last_default_id"] = new_default
    return current


def render_route_list(output: EngineOutput, scenario: Scenario, config: EngineConfig) -> None:
    state = st.session_state
    criterion = output.config.rank_criterion
    if criterion == RankCriterion.ON_TIME and output.query.deadline_s is None:
        criterion = RankCriterion.MEAN_ARRIVAL
    st.subheader("경로")
    st.caption(f"{RANK_NAMES[criterion]} · 평가한 여정 {len(output.itineraries)}개")
    st.toggle("다른 걷는 길도 보기", key="show_variants", on_change=_on_variants_change)
    sync_keep(state, "show_variants")
    entries = route_entries(output, bool(state.get("show_variants")))
    if not entries:
        return
    ids = [entry.itinerary_id for entry in entries]
    labels = {entry.itinerary_id: entry.label for entry in entries}
    if state.get("selected_id") not in ids:
        store_value(state, "selected_id", ids[0])
    st.radio("경로 선택", ids, key="selected_id", format_func=labels.get, captions=[entry.caption for entry in entries],
             label_visibility="collapsed", on_change=remember, args=("selected_id",))
    sync_keep(state, "selected_id")
    selected = _items(output)[state["selected_id"]]
    st.html(timeline_html(selected, output.clock_s))
    st.html(guide_html(selected, output, scenario, config))


# ===== U7. 탭 7개와 차트 =====
#
# 탭 안의 내용은 고른 여정 기준이고 ⑥ ⑦ 은 실행 전체를 보인다(§6.3). 화면은 엔진 결과의 값과 순서를 그대로 쓰고 형식만 바꾼다.
# 차트 생성 함수(`histogram_chart`, `arrival_chart`)는 그리기와 분리해 화면 검사가 차트의 데이터를 직접 읽는다(§7.4).
# 탭 안에서는 8단계 화면이 쓰는 클래스(`mr-tl` 로 시작하는 시간 막대, `mr-state`, `mr-chips`, `mr-legend`)와 `st.warning` 을
# 쓰지 않는다. 화면 검사가 그 이름으로 머리말, 비교 패널, 시간 막대를 찾기 때문이다.

TAB_NAMES = ("① 경로 비교", "② 탑승별 확률", "③ 신호", "④ 따릉이", "⑤ 요금", "⑥ 탐색 과정", "⑦ 데이터·기록")
NO_ITINERARY_TEXT = "계산된 여정이 없습니다."
SNAP_FAILED_SEARCH_TEXT = "찍은 점을 길에 붙이지 못해 탐색하지 않았습니다."
KAKAO_BUTTON_LABEL = "카카오 도보 경로와 비교"
KAKAO_PRIVACY_NOTE = "카카오 응답은 이 화면에만 잠시 보이고 저장하지 않습니다."
KAKAO_FAIL_TEXT: Mapping[str, str] = {
    "RATE_LIMITED": "비교 불가(무료 한도 초과 또는 결제 수단 없음)", "FAILED": "비교 불가(오류)", "NO_KEY": "비교 불가(키 없음)",
}
TIE_ORDER_TEXT = ("값이 같으면 계획대로 갈 확률이 큰 쪽, 요금이 싼 쪽, 탑승이 적은 쪽, 계획의 걷는 거리(따릉이 구간의 걷기 포함)가 "
                  "짧은 쪽, 여정 ID 순으로 정합니다.")
RANK_DESCRIPTIONS: Mapping[RankCriterion, str] = {
    RankCriterion.MEAN_ARRIVAL: "걷는 속도와 신호, 차를 놓칠 경우까지 넣은 도착 시각의 평균이 이른 순입니다.",
    RankCriterion.P90_ARRIVAL: "열 번 가운데 아홉 번은 그보다 일찍 닿는 시각(90% 도착)이 이른 순입니다.",
    RankCriterion.ON_TIME: "도착 마감 시각까지 닿을 확률이 높은 순입니다.",
    RankCriterion.UTILITY: "시간, 요금, 위험을 가중치로 더한 종합 점수 J 가 낮은 순입니다.",
}
CATCH_NOTE = "탈 확률은 앞 탑승의 결과를 가리지 않고 그 차나 그보다 이른 차를 탈 확률입니다."
NAIVE_OUTSIDE_NOTE = "기존 앱이 안내하는 차(◆)는 표에 보인 차량보다 앞 차량이라 표에 없습니다."
SIGNAL_PLAN_NOTE = "계획은 평소 속도로 걷고 위상을 모르는 신호는 평균만큼 기다린다고 본 값입니다. 확률은 걷는 속도와 위상 표본마다 다시 계산합니다."
AVERSE_NOTE = "이 여정은 '신호 피하기' 탐색이 찾았습니다. 위상을 모르는 신호를 가장 오래 기다린다고 보고 찾은 길입니다."
SEARCH_NOTE = "탐색은 '언제 어디서 내려 무엇으로 갈아탈지'를 라운드(탑승 횟수)마다 넓혀 가며 찾고, 조건을 바꿔 여러 번 돌려 후보를 모읍니다."
PRUNING_NOTE = "지도의 '탐색 타원'과 '탐색 라운드' 레이어와 함께 보세요."
STORE_MISSING_TEXT = ("기록 저장소가 없습니다. 수집을 시작하려면 키가 있는 컴퓨터에서 `python core_engine.py --collect` 를 실행하세요"
                      "(시연 시간대에만 부릅니다).")
MODELS_MISSING_TEXT = ("학습 모델이 없습니다. 신호 기록이 쌓이면 `python core_engine.py --fit`, 따릉이 대여 이력을 받으면 `--fit-bike` 를 "
                       "실행하세요.")
KEYS_NOTE = "키는 환경변수로만 넣습니다."
DISCARDED_NAME = "버린 후보"
_MISSED_LAST = "MISSED_LAST"
_GRADE_SYMBOLS = {Grade.SAFE: "✓", Grade.RISKY: "!", Grade.GHOST: "✕"}
_SOURCE_SYMBOLS = {SourceState.SUCCESS: "✓", SourceState.FAILED: "✕", SourceState.SKIPPED: "–"}


# --- 형식 (§6.3 의 대입식 규칙) ---


def _g(x: float) -> str:
    """대입식의 입력값, τ, W: `format(x, "g")`. 그 표기가 지수가 되는 큰 수는 소수 둘째 자리까지(끝의 0 은 뺀다)."""
    text = format(float(x), "g")
    if "e" in text:
        text = f"{float(x):.2f}".rstrip("0").rstrip(".")
    return text


def _f2(x: float) -> str:
    """수식 안의 소수 둘째 자리(천 단위 쉼표 없이)."""
    return _fixed(x, 2).replace(",", "")


def _f4(x: float) -> str:
    return _fixed(x, 4).replace(",", "")


def _won_number(krw: float) -> str:
    return str(_half(krw))


def _km(m: float) -> str:
    """요금 표의 거리 "1.39 km" (§6.3 ⑤ 탭, km 소수 둘째 자리)."""
    return f"{_fixed(m / 1000.0, 2)} km"


def _meters(m: float) -> str:
    """타원 가지치기 표의 거리 "2,125.93 m"."""
    return f"{_fixed(m, 2)} m"


def _sub(symbol: str, index: int) -> str:
    """수식의 아래첨자: 한 자리면 중괄호 없이(`Q_2`), 두 자리 이상이면 `Q_{12}`."""
    return f"{symbol}_{index}" if 0 <= index < 10 else f"{symbol}_{{{index}}}"


def _kst_datetime(unix_s: float) -> str:
    moment = datetime.datetime.fromtimestamp(float(unix_s), KST)
    return f"{fmt_date(moment.date().isoformat())} {moment:%H:%M:%S}"


def _source_clock(value: str | None, reference: datetime.date | None) -> str:
    """⑦ 탭 원천 표의 관측 시각. 기준 날짜와 같은 날이면 "HH:MM:SS", 다른 날이면(예: 지하철 시각표 파일의 수정 시각)
    "YYYY-MM-DD HH:MM:SS", 없으면 "-". 기준 날짜는 버스 도착, 따릉이, 신호 가운데 성공한 원천의 가장 이른 관측의 날짜다."""
    if not value:
        return "-"
    try:
        moment = datetime.datetime.fromisoformat(value).astimezone(KST)
    except ValueError:
        return "-"
    return f"{moment:%H:%M:%S}" if reference is None or moment.date() == reference else f"{moment:%Y-%m-%d %H:%M:%S}"


def _reference_date(sources: Sequence[ApiSourceStatus]) -> datetime.date | None:
    moments = []
    for item in sources:
        if item.source in _COLLECTED_SOURCES and item.state == SourceState.SUCCESS and item.observed_at:
            try:
                moments.append(datetime.datetime.fromisoformat(item.observed_at).astimezone(KST))
            except ValueError:
                continue
    return min(moments).date() if moments else None


def _iso_datetime(value: str | None) -> str:
    """ISO 8601 시각을 한국 시각 "YYYY-MM-DD HH:MM" 으로. 읽지 못하면 그대로."""
    if not value:
        return "-"
    try:
        moment = datetime.datetime.fromisoformat(value)
    except ValueError:
        return value
    if moment.tzinfo is not None:
        moment = moment.astimezone(KST)
    return moment.strftime("%Y-%m-%d %H:%M")


# --- 표 도구 ---


def _text_col(label: str, *, right: bool = False, help: str | None = None):
    return st.column_config.TextColumn(label, alignment="right" if right else None, help=help)


def _int_col(label: str, *, help: str | None = None):
    return st.column_config.NumberColumn(label, format="localized", help=help)


def _pct_col(label: str, tokens: Mapping[str, str], *, help: str | None = None):
    """0 ~ 1 의 확률을 막대와 백분율로(§7.4 의 표 안의 막대, `ink2`)."""
    return st.column_config.ProgressColumn(label, min_value=0.0, max_value=1.0, format="percent", step=0.001,
                                           color=tokens["ink2"], help=help)


# 표의 열 폭(px). Streamlit 1.67 의 자동 열 폭은 한글이 섞인 값("2분 15초", "위상 모름", "M1.csv (수정 2026-11-19)")을 좁게 잡아
# 글자가 잘린다(9단계 화면 확인). 그래서 머리글과 값의 글자 폭으로 열 폭을 직접 정하고, 합이 본문 폭을 넘으면 긴 값이 있는 열만
# 깎는다(바닥 = 머리글 폭과 TABLE_KEEP_PX 가운데 큰 것, 필요한 폭보다 크지 않게. 깎은 열의 긴 값은 칸에 올리면 전체가 보인다).
# 바닥의 합도 본문 폭을 넘는 넓은 표는 깎지 않고 가로로 스크롤한다(잘린 값보다 낫다). 글꼴 14 px 기준의 어림이다.
TABLE_WIDE_CHAR_PX = 13.6  # 한글·전각 한 글자
TABLE_BROAD_CHAR_PX = 9.0  # 라틴 대문자, %, m, w
TABLE_NARROW_CHAR_PX = 7.2  # 숫자와 나머지 라틴·기호
TABLE_THIN_CHAR_PX = 4.2  # 빈칸과 얇은 문장 부호
TABLE_THIN_CHARS = frozenset(" .,:;·'()[]-/|!")
TABLE_CELL_PAD_PX = 22  # 칸의 좌우 여백 합
TABLE_HEAD_PAD_PX = 40  # 머리 칸의 여백과 정렬·도움말 표시
TABLE_PROGRESS_PX = 170  # 진행 막대 열(막대와 "95.2%")
TABLE_KEEP_PX = 200  # 이 폭 안에 드는 값(한글 13자 남짓)은 깎지 않는다
# 1440 × 900 화면(§6.1)에서 본문 표의 폭: 본문 폭(1440 - 340 - 2 × 48 = 1,004, 10단계 화면 확인에서 잰 값)에서 테두리 2.
TABLE_BUDGET_PX = REFERENCE_VIEWPORT_PX - SIDEBAR_WIDTH_PX - 2 * MAIN_SIDE_PADDING_PX - 2


def text_px(text: str) -> float:
    """글자 폭 어림(px). 9단계 화면에서 잰 폭(한글 13 ~ 13.7, 숫자 약 7, 문장 부호 3 ~ 4)보다 조금 넉넉하게 잡는다."""
    total = 0.0
    for ch in text:
        if unicodedata.east_asian_width(ch) in ("W", "F"):
            total += TABLE_WIDE_CHAR_PX
        elif ch in TABLE_THIN_CHARS:
            total += TABLE_THIN_CHAR_PX
        elif ch.isupper() or ch in "%mwMW":
            total += TABLE_BROAD_CHAR_PX
        else:
            total += TABLE_NARROW_CHAR_PX
    return total


def _cell_text(value: Any) -> str:
    """표에 보일 글자(숫자 열은 천 단위 쉼표, `format="localized"`)."""
    if value is None or (isinstance(value, float) and math.isnan(value)):
        return ""
    if isinstance(value, bool):
        return str(value)
    if isinstance(value, int):
        return f"{value:,}"
    if isinstance(value, float):
        return f"{value:,.2f}"
    return str(value)


def fit_widths(needs: Mapping[str, float], floors: Mapping[str, float], budget: float) -> dict[str, int]:
    """열마다 필요한 폭 `needs` 의 합이 `budget` 을 넘으면 넓은 열부터 같은 높이 $L$ 로 깎는다: 폭 = min(필요, max($L$, 바닥)).
    합이 `budget` 이 되는 $L$ 을 이분법으로 찾는다. 바닥의 합이 `budget` 이상이면 깎지 않는다(가로 스크롤)."""
    if sum(needs.values()) <= budget or sum(floors.values()) >= budget:
        return {name: int(math.ceil(need)) for name, need in needs.items()}

    def total(level: float) -> float:
        return sum(min(need, max(level, floors[name])) for name, need in needs.items())

    low, high = 0.0, max(needs.values())
    for _ in range(60):
        middle = 0.5 * (low + high)
        if total(middle) > budget:
            high = middle
        else:
            low = middle
    return {name: int(math.floor(min(need, max(low, floors[name])))) for name, need in needs.items()}


def column_widths(rows: Sequence[Mapping[str, Any]], columns: Mapping[str, Any], names: Sequence[str]) -> dict[str, Any]:
    """`columns` 의 설정에 열 폭을 더한 사본. 폭을 이미 정한 열은 그대로 두고, 그 폭만큼 예산에서 뺀다."""
    config = {name: dict(columns.get(name) or {}) for name in names}
    needs: dict[str, float] = {}
    floors: dict[str, float] = {}
    fixed = 0.0
    for name, column in config.items():
        if column.get("width") is not None:
            fixed += float(column["width"]) if isinstance(column["width"], (int, float)) else 0.0
            continue
        head = text_px(str(column.get("label") or name)) + TABLE_HEAD_PAD_PX
        if (column.get("type_config") or {}).get("type") == "progress":
            needs[name] = floors[name] = max(head, TABLE_PROGRESS_PX)
            continue
        needs[name] = max([head] + [text_px(_cell_text(row.get(name))) + TABLE_CELL_PAD_PX for row in rows])
        floors[name] = min(needs[name], max(head, TABLE_KEEP_PX))
    for name, width in fit_widths(needs, floors, TABLE_BUDGET_PX - fixed).items():
        config[name]["width"] = width
    return config


def _table(rows: Sequence[Mapping[str, Any]], columns: Mapping[str, Any], alt_text: str, *, order: Sequence[str] | None = None) -> None:
    """한 표. 열 순서는 `columns` 의 순서(또는 `order`), 숫자 열은 오른쪽 정렬이다(§6.5). 열 폭은 `column_widths`."""
    names = list(order or columns)
    frame = pd.DataFrame([{name: row.get(name) for name in names} for row in rows], columns=names)
    st.dataframe(frame, hide_index=True, column_config=column_widths(rows, columns, names), alt=alt_text, width="stretch")


def _callout(lines: Sequence[str], kind: str) -> str:
    """주의 상자(`warn`)와 걸러진 사유 상자(`ghost`)."""
    body = "".join(f"<p>{esc(line)}</p>" for line in lines)
    return f'<div class="mr-callout {kind}">{body}</div>'


# --- 행 순서와 이름 (① 표, 도착 분포, ⑤ 표가 같이 쓴다) ---


def table_order(output: EngineOutput) -> list[ItineraryResult]:
    """① 표의 행 순서(§6.3): 경로 목록과 같다. 대표 순위 순, 각 대표 바로 아래 다른 걷는 길, 맨 아래 걸러진 여정."""
    items = _items(output)
    return [items[entry.itinerary_id] for entry in route_entries(output, True)]


def rank_cell(it: ItineraryResult) -> str:
    if it.status == RouteStatus.GHOST_PRUNED:
        return "–"
    if it.representative_id is not None or it.rank is None:
        return ""
    return str(it.rank)


def row_name(it: ItineraryResult, output: EngineOutput) -> str:
    """① 표의 여정 이름: 다른 걷는 길은 "↳ {이름}", 기존 방식 1위는 뒤에 " (기존 앱 1위)"."""
    name = f"↳ {it.label}" if it.representative_id is not None and it.status == RouteStatus.RANKED else it.label
    if it.itinerary_id == output.comparison.naive_best_id:
        name += " (기존 앱 1위)"
    return name


def chart_label(it: ItineraryResult, output: EngineOutput) -> str:
    """도착 분포의 행 이름(§7.4): "{순위}위 {이름}", 다른 걷는 길 "↳ {이름}", 걸러진 여정 "✕ {이름}", 기존 방식 1위는 뒤에 표시."""
    if it.status == RouteStatus.GHOST_PRUNED:
        name = f"✕ {it.label}"
    elif it.representative_id is not None or it.rank is None:
        name = f"↳ {it.label}"
    else:
        name = f"{it.rank}위 {it.label}"
    if it.itinerary_id == output.comparison.naive_best_id:
        name += " (기존 앱 1위)"
    return name


def effective_criterion(output: EngineOutput) -> RankCriterion:
    """마감 없이 ON_TIME 을 고르면 엔진이 평균 도착으로 정렬한다(§1.11.1)."""
    criterion = output.config.rank_criterion
    if criterion == RankCriterion.ON_TIME and output.query.deadline_s is None:
        return RankCriterion.MEAN_ARRIVAL
    return criterion


# --- 도착 분포 그림 (§7.4) ---


def arrival_ids(output: EngineOutput, selected_id: str | None) -> list[str]:
    """도착 분포에 넣는 여정(§6.3 ① 탭의 2): 대표(순위 순, 최대 6개), 기존 방식 1위, 고른 여정. 겹치면 한 번, ① 표 순서."""
    wanted = set(output.ranking[:6])
    if output.comparison.naive_best_id:
        wanted.add(output.comparison.naive_best_id)
    if selected_id:
        wanted.add(selected_id)
    return [it.itinerary_id for it in table_order(output) if it.itinerary_id in wanted]


def _tick_values(low: float, high: float) -> list[float]:
    """시계 눈금: 1분 ~ 1시간 가운데 눈금이 8개 이하가 되는 가장 작은 간격의 배수."""
    span = max(high - low, 1.0)
    step = next((value for value in (60, 120, 300, 600, 900, 1800, 3600) if span / value <= 8), 7200)
    first = math.ceil(low / step) * step
    return [float(value) for value in range(int(first), int(high) + 1, step)]


def arrival_chart(output: EngineOutput, ids: Sequence[str], tokens: Mapping[str, str], selected_id: str | None = None) -> alt.LayerChart:
    """도착 분포(§7.4): 한 행에 한 여정. 10% ~ 90% 가로선, 50% 눈금, 평균 점, 기존 앱이 약속한 도착 ×. x 는 시계 초 $c_0 + t$."""
    items = _items(output)
    c0 = output.clock_s
    rows: list[dict[str, Any]] = []
    used: set[str] = set()
    selected_label = None
    for itinerary_id in ids:
        it = items[itinerary_id]
        arrival = it.arrival
        if arrival.mean_s is None:
            continue
        label = chart_label(it, output)
        if label in used:
            label = f"{label} ({itinerary_id})"
        used.add(label)
        if itinerary_id == selected_id:
            selected_label = label
        promised = None if it.naive_promised_s is None else c0 + it.naive_promised_s
        rows.append({
            "label": label,
            "id": itinerary_id,
            "mean": c0 + arrival.mean_s,
            "p10": None if arrival.p10_s is None else c0 + arrival.p10_s,
            "p50": None if arrival.p50_s is None else c0 + arrival.p50_s,
            "p90": None if arrival.p90_s is None else c0 + arrival.p90_s,
            "promised": promised,
            "selected": itinerary_id == selected_id,
            "mean_text": _clock_or_dash(c0, arrival.mean_s),
            "p10_text": _clock_or_dash(c0, arrival.p10_s),
            "p50_text": _clock_or_dash(c0, arrival.p50_s),
            "p90_text": _clock_or_dash(c0, arrival.p90_s),
            "promised_text": _clock_or_dash(c0, it.naive_promised_s),
            "p_star_text": fmt_pct(it.p_star),
        })
    frame = pd.DataFrame(rows, columns=["label", "id", "mean", "p10", "p50", "p90", "promised", "selected", "mean_text",
                                        "p10_text", "p50_text", "p90_text", "promised_text", "p_star_text"])
    values = [value for row in rows for value in (row["p10"], row["p90"], row["mean"], row["promised"]) if value is not None]
    low, high = (min(values), max(values)) if values else (c0, c0 + 600.0)
    pad = max(30.0, 0.04 * (high - low))
    domain = [low - pad, high + pad]
    axis = alt.Axis(title="도착 시각", values=_tick_values(domain[0], domain[1]), labelExpr="utcFormat(datum.value * 1000, '%H:%M')",
                    grid=True, gridColor=tokens["grid"])
    scale = alt.Scale(domain=domain, nice=False, zero=False)
    weight = (alt.ExprRef(expr=f"datum.value === {json.dumps(selected_label, ensure_ascii=False)} ? 'bold' : 'normal'")
              if selected_label is not None else "normal")
    y = alt.Y("label:N", sort=[row["label"] for row in rows], title=None,
              axis=alt.Axis(labelLimit=280, labelFontWeight=weight, grid=False, ticks=False, domain=False))
    tips = [alt.Tooltip("label:N", title="여정"), alt.Tooltip("mean_text:N", title="평균"), alt.Tooltip("p10_text:N", title="10%"),
            alt.Tooltip("p50_text:N", title="50%"), alt.Tooltip("p90_text:N", title="90%"),
            alt.Tooltip("promised_text:N", title="약속 도착"), alt.Tooltip("p_star_text:N", title="계획대로 갈 확률")]
    base = alt.Chart()
    spread = base.mark_rule(color=tokens["ink2"], strokeWidth=2).encode(
        x=alt.X("p10:Q", scale=scale, axis=axis), x2=alt.X2("p90:Q"), y=y, tooltip=tips)
    middle = base.mark_tick(color=tokens["ink2"], thickness=2, size=12).encode(
        x=alt.X("p50:Q", scale=scale, axis=axis), y=y, tooltip=tips)
    promise = base.mark_point(shape="cross", angle=45, filled=True, size=70, color=tokens["muted"], opacity=1).encode(
        x=alt.X("promised:Q", scale=scale, axis=axis), y=y, tooltip=tips).transform_filter("isValid(datum.promised)")
    mean = base.mark_circle(color=tokens["ink"], size=50, opacity=1, stroke=tokens["bg"], strokeWidth=2).encode(
        x=alt.X("mean:Q", scale=scale, axis=axis), y=y, tooltip=tips)
    return alt.layer(spread, middle, promise, mean, data=frame).properties(height=alt.Step(32))


def arrival_legend_html() -> str:
    """도착 분포 위의 한 줄 범례(§7.4). 색이 아니라 모양으로 구분하므로 범례를 둔다."""
    entries = (("mean", "", "평균"), ("mid", "", "50%"), ("range", "", "10 ~ 90%"), ("promise", "×", "기존 앱이 약속한 도착"))
    return '<div class="mr-alegend">' + "".join(
        f'<span class="mr-li"><span class="mr-am {css}" aria-hidden="true">{esc(mark)}</span>{esc(text)}</span>'
        for css, mark, text in entries) + "</div>"


# --- 여유 시간 막대그래프 (§7.4) ---


def histogram_chart(boarding, ride, config: EngineConfig, tokens: Mapping[str, str]) -> alt.LayerChart | None:
    """여유 시간 막대그래프(§7.4): 엔진이 준 칸(왼쪽 경계, 점 수)과 비율 = 점 수 / `n_points`. 왼쪽 경계가 승차 여유 이상인 칸이
    탈 수 있는 쪽이다. 직접 라벨의 확률은 막대의 합이 아니라 엔진의 `p_conditional` 이다. 막대그래프가 없으면 None."""
    histogram = boarding.histogram
    if histogram is None:
        return None
    width = histogram.bin_width_s
    buffer = float(config.safety_buffer_s)
    total = histogram.n_points
    rows = []
    for left, count in histogram.bins:
        ratio = count / total if total else 0.0
        rows.append({
            "left": float(left),
            "right": float(left) + width,
            "x2": float(left) + 0.8 * width,
            "count": int(count),
            "ratio": ratio,
            "side": "탈 수 있음" if left >= buffer else "못 탐",
            "tip": f"{_g(left)} ~ {_g(left + width)}초 · {fmt_pct(ratio)}",
        })
    frame = pd.DataFrame(rows, columns=["left", "right", "x2", "count", "ratio", "side", "tip"])
    lefts = [row["left"] for row in rows] or [0.0]
    rights = [row["right"] for row in rows] or [width]
    low, high = min(min(lefts), 0.0, buffer), max(max(rights), buffer, 0.0)
    pad = max(width, 0.03 * (high - low))
    domain = [low - pad, high + pad]
    top = max([row["ratio"] for row in rows] or [0.0]) * 1.45 or 0.1
    x_scale = alt.Scale(domain=domain, nice=False, zero=False)
    y_scale = alt.Scale(domain=[0.0, top], nice=False)
    x_axis = alt.Axis(title="여유 = 안내 차량 출발 − 내 정류장 도착 (초)", grid=True, gridColor=tokens["grid"])
    y_axis = alt.Axis(title="점의 비율", format="%", grid=False)
    sides = ["탈 수 있음", "못 탐"]
    bars = alt.Chart().mark_rect(cornerRadiusTopLeft=2, cornerRadiusTopRight=2).encode(
        x=alt.X("left:Q", scale=x_scale, axis=x_axis), x2=alt.X2("x2:Q"),
        y=alt.Y("ratio:Q", scale=y_scale, axis=y_axis), y2=alt.datum(0.0),
        color=alt.Color("side:N", scale=alt.Scale(domain=sides, range=[tokens["ink2"], tokens["muted"]]), legend=None),
        opacity=alt.Opacity("side:N", scale=alt.Scale(domain=sides, range=[1.0, 0.6]), legend=None),
        tooltip=[alt.Tooltip("tip:N", title="칸"), alt.Tooltip("count:Q", title="점 수", format=",")])
    marks = pd.DataFrame({"x": [buffer, 0.0], "y": [top, top], "kind": ["buffer", "zero"]})
    threshold = alt.Chart(marks).transform_filter("datum.kind == 'buffer'").mark_rule(
        color=tokens["ink"], strokeWidth=1, strokeDash=[4, 4]).encode(x=alt.X("x:Q", scale=x_scale))
    zero = alt.Chart(marks).transform_filter("datum.kind == 'zero'").mark_rule(
        color=tokens["muted"], strokeWidth=1).encode(x=alt.X("x:Q", scale=x_scale))
    right_side = (buffer - domain[0]) / (domain[1] - domain[0]) <= 0.55
    label = f"승차 여유 {_g(buffer)}초 이상이면 탐 · 이 탑승만의 확률 {fmt_pct(boarding.p_conditional)}"

    def text_layers(kind: str, text: str, left: bool, dy: int, size: int, color: str) -> list[alt.Chart]:
        """직접 라벨 둘(바탕색 테두리를 두른 글자 아래 층 + 글자). 라벨이 다른 쪽의 세로선이나 막대를 지나도 읽히게 한다."""
        style = dict(text=text, align="left" if left else "right", baseline="top", dx=5 if left else -5, dy=dy, fontSize=size)
        encode = dict(x=alt.X("x:Q", scale=x_scale), y=alt.Y("y:Q", scale=y_scale))
        base = alt.Chart(marks).transform_filter(f"datum.kind == '{kind}'")
        halo = base.mark_text(color=tokens["bg"], stroke=tokens["bg"], strokeWidth=4, strokeJoin="round", **style).encode(**encode)
        return [halo, base.mark_text(color=color, **style).encode(**encode)]

    direct = text_layers("buffer", label, right_side, 2, 12, tokens["ink"])
    # "동시 도착" 은 여유 0 의 양쪽 가운데 x 범위가 넓은 쪽에 둔다(§7.4). 좁은 쪽에 두면 여유가 모두 0 이상일 때 y 축 눈금 위로 나간다.
    same = text_layers("zero", "동시 도착", domain[1] >= -domain[0], 20, 11, tokens["muted"])
    return alt.layer(bars, threshold, zero, *direct, *same, data=frame).properties(height=220)


# --- ① 경로 비교 ---


def render_compare_tab(p: Prepared, output: EngineOutput, selected: ItineraryResult, tokens: Mapping[str, str]) -> None:
    c0 = output.clock_s
    config = output.config
    deadline = output.query.deadline_s is not None
    criterion = effective_criterion(output)
    utility = criterion == RankCriterion.UTILITY
    rows = []
    for it in table_order(output):
        row: dict[str, Any] = {
            "순위": rank_cell(it),
            "여정": row_name(it, output),
            "찾은 탐색": " · ".join(RUN_NAMES[run] for run in it.found_by),
            "계획 도착": _clock_or_dash(c0, it.plan_arrival_s),
            "평균 도착": _clock_or_dash(c0, it.arrival.mean_s),
            "90% 도착": _clock_or_dash(c0, it.arrival.p90_s),
            "마감 확률": "-" if it.arrival.p_on_time is None else fmt_pct(it.arrival.p_on_time),
            "계획대로 갈 확률": fmt_pct(it.p_star),
            "등급": f"{_GRADE_SYMBOLS[it.grade]} {GRADE_NAMES[it.grade]}",
            "요금": fmt_won(it.fare.total_krw),
            "탑승 수": len(it.rides),
            "걷는 거리": fmt_dist(it.walk_distance_m),
            "유령 환승 수": it.ghost_count,
            "상태": STATUS_NAMES[RouteStatus.RANKED] if it.status == RouteStatus.RANKED else
            " · ".join((STATUS_NAMES[RouteStatus.GHOST_PRUNED], *(REASON_NAMES[reason] for reason in it.reasons))),
        }
        if utility:
            terms = it.utility
            row.update({"시간 항": None if terms is None else terms.time_term, "요금 항": None if terms is None else terms.cost_term,
                        "위험 항": None if terms is None else terms.risk_term})
        rows.append(row)
    columns: dict[str, Any] = {
        "순위": _text_col("순위", right=True), "여정": _text_col("여정"), "찾은 탐색": _text_col("찾은 탐색"),
        "계획 도착": _text_col("계획 도착", right=True), "평균 도착": _text_col("평균 도착", right=True),
        "90% 도착": _text_col("90% 도착", right=True),
    }
    if deadline:
        columns["마감 확률"] = _text_col("마감 확률", right=True)
    columns.update({
        "계획대로 갈 확률": _text_col("계획대로 갈 확률", right=True), "등급": _text_col("등급"), "요금": _text_col("요금", right=True),
        "탑승 수": _int_col("탑승 수"), "걷는 거리": _text_col("걷는 거리", right=True), "유령 환승 수": _int_col("유령 환승 수"),
        "상태": _text_col("상태"),
    })
    if utility:
        weights = (config.w_time, config.w_cost, config.w_risk)
        top = max(weights) / sum(weights) if sum(weights) > 0 else 1.0
        for name in ("시간 항", "요금 항", "위험 항"):
            columns[name] = st.column_config.ProgressColumn(name, min_value=0.0, max_value=top, format="%.3f",
                                                            color=tokens["ink2"])
    _table(rows, columns, "평가한 여정 전체의 비교 표")
    # 2. 도착 분포
    st.markdown("**도착 분포**")
    ids = arrival_ids(output, selected.itinerary_id)
    st.html(arrival_legend_html())
    st.altair_chart(arrival_chart(output, ids, tokens, selected.itinerary_id), width="stretch",
                    alt="여정별 도착 시각의 평균, 10%, 50%, 90% 와 기존 앱이 약속한 도착")
    items = _items(output)
    with st.expander("도착 분포 표"):
        table = []
        for itinerary_id in ids:
            it = items[itinerary_id]
            late = None if it.arrival.mean_s is None or it.naive_promised_s is None else it.arrival.mean_s - it.naive_promised_s
            table.append({"여정": chart_label(it, output), "평균": _clock_or_dash(c0, it.arrival.mean_s),
                          "10%": _clock_or_dash(c0, it.arrival.p10_s), "50%": _clock_or_dash(c0, it.arrival.p50_s),
                          "90%": _clock_or_dash(c0, it.arrival.p90_s), "약속 도착": _clock_or_dash(c0, it.naive_promised_s),
                          "약속보다 늦는 시간": "-" if late is None else fmt_delta_dur(late)})
        _table(table, {"여정": _text_col("여정"), **{name: _text_col(name, right=True) for name in
                                                      ("평균", "10%", "50%", "90%", "약속 도착", "약속보다 늦는 시간")}},
               "도착 분포 그림의 표 보기")
    # 3. 순위 기준
    st.markdown(f"**순위 기준: {RANK_NAMES[criterion]}** · {RANK_DESCRIPTIONS[criterion]} {TIE_ORDER_TEXT}")
    if output.config.rank_criterion == RankCriterion.ON_TIME and not deadline:
        st.caption("도착 마감이 없어 평균 도착으로 정렬했습니다.")
    if utility:
        render_utility(output, selected)
    # 4. 카카오 비교
    render_kakao(p, output, selected)


def render_utility(output: EngineOutput, selected: ItineraryResult) -> None:
    """종합 점수 식과 고른 여정의 대입식, $T_{max}$ 와 $Cost_{max}$ 가 온 여정(§6.3 ① 탭의 3)."""
    st.latex(r"J = w_t \frac{\bar T}{T_{max}} + w_c \frac{\text{Cost}}{\text{Cost}_{max}} + w_r (1 - P^{*})")
    terms = selected.utility
    if terms is None:
        st.caption("걸러진 여정은 종합 점수를 매기지 않습니다.")
    else:
        w_t, w_c, w_r = terms.weights
        st.latex(f"J = {_g(w_t)} \\cdot \\frac{{{_f2(selected.arrival.mean_s or 0.0)}}}{{{_f2(terms.t_max_s)}}} + "
                 f"{_g(w_c)} \\cdot \\frac{{{_won_number(selected.fare.total_krw)}}}{{{_won_number(terms.cost_max_krw)}}} + "
                 f"{_g(w_r)} \\cdot (1 - {_f4(selected.p_star)}) = {_f4(terms.total)}")
    reference = terms or next((it.utility for it in output.itineraries if it.utility is not None), None)
    if reference is None:
        return
    ranked = sorted((it for it in output.itineraries if it.status == RouteStatus.RANKED), key=lambda it: it.itinerary_id)
    time_from = next((it for it in ranked if it.arrival.mean_s is not None and abs(it.arrival.mean_s - reference.t_max_s) <= 1e-9), None)
    cost_from = next((it for it in ranked if abs(it.fare.total_krw - reference.cost_max_krw) <= 1e-9), None)
    st.caption(f"T_max {_fixed(reference.t_max_s, 2)}초 ({time_from.label if time_from else '-'}) · "
               f"Cost_max {fmt_won(reference.cost_max_krw)} ({cost_from.label if cost_from else '-'})")


def kakao_button_state(p: Prepared, units: Sequence[Any]) -> str | None:
    """버튼을 막는 사유(§6.3 의 카카오 비교 버튼 규칙). 누를 수 있으면 None."""
    calls = int(st.session_state.get("kakao_calls", 0) or 0)
    if not p.ctx.keys.get(p.config.env_kakao_key):
        return KAKAO_FAIL_TEXT["NO_KEY"]
    if calls >= KAKAO_SESSION_CALL_LIMIT or calls + 2 * len(units) > KAKAO_SESSION_CALL_LIMIT:
        return f"이 세션의 비교 한도(호출 {KAKAO_SESSION_CALL_LIMIT}회)를 다 썼습니다"
    if not units:
        return "이 여정에는 카카오와 비교할 역 밖 걷는 길이 없습니다"
    return None


def render_kakao(p: Prepared, output: EngineOutput, selected: ItineraryResult) -> None:
    st.markdown("**카카오 도보 경로와 비교**")
    result = (st.session_state.get("kakao_results") or {}).get((p.scenario_id, selected.itinerary_id))
    if result is not None:
        render_kakao_result(result, output.config)
    else:
        units = kakao_units(selected, p.display, output.query)
        reason = kakao_button_state(p, units)
        st.button(KAKAO_BUTTON_LABEL, key="kakao_button", disabled=reason is not None, on_click=_on_kakao_compare,
                  kwargs={"scenario_id": p.scenario_id, "itinerary": selected, "scenario": p.display, "query": output.query,
                          "config": p.config},
                  help="고른 여정의 걷는 길을 카카오 도보 경로(기본, 최단)와 견줍니다. 걷는 길마다 호출 2회를 씁니다.")
        if reason:
            st.caption(reason)
    st.caption(KAKAO_PRIVACY_NOTE)


def render_kakao_result(result: Mapping[str, Any], config: EngineConfig) -> None:
    if result.get("state") != "OK":
        st.caption(KAKAO_FAIL_TEXT.get(str(result.get("state")), KAKAO_FAIL_TEXT["FAILED"]))
    rows = []
    for unit in result.get("units", ()):
        if unit.get("state") != "OK":
            continue
        basic, shortest = unit.get("basic"), unit.get("shortest")
        rows.append({
            "이동": unit["name"],
            "우리 최단거리": fmt_dist(unit["ours_m"]),
            "카카오 기본": "-" if basic is None else f"{fmt_dist(basic[0])} · {fmt_dur(basic[1])}",
            "카카오 최단": "-" if shortest is None else f"{fmt_dist(shortest[0])} · {fmt_dur(shortest[1])}",
            "차이": "-" if unit.get("ratio") is None else fmt_pct(unit["ratio"]),
        })
    if rows:
        _table(rows, {"이동": _text_col("이동"), "우리 최단거리": _text_col("우리 최단거리", right=True),
                      "카카오 기본": _text_col("카카오 기본", right=True), "카카오 최단": _text_col("카카오 최단", right=True),
                      "차이": _text_col("차이", right=True, help="|카카오 최단 − 우리| / 우리")},
               "카카오 도보 경로 비교 결과")
    if any(unit.get("warn") for unit in result.get("units", ()) if unit.get("state") == "OK"):
        threshold = format(100.0 * config.kakao_shortest_diff_warn, "g")
        st.html(_callout([f"우리 보행망과 카카오 최단 거리가 {threshold}% 넘게 다릅니다. 보행망을 확인하세요"], "warn"))


# --- ② 탑승별 확률 ---


def _train_display(scenario: Scenario, pattern_id: str, trip_id: str) -> str:
    for pattern in scenario.subway_patterns:
        if pattern.id == pattern_id:
            for trip in pattern.trips:
                if trip.id == trip_id:
                    return f"급행 열차 {trip.train_no}" if trip.express else f"열차 {trip.train_no}"
    return f"열차 {trip_id}"


def vehicle_display(ride, trip_id: str, scenario: Scenario, *, last: bool = False, route_id: str | None = None) -> str:
    """차량 표시(§6.5): 버스 "차량 {ID}" 또는 "배차 간격으로 이은 차", 지하철 "열차 {번호}" 또는 "급행 열차 {번호}", 막차면 " (막차)".
    `route_id` 는 그 차량의 노선(`VehicleOption.route_id`)이고, 주지 않으면 `vehicle_route` 로 찾는다(묶음 탑승, §1.7.4)."""
    route = route_id if route_id is not None else vehicle_route(ride, trip_id, scenario)
    if ride.mode == TravelMode.BUS:
        text = vehicle_text(trip_id, route)
    else:
        text = _train_display(scenario, route, trip_id)
    return f"{text} (막차)" if last else text


def boarding_header(ride, boarding, names: Mapping[str, str]) -> str:
    alight = names.get(ride.alight_node_id, ride.alight_node_id)
    if ride.board_index is None:
        return f"탑승 {ride.index}: 지금 탄 차량 · {alight} 하차"
    board = names.get(ride.board_node_id or "", ride.board_node_id or "-")
    return f"탑승 {ride.index}: {ride_name(ride)} · {board} 승차 → {alight} 하차"


def verdict_lines(ride, boarding, output: EngineOutput, scenario: Scenario | None) -> list[str]:
    """판정 문장(§6.3 ② 탭의 3). 묶음 탑승이면 "{n}번째 차" 가 모두 "{차량 노선 이름} {n}번째 차" 이고, 기존 앱 차량이 표에 있으면
    "기존 앱: {탑승 노선 이름} {n}번째 차" 의 탑승 노선 이름 자리를 차량 노선 이름이 대신한다(§6.5)."""
    c0 = output.clock_s
    threshold = fmt_pct(output.config.p_ghost)
    if ride.board_index is None:
        return [f"지금 탄 차량이라 이 탑승은 놓치지 않습니다(탈 확률 {fmt_pct(boarding.p_conditional)})."]
    guided = _vehicle(boarding, boarding.guided_trip_id)
    naive = _vehicle(boarding, boarding.naive_trip_id)
    lines: list[str] = []
    if boarding.naive_trip_id is None:
        lines.append("기존 앱 방식으로는 이 정류장에서 탈 차가 없습니다.")
    elif boarding.ghost:
        if naive is not None:
            naive_text = f"{nth_vehicle(ride, naive, scenario)}(지금부터 {fmt_dur(naive.dep_s)} 뒤 출발)"
        elif boarding.naive_stop_arrival_s is not None and boarding.naive_margin_s is not None:
            # 차량 표(§1.4.5 (2), 끝에서 6대)보다 앞 차량이라 몇 번째인지는 표에 없다. 출발 시각은 기존 방식의 도착 + 여유다.
            naive_text = f"차(지금부터 {fmt_dur(boarding.naive_stop_arrival_s + boarding.naive_margin_s)} 뒤 출발)"
        else:
            naive_text = "차"
        p_naive = boarding.p_catch_naive if boarding.p_catch_naive is not None else 0.0
        subject = "" if ride.bundle and naive is not None else f"{ride_name(ride)} "
        text = (f"기존 앱: {subject}{naive_text}를 탈 수 있다고 안내 → 실제로 탈 확률 {fmt_pct(p_naive)} "
                f"(유령 환승, 기준 {threshold}).")
        if boarding.guided_found and guided is not None:
            text += (f" 이 앱의 안내: {nth_vehicle(ride, guided, scenario)}({fmt_dur(guided.dep_s)} 뒤 출발, "
                     f"탈 확률 {fmt_pct(guided.p_catch)}).")
        else:
            text += " 이 앱의 안내: 막차까지 따져도 기준을 넘는 차가 없어 이 경로를 거릅니다."
        lines.append(text)
    else:
        p_naive = boarding.p_catch_naive if boarding.p_catch_naive is not None else (naive.p_catch if naive else 0.0)
        nth = nth_vehicle(ride, naive, scenario) if naive is not None else "-번째 차"
        lines.append(f"기존 앱이 안내하는 {nth}를 탈 확률은 {fmt_pct(p_naive)}입니다.")
    if (boarding.guided_found and guided is not None and boarding.naive_trip_id is not None
            and guided.trip_id != boarding.naive_trip_id):
        lines.append(f"이 앱은 앞 탑승까지 함께 따져 {nth_vehicle(ride, guided, scenario)}를 안내합니다.")
    if boarding.naive_stop_arrival_s is not None and boarding.naive_margin_s is not None:
        lines.append(f"기존 앱 방식으로는 {fmt_clock(c0, boarding.naive_stop_arrival_s)}에 정류장에 닿아 "
                     f"{fmt_dur(boarding.naive_margin_s)} 여유가 있다고 봅니다.")
    return lines


def joint_line(boarding, config: EngineConfig) -> str:
    """함께 갈 확률(§6.3 ② 탭의 4)."""
    if not boarding.guided_found:
        return f"막차까지 따져도 탈 확률이 {fmt_pct(config.p_ghost)}에 못 미칩니다(막차 위험)."
    return (f"여기까지 모든 탑승에서 안내 차량(또는 더 이른 차)을 탈 확률 $Q_l$ = {fmt_pct(boarding.q_joint)}, "
            f"앞 탑승을 계획대로 했을 때 이 탑승만의 확률 {fmt_pct(boarding.p_conditional)}")


def histogram_notes(histogram) -> list[str]:
    lines = [f"막대는 준난수 {histogram.n_points:,}점의 분포입니다. 판정은 이 그림이 아니라 문턱값 계산을 씁니다"
             f"(그림 기준 {fmt_pct(histogram.success_mass)})."]
    if histogram.n_under or histogram.n_over or histogram.n_infinite:
        lines.append(f"그림 밖: 왼쪽 {histogram.n_under:,}점 · 오른쪽 {histogram.n_over:,}점 · "
                     f"정류장에 닿지 못함 {histogram.n_infinite:,}점")
    return lines


def pstar_tex(it: ItineraryResult) -> str:
    """$P^{*}$ 대입식(§6.3 ② 탭의 6): 따릉이 구간마다 $P_{bike,b}$, 탑승이 있으면 마지막 탑승의 $Q_L$."""
    terms = [(f"P_{{bike,{number}}}", value) for number, value in enumerate(it.p_bikes, start=1)]
    if it.boardings:
        last = it.boardings[-1]
        terms.append((_sub("Q", last.ride_index), last.q_joint))
    if not terms:
        return f"P^{{*}} = {_f4(it.p_star)}"
    if len(terms) == 1:
        return f"P^{{*}} = {terms[0][0]} = {_f4(it.p_star)}"
    symbols = " \\times ".join(symbol for symbol, _ in terms)
    values = " \\times ".join(_f4(value) for _, value in terms)
    return f"P^{{*}} = {symbols} = {values} = {_f4(it.p_star)}"


def method_text(arrival) -> str:
    if arrival.method == ProbMethod.EXACT:
        return f"탈 확률: 문턱값 정확 계산 · 도착 분포: 걷는 속도 점 {arrival.n_points:,}개"
    if arrival.method == ProbMethod.QMC:
        return f"탈 확률과 도착 분포: 준난수 {arrival.n_points:,}점 · 위상을 모르는 신호 {arrival.n_sampled_signals}개"
    return "걷는 속도 변동 없음"


def render_boarding_tab(p: Prepared, output: EngineOutput, it: ItineraryResult, tokens: Mapping[str, str]) -> None:
    config = output.config
    c0 = output.clock_s
    if it.status == RouteStatus.GHOST_PRUNED:
        st.html(_callout([reason_text(reason, it, output, config) for reason in it.reasons], "ghost mr-reasons"))
    names = node_names(p.display)
    rides = {ride.index: ride for ride in it.rides}
    if not it.boardings:
        st.info("이 여정은 차량을 타지 않습니다.")
    for boarding in it.boardings:
        ride = rides.get(boarding.ride_index)
        if ride is None:
            continue
        badge = ""
        if boarding.ghost:
            badge = badge_html("유령 환승", "ghost", "✕")
        elif boarding.naive_trip_id is not None and boarding.naive_trip_id == boarding.guided_trip_id:
            badge = chip_html("기존 앱과 같은 차")
        st.html(f'<div class="mr-bhead"><span class="mr-bt">{esc(boarding_header(ride, boarding, names))}</span>{badge}</div>')
        if boarding.vehicles:
            rows = []
            for option in boarding.vehicles:
                guided_mark = boarding.guided_found and option.trip_id == boarding.guided_trip_id
                marks = ("★" if guided_mark else "") + ("◆" if option.trip_id == boarding.naive_trip_id else "")
                row: dict[str, Any] = {"표시": marks}
                if ride.bundle:
                    row["노선"] = vehicle_line_name(ride, option.route_id, option.trip_id, p.display)
                row.update({
                    "몇 번째 차": f"{option.ordinal}번째 차",
                    "차량": vehicle_display(ride, option.trip_id, p.display, last=option.is_last, route_id=option.route_id),
                    "출발 시각": fmt_clock(c0, option.dep_s),
                    "하차 시각": fmt_clock(c0, option.alight_arr_s),
                    "시각 출처": TIME_SOURCE_NAMES[option.time_source],
                    "만차": full_text(option),
                    "막차": "예" if option.is_last else "아니오",
                    "탈 확률": option.p_catch,
                })
                rows.append(row)
            columns: dict[str, Any] = {"표시": _text_col("표시", help="★ 이 앱이 안내하는 차, ◆ 기존 앱이 안내하는 차")}
            if ride.bundle:
                columns["노선"] = _text_col("노선")
            columns.update({"몇 번째 차": _text_col("몇 번째 차"), "차량": _text_col("차량"),
                            "출발 시각": _text_col("출발 시각", right=True), "하차 시각": _text_col("하차 시각", right=True),
                            "시각 출처": _text_col("시각 출처"), "만차": _text_col("만차"), "막차": _text_col("막차"),
                            "탈 확률": _pct_col("탈 확률", tokens)})
            _table(rows, columns, f"탑승 {ride.index}의 차량 표")
            st.caption(CATCH_NOTE)
            if boarding.naive_trip_id is not None and _vehicle(boarding, boarding.naive_trip_id) is None:
                st.caption(NAIVE_OUTSIDE_NOTE)
            if ride.bundle:
                st.caption(f"{ride_name(ride)} 가운데 하차 정류장에 먼저 닿는 차를 보입니다. 먼저 와도 더 늦게 닿는 차는 표에서 뺍니다.")
        verdicts = verdict_lines(ride, boarding, output, p.display)
        st.html('<div class="mr-verdict">' + "".join(f"<p>{esc(line)}</p>" for line in verdicts) + "</div>")
        st.markdown(joint_line(boarding, config))
        chart = histogram_chart(boarding, ride, config, tokens)
        if chart is not None:
            st.altair_chart(chart, width="stretch", alt=f"탑승 {ride.index}({ride_name(ride)})의 여유 시간 막대그래프")
            for line in histogram_notes(boarding.histogram):
                st.caption(line)
            with st.expander("막대그래프 표"):
                histogram = boarding.histogram
                table = [{"칸": f"{_g(left)} ~ {_g(left + histogram.bin_width_s)}초", "점 수": int(count),
                          "비율": count / histogram.n_points if histogram.n_points else 0.0} for left, count in histogram.bins]
                _table(table, {"칸": _text_col("칸", right=True), "점 수": _int_col("점 수"), "비율": _pct_col("비율", tokens)},
                       f"탑승 {ride.index}의 막대그래프 표 보기")
        if boarding.trip_distribution:
            with st.expander("실제로 탄 차량의 분포"):
                listed = {option.trip_id: option.route_id for option in boarding.vehicles}
                table = [{"차량": "막차 놓침" if trip_id == _MISSED_LAST
                          else vehicle_display(ride, trip_id, p.display, route_id=listed.get(trip_id)),
                          "무게": weight} for trip_id, weight in boarding.trip_distribution]
                _table(table, {"차량": _text_col("차량"), "무게": _pct_col("무게", tokens)}, f"탑승 {ride.index}에서 실제로 탄 차량의 분포")
    render_itinerary_summary(output, it)


def render_itinerary_summary(output: EngineOutput, it: ItineraryResult) -> None:
    """② 탭의 6: $P^{*}$ 식, 도착 통계, 계산 방법."""
    c0 = output.clock_s
    arrival = it.arrival
    st.markdown("**여정 전체**")
    st.latex(pstar_tex(it))
    row: dict[str, Any] = {"평균": _clock_or_dash(c0, arrival.mean_s), "10%": _clock_or_dash(c0, arrival.p10_s),
                           "50%": _clock_or_dash(c0, arrival.p50_s), "90%": _clock_or_dash(c0, arrival.p90_s)}
    columns = {name: _text_col(name, right=True) for name in row}
    if output.query.deadline_s is not None:
        row["마감 확률"] = "-" if arrival.p_on_time is None else fmt_pct(arrival.p_on_time)
        columns["마감 확률"] = _text_col("마감 확률", right=True)
    row.update({
        "도착하지 못할 확률": fmt_pct(arrival.p_unreachable),
        "막차를 놓쳐 걸은 무게": fmt_pct(arrival.missed_last_mass),
        "자전거가 없어 걸은 무게": " · ".join(fmt_pct(mass) for mass in arrival.bike_fallback_mass) or "-",
    })
    for name in ("도착하지 못할 확률", "막차를 놓쳐 걸은 무게", "자전거가 없어 걸은 무게"):
        columns[name] = _text_col(name, right=True)
    _table([row], columns, "고른 여정의 도착 통계")
    st.caption(f"계산 방법: {method_text(arrival)}")
    if arrival.capped_signal_ids:
        st.caption(f"신호 {len(arrival.capped_signal_ids)}개는 준난수 차원 한도로 평균 대기를 썼습니다")


# --- ③ 신호 ---


def plan_signal_events(it: ItineraryResult) -> list[Any]:
    """계획이 지나는 신호 이벤트를 지나는 순서대로. 이동(따릉이는 ①③⑤)과, 계획이 막차를 놓친 탑승의 대체 보행(여정 안내와 같은 규칙)."""
    moves = {move.index: move for move in it.moves}
    events: list[Any] = []
    for k in range(len(it.rides) + 1):
        move = moves.get(k)
        if move is not None:
            if move.bike is not None:
                for path in (move.bike.walk_in, move.bike.ride, move.bike.walk_out):
                    events.extend(path.events)
            elif move.walk is not None:
                events.extend(move.walk.events)
        if k == len(it.rides):
            break
        ride = it.rides[k]
        if it.plan_missed_last and ride.plan_dep_s is None and ride.board_index is not None:
            if ride.fallback is not None:
                events.extend(ride.fallback.events)
            break
    return events


def signal_source_text(event) -> str:
    """출처 "실시간 개방"/"위상 모름" + " · 감응" + " · 설계 현시"/" · 기록 학습"(§6.3 ③ 탭)."""
    parts = ["실시간 개방" if event.tau_s is not None else "위상 모름"]
    if event.actuated:
        parts.append("감응")
    parts.append(SIGNAL_SOURCE_NAMES[event.source])
    return " · ".join(parts)


def _anchor(fraction: float) -> str:
    """막대 위 글자의 위치: 가운데 정렬, 양 끝 가까이에서는 막대 밖으로 나가지 않게 한쪽 정렬."""
    left = f"left: {100.0 * fraction:.2f}%"
    if fraction < 0.12:
        return left
    if fraction > 0.88:
        return f"{left}; transform: translateX(-100%)"
    return f"{left}; transform: translateX(-50%)"


def phase_html(phase, event, head: str) -> str:
    """위상 막대(§7.5 `mr-phase`). 개방 신호는 녹색·적색 구간과 도착 위상 τ, 미개방 고정 신호(`unknown`)는 빗금과 녹색 비율
    경계선, 감응 신호(`actuated`)는 경계선 없는 빗금이다."""
    cycle, green, red = phase.cycle_s, phase.green_s, phase.red_s
    head_html = f'<div class="mr-ph-head">{esc(head)}</div>'
    if event.tau_s is not None:
        tau = min(max(event.tau_s / cycle, 0.0), 1.0)
        split = green / cycle
        bar = (f'<div class="mr-ph-bar"><span class="mr-ph-green" style="flex: {green:.3f} 1 0px" title="녹색 {esc(_g(green))}초"></span>'
               f'<span class="mr-ph-red" style="flex: {red:.3f} 1 0px" title="적색 {esc(_g(red))}초"></span></div>')
        track = (f'<div class="mr-ph-track"><span class="mr-ph-label" style="{_anchor(tau)}">도착 τ = {esc(_g(event.tau_s))}초</span>'
                 f'{bar}<span class="mr-ph-tau" style="left: {100.0 * tau:.2f}%"></span></div>')
        ticks = ['<span style="left: 0">0</span>']
        if 0.12 <= split <= 0.88:
            ticks.append(f'<span style="{_anchor(split)}">녹색 끝 {esc(_g(green))}</span>')
        ticks.append(f'<span style="right: 0">{esc(_g(cycle))}초</span>')
        note = (f"녹색 {_g(green)}초 / 적색 {_g(red)}초 · 도착하면 {SIGNAL_STATE_NAMES[event.state]}, "
                f"대기 {fmt_dur(event.wait_s)}")
        return (f'<div class="mr-phase">{head_html}{track}<div class="mr-ph-ticks">{"".join(ticks)}</div>'
                f'<div class="mr-ph-note">{esc(note)}</div></div>')
    if phase.actuated:
        samples = phase.gap_samples_s
        bar = '<div class="mr-ph-bar"><span class="mr-ph-hatch" title="감응 신호"></span></div>'
        note = (f"감응 신호: 주기 {_g(min(samples))} ~ {_g(max(samples))}초 (표본 {len(samples)}개) · "
                f"평균 대기 {_f2(event.wait_s)}초")
        return f'<div class="mr-phase actuated">{head_html}<div class="mr-ph-track">{bar}</div><div class="mr-ph-note">{esc(note)}</div></div>'
    split = green / cycle
    bar = (f'<div class="mr-ph-bar"><span class="mr-ph-hatch" title="위상 모름">'
           f'<span class="mr-ph-edge" style="left: {100.0 * split:.2f}%"></span></span></div>')
    note = f"위상 모름: 평균 대기 {_f2(event.wait_s)}초 · 가장 길게 {_g(red)}초 (녹색 {_g(green)}초 / 적색 {_g(red)}초)"
    return f'<div class="mr-phase unknown">{head_html}<div class="mr-ph-track">{bar}</div><div class="mr-ph-note">{esc(note)}</div></div>'


def signal_formulas(phase, event) -> list[str]:
    """대입식(§6.3 ③ 탭): 개방 신호는 τ 와 W, 미개방 고정 신호는 E[W] 와 Var, 감응 신호는 표본과 E[W], Var."""
    cycle, green, red = phase.cycle_s, phase.green_s, phase.red_s
    if event.tau_s is not None:
        theta = phase.offset_s if phase.offset_s is not None else 0.0
        lines = [f"\\tau = (\\theta + t_{{arr}}) \\bmod C = ({_g(theta)} + {_g(event.t_arr_s)}) \\bmod {_g(cycle)} = {_g(event.tau_s)}"]
        if event.state == SignalState.RED:
            lines.append(f"W = C - \\tau = {_g(cycle)} - {_g(event.tau_s)} = {_g(event.wait_s)}")
        else:
            lines.append(f"W = 0 \\quad (\\tau < T_{{green}} = {_g(green)})")
        return lines
    if phase.actuated:
        samples = phase.gap_samples_s
        reds = [max(0.0, sample - green) for sample in samples]
        half_squares = sum(value * value / 2.0 for value in reds)
        thirds = sum(value ** 3 / 3.0 for value in reds)
        total = sum(samples)
        mean = event.wait_s
        return [
            f"c_i = {', '.join(_g(sample) for sample in samples)}, \\quad \\rho_i = \\max(0, c_i - T_{{green}}) = "
            f"{', '.join(_g(value) for value in reds)} \\quad (T_{{green}} = {_g(green)})",
            f"E[W] = \\sum_i \\rho_i^2 / 2 \\,/\\, \\sum_i c_i = {_g(half_squares)} / {_g(total)} = {_f2(mean)}",
            f"Var = \\sum_i \\rho_i^3 / 3 \\,/\\, \\sum_i c_i - E[W]^2 = {_g(thirds)} / {_g(total)} - {_f2(mean)}^2 = {_f2(event.var_s2)}",
        ]
    mean = event.wait_s
    return [
        f"E[W] = T_{{red}}^2 / 2C = {_g(red)}^2 / (2 \\times {_g(cycle)}) = {_f2(mean)}",
        f"Var = T_{{red}}^3 / 3C - E[W]^2 = {_g(red)}^3 / (3 \\times {_g(cycle)}) - {_f2(mean)}^2 = {_f2(event.var_s2)}",
    ]


def render_signal_tab(p: Prepared, output: EngineOutput, it: ItineraryResult) -> None:
    c0 = output.clock_s
    phases = {phase.id: phase for phase in p.display.signals}
    names = node_names(p.display)
    events = [event for event in plan_signal_events(it) if event.signal_id in phases]
    if events:
        st.caption(SIGNAL_PLAN_NOTE)
    if tuple(it.found_by) == (SearchRun.AVERSE,):
        st.caption(AVERSE_NOTE)
    if not events:
        st.info("이 여정에는 신호가 없습니다.")
    else:
        rows = []
        for event in events:
            phase = phases[event.signal_id]
            rows.append({
                "ID": event.signal_id,
                "신호": f"{names.get(phase.intersection_id, phase.intersection_id)} {phase.direction}".strip(),
                "출처": signal_source_text(event),
                "계획 도착": fmt_clock(c0, event.t_arr_s),
                "τ": "-" if event.tau_s is None else fmt_dur(event.tau_s),
                "상태": SIGNAL_STATE_NAMES[event.state],
                "대기": fmt_dur(event.wait_s),
                "분산": _fixed(event.var_s2, 2),
            })
        _table(rows, {"ID": _text_col("ID"), "신호": _text_col("신호"), "출처": _text_col("출처"),
                      "계획 도착": _text_col("계획 도착", right=True), "τ": _text_col("τ", right=True, help="도착 위상(개방 신호만)"),
                      "상태": _text_col("상태"), "대기": _text_col("대기", right=True),
                      "분산": _text_col("분산", right=True, help="대기의 분산(초²)")},
               "고른 여정이 지나는 신호")
        for event, row in zip(events, rows):
            phase = phases[event.signal_id]
            st.html(phase_html(phase, event, f"{row['ID']} · {row['신호']} · {row['계획 도착']} 도착 · {row['출처']}"))
            for line in signal_formulas(phase, event):
                st.latex(line)
    with st.expander("시나리오의 모든 신호"):
        render_all_signals(p.display, names)


def render_all_signals(scenario: Scenario, names: Mapping[str, str]) -> None:
    rows = []
    for phase in sorted(scenario.signals, key=lambda item: item.id):
        now = ce.signal_event(phase, 0.0, WaitRule.EXPECTED)
        open_signal = ce.is_open_signal(phase)
        mean, var = (None, None) if open_signal else ce.stochastic_wait(phase)
        samples = phase.gap_samples_s
        rows.append({
            "ID": phase.id,
            "교차로": names.get(phase.intersection_id, phase.intersection_id),
            "방향": phase.direction or "-",
            "C": _g(phase.cycle_s),
            "T_green": _g(phase.green_s),
            "T_red": _g(phase.red_s),
            "θ": "-" if phase.offset_s is None else _g(phase.offset_s),
            "개방": "실시간 개방" if phase.realtime_open else "위상 모름",
            "출처": SIGNAL_SOURCE_NAMES[phase.source],
            "감응": f"{_g(min(samples))} ~ {_g(max(samples))}초 (표본 {len(samples)}개)" if phase.actuated and samples else "-",
            "E[W]": "-" if mean is None else _fixed(mean, 2),
            "Var": "-" if var is None else _fixed(var, 2),
            "가장 긴 대기": fmt_dur(ce.worst_wait(phase)),
            "지금 상태": SIGNAL_STATE_NAMES[now.state],
        })
    if not rows:
        st.caption("이 시나리오에는 신호가 없습니다.")
        return
    right = ("C", "T_green", "T_red", "θ", "E[W]", "Var", "가장 긴 대기")
    _table(rows, {name: _text_col(name, right=name in right) for name in rows[0]}, "시나리오의 모든 신호")
    st.caption("θ 는 출발 늦추기를 반영한 오프셋, 지금 상태는 기준 시각의 상태입니다.")


# --- ④ 따릉이 ---


def bike_stages(bike) -> list[tuple[str, LegKind, float, float, float | None, float | None]]:
    """5단계 (이름, 구간 종류, 시작, 끝, 거리, 신호 대기): ① 걷기, ② 대여, ③ 따릉이, ④ 반납, ⑤ 걷기."""
    return [
        ("① 걷기", LegKind.WALK, bike.walk_in.t_start_s, bike.walk_in.t_end_s, bike.walk_in.distance_m, bike.walk_in.wait_s),
        ("② 대여", LegKind.BIKE_UNLOCK, bike.walk_in.t_end_s, bike.ride.t_start_s, None, None),
        ("③ 따릉이", LegKind.BIKE, bike.ride.t_start_s, bike.ride.t_end_s, bike.ride.distance_m, bike.ride.wait_s),
        ("④ 반납", LegKind.BIKE_DOCK, bike.ride.t_end_s, bike.walk_out.t_start_s, None, None),
        ("⑤ 걷기", LegKind.WALK, bike.walk_out.t_start_s, bike.walk_out.t_end_s, bike.walk_out.distance_m, bike.walk_out.wait_s),
    ]


def stages_html(bike, clock_s: float) -> str:
    """따릉이 구간의 5단계 막대(§7.5 의 시간 막대 부품을 단계 단위로). 뿌리 클래스는 `mr-stages mr-tl` 이다."""
    stages = bike_stages(bike)
    durations = [max(0.0, end - start) for _, _, start, end, _, _ in stages]
    total = sum(durations) or 1.0
    segments = []
    for (name, kind, start, end, _, _), duration in zip(stages, durations):
        title = f"{name} {fmt_dur(duration)}"
        inner = esc(f"{name[0]} {fmt_dur(duration)}") if duration / total >= 0.15 else ""
        segments.append(f'<div class="mr-seg mr-k-{kind.value.lower()}" style="flex: {duration:.3f} 1 0px" '
                        f'title="{esc(title)}">{inner}</div>')
    legend = " · ".join(f"{name} {fmt_dur(duration)}" for (name, *_), duration in zip(stages, durations))
    return (f'<div class="mr-stages mr-tl"><div class="mr-bar">{"".join(segments)}</div>'
            f'<div class="mr-ends"><span>{esc(fmt_clock(clock_s, stages[0][2]))}</span>'
            f'<span>{esc(fmt_clock(clock_s, stages[-1][3]))}</span></div>'
            f'<div class="mr-slegend">{esc(legend)}</div></div>')


def pbike_lines(station, bike) -> tuple[list[str], list[str]]:
    """$P_{bike}$ 대입식(§6.3 ④ 탭)과 그 아래 글자. 대여 속도가 없으면 식 대신 "대여 속도 정보 없음, 자전거 수만 확인"."""
    n0 = station.bikes_available if station is not None else 0
    rate = station.rental_rate_per_hour if station is not None else None
    g, a = bike.obs_age_s, bike.arrival_at_pick_s
    if rate is None:
        return ([f"n_0 = {n0} \\;\\Rightarrow\\; P_{{bike}} = {_f4(bike.p_bike)}"],
                ["대여 속도 정보 없음, 자전거 수만 확인", f"자전거가 남아 있을 확률 {fmt_pct(bike.p_bike)}"])
    lam = rate / 3600.0
    load = lam * (g + a)
    return ([
        "P_{bike} = \\sum_{j=0}^{n_0 - 1} \\frac{e^{-\\lambda (g + a)} (\\lambda (g + a))^j}{j!}, \\quad \\lambda = \\lambda_h / 3600",
        f"n_0 = {n0},\\; \\lambda_h = {_g(rate)},\\; g = {_g(g)},\\; a = {_g(a)} \\;\\Rightarrow\\; "
        f"\\lambda (g + a) = {_f4(load)},\\; P_{{bike}} = {_f4(bike.p_bike)}",
    ], [f"자전거가 남아 있을 확률 {fmt_pct(bike.p_bike)} (n_0 대여소의 자전거 수, λ_h 시간당 대여, g 관측 뒤 지난 초, a 대여소 계획 도착)"])


def render_bike_tab(p: Prepared, output: EngineOutput, it: ItineraryResult, tokens: Mapping[str, str]) -> None:
    c0 = output.clock_s
    names = node_names(p.display)
    stations = {station.id: station for station in p.display.bike_stations}
    bike_moves = [move for move in it.moves if move.bike is not None]
    if not bike_moves:
        st.info("이 여정에는 따릉이 구간이 없습니다.")
    for number, move in enumerate(bike_moves, start=1):
        bike = move.bike
        pick, drop = names.get(bike.pick_id, bike.pick_id), names.get(bike.drop_id, bike.drop_id)
        st.markdown(f"**따릉이 구간 {number}: {md_escape(pick)} → {md_escape(drop)}**")
        st.html(stages_html(bike, c0))
        rows = [{"단계": name, "시작": fmt_clock(c0, start), "끝": fmt_clock(c0, end), "시간": fmt_dur(max(0.0, end - start)),
                 "거리": "" if distance is None else fmt_dist(distance), "신호 대기": "" if wait is None else fmt_dur(wait)}
                for name, _, start, end, distance, wait in bike_stages(bike)]
        _table(rows, {"단계": _text_col("단계"), **{name: _text_col(name, right=True) for name in ("시작", "끝", "시간", "거리", "신호 대기")}},
               f"따릉이 구간 {number}의 5단계")
        parts = [max(0.0, end - start) for _, _, start, end, _, _ in bike_stages(bike)]
        st.latex(f"T_{{pm}} = {' + '.join(_g(part) for part in parts)} = {_g(move.t_end_s - move.t_start_s)}")
        formulas, notes = pbike_lines(stations.get(bike.pick_id), bike)
        for line in formulas:
            st.latex(line)
        for line in notes:
            st.caption(line)
        masses = it.arrival.bike_fallback_mass
        mass = masses[number - 1] if number - 1 < len(masses) else 0.0
        target = names.get(move.to_id, move.to_id)
        if bike.fallback is not None:
            st.markdown(md_escape(f"자전거가 없으면 {pick}에서 {target}까지 {fmt_dist(bike.fallback.distance_m)}를 걷습니다"
                                  f"(평소 속도 {fmt_dur(bike.fallback.t_end_s - bike.fallback.t_start_s)}, 이 경우의 무게 {fmt_pct(mass)})."))
        else:
            st.markdown(md_escape(f"자전거가 없으면 {pick}에서 걸어서 갈 길이 없습니다(이 경우의 무게 {fmt_pct(mass)})."))
    render_station_table(p, output, it, tokens)


def render_station_table(p: Prepared, output: EngineOutput, it: ItineraryResult, tokens: Mapping[str, str]) -> None:
    c0 = output.clock_s
    stations = {station.id: station for station in p.display.bike_stations}
    picks = {move.bike.pick_id for move in it.moves if move.bike is not None}
    drops = {move.bike.drop_id for move in it.moves if move.bike is not None}
    rows = []
    for status in sorted(output.stations, key=lambda item: item.station_id):
        station = stations.get(status.station_id)
        if status.station_id in picks:
            use = "이 여정의 대여소"
        elif status.station_id in drops:
            use = "이 여정의 반납소"
        else:
            use = STATION_USE_NAMES[status.use]
        rate = station.rental_rate_per_hour if station is not None else None
        rows.append({
            "대여소": station.name if station is not None else status.station_id,
            "상태": use,
            "자전거 수": status.bikes_available,
            "거치대": station.rack_total if station is not None else None,
            "시간당 대여": "-" if rate is None else fmt_rate(rate),
            "계획 도착": _clock_or_dash(c0, status.arrival_s),
            "P_bike": "-" if status.p_bike is None else fmt_pct(status.p_bike),
        })
    st.markdown("**대여소 상태**")
    if not rows:
        st.caption("이 시나리오에는 따릉이 대여소가 없습니다.")
        return
    _table(rows, {"대여소": _text_col("대여소"), "상태": _text_col("상태"), "자전거 수": _int_col("자전거 수"), "거치대": _int_col("거치대"),
                  "시간당 대여": _text_col("시간당 대여", right=True), "계획 도착": _text_col("계획 도착", right=True),
                  "P_bike": _text_col("P_bike", right=True, help="계획 도착 때 자전거가 남아 있을 확률")},
           "따릉이 대여소 상태")


# --- ⑤ 요금 ---


def fare_formula(it: ItineraryResult) -> str:
    """요금 식의 대입: $C = \\sum_k (B_k + X_k) + F_{bike} - M$. 기후동행카드를 적용하면 대중교통 항은 0 이다."""
    fare = it.fare
    tail = f"{fare.bike_krw} - {fare.mileage_discount_krw} = {fare.total_krw}"
    if fare.chains and not fare.climate_card_applied:
        chains = " + ".join(f"({chain.base_krw} + {chain.distance_extra_krw})" for chain in fare.chains)
        return f"C = \\sum_k (B_k + X_k) + F_{{bike}} - M = {chains} + {tail}"
    return f"C = F_{{bike}} - M = {tail}"


def render_fare_tab(p: Prepared, output: EngineOutput, it: ItineraryResult) -> None:
    rows = []
    for item in table_order(output):
        fare = item.fare
        rows.append({
            "순위": rank_cell(item), "여정": item.label, "묶음 수": len(fare.chains), "대중교통": fmt_won(fare.transit_krw),
            "따릉이": fmt_won(fare.bike_krw), "마일리지": fmt_won(fare.mileage_discount_krw),
            "기후동행카드": "예" if fare.climate_card_applied else "아니오", "합계": fmt_won(fare.total_krw),
            "탑승 거리": _km(sum(ride.distance_m for ride in item.rides)),
        })
    _table(rows, {"순위": _text_col("순위", right=True), "여정": _text_col("여정"), "묶음 수": _int_col("묶음 수"),
                  "대중교통": _text_col("대중교통", right=True), "따릉이": _text_col("따릉이", right=True),
                  "마일리지": _text_col("마일리지", right=True, help="따릉이 마일리지 할인"),
                  "기후동행카드": _text_col("기후동행카드"), "합계": _text_col("합계", right=True), "탑승 거리": _text_col("탑승 거리", right=True)},
           "평가한 여정 전체의 요금 표")
    st.markdown(f"**고른 여정의 요금: {md_escape(it.label)}**")
    fare = it.fare
    if fare.chains:
        chain_rows = [{"묶음": number, "탑승": ", ".join(str(index) for index in chain.ride_indexes), "기본요금": fmt_won(chain.base_krw),
                       "거리": _km(chain.distance_m), "거리 추가요금": fmt_won(chain.distance_extra_krw),
                       "앞 묶음과 끊긴 이유": "-" if chain.break_reason is None else FARE_BREAK_NAMES[chain.break_reason]}
                      for number, chain in enumerate(fare.chains, start=1)]
        _table(chain_rows, {"묶음": _int_col("묶음"), "탑승": _text_col("탑승"), "기본요금": _text_col("기본요금", right=True),
                            "거리": _text_col("거리", right=True), "거리 추가요금": _text_col("거리 추가요금", right=True),
                            "앞 묶음과 끊긴 이유": _text_col("앞 묶음과 끊긴 이유")},
               "고른 여정의 요금 묶음")
    else:
        st.caption("대중교통 탑승이 없어 요금 묶음이 없습니다.")
    st.latex(fare_formula(it))
    st.caption("C 합계, B_k 묶음 k 의 기본요금, X_k 거리 추가요금, F_bike 따릉이 요금, M 마일리지 할인"
               + (" · 기후동행카드 단기권으로 대중교통 요금은 0원" if fare.climate_card_applied else ""))
    messages = []
    for warning in output.warnings:
        if it.itinerary_id not in warning.ref_ids:
            continue
        if warning.code == WarningCode.TRANSFER_WINDOW_EXCEEDED:
            messages.append("환승 인정 시간을 넘겨 기본요금을 다시 냅니다")
        elif warning.code == WarningCode.CLIMATE_CARD_NOT_APPLICABLE:
            messages.append("광역버스가 있어 기후동행카드 단기권을 적용하지 않았습니다")
    if messages:
        st.html(_callout(messages, "warn"))
    notes = ce.fare_notes(output.config)
    st.markdown("**요금 안내**")
    st.html('<ul class="mr-notes">' + "".join(f"<li>{esc(note)}</li>" for note in notes) + "</ul>")


# --- ⑥ 탐색 과정 ---


def search_summary_line(search) -> str:
    skipped = sum(1 for run in search.runs if run.skipped)
    return (f"실행 {len(search.runs)}개(건너뜀 {skipped}개) · 찾은 여정 {search.found_total}개 → 합친 뒤 {search.distinct}개 → "
            f"평가 {search.kept}개(버림 {len(search.discarded_ids)}개)")


def line_name(route_id: str, scenario: Scenario) -> str:
    names = node_names(scenario)
    for line in scenario.bus_lines:
        if line.id == route_id:
            return f"{line.name}번"
    stations = {station.key: station.name for station in scenario.subway_stations}
    for pattern in scenario.subway_patterns:
        if pattern.id == route_id:
            last = stations.get(pattern.station_keys[-1], pattern.station_keys[-1])
            return f"{pattern.line} {pattern.direction} {last}행"
    return names.get(route_id, route_id)


def render_search_tab(p: Prepared, output: EngineOutput, tokens: Mapping[str, str]) -> None:
    state = st.session_state
    search = output.search
    c0 = output.clock_s
    items = _items(output)
    st.markdown(search_summary_line(search))
    st.caption(SEARCH_NOTE)
    # 2. 실행 표
    rows = [{
        "실행": RUN_NAMES[run.run],
        "수단": " · ".join(TRAVEL_MODE_NAMES[mode] for mode in run.modes) or "도보만",
        "걷는 속도 배수": fmt_mult(run.m_run),
        "신호 대기 규칙": WAIT_RULE_NAMES[run.wait_rule],
        "따릉이 상한": run.bike_limit,
        "승차 여유(초)": _half(run.buffer_s),
        "라운드 수": len(run.rounds),
        "D 의 파레토 라벨 수": len(run.d_labels),
        "찾은 여정 수": len(run.itinerary_ids),
        "건너뛴 이유": run.skip_reason if run.skipped else "",
    } for run in search.runs]
    _table(rows, {"실행": _text_col("실행"), "수단": _text_col("수단"), "걷는 속도 배수": _text_col("걷는 속도 배수", right=True),
                  "신호 대기 규칙": _text_col("신호 대기 규칙"), "따릉이 상한": _int_col("따릉이 상한"), "승차 여유(초)": _int_col("승차 여유(초)"),
                  "라운드 수": _int_col("라운드 수"), "D 의 파레토 라벨 수": _int_col("D 의 파레토 라벨 수"),
                  "찾은 여정 수": _int_col("찾은 여정 수"), "건너뛴 이유": _text_col("건너뛴 이유")},
           "탐색 실행 7개의 조건과 결과")
    # 3. 실행 상세
    runs = {run.run.value: run for run in search.runs}
    if runs:
        options = list(runs)
        restore(state, "trace_run", SearchRun.FULL.value)
        if state.get("trace_run") not in options:
            store_value(state, "trace_run", SearchRun.FULL.value if SearchRun.FULL.value in options else options[0])
        st.selectbox("실행", options, key="trace_run", format_func=lambda value: RUN_NAMES[SearchRun(value)],
                     on_change=remember, args=("trace_run",))
        sync_keep(state, "trace_run")
        run = runs[state["trace_run"]]
        if run.skipped:
            st.caption(f"이 실행은 건너뛰었습니다: {run.skip_reason}")
        else:
            _table([{"라운드": item.round, "새 걷기 라벨": item.new_labels, "표시된 정류장": item.marked_stops, "훑은 노선": item.routes_scanned,
                     "가장 이른 D 도착": _clock_or_dash(c0, item.best_d_s)} for item in run.rounds],
                   {"라운드": _int_col("라운드"), "새 걷기 라벨": _int_col("새 걷기 라벨"), "표시된 정류장": _int_col("표시된 정류장"),
                    "훑은 노선": _int_col("훑은 노선"), "가장 이른 D 도착": _text_col("가장 이른 D 도착", right=True)},
                   f"{RUN_NAMES[run.run]}의 라운드")
            labels = []
            for (arrival_s, rides, bikes), itinerary_id in zip(run.d_labels, run.itinerary_ids):
                found = items.get(itinerary_id)
                labels.append({"도착 시각": fmt_clock(c0, arrival_s), "탑승 수": rides, "따릉이 수": bikes,
                               "여정": found.label if found is not None else DISCARDED_NAME})
            if labels:
                _table(labels, {"도착 시각": _text_col("도착 시각", right=True), "탑승 수": _int_col("탑승 수"),
                                "따릉이 수": _int_col("따릉이 수"), "여정": _text_col("여정")},
                       f"{RUN_NAMES[run.run]}의 D 파레토 라벨")
            else:
                st.caption("이 실행은 도착지에 닿는 라벨을 찾지 못했습니다.")
    # 4. 노선별 차량
    st.markdown("**노선별 차량**")
    line_rows = []
    for times in output.line_times:
        if times.mode == TravelMode.BUS:
            counts = {source: sum(1 for value in times.run_source if value == source) for source in RunTimeSource}
            source_text = f"예측 {counts[RunTimeSource.PREDICTION]}구간 · 설계 속도 {counts[RunTimeSource.DESIGN]}구간"
        else:
            source_text = "-"
        line_rows.append({"노선": times.route_id, "이름": line_name(times.route_id, p.display), "수단": TRAVEL_MODE_NAMES[times.mode],
                          "알려진 차량 수": times.n_known, "합성 차량 수": times.n_synthetic, "구간 운행시간 출처": source_text,
                          "쓸 수 있음": "✓" if times.usable else "✕"})
    if line_rows:
        _table(line_rows, {"노선": _text_col("노선"), "이름": _text_col("이름"), "수단": _text_col("수단"),
                           "알려진 차량 수": _int_col("알려진 차량 수"), "합성 차량 수": _int_col("합성 차량 수"),
                           "구간 운행시간 출처": _text_col("구간 운행시간 출처"), "쓸 수 있음": _text_col("쓸 수 있음")},
               "노선별 차량 시각")
    else:
        st.caption("이번 실행에 쓴 노선이 없습니다.")
    bus = {times.route_id: times for times in output.line_times if times.mode == TravelMode.BUS}
    if bus:
        options = list(bus)
        restore(state, "trace_line", options[0])
        if state.get("trace_line") not in options:
            store_value(state, "trace_line", options[0])
        st.selectbox("노선", options, key="trace_line", format_func=lambda value: f"{value} ({line_name(value, p.display)})",
                     on_change=remember, args=("trace_line",))
        sync_keep(state, "trace_line")
        times = bus[state["trace_line"]]
        names = node_names(p.display)
        line = next((item for item in p.display.bus_lines if item.id == times.route_id), None)
        stops = line.stop_ids if line is not None else ()
        segment_rows = []
        for number, (run_s, source) in enumerate(zip(times.run_s, times.run_source), start=1):
            a = stops[number - 1] if number - 1 < len(stops) else "-"
            b = stops[number] if number < len(stops) else "-"
            segment_rows.append({"구간": number, "정류장 → 정류장": f"{names.get(a, a)} → {names.get(b, b)}", "운행시간": fmt_dur(run_s),
                                 "출처": RUN_TIME_SOURCE_NAMES[source]})
        _table(segment_rows, {"구간": _int_col("구간"), "정류장 → 정류장": _text_col("정류장 → 정류장"),
                              "운행시간": _text_col("운행시간", right=True, help="구간 운행시간 r_i"), "출처": _text_col("출처")},
               f"{times.route_id} 노선의 구간 운행시간")
    # 5. 타원 가지치기
    st.markdown("**탐색 타원 가지치기**")
    pruning = output.pruning
    if pruning is None:
        st.caption("찍은 점을 길에 붙이지 못해 가지치기를 하지 않았습니다.")
        return
    transfer = sum(1 for record in output.pruning_records if record.kept_for_transfer)
    st.markdown(f"유지 {pruning.kept_count} / {pruning.total_count} · d(S, D) {fmt_dist(pruning.d_sd_m)} · "
                f"임계값 {fmt_dist(pruning.threshold_m)} · a {fmt_dist(pruning.a_m)} · b {fmt_dist(pruning.b_m)} · 환승용 유지 {transfer}개")
    st.caption(PRUNING_NOTE)
    names = node_names(p.display)
    types = {node.id: node.node_type for node in (*p.display.nodes, *p.display.bike_stations)}
    types.update({ce.ORIGIN_POINT_ID: NodeType.POINT, ce.DESTINATION_POINT_ID: NodeType.POINT})
    records = sorted(output.pruning_records, key=lambda record: (record.sum_m, record.node_id))
    _table([{"노드": record.node_id, "이름": names.get(record.node_id, record.node_id),
             "종류": NODE_TYPE_NAMES.get(types.get(record.node_id), "-"), "d(S, X)": _meters(record.d_s_m),
             "d(X, D)": _meters(record.d_d_m), "합": _meters(record.sum_m), "임계값": _meters(record.threshold_m),
             "유지": "✓" if record.kept else "✕", "환승용 유지": "✓" if record.kept_for_transfer else ""} for record in records],
           {"노드": _text_col("노드"), "이름": _text_col("이름"), "종류": _text_col("종류"),
            **{name: _text_col(name, right=True) for name in ("d(S, X)", "d(X, D)", "합", "임계값")},
            "유지": _text_col("유지"), "환승용 유지": _text_col("환승용 유지", help="타원 밖이지만 승하차·역 안 노드라 남김")},
           "탐색 타원 가지치기 표(합이 작은 순)")


# --- ⑦ 데이터·기록 ---


def collection_badge(summary: Mapping[str, Any], now: float) -> str:
    """수집 상태(§6.3 ⑦ 탭의 2): 마지막 조회가 조회 주기의 2배 안이면 "수집 중", 아니면 "멈춤 · 마지막 조회 {n}분 전"
    (하루 이상이면 "{d}일 전")."""
    sources = summary.get("sources", [])
    if not sources:
        return "조회 기록 없음"
    period = max(float(item["period_s"]) for item in sources)
    last = max(float(item["last_unix"]) for item in sources)
    if now - last <= 2.0 * period:
        return "수집 중"
    minutes = int(max(0.0, now - last) // 60)
    if minutes >= 1440:
        return f"멈춤 · 마지막 조회 {minutes // 1440}일 전"
    return f"멈춤 · 마지막 조회 {minutes}분 전"


def _failure_text(reasons: Sequence[Sequence[Any]]) -> str:
    return ", ".join(f"{reason} · {int(count):,}회" for reason, count in list(reasons)[:3])


def timetable_rows(scenario: Scenario, folder: Path) -> tuple[list[dict[str, Any]], list[str]]:
    """시나리오 역의 호선마다 (역, 호선, 역코드, 시각표, 출처, 지나는 정차 패턴 수)와 시각표가 없는 역코드."""
    rows, missing = [], []
    for station in sorted(scenario.subway_stations, key=lambda item: item.key):
        for line, _ in station.platforms:
            code = station.line_key(line)
            path = folder / "timetables" / f"{code}.csv"
            found = path.is_file()
            source = "-"
            if found:
                modified = datetime.datetime.fromtimestamp(path.stat().st_mtime, KST).date().isoformat()
                source = f"{path.name} (수정 {modified})"
            elif code not in missing:
                missing.append(code)
            patterns = sum(1 for pattern in scenario.subway_patterns if pattern.line == line and station.key in pattern.station_keys)
            rows.append({"역": station.name, "호선": line, "역코드": code, "시각표": "있음" if found else "없음", "출처": source,
                         "지나는 정차 패턴": patterns})
    return rows, missing


def distance_line(scenario: Scenario, folder: Path) -> str:
    """역간 거리표(§6.3 ⑦ 탭의 3): 데이터 폴더의 `subway_distances.csv` 가 있으면 "있음 · 확인된 구간 {n} / {전체}"."""
    if not (folder / "subway_distances.csv").is_file():
        return "역간 거리: 없음(직선거리로 둠)"
    segments: dict[tuple[str, str], bool] = {}
    for pattern in scenario.subway_patterns:
        for index, verified in enumerate(pattern.distance_verified):
            key = (pattern.line, *sorted((pattern.station_keys[index], pattern.station_keys[index + 1])))
            segments[key] = segments.get(key, False) or bool(verified)
    return f"역간 거리: 있음 · 확인된 구간 {sum(segments.values())} / {len(segments)}"


def render_data_tab(p: Prepared, output: EngineOutput, tokens: Mapping[str, str]) -> None:
    ctx = p.ctx
    config = EngineConfig()
    # 1. 이번 계산의 원천
    st.markdown(f"**데이터 모드 {MODE_NAMES[p.mode]} · 기준 시각 {fmt_clock(output.clock_s, 0.0)}**")
    if p.mode == DataMode.SIMULATION.value:
        st.caption(f"시나리오에 적힌 값으로 계산했습니다. {p.scenario.simulated_time_note}")
    else:
        reference = _reference_date(output.sources)
        rows = [{"원천": SOURCE_NAMES[item.source], "대상": item.target, "상태": f"{_SOURCE_SYMBOLS[item.state]} {SOURCE_STATE_NAMES[item.state]}",
                 "관측 시각": _source_clock(item.observed_at, reference), "받은 수": item.fetched_count, "연결 수": item.matched_count,
                 "시도 수": item.attempts, "사유": item.reason} for item in output.sources]
        if rows:
            _table(rows, {"원천": _text_col("원천"), "대상": _text_col("대상"), "상태": _text_col("상태"),
                          "관측 시각": _text_col("관측 시각", right=True, help="다른 날의 시각(지하철 시각표 파일의 수정 시각 등)은 날짜를 붙입니다"),
                          "받은 수": _int_col("받은 수"), "연결 수": _int_col("연결 수"),
                          "시도 수": _int_col("시도 수"), "사유": _text_col("사유")},
                   "이번 계산에 쓴 원천의 상태")
        else:
            st.caption("이번 계산에 쓴 원천이 없습니다.")
    # 2. 기록 저장소와 수집
    st.markdown("**기록 저장소와 수집**")
    summary = ctx.summary
    if summary is None:
        st.info(STORE_MISSING_TEXT)
    else:
        size = f"{_fixed(int(summary['size_bytes']) / 1_000_000.0, 1)} MB"
        st.html('<div class="mr-chiprow">' + chip_html(collection_badge(summary, time.time())) + chip_html(f"{ctx.store_path.name} · {size}")
                + "</div>")
        rows = [{"원천": SOURCE_NAMES.get(SourceKind(item["source"]), item["source"]) if item["source"] in SourceKind.__members__ else item["source"],
                 "대상 수": int(item["targets"]), "조회 수": int(item["polls"]), "성공률": fmt_pct(float(item["success_rate"])),
                 "첫 조회": _kst_datetime(item["first_unix"]) if item["polls"] else "-",
                 "마지막 조회": _kst_datetime(item["last_unix"]) if item["polls"] else "-",
                 "조회 주기": fmt_dur(float(item["period_s"])) if item["polls"] else "-",
                 "실패 사유": _failure_text(item.get("failure_reasons") or ())} for item in summary.get("sources", [])]
        if rows:
            _table(rows, {"원천": _text_col("원천"), "대상 수": _int_col("대상 수"), "조회 수": _int_col("조회 수"),
                          "성공률": _text_col("성공률", right=True), "첫 조회": _text_col("첫 조회", right=True),
                          "마지막 조회": _text_col("마지막 조회", right=True), "조회 주기": _text_col("조회 주기", right=True),
                          "실패 사유": _text_col("실패 사유", help="많은 순 3개")},
                   "기록 저장소의 원천별 조회")
        windows = sorted(summary.get("windows", []), key=lambda item: (item["first_unix"], item["date"], item["window"]), reverse=True)
        st.markdown("시연 시간대별 기록")
        if windows:
            _table([{"날짜": fmt_date(item["date"]), "시간대": item["window"], "조회 수": int(item["polls"]),
                     "성공률": fmt_pct(float(item["success_rate"]))} for item in windows],
                   {"날짜": _text_col("날짜"), "시간대": _text_col("시간대"), "조회 수": _int_col("조회 수"),
                    "성공률": _text_col("성공률", right=True)},
                   "시연 시간대별 기록")
        else:
            st.caption("시연 시간대에 모은 기록이 없습니다.")
    # 3. 지하철 시각표와 역간 거리
    st.markdown("**지하철 시각표와 역간 거리**")
    rows, missing = timetable_rows(p.display, ctx.folder)
    if rows:
        _table(rows, {"역": _text_col("역"), "호선": _text_col("호선"), "역코드": _text_col("역코드"), "시각표": _text_col("시각표"),
                      "출처": _text_col("출처"), "지나는 정차 패턴": _int_col("지나는 정차 패턴")},
               "시나리오 역의 시각표")
        if missing:
            st.caption(f"시각표 받기: `python core_engine.py --fetch-timetable {' '.join(missing)}`")
        st.caption(distance_line(p.display, ctx.folder))
    else:
        st.caption("이 시나리오에는 지하철역이 없습니다.")
    # 4. 학습 모델
    st.markdown("**학습 모델**")
    summaries = tuple(ctx.models.summaries) if ctx.models is not None else ()
    if summaries:
        _table([{"종류": MODEL_KIND_NAMES.get(item.kind, item.kind), "만든 시각": _iso_datetime(item.created_at), "기간": item.period or "-",
                 "대상 수": item.targets, "행 수": item.rows, "요약": " · ".join(item.notes)} for item in summaries],
               {"종류": _text_col("종류"), "만든 시각": _text_col("만든 시각", right=True), "기간": _text_col("기간"),
                "대상 수": _int_col("대상 수"), "행 수": _int_col("행 수"), "요약": _text_col("요약")},
               "학습 모델 요약")
    else:
        st.info(MODELS_MISSING_TEXT)
    # 5. 키
    st.markdown("**키**")
    chips = "".join(chip_html(f"{name} 키 {'감지됨' if ctx.keys.get(env) else '없음'}")
                    for name, env in (("열린데이터광장", config.env_seoul_key), ("공공데이터포털", config.env_data_go_kr_key),
                                      ("카카오", config.env_kakao_key), ("서울 신호", config.env_tdata_key)))
    st.html(f'<div class="mr-chiprow">{chips}</div>')
    st.caption(KEYS_NOTE)


# --- 탭 묶음 ---


def render_tabs(p: Prepared, output: EngineOutput, selected_id: str | None, tokens: Mapping[str, str]) -> None:
    """탭 7개(§6.3). SNAP_FAILED 면 ① ~ ⑤ 는 "계산된 여정이 없습니다.", ⑥ 은 붙이지 못한 안내, NO_ROUTE 면 ① ~ ⑤ 만 비운다."""
    tabs = st.tabs(TAB_NAMES, key="tabs", on_change="rerun")
    selected = _items(output).get(selected_id) if selected_id else None
    if selected is None or output.status == EngineStatus.SNAP_FAILED:
        for tab in tabs[:5]:
            with tab:
                st.info(NO_ITINERARY_TEXT)
    else:
        with tabs[0]:
            render_compare_tab(p, output, selected, tokens)
        with tabs[1]:
            render_boarding_tab(p, output, selected, tokens)
        with tabs[2]:
            render_signal_tab(p, output, selected)
        with tabs[3]:
            render_bike_tab(p, output, selected, tokens)
        with tabs[4]:
            render_fare_tab(p, output, selected)
    with tabs[5]:
        if output.status == EngineStatus.SNAP_FAILED:
            st.info(SNAP_FAILED_SEARCH_TEXT)
        else:
            render_search_tab(p, output, tokens)
    with tabs[6]:
        render_data_tab(p, output, tokens)


# ===== U8. main, 실행기, 화면 검사 =====


def render_map(p: Prepared, output: EngineOutput | None, selected_id: str | None, tokens: Mapping[str, str],
               simple: bool = False) -> bool:
    """지도, 범례, 지도 출처(§6.3). 지도를 눌러 출발이나 목적지가 바뀌면 참(부른 쪽이 한 번 다시 실행한다, §8.3)."""
    state = st.session_state
    if simple:  # 간단히 보기(§6.9): 추천 경로만, 카카오 비교선과 범례 없이
        kakao = None
        fmap = build_simple_map(p.display, output, selected_id, pick=p.pick, tokens=tokens)
    else:
        kakao = (state.get("kakao_results") or {}).get((p.scenario_id, selected_id)) if selected_id else None
        fmap = build_map(p.display, output, selected_id, kakao=kakao, pick=p.pick, tokens=tokens)
    returned = ["last_clicked"] if p.pick is not None else []
    result = st_folium(fmap, key="map", height=SIMPLE_MAP_HEIGHT_PX if simple else 480, use_container_width=True,
                       returned_objects=returned)
    if not simple:
        st.html(legend_html(tokens, kakao=bool(kakao)))
    st.caption((MAP_SIMPLE_NOTE if simple else "") + MAP_NOTE + (KAKAO_NOTE if kakao else ""))
    if p.pick is None or not isinstance(result, Mapping):
        return False
    return apply_map_click(state, result.get("last_clicked"))


def _on_view_detail() -> None:
    st.session_state["view_mode"] = "DETAIL"
    drop_keys(st.session_state, ("guide",))  # 안내는 간단히 보기에서만(§6.10)


def render_view_switch() -> None:
    state = st.session_state
    _required_guard(state, "view_mode", list(VIEW_NAMES), "SIMPLE")
    st.segmented_control(VIEW_LABEL, list(VIEW_NAMES), key="view_mode", required=True, format_func=VIEW_NAMES.get,
                         label_visibility="collapsed")


def _on_pick(itinerary_id: str) -> None:
    """다른 경로 줄과 "추천 경로로 돌아가기"의 콜백(§6.9 보는 경로)."""
    store_value(st.session_state, "selected_id", itinerary_id)


def compare_htmls(output: EngineOutput, scenario: Scenario | None, shown_id: str | None = None) -> list[str]:
    """경로 비교 표가 그리는 HTML 차례(머리, 줄들, 기존 방식 가정 문장). 그리지 않으면 빈 목록. 검사가 화면과 맞춰 본다."""
    rows = compare_rows(output, scenario, shown_id)
    if len(rows) < 2 and not any(row.notes for row in rows):
        return []
    foot = [f'<div class="mr-cmp-foot">{esc(NAIVE_EASY_NOTE)}</div>'] if any(row.naive for row in rows) else []
    return [COMPARE_HEAD_HTML, *(compare_row_html(row) for row in rows), *foot]


def render_simple_alternatives(output: EngineOutput, scenario: Scenario, shown_id: str | None, *, picks: bool = True) -> None:
    """경로 비교 표(§6.9, 32단계). 지금 보는 줄과 걸러진 줄에는 단추가 없다. 안내 중에는 단추를 두지 않는다(`picks`)."""
    rows = compare_rows(output, scenario, shown_id)
    if len(rows) < 2 and not any(row.notes for row in rows):
        return
    with st.container(key="mr_alts"):
        st.html(COMPARE_HEAD_HTML)
        for n, row in enumerate(rows, start=1):
            st.html(compare_row_html(row))
            if picks and not row.shown and row.pickable:
                st.button(BACK_TO_BEST_LABEL if row.recommended else ALT_PICK_LABEL, key=f"alt_pick_{n}", type="secondary",
                          on_click=_on_pick, args=(row.itinerary_id,))
        if any(row.naive for row in rows):
            st.html(f'<div class="mr-cmp-foot">{esc(NAIVE_EASY_NOTE)}</div>')


def fast_run(p: Prepared) -> EngineOutput | None:
    """빠른 걸음 결과(28단계): 화면과 같은 입력을 걷는 속도만 "빠르게" 로 바꿔 `cached_run` 으로 계산한다.
    이미 그보다 빠르게 걷는 설정이거나 결과가 없으면 None."""
    if p.config is None or p.query is None:
        return None
    config = fast_config(p.config)
    if config is None:
        return None
    output_json, _ = cached_run(p.base_json, p.shifted_json, p.dt_s, p.query.model_dump_json(), config.model_dump_json(),
                                p.sources_json)
    return output_object(output_json) if output_json else None


def guide_needs_fast(output: EngineOutput, guide: Mapping[str, Any]) -> bool:
    """안내 카드가 빠른 걸음 판정을 쓸 수 있나(28단계): 따라가는 경로의 다음 탑승에서 지켜볼 차의 탈 확률이 p_safe 미만일 때만."""
    follow = guide_match(output, guide["plan"], int(guide.get("k", 0)), bool(guide.get("on")), bool(guide.get("bike")))
    if follow is None:
        return False
    index = _next_ride(follow)
    boarding = _boardings(follow).get(index) if index is not None else None
    if boarding is None:
        return False
    option = _vehicle(boarding, guide.get("kept") or boarding.guided_trip_id)
    return option is not None and option.p_catch < output.config.p_safe


def render_simple(p: Prepared, output: EngineOutput | None, moved: Query | None, slots: Mapping[str, Any],
                  tokens: Mapping[str, str]) -> bool:
    state = st.session_state
    ok = output is not None and output.status == EngineStatus.OK
    shown_id = None
    if ok and output.itineraries:
        shown_id = adjust_selection(state, output)
        if output.comparison.best_id is None:  # 모든 여정이 걸러짐: 답 카드 대신 상태 카드, 지도는 출발·도착만
            shown_id = None
        elif shown_id not in _items(output):
            shown_id = output.comparison.best_id
    guide = state.get("guide")
    status = None
    fast_cache: list[EngineOutput | None] = []

    def fast_output() -> EngineOutput | None:  # 빠른 걸음 결과(28단계): 판정이 필요할 때 한 번만 계산한다
        if not fast_cache:
            fast_cache.append(fast_run(p))
        return fast_cache[0]

    if ok and isinstance(guide, MutableMapping):  # 안내 중(§6.10): 따라가는 경로를 보이고, 지켜볼 차를 새로 정한다
        status = guide_status(output, p.display, guide, fast_output() if guide_needs_fast(output, guide) else None)
        guide["kept"] = status.kept
        if status.follow_id is not None:
            shown_id = status.follow_id
    if isinstance(guide, Mapping) and status is None:  # 안내 중인데 답이 없으면 끝내기만
        with slots["guide"]:
            st.button(GUIDE_STOP_LABEL, key="guide_stop", width="stretch", on_click=_on_guide_stop)
            guide_timer()
    slots["trip"].html(trip_html(_origin_display(p, state, output, moved, simple=True), _dest_display(p, state, simple=True)))
    clicked = False
    walk_drawn = False

    def walk_control() -> None:  # 내 걸음 빠르기(22단계)와 타는 것(24단계): 답 카드 바로 아래, 답이 없어도 그린다
        nonlocal walk_drawn
        with st.container(key="mr_walk"):
            sidebar_walk(WALK_EASY_LABEL)
            sidebar_mode_toggles(MODES_EASY_LABEL)
        walk_drawn = True

    with slots["answer"]:
        if output is None or p.config is None:
            if p.block:
                st.info(p.block)
        elif output.status == EngineStatus.SNAP_FAILED:
            st.html(f'<div class="mr-state ghost">{esc(snap_failed_text(snap_distance(p, output), p.config))}</div>')
        elif output.status == EngineStatus.NO_ROUTE:
            st.html(f'<div class="mr-state">{esc(no_route_text(output))}</div>')
        else:
            best_id = output.comparison.best_id
            leave = None
            if status is not None:
                with slots["guide"]:
                    render_guide(p, output, status)
            elif best_id is not None and shown_id == best_id and output.query.origin.kind in LEAVE_ORIGIN_KINDS:
                runs = leave_runs(p)  # 마감이 있으면 마감 여유(23단계), 없으면 출발 여유(19단계)
                leave = (easy_deadline_leave(output, runs, p.display) if output.query.deadline_s is not None
                         else easy_leave(output, runs))
            st.html(easy_answer_html(output, p.display, shown_id, leave))
            if status is None and best_id is not None and shown_id != best_id:
                st.button(BACK_TO_BEST_LABEL, key="pick_best", on_click=_on_pick, args=(best_id,), width="stretch")
            if status is None and shown_id is not None and _items(output)[shown_id].status == RouteStatus.RANKED:
                render_guide_start(p, _items(output)[shown_id])
            # 33단계: 경로 비교 표는 답 카드(안내 시작) 바로 아래. 기존 앱 1위의 설명은 그 줄에 붙는다.
            # 안내 중에는 바꾸기를 안내 카드가 한다(§6.10)
            if ok:
                render_simple_alternatives(output, p.display, shown_id, picks=status is None)
            walk_control()
            if best_id is not None and shown_id is not None:
                shown = _items(output)[shown_id]
                need = any(b.p_conditional < output.config.p_safe for b in shown.boardings if b.guided_trip_id)
                fast = fast_map(shown, output, fast_output()) if need else None
                st.html(easy_steps_html(shown, output, p.display, fast))
        if not walk_drawn:
            walk_control()
    with slots["side"]:
        clicked = render_map(p, output, shown_id, tokens, simple=True)
    st.button(DETAIL_BUTTON_LABEL, key="view_detail", on_click=_on_view_detail, width="stretch")
    if output is not None and output.warnings:
        st.caption(WARNINGS_EASY_TEXT.format(n=len(output.warnings)))
    return clicked


# --- 실제 기록 장면 (§6.11, 29단계) ---
#
# 데이터 폴더의 `demo_scenes.json` 이 고른 시각들(기록 일괄 재생에서 효과가 잘 드러난 실제 장면)을 소개 페이지(§6.12, 34단계)의
# 단추로 보인다(29~33단계는 간단히 보기 위쪽의 알약). 누르면 그 시나리오, 기록 재생, 그 날짜와 시각으로 바꾼다. 계산은 기록 재생 그대로다(새 규칙 없음).

DEMO_SCENES_FILE = "demo_scenes.json"


@dataclasses.dataclass(frozen=True)
class DemoScene:
    at_unix: int
    name: str
    scenario_id: str

    @property
    def moment(self) -> datetime.datetime:
        return datetime.datetime.fromtimestamp(self.at_unix, KST)

    @property
    def label(self) -> str:
        """단추 글자: "11/21(토) 11:40 대표 장면"."""
        m = self.moment
        return f"{m.month}/{m.day}({_WEEKDAYS_KO[m.weekday()]}) {m:%H:%M} {self.name}"


def load_scenes(folder: Path) -> tuple[DemoScene, ...]:
    """`demo_scenes.json` 의 장면(§6.11). 파일이 없거나 읽지 못하면 빈 튜플, 형식이 틀린 항목은 건너뛴다.
    각 항목은 "at" ("YYYY-MM-DD HH:MM:SS", 한국 시각), "name", "scenario" (시나리오 ID)."""
    path = folder / DEMO_SCENES_FILE
    try:
        items = json.loads(path.read_text(encoding="utf-8"))["scenes"]
    except (OSError, ValueError, KeyError, TypeError):
        return ()
    scenes = []
    for item in items if isinstance(items, list) else []:
        try:
            moment = datetime.datetime.strptime(str(item["at"]), "%Y-%m-%d %H:%M:%S").replace(tzinfo=KST)
            name, scenario_id = str(item["name"]).strip(), str(item["scenario"])
        except (KeyError, TypeError, ValueError):
            continue
        if name and scenario_id:
            scenes.append(DemoScene(int(moment.timestamp()), name, scenario_id))
    return tuple(scenes)


def scene_choices(ctx: DataContext) -> tuple[DemoScene, ...]:
    """보일 장면(§6.11): 기록이 있고, 시나리오가 목록에 있고, 날짜가 기록 날짜 안에 있는 것."""
    if not ctx.has_records:
        return ()
    ids = {entry_id for entry_id, _, _ in ctx.entries}
    dates = {str(item[0]) for item in (ctx.summary or {}).get("dates", [])}
    return tuple(scene for scene in load_scenes(ctx.folder)
                 if scene.scenario_id in ids and scene.moment.date().isoformat() in dates)


def scene_apply(state: MutableMapping[str, Any], scene: DemoScene) -> None:
    """장면 단추(§6.11): 시나리오를 바꿀 때처럼 질의 키와 안내를 지우고, 기록 재생과 그 날짜·시각, 출발 늦추기 0 으로 둔다."""
    drop_keys(state, (*QUERY_KEYS, "guide"))
    state["kakao_results"] = {}
    store_value(state, "scenario_id", scene.scenario_id)
    store_value(state, "data_mode", DataMode.REPLAY.value)
    store_value(state, "replay_date", scene.moment.date())
    store_value(state, "replay_time", scene.moment.time().replace(tzinfo=None))
    store_value(state, "depart_offset_s", 0)

# --- 소개 페이지 (§6.12, 34단계) ---
#
# 첫 화면은 내려 보며 읽는 소개 페이지다. 실제 기록 장면 단추는 길찾기 화면에서 빼고 여기에 둔다(실제로 쓰는 화면에는 길찾기만).
# "길찾기 시작" 이나 장면 단추를 누르면 길찾기 화면으로 간다. 주소에 `?page=app` 이 있으면 소개를 건너뛴다.
# 숫자와 장면 시각은 기획안 6절과 같은 값이다(실제 수집 기록 재생, `reports/` 의 근거). 새 계산은 없다.

PAGE_KEY = "mr_page"
PAGE_INTRO, PAGE_APP = "intro", "app"
INTRO_START = "길찾기 시작"
INTRO_BACK = "소개"
INTRO_SCENES_HEAD = "실제 기록으로 직접 보기"
INTRO_SCENES_NOTE = "누르면 길찾기 화면이 그 날짜와 시각의 실제 수집 기록으로 열립니다."
# 대표 장면(기획안 6절 표 첫 줄): 토 16:13, 2호선을 타고 가는 중에 출발
INTRO_SCENE_ROWS: tuple[tuple[str, str, str, int, str], ...] = (
    ("기존 앱 1위 안내", "16:23 도착", "muted", 10, "2호선 → 345번 → 143번"),
    ("그대로 따라가면 실제로", "16:41 도착 · 18분 늦음", "ghost", 28, "345번과 143번이 도착 예측보다 늦게 옴"),
    ("이 앱의 추천", "16:28 도착 · 13분 빠름", "safe", 15, "버스·지하철만으로"),
)
INTRO_SCENE_SPAN_MIN = 30
INTRO_STATS: tuple[tuple[str, str, str], ...] = (
    ("46~57%", "기존 앱 1위가 놓치기 쉬운 환승을 끼고 있던 출발의 비율",
     "강남역 → 신사역, 금·토 네 시간대, 1분마다 출발을 실제 기록으로 재생(신분당선 포함)"),
    ("최대 21분", "기존 앱 1위를 따라갔을 때 안내보다 늦게 도착한 시간",
     "토 11:40 강남역 → 신사역. 논현역에서 갈아탈 140번을 놓침. 이 앱의 추천은 11:53 도착"),
    ("94%", "이 앱이 탈 확률 80% 이상이라 계산한 환승을 실제로 탄 비율",
     "실측 추적 3,000회 중 2,392건, 금 20:35~자정"),
    ("24번", "카카오맵 1위 길을 같은 분의 실제 기록으로 따라간 59번 중 안내보다 2분 넘게 늦은 횟수",
     "일 09:00~13:30, 10분마다 카카오맵에서 조회(버스 길은 최대 10분 늦음)"),
)
INTRO_FEATURES: tuple[tuple[str, str, str], ...] = (
    ("filter_alt", "놓치기 쉬운 환승을 미리 걸러요",
     "걸음 차이, 신호 대기, 버스가 일찍 오는 오차로 환승마다 탈 확률을 계산합니다. 놓치면 다음 차를 기다리는 시간까지 넣어 실제로 언제 도착하는지로 길을 고릅니다."),
    ("schedule", "몇 시 도착, 늦어도 몇 시",
     "답 카드에 걸리는 시간과 도착 시각, 늦어도 도착하는 시각, 지금 할 일을 먼저 보여 줍니다. 여유 있음, 빠듯함, 놓치기 쉬움 세 단계로 알려 줍니다."),
    ("compare_arrows", "기존 앱 1위와 나란히 비교",
     "경로 비교 표에서 기존 길찾기 앱이 1위로 안내하는 경로와 이 앱의 추천을 같은 칸에 놓고, 안내 도착과 실제 계산 도착을 함께 보여 줍니다."),
    ("directions_subway", "지금 서 있는 곳, 타고 가는 차에서",
     "휴대폰 위치에서, 또는 이미 탄 지하철에서 출발할 수 있습니다. 안내 모드는 1분마다 다시 계산해 환승이 위험해지면 알려 줍니다."),
)
INTRO_STEPS: tuple[tuple[str, str], ...] = (
    ("지금 상태", "서 있는 곳이나 타고 있는 지하철·버스에서 출발"),
    ("조합 찾기", "내릴 곳, 수단(도보·버스·지하철·따릉이), 탈 차의 조합"),
    ("확률 계산", "걸음 차이, 신호, 버스 도착 오차로 차마다 탈 확률과 도착 분포"),
    ("쉬운 답", "몇 분 걸려 몇 시 도착, 지금 할 일, 기존 앱 1위와 비교"),
)
INTRO_SOURCES = ("데이터: 서울 열린데이터광장(버스·지하철·따릉이·신호), 공공데이터포털, © OpenStreetMap 기여자(ODbL). "
                 "개발에 생성형 AI(Claude)를 썼고, 앱 실행 중에는 부르지 않습니다.")


# 소개 페이지를 그리는 실행에서는 길찾기 위젯이 없어 Streamlit 이 그 값을 지운다. 값 위젯의 키를 자기 값으로 다시 넣어 남긴다
# (단추, 접힘, 지도 같은 값을 넣을 수 없는 위젯은 넣지 않는다).
INTRO_KEEP_KEYS: tuple[str, ...] = (
    "scenario_id", "data_mode", "view_mode", "depart_offset_s", "origin_kind", "origin_place", "train_station", "train_key",
    "bus_line", "bus_stop_index", "bus_vehicle", "prior_km", "dest_kind", "dest_place", "map_pick", "use_deadline",
    "deadline_time", "selected_id", "replay_window", "replay_date", "replay_time", "use_bus", "use_subway", "use_bike",
    "full_skip", "show_variants", "walk_preset", "v_walk", "v_pm", "weight_preset", "w_time", "w_cost", "w_risk",
    "rank_criterion", "safety_buffer", "gamma", "max_rides", "max_bike_legs", "trace_run", "trace_line",
)


def keep_for_intro(state: MutableMapping[str, Any]) -> None:
    for key in INTRO_KEEP_KEYS:
        if key in state:
            state[key] = state[key]


def current_page(state: MutableMapping[str, Any]) -> str:
    """보일 페이지(§6.12): 안내 중이거나 자세히 보기면 길찾기, 주소의 `page=app` 이면 길찾기, 아니면 상태(처음은 소개)."""
    if isinstance(state.get("guide"), Mapping) or state.get("view_mode") == "DETAIL":
        state[PAGE_KEY] = PAGE_APP
    elif PAGE_KEY not in state:
        try:
            wanted = st.query_params.get("page")
        except Exception:  # noqa: BLE001 - 실행 맥락 밖
            wanted = None
        state[PAGE_KEY] = PAGE_APP if wanted == PAGE_APP else PAGE_INTRO
    return PAGE_APP if state.get(PAGE_KEY) == PAGE_APP else PAGE_INTRO


def _go_app() -> None:
    st.session_state[PAGE_KEY] = PAGE_APP


def _go_intro() -> None:
    st.session_state[PAGE_KEY] = PAGE_INTRO


def _intro_scene(index: int) -> None:
    """소개의 장면 단추: 그 장면을 적용하고 길찾기 화면으로 간다."""
    scenes = load_scenes(data_folder())
    if 0 <= index < len(scenes):
        scene_apply(st.session_state, scenes[index])
    st.session_state[PAGE_KEY] = PAGE_APP


def intro_css() -> str:
    return """<style>
[data-testid="stMainBlockContainer"] { max-width: 1040px; margin-left: auto; margin-right: auto; }
.mr-lp-hero { padding: 0 0 8px; }
.mr-lp-eyebrow { font-size: 0.85rem; font-weight: 600; color: var(--mr-safe); letter-spacing: 0.02em; margin-bottom: 10px; }
.mr-lp-hero h1 { font-size: clamp(2rem, 6vw, 3.2rem); line-height: 1.2; font-weight: 800; margin: 0 0 14px; padding: 0; word-break: keep-all; }
.mr-lp-lead { font-size: clamp(1.05rem, 2.6vw, 1.3rem); line-height: 1.6; color: var(--mr-ink2); max-width: 720px; word-break: keep-all; margin: 0; }
.mr-lp-sec { padding: 40px 0 6px; }
.mr-lp-kicker { font-size: 0.85rem; font-weight: 600; color: var(--mr-muted); margin-bottom: 6px; }
.mr-lp-sec h2 { font-size: clamp(1.4rem, 3.6vw, 2rem); line-height: 1.3; font-weight: 750; margin: 0 0 10px; padding: 0; word-break: keep-all; }
.mr-lp-p { font-size: 1rem; line-height: 1.65; color: var(--mr-ink2); max-width: 760px; word-break: keep-all; margin: 0 0 14px; }
.mr-lp-card { border: 1px solid var(--mr-border); border-radius: 14px; padding: 20px 20px 14px; }
.mr-lp-row { margin-bottom: 16px; }
.mr-lp-rowhead { display: flex; justify-content: space-between; gap: 12px; flex-wrap: wrap; font-size: 0.95rem; margin-bottom: 6px; }
.mr-lp-rowhead b { font-weight: 650; }
.mr-lp-rowhead span { font-variant-numeric: tabular-nums; font-weight: 650; }
.mr-lp-track { position: relative; height: 14px; border-radius: 7px; background: var(--mr-grid); overflow: hidden; }
.mr-lp-fill { position: absolute; left: 0; top: 0; bottom: 0; border-radius: 7px; }
.mr-lp-sub { font-size: 0.85rem; color: var(--mr-muted); margin-top: 4px; }
.mr-lp-axis { display: flex; justify-content: space-between; font-size: 0.8rem; color: var(--mr-muted); font-variant-numeric: tabular-nums; margin-top: 4px; }
.mr-lp-grid { display: grid; grid-template-columns: repeat(auto-fit, minmax(210px, 1fr)); gap: 14px; }
.mr-lp-stat b { display: block; font-size: clamp(2rem, 5vw, 2.6rem); line-height: 1.1; font-weight: 800; font-variant-numeric: tabular-nums; margin-bottom: 8px; }
.mr-lp-stat div { font-size: 0.98rem; line-height: 1.5; word-break: keep-all; }
.mr-lp-stat small { display: block; font-size: 0.82rem; line-height: 1.45; color: var(--mr-muted); margin-top: 8px; word-break: keep-all; }
.mr-lp-feat .mr-lp-icon { font-family: 'Material Symbols Rounded'; font-weight: normal; font-style: normal; line-height: 1; font-size: 28px; color: var(--mr-safe); }
.mr-lp-feat h3 { font-size: 1.1rem; font-weight: 700; margin: 6px 0 6px; padding: 0; word-break: keep-all; }
.mr-lp-feat p { font-size: 0.95rem; line-height: 1.6; color: var(--mr-ink2); margin: 0 0 6px; word-break: keep-all; }
.mr-lp-steps { display: grid; grid-template-columns: repeat(auto-fit, minmax(190px, 1fr)); gap: 12px; counter-reset: mrstep; }
.mr-lp-step { border-left: 3px solid var(--mr-safe); padding: 4px 0 4px 14px; }
.mr-lp-step b { display: block; font-size: 1rem; margin-bottom: 4px; }
.mr-lp-step b::before { counter-increment: mrstep; content: counter(mrstep) ". "; color: var(--mr-safe); }
.mr-lp-step span { font-size: 0.92rem; line-height: 1.55; color: var(--mr-ink2); word-break: keep-all; }
.mr-lp-foot { font-size: 0.85rem; line-height: 1.6; color: var(--mr-muted); word-break: keep-all; }
.st-key-mr_intro_scenes button { width: 100%; justify-content: flex-start; text-align: left; min-height: 3rem; }
.st-key-intro_start button, .st-key-intro_start2 button { min-height: 3rem; padding-left: 28px; padding-right: 28px; font-size: 1.05rem;
  background: var(--mr-ink); border-color: var(--mr-ink); color: var(--mr-bg); }
.st-key-intro_start button:hover, .st-key-intro_start2 button:hover { background: var(--mr-ink2); border-color: var(--mr-ink2); color: var(--mr-bg); }
.st-key-intro_start button p, .st-key-intro_start2 button p, .st-key-intro_start button span, .st-key-intro_start2 button span { color: var(--mr-bg); }
</style>"""


def intro_scene_html() -> str:
    rows = []
    for name, when, color, minutes, sub in INTRO_SCENE_ROWS:
        width = 100.0 * minutes / INTRO_SCENE_SPAN_MIN
        rows.append(f'<div class="mr-lp-row"><div class="mr-lp-rowhead"><b>{esc(name)}</b><span>{esc(when)}</span></div>'
                    f'<div class="mr-lp-track"><div class="mr-lp-fill" style="width:{width:.1f}%;background:var(--mr-{color})"></div></div>'
                    f'<div class="mr-lp-sub">{esc(sub)}</div></div>')
    return (f'<div class="mr-lp-card">{"".join(rows)}'
            '<div class="mr-lp-axis"><span>16:13 출발</span><span>16:28</span><span>16:43</span></div></div>')


def render_intro(ctx: DataContext) -> None:
    """소개 페이지(§6.12): 내려 보며 읽는 한 장. 장면 단추는 기록이 있을 때만."""
    keep_for_intro(st.session_state)
    st.html(intro_css())
    st.html('<div class="mr-lp"><div class="mr-lp-hero">'
            '<div class="mr-lp-eyebrow">서울 대중교통 · 실제 수집 기록으로 확인</div>'
            f'<h1>{esc(APP_TITLE)}</h1>'
            '<p class="mr-lp-lead">지도 앱이 “탈 수 있다”고 한 그 차, 실제로는 놓치기 쉽습니다. '
            '환승마다 탈 확률을 계산해 지금 출발하면 실제로 가장 빨리 도착하는 길을 찾아 줍니다.</p></div></div>')
    st.button(INTRO_START, key="intro_start", type="primary", icon=":material/arrow_forward:", on_click=_go_app)
    st.html('<div class="mr-lp"><div class="mr-lp-sec"><div class="mr-lp-kicker">같은 순간, 두 안내</div>'
            '<h2>화면에서 가장 빠른 길이 실제로는 가장 늦어집니다</h2>'
            '<p class="mr-lp-p">토요일 16:13, 2호선을 타고 가는 중에 출발한 실제 장면입니다. 기존 길찾기 방식은 그 순간의 도착 예측, 보통 걸음(1.25 m/s), '
            '신호 대기 0으로 계산해 “탈 수 있다”고 안내합니다. 실제로는 버스가 예측보다 일찍 오거나 늦게 오고, 걸음이 느리거나 신호에 걸립니다. '
            '이 장면에서는 345번과 143번이 예측보다 늦게 와서 안내보다 18분 늦었습니다. 이 앱은 수집한 기록으로 실제 도착을 계산해 다른 길을 고릅니다.</p>'
            f'{intro_scene_html()}</div>'
            '<div class="mr-lp-sec"><div class="mr-lp-kicker">실제 기록으로 확인한 숫자</div>'
            '<h2>강남·삼성 일대 버스 6개 노선, 따릉이, 신호를 금·토요일에 수집해 다시 계산했습니다</h2>'
            '<div class="mr-lp-grid">'
            + "".join(f'<div class="mr-lp-card mr-lp-stat"><b>{esc(big)}</b><div>{esc(what)}</div><small>{esc(basis)}</small></div>'
                      for big, what, basis in INTRO_STATS)
            + '</div></div>'
            '<div class="mr-lp-sec"><div class="mr-lp-kicker">무엇이 다른가요</div><h2>답부터, 쉬운 말로</h2><div class="mr-lp-grid">'
            + "".join(f'<div class="mr-lp-card mr-lp-feat"><span class="mr-lp-icon" aria-hidden="true">{icon}</span>'
                      f'<h3>{esc(title)}</h3><p>{esc(body)}</p></div>' for icon, title, body in INTRO_FEATURES)
            + '</div></div>'
            '<div class="mr-lp-sec"><div class="mr-lp-kicker">어떻게 계산하나요</div><h2>네 단계로 실제 도착을 계산합니다</h2>'
            '<div class="mr-lp-steps">'
            + "".join(f'<div class="mr-lp-step"><b>{esc(title)}</b><span>{esc(body)}</span></div>' for title, body in INTRO_STEPS)
            + '</div></div></div>')
    choices = scene_choices(ctx)
    if choices:
        all_scenes = load_scenes(ctx.folder)
        st.html(f'<div class="mr-lp"><div class="mr-lp-sec"><div class="mr-lp-kicker">직접 확인</div>'
                f'<h2>{esc(INTRO_SCENES_HEAD)}</h2><p class="mr-lp-p">{esc(INTRO_SCENES_NOTE)}</p></div></div>')
        with st.container(key="mr_intro_scenes"):
            for scene in choices:
                index = all_scenes.index(scene)
                st.button(scene.label, key=f"intro_scene_{index}", icon=":material/play_circle:",
                          on_click=_intro_scene, args=(index,))
    st.html('<div class="mr-lp"><div class="mr-lp-sec"><h2>지금 출발하면, 실제로 언제 도착할까요?</h2></div></div>')
    st.button(INTRO_START, key="intro_start2", type="primary", icon=":material/arrow_forward:", on_click=_go_app)
    st.divider()
    st.html(f'<div class="mr-lp-foot">{esc(INTRO_SOURCES)}</div>')

# --- 안내 모드 (§6.10, 27단계) ---
#
# 간단히 보기에서 "이 경로로 안내 시작"을 누르면 그 경로(따라가는 경로)를 기억하고, 화면이 켜져 있는 동안
# 1분마다 앱 전체를 다시 실행한다. 다시 실행할 때마다 지금의 자료(실시간은 새로 조회, 기록 재생은 기준 시각 + 지난 시간,
# 시뮬레이션은 출발 늦추기 = 지난 시간)와 지금 위치(받았으면)로 엔진을 다시 부르고, 따라가는 경로를 새 결과에서 찾아
# 타려던 차의 탈 확률과 더 빠른 길을 비교한다. 계산은 모두 엔진이 하고, 여기서는 찾고 비교하고 문장을 만든다.

GUIDE_TICK_S = 60  # 다시 계산하는 간격(초)
GUIDE_BETTER_S = 60.0  # 더 빠른 길을 알리는 평균 도착 차이(초)
GUIDE_GONE_P = 0.0005  # 이 아래의 탈 확률은 화면에 0.0% 로 보이므로 "이제 타기 어렵다"로 말한다
GUIDE_GPS_MIN_S = 20  # 위치를 다시 보내는 가장 짧은 간격(초)
GUIDE_GPS_MOVE_M = 25  # 이만큼 움직이면 간격 전에도 보낸다(m)
GUIDE_COMPONENT_NAME = "mr_guide_watch"
GUIDE_COMPONENT_KEY = "guide_watch"
GUIDE_START_LABEL = "이 경로로 안내 시작"
GUIDE_STOP_LABEL = "안내 끝내기"
GUIDE_SWITCH_LABEL = "이 길로 바꾸기"
GUIDE_SKIP_LABEL = "1분 지난 것으로 보기"
GUIDE_BOARD_LABEL = "{vehicle} 탔어요"
GUIDE_ALIGHT_LABEL = "{stop}에서 내렸어요"
GUIDE_SCREEN_NOTE = "안내하는 동안 화면을 켜 두세요. 화면이 켜져 있으면 위치를 받고 1분마다 다시 계산합니다."
GUIDE_DT_BLOCK = "출발 늦추기를 지금으로 두면 이 경로로 안내를 시작할 수 있습니다."
GUIDE_NO_GPS_TEXT = "위치를 받지 못해 마지막 출발점에 그대로 있다고 보고 계산합니다."
GUIDE_ON_VEHICLE_TEXT = "차 안에서는 위치 대신 탄 차의 운행으로 계산합니다."
GUIDE_SKIP_NOTE = "{mode}에서는 단추로 1분씩 시간을 앞당겨 볼 수 있습니다."
GUIDE_TICK_TEXT = "{clock} 기준으로 다시 계산했습니다. 다음 계산은 약 1분 뒤입니다."
GUIDE_START_KINDS = ("PLACE", "POINT")  # 안내를 시작할 수 있는 출발(차량 안 출발은 "탔어요"로 들어간다)
GUIDE_WATCH_HTML = '<div class="mr-gwatch" aria-live="polite"></div>'
# 화면이 켜져 있는 동안 위치를 계속 받고(watchPosition), 화면 꺼짐을 막는다(Screen Wake Lock, 지원하는 브라우저만).
# 다시 그릴 때마다 함수가 다시 불리므로, 마지막으로 보낸 위치와 시각은 window 에 두어 다시 그려도 바로 보내지 않는다.
GUIDE_WATCH_JS = """
export default function (component) {
  const { data, parentElement, setTriggerValue } = component;
  if (!data) {
    return;
  }
  const memo = window.__mrGuideMemo || (window.__mrGuideMemo = { t: 0, lat: null, lon: null });
  let lock = null;
  const takeLock = () => {
    if (!("wakeLock" in navigator) || document.visibilityState !== "visible") {
      return;
    }
    navigator.wakeLock.request("screen").then((sentinel) => { lock = sentinel; }).catch(() => { lock = null; });
  };
  const onVisible = () => { if (document.visibilityState === "visible") { takeLock(); } };
  document.addEventListener("visibilitychange", onVisible);
  takeLock();
  let watch = null;
  if (!window.isSecureContext) {
    if (memo.error !== "INSECURE") { memo.error = "INSECURE"; setTriggerValue("fix", { error: "INSECURE" }); }
  } else if (!("geolocation" in navigator)) {
    if (memo.error !== "UNSUPPORTED") { memo.error = "UNSUPPORTED"; setTriggerValue("fix", { error: "UNSUPPORTED" }); }
  } else {
    watch = navigator.geolocation.watchPosition(
      (position) => {
        const c = position.coords;
        const now = Date.now();
        let moved = Infinity;
        if (memo.lat !== null) {
          const dy = (c.latitude - memo.lat) * 111320;
          const dx = (c.longitude - memo.lon) * 111320 * Math.cos(c.latitude * Math.PI / 180);
          moved = Math.hypot(dx, dy);
        }
        if (now - memo.t < data.min_s * 1000 && moved < data.move_m) {
          return;
        }
        memo.t = now; memo.lat = c.latitude; memo.lon = c.longitude; memo.error = null;
        setTriggerValue("fix", { lat: c.latitude, lon: c.longitude, accuracy: c.accuracy });
      },
      (error) => {
        const codes = { 1: "PERMISSION_DENIED", 2: "POSITION_UNAVAILABLE", 3: "TIMEOUT" };
        const code = codes[error.code] || "POSITION_UNAVAILABLE";
        if (memo.error !== code) { memo.error = code; setTriggerValue("fix", { error: code }); }
      },
      { enableHighAccuracy: true, timeout: data.timeout_ms, maximumAge: 0 },
    );
  }
  return () => {
    if (watch !== null) { navigator.geolocation.clearWatch(watch); }
    document.removeEventListener("visibilitychange", onVisible);
    if (lock) { lock.release().catch(() => {}); }
  };
}
"""


def ride_sig(ride) -> list[Any]:
    """따라가는 경로의 탑승 하나(§6.10): [노선들(묶음이면 묶음의 노선 모두, 정렬), 승차 지점, 하차 지점]. 차량 안 출발의 첫 탑승은 승차 지점이 None."""
    routes = sorted({line.route_id for line in ride.bundle} or {ride.route_id})
    return [routes, ride.board_node_id, ride.alight_node_id]


def guide_plan(it: ItineraryResult) -> list[list[Any]]:
    return [ride_sig(ride) for ride in it.rides]


def _bike_used(it: ItineraryResult) -> bool:
    return any(move.bike is not None for move in it.moves)


def guide_match(output: EngineOutput, plan: Sequence[Sequence[Any]], k: int, on_vehicle: bool,
                bike: bool = False) -> ItineraryResult | None:
    """새 결과에서 따라가는 경로를 찾는다(§6.10). 남은 탑승 plan[k:] 과 여정의 탑승이 차례로 같아야 한다: 노선이 하나라도
    겹치고 하차 지점이 같고 승차 지점이 같다(차량 안이면 첫 탑승의 승차 지점은 보지 않는다). 탑승이 없는 경로는 탑승이 없고
    따릉이 사용 여부가 같은 여정이다. 순위 여정을 순위 차례로 먼저, 다음에 걸러진 여정을 결과 차례로 본다."""
    rest = list(plan[k:])
    items = _items(output)
    order = [items[rid] for rid in output.ranking if rid in items]
    order += [it for it in output.itineraries if it.itinerary_id not in output.ranking]
    for it in order:
        if len(it.rides) != len(rest):
            continue
        if not rest:
            if _bike_used(it) == bike:
                return it
            continue
        same = True
        for i, (ride, want) in enumerate(zip(it.rides, rest)):
            routes, board, alight = ride_sig(ride)
            if not set(routes) & set(want[0]) or alight != want[2] or (board != want[1] and not (i == 0 and on_vehicle)):
                same = False
                break
        if same:
            return it
    return None


def _next_ride(it: ItineraryResult) -> int | None:
    """다음에 탈 탑승(1부터): 승차 지점이 있는 첫 탑승. 없으면 None."""
    return next((ride.index for ride in it.rides if ride.board_index is not None), None)


@dataclasses.dataclass(frozen=True)
class GuideStatus:
    tone: str  # safe(계획대로), warn(놓치기 쉬움, 더 빠른 길), ghost(이제 타기 어려움, 계획대로 갈 수 없음)
    head: str
    lines: tuple[str, ...]
    switch_id: str | None  # "이 길로 바꾸기"가 고를 여정
    kept: str | None  # 다음 계산에서 지켜볼 차량(타려던 차)
    follow_id: str | None  # 새 결과에서 찾은 따라가는 경로


def _arrive(c0: float, it: ItineraryResult) -> str:
    return fmt_hm(c0, it.arrival.mean_s)


def guide_status(output: EngineOutput, scenario: Scenario | None, guide: Mapping[str, Any],
                 fast_output: EngineOutput | None = None) -> GuideStatus:
    """안내 카드(§6.10, 28단계 결정 문장). `guide` 의 plan, k, on, bike, kept 를 읽는다. `fast_output` 은 같은 입력을
    빠른 걸음으로 계산한 결과(없으면 빠른 걸음 판정은 거짓). 순수 함수."""
    c0 = output.clock_s
    items = _items(output)
    best = items.get(output.comparison.best_id) if output.comparison.best_id else None
    follow = guide_match(output, guide["plan"], int(guide.get("k", 0)), bool(guide.get("on")), bool(guide.get("bike")))
    usable = follow is not None and follow.status == RouteStatus.RANKED and follow.arrival.mean_s is not None

    def name(it: ItineraryResult) -> str:
        shown = [it.itinerary_id] + ([follow.itinerary_id] if follow is not None else [])
        return easy_title(it, shown, output, scenario)

    def offer(base_line: str | None) -> tuple[str | None, list[str]]:
        """최선 여정이 따라가는 경로와 다르고 화면의 도착 분이 1분 이상 이르면 바꾸기를 권한다."""
        if best is None or best.arrival.mean_s is None or (follow is not None and best.itinerary_id == follow.itinerary_id):
            return None, [base_line] if base_line else []
        if usable and minute_of(c0 + follow.arrival.mean_s) - minute_of(c0 + best.arrival.mean_s) < 1:
            return None, [base_line] if base_line else []
        title = name(best)
        tail = f"(지금 경로는 {_arrive(c0, follow)})" if usable else ""
        return best.itinerary_id, [f"{title}{josa_ro(title)} 바꾸면 {_arrive(c0, best)} 도착합니다{tail}."]

    if follow is None:  # 새 결과에 같은 경로가 없음(차가 끊겼거나 더 나은 길에 밀려 찾지 않음)
        switch, lines = offer(None)
        return GuideStatus("warn", "이번 계산에서 지금 경로를 찾지 못했습니다.", tuple(lines), switch, guide.get("kept"), None)
    if not usable:
        switch, lines = offer(None)
        if switch is None:
            return GuideStatus("ghost", "지금 경로로는 계획대로 가기 어렵고, 갈 수 있는 다른 길도 없습니다.", (), None,
                               guide.get("kept"), follow.itinerary_id if follow is not None else None)
        return GuideStatus("ghost", "지금 경로로는 계획대로 가기 어렵습니다.", tuple(lines), switch, guide.get("kept"),
                           follow.itinerary_id)
    keep_line = f"지금 경로로 가면 {_arrive(c0, follow)} 도착 예상입니다."
    index = _next_ride(follow)
    if index is None:  # 남은 탑승이 없거나 지금 탄 차에서 내리기만 남음
        if (best is not None and best.arrival.mean_s is not None and best.itinerary_id != follow.itinerary_id
                and follow.arrival.mean_s - best.arrival.mean_s >= GUIDE_BETTER_S):
            switch, lines = offer(None)
            if switch is not None:
                return GuideStatus("warn", "더 빠른 길이 생겼습니다.", tuple(lines), switch, None, follow.itinerary_id)
        return GuideStatus("safe", "계획대로 가세요.", (keep_line,), None, None, follow.itinerary_id)
    ride = follow.rides[index - 1]
    boarding = _boardings(follow).get(index)
    guided = boarding.guided_trip_id if boarding is not None else None
    kept = guide.get("kept") or guided
    option = _vehicle(boarding, kept)
    if option is None or option.p_catch < GUIDE_GONE_P:
        old = option if option is not None else None
        new_kept = guided
        if old is not None:
            head = f"{easy_vehicle(ride, old, scenario, c0, ('은', '는'))} 이제 타기 어렵습니다."
        else:
            head = "타려던 차는 이제 타기 어렵습니다."
        switch, lines = offer(keep_line)
        return GuideStatus("ghost", head, tuple(lines), switch, new_kept, follow.itinerary_id)
    p = option.p_catch
    fast = fast_catch(follow, index, option, fast_output, output.config.p_safe)
    if p < output.config.p_ghost:
        head = f"{easy_vehicle(ride, option, scenario, c0, ('을', '를'))} 놓치기 쉬워졌습니다."
        switch, lines = offer(keep_line)
        if fast:
            lines.insert(0, "빠른 걸음이면 탈 수 있습니다.")
        return GuideStatus("warn", head, tuple(lines), switch, kept, follow.itinerary_id)
    if (best is not None and best.arrival.mean_s is not None and best.itinerary_id != follow.itinerary_id
            and follow.arrival.mean_s - best.arrival.mean_s >= GUIDE_BETTER_S):
        switch, lines = offer(None)
        if switch is not None:
            return GuideStatus("warn", "더 빠른 길이 생겼습니다.", tuple(lines), switch, kept, follow.itinerary_id)
    line = (f"{easy_vehicle(ride, option, scenario, c0, ('은', '는'))} {catch_text(p, output.config.p_safe, fast)}. "
            f"{_arrive(c0, follow)} 도착 예상입니다.")
    return GuideStatus("safe", "계획대로 가세요.", (line,), None, kept, follow.itinerary_id)


def guide_status_html(status: GuideStatus, note: str) -> str:
    body = "".join(f"<p>{esc(line)}</p>" for line in status.lines)
    return (f'<div class="mr-guide {status.tone}"><div class="mr-ghead">{esc(status.head)}</div>{body}'
            f'<p class="mr-gnote">{esc(note)}</p></div>')


def guide_start(state: MutableMapping[str, Any], it: ItineraryResult, scenario_id: str, mode: str, replay_at: int | None,
                now: float) -> None:
    """안내 시작(§6.10): 따라가는 경로와 기준(시나리오, 모드, 목적지, 기록 재생의 기준 시각)을 둔다. 순수 함수(상태 사전만 고친다)."""
    first = _next_ride(it)
    boarding = _boardings(it).get(first) if first is not None else None
    state["guide"] = {
        "plan": guide_plan(it), "k": 0, "on": False, "bike": _bike_used(it),
        "kept": boarding.guided_trip_id if boarding is not None else None,
        "scenario_id": scenario_id, "mode": mode, "dest": guide_dest(state),
        "t0": now, "last_tick": now, "elapsed": 0, "skip": 0,
        "at0": int(replay_at or 0) if mode == DataMode.REPLAY.value else None, "vehicle": None,
        "gps_error": None,
    }
    store_value(state, "selected_id", it.itinerary_id)


def guide_dest(state: Mapping[str, Any]) -> list[Any]:
    point = state.get("dest_point")
    return [state.get("dest_kind"), state.get("dest_place") if state.get("dest_kind") != "POINT" else None,
            list(point) if state.get("dest_kind") == "POINT" and point is not None else None]


def guide_tick(state: MutableMapping[str, Any], now: float) -> bool:
    """간격이 지났으면 지난 시간을 새로 정하고 실시간 조회 번호를 올린다(§6.10). 바꿨으면 참. 순수 함수."""
    guide = state.get("guide")
    if not isinstance(guide, MutableMapping) or now - float(guide["last_tick"]) < GUIDE_TICK_S:
        return False
    guide["last_tick"] = now
    guide["elapsed"] = int(now - float(guide["t0"])) + int(guide.get("skip", 0))
    if guide["mode"] == DataMode.LIVE.value:
        state["live_refresh"] = int(state.get("live_refresh", 0)) + 1
    return True


def guide_valid(state: Mapping[str, Any], p: "Prepared") -> bool:
    guide = state.get("guide")
    return (isinstance(guide, Mapping) and guide["scenario_id"] == p.scenario_id and guide["mode"] == p.mode
            and guide["dest"] == guide_dest(state))


def guide_clock(guide: Mapping[str, Any] | None, mode: str, at: int | None, dt_s: int) -> tuple[int | None, int]:
    """안내 중이면 (기록 재생 시각, 출발 늦추기)를 바꾼다(§6.10): 기록 재생은 시작 때의 기준 시각 + 지난 시간, 늦추기는 모든
    모드에서 0 이다(시뮬레이션은 기준 시나리오 자체를 지난 시간만큼 옮긴다, `guide_sim_base`). 안내 중이 아니면 그대로.
    출발 늦추기로 옮기면 차량 안 출발이 "그만큼 늦게 닿는 차"로 바뀌므로(§4.6) 안내에는 쓰지 않는다."""
    if not isinstance(guide, Mapping):
        return at, dt_s
    if mode == DataMode.REPLAY.value:
        return int(guide["at0"]) + int(guide.get("elapsed", 0)), 0
    return at, 0


def guide_sim_base(scenario_json: str, guide: Mapping[str, Any]) -> str:
    """시뮬레이션 안내의 기준 시나리오: `advance_clock(시나리오, 지난 시간)` 의 JSON (같은 차량이 지난 시간만큼 다가온다)."""
    elapsed = int(guide.get("elapsed", 0))
    return shifted_object(scenario_json, elapsed).model_dump_json() if elapsed else scenario_json


def vehicle_next_index(base: Scenario, mode: TravelMode, route_id: str, trip_id: str, start: int,
                       config: EngineConfig) -> int | None:
    """탄 차가 다음에 설 순번(§6.10): `start` 이상에서 그 차의 도착 시각이 0 이상인 첫 순번. 없으면 None."""
    if mode == TravelMode.SUBWAY:
        pattern = next((item for item in base.subway_patterns if item.id == route_id), None)
        trip = next((item for item in pattern.trips if item.id == trip_id), None) if pattern is not None else None
        if trip is None:
            return None
        return next((j for j in range(start, len(pattern.station_keys)) if float(trip.arr_s[j]) >= 0.0), None)
    rows = json.loads(cached_bus_vehicles(base.model_dump_json(), route_id, config.model_dump_json()))
    return next((j for j in sorted(int(key) for key in rows) if j >= start and any(row[0] == trip_id for row in rows[str(j)])),
                None)


def _set_vehicle_origin(state: MutableMapping[str, Any], mode: TravelMode, route_id: str, trip_id: str, index: int,
                        base: Scenario) -> None:
    if mode == TravelMode.SUBWAY:
        pattern = next(item for item in base.subway_patterns if item.id == route_id)
        store_value(state, "origin_kind", "TRAIN")
        store_value(state, "train_station", pattern.station_keys[index])
        store_value(state, "train_key", train_key_of(route_id, trip_id, index))
    else:
        store_value(state, "origin_kind", "BUS")
        store_value(state, "bus_line", route_id)
        store_value(state, "bus_stop_index", index)
        store_value(state, "bus_vehicle", trip_id)


def guide_follow_vehicle(state: MutableMapping[str, Any], base: Scenario, config: EngineConfig) -> None:
    """차 안이면 탄 차가 다음에 설 순번을 지금 시각에 맞춘다(§6.10). 사이드바의 출발 위젯 앞에서 부른다."""
    guide = state.get("guide")
    if not isinstance(guide, MutableMapping) or not guide.get("on") or not guide.get("vehicle"):
        return
    mode, route_id, trip_id, board = guide["vehicle"]
    mode = TravelMode(mode)
    index = vehicle_next_index(base, mode, route_id, trip_id, int(board) + 1, config)
    if index is not None:
        _set_vehicle_origin(state, mode, route_id, trip_id, index, base)


def _on_guide_start(it_json: str, scenario_id: str, mode: str, replay_at: int | None) -> None:
    guide_start(st.session_state, ItineraryResult.model_validate_json(it_json), scenario_id, mode, replay_at, time.time())


def _on_guide_stop() -> None:
    drop_keys(st.session_state, ("guide",))


def _on_guide_skip() -> None:
    guide = st.session_state.get("guide")
    if isinstance(guide, MutableMapping):
        guide["skip"] = int(guide.get("skip", 0)) + 60
        guide["last_tick"] = float(guide["last_tick"]) - GUIDE_TICK_S  # 바로 다음 실행에서 다시 계산한다


def _on_guide_switch(it_json: str) -> None:
    state = st.session_state
    guide = state.get("guide")
    if not isinstance(guide, MutableMapping):
        return
    it = ItineraryResult.model_validate_json(it_json)
    first = _next_ride(it)
    boarding = _boardings(it).get(first) if first is not None else None
    on_vehicle = bool(it.rides) and it.rides[0].board_index is None
    guide.update({"plan": [ride_sig(ride) for ride in it.rides], "k": 0, "on": on_vehicle and guide.get("on", False),
                  "bike": _bike_used(it), "kept": boarding.guided_trip_id if boarding is not None else None})
    if not guide["on"]:
        guide["vehicle"] = None
    store_value(state, "selected_id", it.itinerary_id)


def _on_guide_board(vehicle: tuple[str, str, str, int], base_json: str) -> None:
    """"{차} 탔어요"(§6.10): 출발을 그 차 안으로 바꾼다. 차가 다음에 설 순번은 승차 순번 + 1 부터 지금 시각에 맞춘다."""
    state = st.session_state
    guide = state.get("guide")
    if not isinstance(guide, MutableMapping):
        return
    mode, route_id, trip_id, board = vehicle
    base = scenario_object(base_json)
    travel = TravelMode(mode)
    index = vehicle_next_index(base, travel, route_id, trip_id, board + 1, load_context().data_config)
    _set_vehicle_origin(state, travel, route_id, trip_id, board + 1 if index is None else index, base)
    guide["on"] = True
    guide["vehicle"] = [mode, route_id, trip_id, board]
    drop_keys(state, ("origin_gps", "gps_note"))


def _on_guide_alight(node: tuple[float, float]) -> None:
    """"{정류장}에서 내렸어요"(§6.10): 출발을 내린 지점으로 바꾸고 다음 탑승으로 넘어간다."""
    state = st.session_state
    guide = state.get("guide")
    if not isinstance(guide, MutableMapping):
        return
    guide["k"] = int(guide.get("k", 0)) + 1
    guide["on"] = False
    guide["vehicle"] = None
    guide["kept"] = None
    store_value(state, "origin_kind", "POINT")
    store_value(state, "origin_point", (float(node[0]), float(node[1])))
    drop_keys(state, ("origin_gps", "gps_note"))


def _on_guide_fix() -> None:
    """안내 중 위치 받기의 트리거(§6.10): 차 안이 아니면 위치 단추와 같은 길(`gps_pending`)로 출발을 바꾼다. 오류는 안내에만 적는다."""
    state = st.session_state
    guide = state.get("guide")
    value = state.get(GUIDE_COMPONENT_KEY)
    fix = value.get("fix") if isinstance(value, Mapping) else None
    if not isinstance(guide, MutableMapping) or not isinstance(fix, Mapping):
        return
    if "error" in fix:
        guide["gps_error"] = str(fix["error"])
        return
    guide["gps_error"] = None
    if not guide.get("on"):
        state["gps_pending"] = dict(fix)


@st.fragment(run_every=GUIDE_TICK_S)
def guide_timer() -> None:
    """안내 중이면 간격마다 앱 전체를 다시 실행한다(§6.10). 처음 그릴 때는 아무것도 하지 않는다."""
    guide = st.session_state.get("guide")
    if isinstance(guide, Mapping) and time.time() - float(guide["last_tick"]) >= GUIDE_TICK_S - 1:
        st.rerun()


def guide_vehicle_args(follow: ItineraryResult, kept: str | None) -> tuple[str, str, str, int] | None:
    """"탔어요" 단추가 넘길 차: (수단, 노선 또는 패턴, 차량, 승차 순번). 묶음이면 그 차의 노선과 그 노선의 승차 순번."""
    index = _next_ride(follow)
    if index is None or kept is None:
        return None
    ride = follow.rides[index - 1]
    option = _vehicle(_boardings(follow).get(index), kept)
    if option is None or ride.board_index is None:
        return None
    route_id, board = ride.route_id, ride.board_index
    for line in ride.bundle:
        if line.route_id == option.route_id:
            route_id, board = line.route_id, line.board_index
    return (ride.mode.value, route_id, option.trip_id, int(board))


def render_guide(p: Prepared, output: EngineOutput, follow_status: GuideStatus) -> None:
    """안내 카드와 단추(§6.10). 답 카드 위에 그린다."""
    state = st.session_state
    guide = state["guide"]
    items = _items(output)
    c0 = output.clock_s
    notes = [GUIDE_TICK_TEXT.format(clock=fmt_clock(c0, 0.0))]
    if guide.get("on"):
        notes.append(GUIDE_ON_VEHICLE_TEXT)
    elif guide.get("gps_error") is not None or gps_origin(state) is None:
        notes.append(GUIDE_NO_GPS_TEXT)
    with st.container(key="mr_guide"):
        st.html(guide_status_html(follow_status, " ".join(notes)))
        if follow_status.switch_id is not None and follow_status.switch_id in items:
            st.button(GUIDE_SWITCH_LABEL, key="guide_switch", type="primary", width="stretch", on_click=_on_guide_switch,
                      args=(items[follow_status.switch_id].model_dump_json(),))
        follow = items.get(follow_status.follow_id) if follow_status.follow_id else None
        if follow is not None:
            if guide.get("on") and follow.rides and follow.rides[0].board_index is None:
                ride = follow.rides[0]
                coords = _node_latlon(p.display, ride.alight_node_id)
                if coords is not None:
                    stop = short_stop_name(ride.alight_node_id, p.display)
                    st.button(GUIDE_ALIGHT_LABEL.format(stop=stop), key="guide_alight", width="stretch",
                              on_click=_on_guide_alight, args=(coords,))
            else:
                vehicle = guide_vehicle_args(follow, follow_status.kept)
                if vehicle is not None:
                    index = _next_ride(follow)
                    option = _vehicle(_boardings(follow).get(index), follow_status.kept)
                    label = GUIDE_BOARD_LABEL.format(vehicle=easy_vehicle(follow.rides[index - 1], option, p.display, c0))
                    st.button(label, key="guide_board", width="stretch", on_click=_on_guide_board,
                              args=(vehicle, p.base_json))
        if p.mode in (DataMode.REPLAY.value, DataMode.SIMULATION.value):
            st.caption(GUIDE_SKIP_NOTE.format(mode=MODE_NAMES[p.mode]))
            st.button(GUIDE_SKIP_LABEL, key="guide_skip", width="stretch", on_click=_on_guide_skip)
        st.button(GUIDE_STOP_LABEL, key="guide_stop", width="stretch", on_click=_on_guide_stop)
        watch = st.components.v2.component(GUIDE_COMPONENT_NAME, html=GUIDE_WATCH_HTML, js=GUIDE_WATCH_JS)
        watch(key=GUIDE_COMPONENT_KEY, data={"min_s": GUIDE_GPS_MIN_S, "move_m": GUIDE_GPS_MOVE_M, "timeout_ms": GPS_TIMEOUT_MS},
              on_fix_change=_on_guide_fix)
    guide_timer()


def render_guide_start(p: Prepared, it: ItineraryResult) -> None:
    """안내 시작 단추(§6.10): 보는 경로가 순위 여정이고 출발이 장소나 지점일 때. 출발 늦추기가 0 이 아니면 단추 대신 안내 문장."""
    if st.session_state.get("origin_kind") not in GUIDE_START_KINDS:
        return
    if p.dt_s != 0:
        st.caption(GUIDE_DT_BLOCK)
        return
    st.button(GUIDE_START_LABEL, key="guide_start", type="primary", width="stretch", on_click=_on_guide_start,
              args=(it.model_dump_json(), p.scenario_id, p.mode, p.replay_at))


def _node_latlon(scenario: Scenario, node_id: str) -> tuple[float, float] | None:
    node = next((item for item in scenario.nodes if item.id == node_id), None)
    return (float(node.lat), float(node.lon)) if node is not None else None


def main() -> None:
    """한 번의 실행(§8.4 의 1 ~ 8): 사이드바가 입력을 정하고, 엔진을 (캐시를 거쳐) 부르고, 본문을 그린다."""
    st.set_page_config(page_title=APP_TITLE, page_icon=":material/alt_route:", layout="wide",
                       initial_sidebar_state=SIDEBAR_WIDTH_PX)
    tokens = theme_tokens()
    st.html(page_css(tokens))
    ctx = load_context()
    init_session(ctx)
    state = st.session_state
    if current_page(state) == PAGE_INTRO:  # 소개 페이지(§6.12, 34단계)
        render_intro(ctx)
        return
    simple = state.get("view_mode") != "DETAIL"
    slots: dict[str, Any] = {}
    if simple:
        slots["head"] = st.container()
        slots["guide"] = st.container()  # 안내 카드(§6.10): 휴대폰에서도 맨 먼저 보이게 출발·도착 상자 위
        left, right = st.columns([5, 7], gap="medium")
        with left:
            with st.container(border=True, key="mr_trip"):
                slots["trip"] = st.empty()
                slots["trip_body"] = st.container()
            slots["answer"] = st.container()
        slots["side"] = right
    if simple:
        guide_tick(state, time.time())
    p = render_sidebar(ctx, slots.get("trip_body"))
    if "guide" in state and (not simple or not guide_valid(state, p)):
        drop_keys(state, ("guide",))
    output: EngineOutput | None = None
    moved: Query | None = None
    if p.block is None and p.config is not None and p.query is not None:
        output_json, moved_json = cached_run(p.base_json, p.shifted_json, p.dt_s, p.query.model_dump_json(),
                                             p.config.model_dump_json(), p.sources_json)
        if output_json:
            output = output_object(output_json)
            moved = Query.model_validate_json(moved_json)
        else:
            p.block = (f"{p.dt_s // 60}분 늦추면 이 역(정류장)에 닿는 차가 없습니다. "
                       "출발 늦추기를 줄이거나 출발을 다시 고르세요.")
    if simple:
        with slots["head"]:
            render_header(p, output, moved, simple=True)
        clicked = render_simple(p, output, moved, slots, tokens)
        render_footer()
        if clicked:
            st.rerun()
        return
    render_header(p, output, moved)
    if output is None or p.config is None:
        if p.block:
            st.info(p.block)
        clicked = render_map(p, None, None, tokens)
        render_footer()
        if clicked:
            st.rerun()
        return
    st.html(compare_panel_html(output, p.config, p.display, snap_distance_m=snap_distance(p, output)))
    render_kpi(output, p.config)
    if output.itineraries:
        adjust_selection(state, output)
    left, right = st.columns([7, 5], gap="medium")
    with right:  # 경로 목록이 고른 여정을 고칠 수 있으므로 지도보다 먼저 그린다(화면 배치는 열이 정한다)
        if output.itineraries:
            render_route_list(output, p.display, p.config)
    with left:
        clicked = render_map(p, output, state.get("selected_id") if output.itineraries else None, tokens)
    render_tabs(p, output, state.get("selected_id") if output.itineraries else None, tokens)
    render_warnings(output)
    render_footer()
    if clicked:
        st.rerun()


# --- 화면 검사 (§8.7, §9.9) ---
#
# 기대값은 core_engine 을 직접 불러 얻고, 골든·골든 변형·합성 기록은 명세의 문구를 그대로 비교한다(§9.9.1).
# 검사 하나는 실패를 모두 모아 보이고, 실패가 하나라도 있으면 그 검사는 FAIL 이다.

_APP_FILE = Path(__file__).resolve()
_BANNED_WORDS = ("TODO", "다음 단계", "준비 중", "placeholder")
_FOOTER = "데이터: 서울 열린데이터광장, 공공데이터포털, © OpenStreetMap 기여자(ODbL)"
_GOLDEN_LABEL = "골든 미니 시나리오 (검산용)"
_KPI_LABELS = ("평균 도착", "90% 도착", "계획대로 갈 확률", "요금")
_GOLDEN_KPI = [("평균 도착", "08:11:14", "-10분 44초"), ("90% 도착", "08:21:41", "-21초"), ("계획대로 갈 확률", "87.5%", ""),
               ("요금", "1,000원", "-500원")]
_KST = datetime.timezone(datetime.timedelta(hours=9))


class _Missing:
    def __repr__(self) -> str:
        return "(없음)"


_MISSING = _Missing()


def _brief(value: Any, limit: int = 400) -> str:
    text = value if isinstance(value, str) else repr(value)
    return text if len(text) <= limit else f"{text[:limit]}… ({len(text):,}자)"


class _Checker:
    """검사 하나의 판정을 모은다."""

    def __init__(self) -> None:
        self.failures: list[str] = []
        self.count = 0

    def true(self, label: str, condition: Any, detail: Any = None) -> bool:
        self.count += 1
        if not condition:
            self.failures.append(label + (f" ({_brief(detail)})" if detail is not None else ""))
        return bool(condition)

    def eq(self, label: str, expected: Any, actual: Any) -> bool:
        self.count += 1
        if expected != actual:
            self.failures.append(f"{label}: 기대 {_brief(expected)}, 실제 {_brief(actual)}")
            return False
        return True


class _Counted:
    """엔진 함수를 감싸 불린 횟수를 센다(§9.9.1 의 엔진 호출 세기)."""

    def __init__(self, func: Callable[..., Any]) -> None:
        self.func = func
        self.calls = 0

    def __call__(self, *args: Any, **kwargs: Any) -> Any:
        self.calls += 1
        return self.func(*args, **kwargs)


@contextlib.contextmanager
def _replaced(owner: Any, name: str, value: Any):
    """모듈 속성을 잠시 바꾸고 끝나면 되돌린다."""
    original = getattr(owner, name)
    setattr(owner, name, value)
    try:
        yield value
    finally:
        setattr(owner, name, original)


class _MapCalls:
    """`streamlit_folium.st_folium` 의 대역. 화면 검사는 지도 컴포넌트에 값을 넣을 수 없으므로(§8.7) 부른 인자를 적어 두고,
    누른 좌표를 정해 두면 그 값을 돌려준다. `render` 가 참이면 지도 HTML 을 만들어 예외가 없는지 본다."""

    def __init__(self) -> None:
        self.calls: list[dict[str, Any]] = []
        self.errors: list[str] = []
        self.click: Mapping[str, Any] | None = None
        self.render = False

    def __call__(self, fig: folium.Map, key: str | None = None, height: int = 700, width: int = 500,
                 returned_objects: Iterable[str] | None = None, use_container_width: bool = False, **kwargs: Any) -> dict:
        returned = list(returned_objects) if returned_objects is not None else None
        self.calls.append({"key": key, "height": height, "use_container_width": use_container_width,
                           "returned_objects": returned, "layers": tuple(feature_groups(fig))})
        if self.render:
            try:
                fig.get_root().render()
            except Exception as error:  # noqa: BLE001 - 검사 결과로 보인다
                self.errors.append(repr(error))
        if returned and "last_clicked" in returned:
            return {"last_clicked": dict(self.click) if self.click else None}
        return {}


def _proto_strings(message: Any) -> Iterable[str]:
    """protobuf 메시지 안의 모든 문자열 값(필드 이름은 빼고)."""
    for field, value in message.ListFields():
        repeated = getattr(field, "is_repeated", None)
        if repeated is None:
            repeated = field.label == field.LABEL_REPEATED
        if field.type == field.TYPE_STRING:
            if repeated:
                yield from value
            else:
                yield value
        elif field.type == field.TYPE_MESSAGE:
            if field.message_type.GetOptions().map_entry:
                for map_key, map_value in value.items():
                    if isinstance(map_key, str):
                        yield map_key
                    if isinstance(map_value, str):
                        yield map_value
                    elif hasattr(map_value, "ListFields"):
                        yield from _proto_strings(map_value)
            elif repeated:
                for item in value:
                    yield from _proto_strings(item)
            else:
                yield from _proto_strings(value)


def _plain(markup: str) -> str:
    """HTML 조각의 글자: 태그를 빈칸으로 바꾸고, 문자 참조를 풀고, 빈칸을 하나로 줄인다."""
    return " ".join(html.unescape(re.sub(r"<[^>]+>", " ", markup)).split())


class _Screen:
    """AppTest 한 개와 그 검사 도우미. 실행마다 화면 예외를 판정에 넣는다."""

    def __init__(self, checker: _Checker, maps: _MapCalls, view: str | None = "DETAIL", scenario: str | None = None,
                 page: str | None = PAGE_APP) -> None:
        from streamlit.testing.v1 import AppTest

        self.c = checker
        self.maps = maps
        self.at = AppTest.from_file(str(_APP_FILE), default_timeout=60)
        if view is not None:  # UI-01 ~ UI-29 는 자세히 보기로 시작한다(§8.7). UI-30 은 None(기본값 "SIMPLE")
            self.at.session_state["view_mode"] = view
        if page is not None:  # 34단계: 검사는 길찾기 화면에서 시작한다. 소개 페이지는 UI-43 이 page=None 으로 본다
            self.at.session_state[PAGE_KEY] = page
        if scenario is not None:  # 첫 실행 전에 시나리오를 정해 두면 첫 화면 규칙(첫 예시 경로, §6.3 30단계)을 건너뛴다
            self.at.session_state["scenario_id"] = scenario

    def run(self, label: str = "실행") -> "_Screen":
        self.at.run()
        _quiet()
        if self.at.exception:
            first = self.at.exception[0]
            self.c.true(f"{label}: 화면 예외 없음", False, f"{first.message} {''.join(first.stack_trace)[-600:]}")
        return self

    def set(self, kind: str, key: str, value: Any) -> "_Screen":
        getattr(self.at, kind)(key=key).set_value(value)
        return self.run(f"{key} ← {value!r}")

    def put(self, key: str, value: Any) -> "_Screen":
        """위젯이 아닌 세션 상태 값을 넣고 실행한다(지도에서 찍은 점처럼)."""
        self.at.session_state[key] = value
        return self.run(f"상태 {key} ← {value!r}")

    def click(self, key: str) -> "_Screen":
        self.at.button(key=key).click()
        return self.run(f"{key} 누름")

    def scenario(self, scenario_id: str) -> "_Screen":
        return self.set("selectbox", "scenario_id", scenario_id)

    def state(self, key: str, default: Any = _MISSING) -> Any:
        return self.at.session_state[key] if key in self.at.session_state else default

    def has(self, kind: str, key: str) -> bool:
        try:
            getattr(self.at, kind)(key=key)
        except KeyError:
            return False
        return True

    def kpi(self) -> list[tuple[str, str, str]]:
        return [(item.label, item.value, item.delta or "") for item in self.at.metric]

    def htmls(self, css: str) -> list[str]:
        return [item.value for item in self.at.html if f'class="{css}' in item.value]

    def html_text(self, css: str) -> str:
        return " ".join(_plain(value) for value in self.htmls(css))

    def compare(self) -> list[str]:
        """경로 비교 표의 HTML (32단계): 머리, 줄, 가정 문장."""
        return [item.value for item in self.at.html if 'class="mr-alts-h' in item.value or 'class="mr-cmp' in item.value]

    def chips(self) -> str:
        return self.html_text("mr-chips")

    def description(self) -> str:
        return self.html_text("mr-desc")

    def side_captions(self) -> list[str]:
        return [item.value for item in self.at.sidebar.caption]

    def side_texts(self, kind: str) -> list[str]:
        return [item.value for item in getattr(self.at.sidebar, kind)]

    def main_texts(self, kind: str) -> list[str]:
        return [item.value for item in getattr(self.at.main, kind)]

    def strings(self) -> list[str]:
        """화면의 모든 글자(마크다운, 캡션, HTML, 안내 상자, 위젯 이름과 선택지, 도움말)."""
        found: list[str] = []

        def walk(node: Any) -> None:
            proto = getattr(node, "proto", None)
            if proto is not None and hasattr(proto, "ListFields"):
                found.extend(_proto_strings(proto))
            children = getattr(node, "children", None)
            if isinstance(children, dict):
                for child in children.values():
                    walk(child)

        walk(self.at._tree)
        return found

    def options(self, kind: str, key: str) -> list[str]:
        return list(getattr(self.at, kind)(key=key).options)


def _quiet() -> None:
    """검사 쪽에서 실행 맥락 밖의 Streamlit 을 부를 때 나오는 안내를 숨긴다. AppTest 는 실행할 때마다 로그 수준을
    설정값(info)으로 되돌리므로 실행 뒤에 다시 낮춘다."""
    from streamlit import logger as streamlit_logger

    streamlit_logger.set_log_level("error")


def _clear_caches() -> None:
    _quiet()
    st.cache_data.clear()
    st.cache_resource.clear()


def _items_of(output: EngineOutput) -> dict[str, ItineraryResult]:
    return {it.itinerary_id: it for it in output.itineraries}


def _kpi_expect(output: EngineOutput) -> list[tuple[str, str, str]]:
    """§6.3 의 KPI 규칙을 기대 `EngineOutput` 에 그대로 적용한 (라벨, 값, 변화량). 화면의 타일 함수는 쓰지 않는다."""
    items = _items_of(output)
    best = items.get(output.best_id) if output.best_id else None
    if best is None:
        return [(label, "-", "") for label in _KPI_LABELS]
    cmp = output.comparison
    naive = items.get(cmp.naive_best_id) if cmp.naive_best_id else None
    differ = naive is not None and not cmp.same
    c0 = output.clock_s

    def clock(value: float | None) -> str:
        return "-" if value is None else fmt_clock(c0, value)

    def delta(mine: float | None, theirs: float | None) -> str:
        return fmt_delta_dur(mine - theirs) if differ and mine is not None and theirs is not None else ""

    deadline = ""
    if output.query.deadline_s is not None and best.arrival.p_on_time is not None:
        deadline = f"마감까지 도착할 확률 {fmt_pct(best.arrival.p_on_time)}"
    if naive is None:
        fare = ""
    elif naive.plan_missed_last and not cmp.same:
        fare = FARE_MISSED_NOTE
    else:
        fare = fmt_delta_won(0 if cmp.same else best.fare.total_krw - naive.fare.total_krw)
    return [
        (_KPI_LABELS[0], clock(best.arrival.mean_s), delta(best.arrival.mean_s, naive.arrival.mean_s if naive else None)),
        (_KPI_LABELS[1], clock(best.arrival.p90_s), delta(best.arrival.p90_s, naive.arrival.p90_s if naive else None)),
        (_KPI_LABELS[2], fmt_pct(best.p_star), deadline),
        (_KPI_LABELS[3], fmt_won(best.fare.total_krw), fare),
    ]


def _route_labels(output: EngineOutput) -> list[str]:
    """경로 목록의 대표 여정 선택지(§6.3 의 "**{순위}위** {여정 이름}")."""
    items = _items_of(output)
    return [f"**{items[rep].rank}위** {items[rep].label}" for rep in output.ranking]


def _golden_variant(variant_id: str) -> Scenario:
    """§9.9.1 의 골든 변형. 바꾼 것 말고는 골든과 같고 제목은 "골든 변형 {ID}" 다."""
    base = ce.golden_last_vehicle_scenario() if variant_id == "GV-LAST" else ce.golden_scenario()
    data = base.model_dump()
    data["id"] = variant_id
    data["title"] = f"골든 변형 {variant_id}"
    if variant_id == "GV-ESC":
        for line in data["bus_lines"]:
            if line["id"] == "G1":
                line["name"] = "<b>가상1</b>"
        for node in data["nodes"]:
            if node["id"] == "B1":
                node["name"] = "정류장<i>1"
    elif variant_id in ("GV-MANYW", "GV-MANYI"):
        kind = NodeType.WAYPOINT if variant_id == "GV-MANYW" else NodeType.INTERSECTION
        anchor = next(node for node in data["nodes"] if node["id"] == "W9")
        y0 = round((anchor["lat"] - 37.5) * 111_194.93)  # §9.2 의 좌표 규칙으로 W9 의 y (900 m)
        template = next(edge for edge in data["edges"] if edge["id"] == "e05")  # 걷기만 되는 SIDEWALK, 신호 없음
        data["nodes"], data["edges"] = list(data["nodes"]), list(data["edges"])
        previous = "W9"
        for n in range(1, 601):
            node_id = f"F{n:03d}"
            node = dict(anchor)
            node.update(id=node_id, name=f"먼 길 {n}", node_type=kind, lat=ce._golden_lat(y0 + 10 * n))
            data["nodes"].append(node)
            edge = dict(template)
            edge.update(id=f"f{n:03d}", source=previous, target=node_id, distance_m=10.0)
            data["edges"].append(edge)
            previous = node_id
    elif variant_id == "GV-LATE":
        for pattern in data["subway_patterns"]:
            for trip in pattern["trips"]:
                trip["arr_s"] = tuple(value + 3600.0 for value in trip["arr_s"])
                trip["dep_s"] = tuple(value + 3600.0 for value in trip["dep_s"])
    elif variant_id == "GV-NOSUB":
        data["subway_patterns"] = ()
    elif variant_id == "GV-NORATE":
        for station in data["bike_stations"]:
            if station["id"] == "K1":
                station["rental_rate_per_hour"] = None
    elif variant_id == "GV-WIDE":
        for line in data["bus_lines"]:
            if line["id"] == "G2":
                line["route_type"] = BusRouteType.WIDE_AREA
    elif variant_id != "GV-LAST":
        raise ValueError(variant_id)
    return Scenario.model_validate(data)


def _save_variant(folder: Path, variant_id: str) -> Scenario:
    scenario = _golden_variant(variant_id)
    ce.save_scenario_json(scenario, folder / "scenarios" / f"{variant_id}.json")
    return scenario


def _coord(scenario: Scenario, node_id: str) -> tuple[float, float]:
    for node in (*scenario.nodes, *scenario.bike_stations):
        if node.id == node_id:
            return (round(node.lat, 7), round(node.lon, 7))
    raise KeyError(node_id)


def _route_sequences(scenario: Scenario, it: ItineraryResult) -> set[tuple[tuple[float, float], ...]]:
    """고른 여정의 선: 이동 `polyline` 들(따릉이는 ①③⑤)과 탑승마다 승차부터 하차까지의 정류장·승강장 좌표열(§9.9 UI-05)."""
    sequences: set[tuple[tuple[float, float], ...]] = set()

    def add(points: Iterable[Sequence[float]]) -> None:
        line = tuple((round(float(lat), 7), round(float(lon), 7)) for lat, lon in points)
        if len(line) >= 2:
            sequences.add(line)

    for move in it.moves:
        if move.bike is not None:
            for path in (move.bike.walk_in, move.bike.ride, move.bike.walk_out):
                if path is not None:
                    add(path.polyline)
        elif move.walk is not None:
            add(move.walk.polyline)
    for ride in it.rides:
        if ride.mode == TravelMode.BUS:
            stops = next(line.stop_ids for line in scenario.bus_lines if line.id == ride.route_id)
        else:
            stops = next(pattern.platform_ids for pattern in scenario.subway_patterns if pattern.id == ride.route_id)
        start = ride.board_index if ride.board_index is not None else ride.alight_index
        add(_coord(scenario, stop) for stop in stops[start:ride.alight_index + 1])
    return sequences


def _group_lines(group: folium.FeatureGroup) -> set[tuple[tuple[float, float], ...]]:
    return {tuple((round(float(lat), 7), round(float(lon), 7)) for lat, lon in child.locations)
            for child in group._children.values() if isinstance(child, folium.PolyLine)}


def _group_markers(group: folium.FeatureGroup, *, circles: bool = False) -> list[Any]:
    return [child for child in group._children.values()
            if isinstance(child, folium.Marker) and isinstance(child, folium.CircleMarker) == circles]


def _marker_place(marker: Any) -> tuple[float, float]:
    return (round(float(marker.location[0]), 7), round(float(marker.location[1]), 7))


def _kst_unix(year: int, month: int, day: int, hour: int, minute: int) -> float:
    return datetime.datetime(year, month, day, hour, minute, tzinfo=_KST).timestamp()


def _synthetic(folder: Path):
    """합성 기록(§9.7.4)과 그 기대값 계산에 쓰는 것들: (진실, 시나리오 SYN, 설정, 모델)."""
    truth = ce.make_synthetic_records(folder)
    targets = CollectTargets.model_validate_json(truth.targets_path.read_bytes())
    config = EngineConfig(data_dir=str(folder), holidays=tuple(targets.holidays))
    return truth, ce.load_scenario_json(truth.scenario_path), config, ce.load_models(folder)


def _replayed(truth: Any, scenario: Scenario, config: EngineConfig, models: Any, at_unix: float):
    with ce.RecordStore(truth.store_path, read_only=True) as store:
        return ce.replay_scenario(scenario, store, models, at_unix, config)


def _base_defaults() -> dict[str, Any]:
    """§8.3 의 기본값 가운데 시나리오와 무관하고 늘 상태에 있는 키."""
    config = EngineConfig()
    return {
        "data_mode": "SIMULATION",
        "live_refresh": 0,
        "live_fetched_at": None,
        "origin_point": None,
        "dest_point": None,
        "last_map_click": None,
        "depart_offset_s": 0,
        "use_deadline": False,
        "rank_criterion": config.rank_criterion.value,
        "walk_preset": "보통",
        "use_bus": True,
        "use_subway": True,
        "use_bike": True,
        "max_rides": config.max_rides,
        "climate_card": False,
        "bike_mileage": False,
        "gamma": config.gamma,
        "safety_buffer": config.safety_buffer_s,
        "v_pm": config.v_pm_mps,
        "max_bike_legs": config.max_bike_legs,
        "full_skip": False,
        "k_pm": config.k_pm,
        "show_variants": False,
        "kakao_results": {},
        "kakao_calls": 0,
        "trace_run": "FULL",
        "tabs": "① 경로 비교",
    }


def _conditional_defaults(scenario: Scenario) -> dict[str, Any]:
    """조건이 맞을 때만 그리는 위젯의 기본값(§8.3): 마감 시각, 가중치, 걷는 속도."""
    config = EngineConfig()
    floor_s = int((scenario.clock_s + 1800.0) // 60 * 60) % 86_400
    return {
        "deadline_time": datetime.time(floor_s // 3600, floor_s % 3600 // 60),
        "weight_preset": "균형",
        "w_time": config.w_time,
        "w_cost": config.w_cost,
        "w_risk": config.w_risk,
        "v_walk": config.v_walk_mps,
    }


def _query_key_defaults(scenario: Scenario) -> dict[str, Any]:
    """시나리오의 기본 질의로 정해지는 출발·목적지 키(§8.3). 화면의 변환 함수 없이 질의에서 바로 만든다."""
    query = scenario.default_query
    place_of = {place.node_id: place.name for place in scenario.places}
    origin = query.origin
    result: dict[str, Any] = {"dest_kind": "PLACE", "dest_place": place_of[query.destination_node_id]}
    if origin.kind == OriginKind.AT_NODE:
        result.update(origin_kind="PLACE", origin_place=place_of[origin.node_id])
    elif origin.kind == OriginKind.ON_TRAIN:
        pattern = next(item for item in scenario.subway_patterns if item.id == origin.pattern_id)
        result.update(origin_kind="TRAIN", train_station=pattern.station_keys[origin.next_index],
                      train_key=f"{origin.pattern_id}|{origin.trip_id}|{origin.next_index}",
                      prior_km=origin.prior_distance_m / 1000.0)
    elif origin.kind == OriginKind.ON_BUS:
        result.update(origin_kind="BUS", bus_line=origin.line_id, bus_stop_index=origin.next_index,
                      bus_vehicle=origin.trip_id, prior_km=origin.prior_distance_m / 1000.0)
    else:
        result.update(origin_kind="POINT", origin_point=(origin.lat, origin.lon))
    return result


_CONDITIONAL_WIDGETS = (
    ("selectbox", "replay_window"), ("date_input", "replay_date"), ("time_input", "replay_time"),
    ("button", "live_refresh_button"), ("time_input", "deadline_time"), ("slider", "w_time"), ("slider", "w_cost"),
    ("slider", "w_risk"), ("slider", "v_walk"), ("segmented_control", "map_pick"), ("number_input", "prior_km"),
    ("selectbox", "train_station"), ("selectbox", "train_key"), ("selectbox", "bus_line"), ("selectbox", "bus_stop_index"),
    ("selectbox", "bus_vehicle"),
)


def _conditional_present(s: _Screen) -> set[str]:
    return {key for kind, key in _CONDITIONAL_WIDGETS if s.has(kind, key)}


# --- UI-01 ~ UI-12 ---


def _root_token(screen: "_Screen", name: str) -> str | None:
    """page_css 의 :root 에 들어간 색 토큰 값(§7.2)."""
    for item in screen.at.html:
        match = re.search(rf"--mr-{name}: ([^;]+);", item.value)
        if match:
            return match.group(1)
    return None


def _ui01(c: _Checker, folder: Path, maps: _MapCalls) -> None:
    hand = ce.build_scenarios()
    _save_variant(folder, "GV-ESC")
    spec = {"id": "GV-ESC", "base": "골든", "bbox": [37.49, 127.0, 37.51, 127.02]}
    (folder / "scenarios" / "GV-ESC.spec.json").write_text(json.dumps(spec, ensure_ascii=False), encoding="utf-8")
    s = _Screen(c, maps).run("첫 실행")
    c.eq("② 시나리오 선택지", [hand["A"].title, hand["B"].title, _GOLDEN_LABEL, "골든 변형 GV-ESC (생성)"],
         s.options("selectbox", "scenario_id"))
    c.eq("③ 기본 시나리오", "A", s.state("scenario_id"))
    for scenario_id in ("A", "B", ce.GOLDEN_ID):
        if s.state("scenario_id") != scenario_id:
            s.scenario(scenario_id)
        c.eq(f"① {scenario_id}: 제목", [APP_TITLE], [item.value for item in s.at.title])
        c.true(f"① {scenario_id}: 제목 아래 한 줄 설명", APP_SUBTITLE in [item.value for item in s.at.main.caption])
        c.true(f"① {scenario_id}: 바닥글", _FOOTER in [item.value for item in s.at.main.caption])
        strings = s.strings()
        for word in _BANNED_WORDS:
            hits = [text for text in strings if word in text]
            c.true(f"① {scenario_id}: 화면 글자에 '{word}' 없음", not hits, hits[:2])
    c.eq("④ 골든 한 줄 설명", "출발: 출발지 · 기준 시각 08:00:00 · 목적지: 도착지", s.description())
    c.true("④ 머리말 배지 '시뮬레이션 값'", "시뮬레이션 값" in s.chips(), s.chips())
    c.true("④ 머리말 배지 '미검증 좌표 29개'", "미검증 좌표 29개" in s.strings())
    # ⑤ 테마(§7.2): 세션 첫 실행은 서버 설정 theme.base 를 쓰고, 그다음 실행부터는 st.context.theme.type (테스트 환경에서 None)
    from unittest import mock

    plain = _Screen(c, maps).run("theme.base 가 없는 첫 실행")
    c.eq("⑤ theme.base 가 없으면 첫 실행도 st.context.theme.type (None → 밝은 토큰)", TOKENS_LIGHT["ink"], _root_token(plain, "ink"))
    original = st.get_option
    with mock.patch.object(st, "get_option", side_effect=lambda key: "dark" if key == "theme.base" else original(key)):
        dark = _Screen(c, maps).run("theme.base 가 dark 인 첫 실행")
        c.eq("⑤ theme.base 가 dark 면 첫 실행은 어두운 토큰", TOKENS_DARK["ink"], _root_token(dark, "ink"))
        dark.run("theme.base 가 dark 인 두 번째 실행")
        c.eq("⑤ 두 번째 실행부터는 st.context.theme.type (None → 밝은 토큰)", TOKENS_LIGHT["ink"], _root_token(dark, "ink"))


def _ui02(c: _Checker, folder: Path, maps: _MapCalls) -> None:
    truth = ce.make_synthetic_records(folder)
    hand = ce.build_scenarios()
    golden = ce.golden_scenario()
    config = EngineConfig()
    s = _Screen(c, maps).run("첫 실행")
    # ① 늘 있는 키와 시나리오별 기본값
    for scenario_id, scenario in (("A", hand["A"]), ("B", hand["B"]), (ce.GOLDEN_ID, golden)):
        if s.state("scenario_id") != scenario_id:
            s.scenario(scenario_id)
        out = ce.run_engine(scenario, scenario.default_query, config)
        best = out.best_id
        first_bus = next((times.route_id for times in out.line_times if times.mode == TravelMode.BUS), None)
        expected = {"scenario_id": scenario_id, **_base_defaults(), **_query_key_defaults(scenario),
                    "selected_id": best, "last_default_id": best, "trace_line": first_bus}
        for key, value in expected.items():
            c.eq(f"① {scenario_id}: {key}", value, s.state(key))
    c.eq("① 골든: 출발 장소와 목적지 장소", ("PLACE", "출발지", "도착지"),
         (s.state("origin_kind"), s.state("origin_place"), s.state("dest_place")))
    # ② 조건부 위젯 (골든)
    c.eq("② 기본 상태의 조건부 위젯", set(), _conditional_present(s))
    defaults = _conditional_defaults(golden)
    s.set("toggle", "use_deadline", True)
    c.eq("② 마감을 켜면", {"deadline_time"}, _conditional_present(s))
    c.eq("① deadline_time 기본값", defaults["deadline_time"], s.state("deadline_time"))
    s.set("toggle", "use_deadline", False)
    s.set("selectbox", "rank_criterion", RankCriterion.UTILITY.value)
    c.eq("② 종합 점수, 프리셋 '균형'", (set(), "균형"), (_conditional_present(s), s.state("weight_preset")))
    s.set("segmented_control", "weight_preset", WEIGHT_CUSTOM)
    c.eq("② 가중치 '직접 설정'", {"w_time", "w_cost", "w_risk"}, _conditional_present(s))
    c.eq("① 가중치 기본값", tuple(defaults[k] for k in ("w_time", "w_cost", "w_risk")),
         tuple(s.state(k) for k in ("w_time", "w_cost", "w_risk")))
    s.set("selectbox", "rank_criterion", RankCriterion.MEAN_ARRIVAL.value)
    c.eq("② 평균 도착 순으로 돌리면", set(), _conditional_present(s))
    s.set("segmented_control", "walk_preset", "직접")
    c.eq("② 걷는 속도 '직접'", ({"v_walk"}, defaults["v_walk"]), (_conditional_present(s), s.state("v_walk")))
    s.set("segmented_control", "walk_preset", "보통")
    s.set("segmented_control", "origin_kind", "POINT")
    c.eq("② 출발만 지도에서", set(), _conditional_present(s))
    s.set("segmented_control", "dest_kind", "POINT")
    c.eq("② 둘 다 지도에서", ({"map_pick"}, "ORIGIN"), (_conditional_present(s), s.state("map_pick")))
    s.set("segmented_control", "dest_kind", "PLACE")
    s.set("segmented_control", "origin_kind", "TRAIN")
    first_train = ce.train_candidates(golden, "M1", config)[0]
    c.eq("② 지금 탄 열차", {"train_station", "train_key", "prior_km"}, _conditional_present(s))
    c.eq("① 열차 기본값", ("M1", f"{first_train.pattern_id}|{first_train.trip_id}|{first_train.index}", 0.0),
         (s.state("train_station"), s.state("train_key"), s.state("prior_km")))
    s.set("segmented_control", "origin_kind", "BUS")
    line = next(item for item in golden.bus_lines if item.id == "G1")
    first_bus = ce.stop_vehicle_order(ce.build_bus_trips(line, golden.clock_s, config), 0)[0][0]
    c.eq("② 지금 탄 버스", {"bus_line", "bus_stop_index", "bus_vehicle", "prior_km"}, _conditional_present(s))
    c.eq("① 버스 기본값", ("G1", 0, first_bus), (s.state("bus_line"), s.state("bus_stop_index"), s.state("bus_vehicle")))
    s.set("segmented_control", "origin_kind", "PLACE")
    c.eq("② 장소로 돌리면", set(), _conditional_present(s))
    keys = EngineConfig()
    for name, value in ((keys.env_seoul_key, "UITEST-SEOUL"),):
        os.environ[name] = value
    try:
        with _replaced(ce, "apply_live_overrides", lambda scenario, config, *args, **kwargs: (scenario, ())):
            s.set("segmented_control", "data_mode", "LIVE")
            c.eq("② 실시간", {"live_refresh_button"}, _conditional_present(s))
            s.set("segmented_control", "data_mode", "SIMULATION")
    finally:
        os.environ.pop(keys.env_seoul_key, None)
    s.scenario(ce.load_scenario_json(truth.scenario_path).id)
    s.set("segmented_control", "data_mode", "REPLAY")
    c.eq("② 기록 재생", {"replay_window", "replay_date", "replay_time"}, _conditional_present(s))
    s.set("segmented_control", "data_mode", "SIMULATION")
    c.eq("② 시뮬레이션으로 돌리면", set(), _conditional_present(s))
    # ③ 보존 키 (골든)
    s.scenario(ce.GOLDEN_ID)
    s.set("segmented_control", "walk_preset", "직접")
    s.set("slider", "v_walk", 1.4)
    s.set("segmented_control", "walk_preset", "보통")
    c.true("③ '보통'이면 v_walk 슬라이더가 없다", not s.has("slider", "v_walk"))
    s.set("segmented_control", "walk_preset", "직접")
    c.eq("③ v_walk 되살림", 1.4, s.state("v_walk"))
    s.set("segmented_control", "walk_preset", "보통")
    s.set("selectbox", "rank_criterion", RankCriterion.UTILITY.value)
    s.set("segmented_control", "weight_preset", WEIGHT_CUSTOM)
    for key, value in (("w_time", 0.7), ("w_cost", 0.1), ("w_risk", 0.4)):
        s.set("slider", key, value)
    s.set("segmented_control", "weight_preset", "균형")
    c.true("③ '균형'이면 가중치 슬라이더가 없다", not s.has("slider", "w_time"))
    s.set("segmented_control", "weight_preset", WEIGHT_CUSTOM)
    c.eq("③ 가중치 되살림", (0.7, 0.1, 0.4), tuple(s.state(k) for k in ("w_time", "w_cost", "w_risk")))
    s.set("selectbox", "rank_criterion", RankCriterion.MEAN_ARRIVAL.value)
    s.set("selectbox", "rank_criterion", RankCriterion.UTILITY.value)
    c.eq("③ 순위 기준을 바꿨다 돌려도 가중치 유지", (WEIGHT_CUSTOM, 0.7, 0.1, 0.4),
         (s.state("weight_preset"), *(s.state(k) for k in ("w_time", "w_cost", "w_risk"))))
    s.set("selectbox", "rank_criterion", RankCriterion.MEAN_ARRIVAL.value)
    s.set("toggle", "use_deadline", True)
    s.set("time_input", "deadline_time", datetime.time(8, 16, 40))
    s.set("toggle", "use_deadline", False)
    s.set("toggle", "use_deadline", True)
    c.eq("③ deadline_time 되살림", datetime.time(8, 16, 40), s.state("deadline_time"))
    s.set("toggle", "use_deadline", False)
    # ④ required 가드
    for kind, key, expected in (("segmented_control", "data_mode", "SIMULATION"), ("segmented_control", "origin_kind", "PLACE"),
                                ("segmented_control", "dest_kind", "PLACE"), ("segmented_control", "walk_preset", "보통")):
        s.set(kind, key, None)
        c.eq(f"④ {key} 에 None", expected, s.state(key))
    # ⑤ 기본 출발이 열차인 A 에서 출발을 "장소"로 돌리면 목적지와 다른 첫 장소에서 출발한다
    s.scenario("A")
    s.set("segmented_control", "origin_kind", "PLACE")
    c.eq("⑤ A: 출발을 장소로 돌리면 (출발 장소, 같은 장소 안내, KPI 칸 수)", ("삼성역 7번 출구", False, 4),
         (s.state("origin_place"), "출발과 목적지가 같은 장소입니다. 다른 장소를 고르세요." in s.main_texts("info"), len(s.kpi())))


def _ui03(c: _Checker, folder: Path, maps: _MapCalls) -> None:
    golden = ce.golden_scenario()
    config = EngineConfig()
    out = ce.run_engine(golden, ce.golden_query(), config)
    panel = compare_panel_html(out, config)

    def cards(markup: str) -> tuple[str, str]:
        naive_at = markup.find('class="mr-card naive')
        app_at = markup.find('class="mr-card app')
        end = markup.find('class="mr-conclusion"')
        return markup[naive_at:app_at], markup[app_at:end]

    def rows(markup: str) -> list[str]:
        return [_plain(part) for part in re.findall(r'<div class="mr-row[^"]*">(.*?)</div>', markup)]

    def part(markup: str, css: str) -> str:
        found = re.search(rf'<div class="{css}">(.*?)</div>', markup)
        return _plain(found.group(1)) if found else ""

    naive_html, best_html = cards(panel)
    naive_rows, best_rows = rows(naive_html), rows(best_html)
    c.eq("골든: 왼쪽 머리글과 제목", ("기존 앱 방식의 1위", "가상1번 → 가상2번"), (part(naive_html, "mr-head"), part(naive_html, "mr-title")))
    badges = _plain(naive_html[naive_html.find("mr-badgerow"):])
    c.true("골든: 왼쪽 배지 '안전', '유령 환승 1'", "안전" in badges and "유령 환승 1" in badges, badges)
    c.true("골든: 왼쪽 줄 1 '약속 도착 08:10:42'", len(naive_rows) == 3 and "약속 도착 08:10:42" in naive_rows[0], naive_rows)
    c.true("골든: 왼쪽 줄 2 '08:21:58', '08:22:02'", len(naive_rows) == 3 and "08:21:58" in naive_rows[1] and "08:22:02" in naive_rows[1],
           naive_rows)
    c.true("골든: 왼쪽 줄 3 '95.2%'", len(naive_rows) == 3 and "95.2%" in naive_rows[2], naive_rows)
    c.eq("골든: 오른쪽 머리글과 제목", ("이 앱의 추천", "따릉이"), (part(best_html, "mr-head"), part(best_html, "mr-title")))
    c.true("골든: 오른쪽 배지 '안전'", "안전" in _plain(best_html[best_html.find("mr-badgerow"):]))
    c.true("골든: 오른쪽 값", len(best_rows) == 3 and "약속 도착 08:09:06" in best_rows[0] and "평균 도착 08:11:14" in best_rows[1]
           and "90% 08:21:41" in best_rows[1] and "87.5%" in best_rows[2], best_rows)
    c.eq("골든: 결론 문장",
         ("기존 앱 방식의 1위는 08:10:42 도착을 약속하지만, 이 앱이 계산한 평균 도착은 08:21:58(11분 16초 늦음)입니다.",
          "이 앱의 추천은 평균 08:11:14에 도착해 10분 44초 줄입니다."),
         conclusion_lines(out, config))
    same = ce.run_engine(golden, ce.golden_train_query(), config)
    c.eq("같은 여정", ("기존 앱 방식의 1위와 이 앱의 추천이 같은 경로입니다.",), conclusion_lines(same, config))
    naive_id = out.comparison.naive_best_id
    ghost_same = out.model_copy(update={"best_id": naive_id,
                                        "comparison": out.comparison.model_copy(update={"best_id": naive_id, "same": True})})
    c.eq("같은 여정에 유령 환승",
         ("기존 앱 방식의 1위와 이 앱의 추천이 같은 경로입니다.",
          "다만 기존 앱이 안내하는 가상2번 차량은 탈 확률이 1.3%라, 이 앱은 2번째 차를 안내합니다."),
         conclusion_lines(ghost_same, config))
    last = ce.run_engine(ce.golden_last_vehicle_scenario(), ce.golden_query(), config)
    last_naive, _ = cards(compare_panel_html(last, config))
    last_badges = _plain(last_naive[last_naive.find("mr-badgerow"):])
    c.true("걸러짐: 왼쪽 배지 '걸러짐', '막차 위험', '확률 낮음'",
           all(word in last_badges for word in ("걸러짐", "막차 위험", "확률 낮음")), last_badges)
    c.eq("걸러짐: 결론 문장",
         ("기존 앱 방식의 1위는 08:10:42 도착을 약속하지만 걸러졌습니다: 탑승 2(가상2번)에서 막차까지 따져도 계획대로 탈 확률이 "
          "1.3%로 기준 40.0%에 못 미칩니다.",
          "이 앱의 추천은 평균 08:11:14에 도착해 9분 13초 줄입니다."),
         conclusion_lines(last, config))
    p90_config = EngineConfig(rank_criterion=RankCriterion.P90_ARRIVAL)
    p90 = ce.run_engine(golden, ce.golden_query(), p90_config)
    c.eq("평균이 아닌 기준: 최선", "Idddde0a626", p90.best_id)
    c.eq("평균이 아닌 기준: 둘째 문장", "이 앱의 추천은 평균 08:17:25에 도착해 4분 34초 줄입니다.",
         conclusion_lines(p90, p90_config)[-1])
    late = p90.model_copy(update={"comparison": p90.comparison.model_copy(update={"saving_s": -30.0})})
    c.eq("평균이 늦은 추천: 둘째 문장", "이 앱의 추천은 90% 도착 기준이라 평균 도착은 30초 늦지만 90% 도착이 3분 16초 이릅니다.",
         conclusion_lines(late, p90_config)[-1])
    no_best = out.model_copy(update={"ranking": (), "best_id": None,
                                     "comparison": out.comparison.model_copy(update={"best_id": None})})
    c.true("최선 없음: 오른쪽 카드",
           "계획대로 갈 수 있는 경로가 없습니다. 걸러진 경로와 사유는 오른쪽 목록에 있습니다." in _plain(cards(compare_panel_html(no_best, config))[1]))
    no_naive = out.model_copy(update={"comparison": out.comparison.model_copy(update={"naive_best_id": None})})
    c.true("기존 방식 없음: 왼쪽 카드",
           "기존 앱 방식으로는 경로를 찾지 못했습니다." in _plain(cards(compare_panel_html(no_naive, config))[0]))
    _save_variant(folder, "GV-ESC")
    s = _Screen(c, maps).run().scenario(ce.GOLDEN_ID)
    c.eq("화면: 비교 패널 HTML 하나가 직접 부른 결과와 같다", [panel], s.htmls("mr-compare"))
    s.scenario("GV-ESC")
    fragments = [item.value for item in s.at.html]
    raw = [text for text in fragments if "<b>가상1</b>" in text or "정류장<i>1" in text]
    c.true("이스케이프: 원래 글자가 HTML 로 나오지 않는다", not raw, raw[:1])
    c.true("이스케이프: '&lt;b&gt;' 가 있다", any("&lt;b&gt;" in text for text in fragments))


def _ui04(c: _Checker, folder: Path, maps: _MapCalls) -> None:
    hand = ce.build_scenarios()
    config = EngineConfig()
    s = _Screen(c, maps).run().scenario(ce.GOLDEN_ID)
    c.eq("골든 기본 KPI", _GOLDEN_KPI, s.kpi())
    s.set("segmented_control", "origin_kind", "TRAIN")
    s.set("selectbox", "train_station", "M2")
    s.set("selectbox", "train_key", f"{ce.GOLDEN_PATTERN_ID}|1000|1")
    c.eq("골든 열차 질의 KPI", [("평균 도착", "08:07:57", ""), ("90% 도착", "08:08:27", ""), ("계획대로 갈 확률", "100.0%", ""),
                              ("요금", "1,550원", "변동 없음")], s.kpi())
    c.eq("골든 열차 질의 KPI = 엔진", _kpi_expect(ce.run_engine(ce.golden_scenario(), ce.golden_train_query(), config)), s.kpi())
    s.set("segmented_control", "origin_kind", "PLACE")
    s.set("toggle", "use_deadline", True)
    s.set("time_input", "deadline_time", datetime.time(8, 16, 40))
    kpi = s.kpi()
    c.eq("마감 08:16:40: 확률 타일의 설명", "마감까지 도착할 확률 87.5%", kpi[2][2] if len(kpi) == 4 else None)
    for scenario_id in ("A", "B"):
        s.scenario(scenario_id)
        scenario = hand[scenario_id]
        c.eq(f"{scenario_id} KPI = 엔진", _kpi_expect(ce.run_engine(scenario, scenario.default_query, config)), s.kpi())


def _ui05(c: _Checker, folder: Path, maps: _MapCalls) -> None:
    golden = ce.golden_scenario()
    config = EngineConfig()
    out = ce.run_engine(golden, ce.golden_query(), config)
    items = _items_of(out)
    fmap = build_map(golden, out, "Ic5c1b22780")
    groups = feature_groups(fmap)
    c.eq("레이어 9개", ["선택한 여정", "기존 앱 방식 1위", "출발·도착", "탐색 타원", "정류장·역", "따릉이 대여소", "신호", "탐색 라운드",
                     "타원 밖 노드"], list(groups))
    c.eq("처음에 꺼진 레이어", ["탐색 라운드", "타원 밖 노드"], [name for name, group in groups.items() if not group.show])
    tiles = [child for child in fmap._children.values() if isinstance(child, folium.TileLayer)]
    c.true("타일은 OpenStreetMap 하나", len(tiles) == 1 and "tile.openstreetmap.org" in str(tiles[0].tiles),
           [str(tile.tiles) for tile in tiles])
    page = fmap.get_root().render()
    c.true("HTML 에 cartodb 없음", "cartodb" not in page.lower())
    c.eq("선택한 여정의 선 (Ic5c1b22780)", _route_sequences(golden, items["Ic5c1b22780"]), _group_lines(groups["선택한 여정"]))
    ghosts = _group_markers(groups["기존 앱 방식 1위"])
    c.eq("기존 앱 방식 1위: 유령 표지 하나, 위치 B4", [_coord(golden, "B4")], [_marker_place(marker) for marker in ghosts])
    rounds = _group_markers(groups["탐색 라운드"])
    c.eq("탐색 라운드 표지 수 = reach 수 = 13", (13, 13), (len(out.search.reach), len(rounds)))
    b3 = [marker for marker in rounds if _marker_place(marker) == _coord(golden, "B3")]
    c.eq("B3 의 라운드 표지 글자", ["1"], [_plain(marker.icon.options.get("html", "")) for marker in b3])
    other = feature_groups(build_map(golden, out, "Ifbf4ec4c04"))
    c.true("Ifbf4ec4c04 를 고르면 기존 앱 방식 1위 레이어가 없다", "기존 앱 방식 1위" not in other, list(other))
    naive_lines = _group_lines(other["선택한 여정"]) if "선택한 여정" in other else set()
    c.eq("선택한 여정의 선 (Ifbf4ec4c04)", _route_sequences(golden, items["Ifbf4ec4c04"]), naive_lines)
    c.true("Ifbf4ec4c04: B1 → B2, B4 → B5 탑승 선",
           (_coord(golden, "B1"), _coord(golden, "B2")) in naive_lines and (_coord(golden, "B4"), _coord(golden, "B5")) in naive_lines)
    kakao = {"state": "OK", "units": [{"name": "출발지 → 대여소1", "ours_m": 50.0, "state": "OK", "basic": (58.0, 50.0),
                                       "shortest": (55.0, 47.0), "ratio": 1.1, "warn": False,
                                       "coords": ((37.5, 127.0), (37.50027, 127.00045))}]}
    c.true("카카오 결과를 주면 '카카오 도보 경로(비교)' 레이어", "카카오 도보 경로(비교)" in feature_groups(build_map(golden, out, "Ic5c1b22780", kakao=kakao)))
    # 어두운 토큰(§7.7): 바탕 타일이 늘 밝으므로 중립 색은 밝은 토큰, 수단 색만 어두운 토큰
    dark_page = build_map(golden, out, "Ic5c1b22780", kakao=kakao, tokens=TOKENS_DARK).get_root().render().lower()
    c.true("어두운 토큰: 지도에 어두운 글자색(ink) 없음", TOKENS_DARK["ink"] not in dark_page)
    c.true("어두운 토큰: '출발'·'도착' 표지와 카카오 선은 밝은 ink, 도보 선은 밝은 ink2",
           TOKENS_LIGHT["ink"] in dark_page and TOKENS_LIGHT["ink2"] in dark_page)
    c.true("어두운 토큰: 따릉이 선과 대여소는 어두운 따릉이 색", TOKENS_DARK["bike"] in dark_page and TOKENS_LIGHT["bike"] not in dark_page)
    for variant_id, count in (("GV-MANYW", 0), ("GV-MANYI", 500)):
        variant = _golden_variant(variant_id)
        variant_out = ce.run_engine(variant, ce.golden_query(), config)
        layers = feature_groups(build_map(variant, variant_out, variant_out.best_id))
        layer = layers.get("타원 밖 노드 (경유점 생략)")
        c.true(f"{variant_id}: 레이어 이름 '타원 밖 노드 (경유점 생략)'", layer is not None, list(layers))
        circles = _group_markers(layer, circles=True) if layer is not None else []
        c.eq(f"{variant_id}: 표지 수", count, len(circles))
        if variant_id == "GV-MANYI":
            kinds = {node.id: node.node_type for node in variant.nodes}
            outside = sorted(record.node_id for record in variant_out.pruning_records
                             if not record.kept and kinds.get(record.node_id) != NodeType.WAYPOINT)
            c.eq("GV-MANYI: 노드 ID 순 앞 500개", {_coord(variant, node_id) for node_id in outside[:500]},
                 {_marker_place(marker) for marker in circles})
    maps.render = True
    _Screen(c, maps).run().scenario(ce.GOLDEN_ID)
    call = maps.calls[-1] if maps.calls else {}
    c.eq("화면: 지도 호출 인자", {"key": "map", "height": 480, "use_container_width": True, "returned_objects": []},
         {key: call.get(key) for key in ("key", "height", "use_container_width", "returned_objects")})
    c.eq("화면: 지도 HTML 을 만들 때 예외 없음", [], maps.errors)
    c.eq("화면: 지도 레이어", list(groups), list(call.get("layers", ())))


def _ui06(c: _Checker, folder: Path, maps: _MapCalls) -> None:
    golden = ce.golden_scenario()
    config = EngineConfig()
    out = ce.run_engine(golden, ce.golden_query(), config)
    items = _items_of(out)
    _save_variant(folder, "GV-LAST")
    s = _Screen(c, maps).run().scenario(ce.GOLDEN_ID)
    radio = s.at.radio(key="selected_id")
    c.eq("라디오 선택지", ["**1위** 따릉이", "**2위** 지하철 가상선", "**3위** 가상1번", "**4위** 가상1번 → 가상2번", "**5위** 도보"],
         list(radio.options))
    c.eq("기본 선택", "Ic5c1b22780", radio.value)
    captions = list(radio.proto.captions)
    order = list(out.ranking)
    for itinerary_id, text in (
        ("Ic5c1b22780", "평균 08:11:14 · 90% 08:21:41 · 확률 87.5% 안전 · 1,000원 · 걷기 120 m"),
        ("Ifbf4ec4c04", "평균 08:21:58 · 90% 08:22:02 · 확률 95.2% 안전 · 1,500원 · 걷기 310 m · 기존 앱 1위 · 유령 환승 1"),
        ("If1e99436b8", "평균 08:22:00 · 90% 08:25:13 · 확률 100.0% 안전 · 0원 · 걷기 1.60 km"),
    ):
        index = order.index(itinerary_id) if itinerary_id in order else -1
        c.eq(f"캡션 {itinerary_id}", text, captions[index] if 0 <= index < len(captions) else None)
    selected = items["Ic5c1b22780"]
    timeline = s.htmls("mr-tl")
    c.eq("시간 막대 구간 수 = legs 수", (1, len(selected.legs)), (len(timeline), timeline[0].count('class="mr-seg ') if timeline else 0))
    ends = _plain(timeline[0]) if timeline else ""
    c.true("시간 막대 양 끝", "08:00:00 출발" in ends and "08:09:06 도착(계획)" in ends, ends)
    c.eq("여정 안내 (Ic5c1b22780)",
         ("따릉이: 대여소1까지 걷기 50 m → 대여 → 대여소2까지 1.64 km 주행 → 반납 → 도착지까지 걷기 70 m · 모두 9분 06초 · "
          "자전거가 남아 있을 확률 87.5%",
          "도착 도착지 · 평균 08:11:14, 90% 08:21:41"),
         guide_lines(selected, out, golden, config))
    c.eq("화면의 여정 안내 = 직접 부른 결과", _plain(guide_html(selected, out, golden, config)), s.html_text("mr-steps"))
    s.set("toggle", "show_variants", True)
    options = s.options("radio", "selected_id")
    anchor = options.index("**2위** 지하철 가상선") if "**2위** 지하철 가상선" in options else -2
    c.eq("다른 걷는 길: 대표 바로 아래", "↳ 다른 걷는 길 · 걷기 730 m", options[anchor + 1] if anchor >= 0 else None)
    c.true("다른 걷는 길의 ID 는 I469424fb69", "I469424fb69" in items["I3a248c7d10"].variant_ids, items["I3a248c7d10"].variant_ids)
    s.set("toggle", "show_variants", False)
    s.set("radio", "selected_id", "Ifbf4ec4c04")
    naive_lines = ("걷기 170 m · 2분 16초 → 정류장1",
                   "가상1번 1번째 차 · 정류장1 08:03:20 → 정류장2 08:05:50 · 탈 확률 95.2% · 1분 04초 기다림",
                   "걷기 60 m · 1분 22초 → 정류장4 (신호 1개, 대기 34초)",
                   "가상2번 2번째 차 · 정류장4 08:17:00 → 정류장5 08:20:00 · 탈 확률 95.2% · 9분 48초 기다림\n"
                   "기존 앱은 1번째 차를 안내하지만 탈 확률이 1.3%입니다(유령 환승).",
                   "걷기 80 m · 1분 53초 → 도착지 (신호 1개, 대기 49초)",
                   "도착 도착지 · 평균 08:21:58, 90% 08:22:02")
    c.eq("여정 안내 (Ifbf4ec4c04)", naive_lines, guide_lines(items["Ifbf4ec4c04"], out, golden, config))
    steps = s.html_text("mr-steps")
    missing = [line for text in naive_lines for line in text.split("\n") if line not in steps]
    c.eq("화면의 여정 안내 (Ifbf4ec4c04)", [], missing)
    s.scenario("GV-LAST")
    options = s.options("radio", "selected_id")
    c.eq("GV-LAST: 맨 아래 선택지", "✕ 가상1번 → 가상2번 (걸러짐)", options[-1] if options else None)
    last_captions = list(s.at.radio(key="selected_id").proto.captions)
    c.true("GV-LAST: 캡션 끝 ' · 막차 위험 · 확률 낮음'", bool(last_captions) and last_captions[-1].endswith(" · 막차 위험 · 확률 낮음"),
           last_captions[-1:] if last_captions else None)


def _ui07(c: _Checker, folder: Path, maps: _MapCalls) -> None:
    golden = ce.golden_scenario()
    query = ce.golden_query()

    def expect(scenario: Scenario = golden, q: Query = query, **changes: Any) -> EngineOutput:
        return ce.run_engine(scenario, q, EngineConfig(**changes))

    s = _Screen(c, maps).run().scenario(ce.GOLDEN_ID)
    # ① 기후동행카드
    s.set("toggle", "climate_card", True)
    c.eq("① 기후동행카드 KPI", _kpi_expect(expect(climate_card=True)), s.kpi())
    c.eq("① 요금과 변화량", ("1,000원", "+1,000원"), s.kpi()[3][1:] if len(s.kpi()) == 4 else None)
    s.set("toggle", "climate_card", False)
    # ② 출발 늦추기 300
    s.set("select_slider", "depart_offset_s", 300)
    shifted = ce.advance_clock(golden, 300.0, EngineConfig())
    moved = expect(shifted)
    c.eq("② 늦추기 300 KPI", _kpi_expect(moved), s.kpi())
    c.eq("② 평균", "08:21:52", s.kpi()[0][1] if s.kpi() else None)
    c.eq("② 선택이 옮겨 간다", "I469424fb69", s.state("selected_id"))
    c.true("② 아래 글씨", "5분 뒤 출발 (08:05:00)" in s.side_captions(), s.side_captions())
    s.set("select_slider", "depart_offset_s", 0)
    # ③ 고른 여정이 결과에 있으면 유지
    s.set("radio", "selected_id", "If1e99436b8")
    s.set("select_slider", "depart_offset_s", 300)
    c.eq("③ 고른 If1e99436b8 유지", "If1e99436b8", s.state("selected_id"))
    s.set("select_slider", "depart_offset_s", 0)
    # ④ 결과에 없으면 기본값
    s.set("radio", "selected_id", "Idddde0a626")
    s.set("select_slider", "depart_offset_s", 300)
    c.true("④ Idddde0a626 은 늦춘 결과에 없다", "Idddde0a626" not in _items_of(moved))
    c.eq("④ 기본값으로 돌아간다", "I469424fb69", s.state("selected_id"))
    s.set("select_slider", "depart_offset_s", 0)
    # ⑤ 종합 점수
    s.set("selectbox", "rank_criterion", RankCriterion.UTILITY.value)
    s.set("segmented_control", "weight_preset", "요금 우선")
    cost_first = expect(rank_criterion=RankCriterion.UTILITY, w_time=0.3, w_cost=0.5, w_risk=0.2)
    c.eq("⑤ '요금 우선' KPI", _kpi_expect(cost_first), s.kpi())
    c.eq("⑤ '요금 우선' 순위", _route_labels(cost_first), s.options("radio", "selected_id")[:len(cost_first.ranking)])
    c.true("⑤ 가중치 문구", "시간 30% · 요금 50% · 위험 20%" in s.side_captions(), s.side_captions())
    s.set("segmented_control", "weight_preset", WEIGHT_CUSTOM)
    for key, value in (("w_time", 0.5), ("w_cost", 0.5), ("w_risk", 1.0)):
        s.set("slider", key, value)
    custom = expect(rank_criterion=RankCriterion.UTILITY, w_time=0.25, w_cost=0.25, w_risk=0.5)
    c.eq("⑤ 직접 설정 (0.5, 0.5, 1.0) KPI = (0.25, 0.25, 0.5) 결과", _kpi_expect(custom), s.kpi())
    c.eq("⑤ 직접 설정 순위", _route_labels(custom), s.options("radio", "selected_id")[:len(custom.ranking)])
    c.true("⑤ 직접 설정 문구", "시간 25% · 요금 25% · 위험 50%" in s.side_captions(), s.side_captions())
    s.set("segmented_control", "weight_preset", "균형")
    s.set("selectbox", "rank_criterion", RankCriterion.MEAN_ARRIVAL.value)
    # ⑥ 마감 확률 순
    s.set("selectbox", "rank_criterion", RankCriterion.ON_TIME.value)
    c.true("⑥ 마감 없음 안내", "마감 시각을 켜면 그 기준으로 정렬합니다. 지금은 평균 도착 순입니다." in s.side_captions(), s.side_captions())
    c.true("⑥ 경고 DEADLINE_MISSING", "DEADLINE_MISSING" in s.html_text("mr-warnlist"))
    s.set("toggle", "use_deadline", True)
    s.set("time_input", "deadline_time", datetime.time(8, 16, 40))
    timed = expect(q=Query(origin=query.origin, destination_node_id=query.destination_node_id, deadline_s=1000.0),
                   rank_criterion=RankCriterion.ON_TIME)
    c.eq("⑥ 마감 1,000 의 순위", ("Ic5c1b22780", "I3a248c7d10", "Idddde0a626", "Ifbf4ec4c04", "If1e99436b8"), tuple(timed.ranking))
    c.eq("⑥ 마감 08:16:40 KPI", _kpi_expect(timed), s.kpi())
    c.eq("⑥ 라디오 순서", _route_labels(timed), s.options("radio", "selected_id")[:len(timed.ranking)])
    captions = list(s.at.radio(key="selected_id").proto.captions)
    c.true("⑥ 캡션 ' · 마감 확률 87.5%'", bool(captions) and captions[0].endswith(" · 마감 확률 87.5%"), captions[:1])
    s.set("time_input", "deadline_time", datetime.time(7, 59))
    c.true("⑥ 지난 마감 안내", "마감 시각이 이미 지났습니다" in s.side_captions(), s.side_captions())
    c.eq("⑥ 지난 마감 KPI = 마감 없는 결과", _kpi_expect(expect(rank_criterion=RankCriterion.ON_TIME)), s.kpi())
    c.eq("⑥ deadline_t", (None, 1000.0), (deadline_t(28_740, 28_800), deadline_t(29_800, 28_800)))
    s.set("toggle", "use_deadline", False)
    s.set("selectbox", "rank_criterion", RankCriterion.MEAN_ARRIVAL.value)
    # ⑦ 수단을 모두 끔
    for key in ("use_bus", "use_subway", "use_bike"):
        s.set("toggle", key, False)
    walk_only = expect(modes_enabled=())
    c.true("⑦ 안내", "걷기만으로 찾습니다" in s.side_captions(), s.side_captions())
    c.eq("⑦ KPI = modes_enabled ()", _kpi_expect(walk_only), s.kpi())
    c.eq("⑦ 최선", ("If1e99436b8", "If1e99436b8"), (walk_only.best_id, s.state("selected_id")))
    for key in ("use_bus", "use_subway", "use_bike"):
        s.set("toggle", key, True)
    # ⑧ 걷는 속도
    s.set("segmented_control", "walk_preset", "느리게")
    c.eq("⑧ '느리게' KPI = v_walk_mps 1.0", _kpi_expect(expect(v_walk_mps=1.0)), s.kpi())
    s.set("segmented_control", "walk_preset", "보통")
    # ⑨ 하나씩
    defaults = _base_defaults()
    for kind, key, value, field, field_value in (
        ("slider", "max_rides", 1, "max_rides", 1),
        ("toggle", "full_skip", True, "full_vehicle_policy", FullVehiclePolicy.SKIP),
        ("slider", "safety_buffer", 60.0, "safety_buffer_s", 60.0),
        ("slider", "gamma", 1.6, "gamma", 1.6),
        ("slider", "v_pm", 5.0, "v_pm_mps", 5.0),
    ):
        s.set(kind, key, value)
        c.eq(f"⑨ {key} {value} KPI = {field} 만 바꾼 결과", _kpi_expect(expect(**{field: field_value})), s.kpi())
        s.set(kind, key, defaults[key])
    c.eq("⑨ 되돌린 뒤 골든 기본 KPI", _GOLDEN_KPI, s.kpi())


def _ui08(c: _Checker, folder: Path, maps: _MapCalls) -> None:
    truth = ce.make_synthetic_records(folder)
    hand = ce.build_scenarios()
    golden = ce.golden_scenario()
    s = _Screen(c, maps).run()
    # 재생 구간·날짜·시각을 정해 둔다(② 에서 그대로인지 본다)
    s.scenario(ce.load_scenario_json(truth.scenario_path).id)
    s.set("segmented_control", "data_mode", "REPLAY")
    window = str(s.state("replay_window")).split("|", 1)[-1]
    s.set("selectbox", "replay_window", f"2026-11-03|{window}")
    s.set("time_input", "replay_time", datetime.time(8, 5))
    replay_values = (s.state("replay_window"), s.state("replay_date"), s.state("replay_time"))
    c.eq("준비: 재생 값", (f"2026-11-03|{window}", datetime.date(2026, 11, 3), datetime.time(8, 5)), replay_values)
    s.set("segmented_control", "data_mode", "SIMULATION")
    # ① 골든에서 여럿 바꾸고 되돌리기
    s.scenario(ce.GOLDEN_ID)
    s.set("radio", "selected_id", "Idddde0a626")
    s.set("select_slider", "depart_offset_s", 600)
    s.set("toggle", "use_deadline", True)
    s.set("time_input", "deadline_time", datetime.time(8, 16, 40))
    s.set("selectbox", "rank_criterion", RankCriterion.UTILITY.value)
    s.set("segmented_control", "weight_preset", WEIGHT_CUSTOM)
    s.set("slider", "w_time", 0.8)
    s.set("segmented_control", "walk_preset", "직접")
    s.set("slider", "v_walk", 1.5)
    s.set("toggle", "use_bus", False)
    s.set("slider", "max_rides", 2)
    s.set("toggle", "climate_card", True)
    s.set("toggle", "bike_mileage", True)
    s.set("slider", "gamma", 1.5)
    s.set("slider", "safety_buffer", 45.0)
    s.set("slider", "v_pm", 4.5)
    s.set("slider", "max_bike_legs", 2)
    s.set("toggle", "full_skip", True)
    s.put("k_pm", 0.2)
    s.set("segmented_control", "origin_kind", "POINT")
    s.put("origin_point", (37.5, 127.0015))
    s.click("reset_button")
    best = ce.run_engine(golden, golden.default_query, EngineConfig()).best_id
    expected = {**_base_defaults(), **_query_key_defaults(golden), "selected_id": best}
    for key, value in expected.items():
        c.eq(f"① 되돌린 뒤 {key}", value, s.state(key))
    for key, value in _conditional_defaults(golden).items():
        actual = s.state(key)
        c.true(f"① 되돌린 뒤 {key} 은 없거나 기본값", actual is _MISSING or actual == value, actual)
    c.eq("① 되돌린 뒤 KPI", _GOLDEN_KPI, s.kpi())
    c.eq("① 되돌려도 시나리오와 데이터 모드는 그대로", (ce.GOLDEN_ID, "SIMULATION"), (s.state("scenario_id"), s.state("data_mode")))
    # ② 시나리오 전환
    s.set("radio", "selected_id", "Idddde0a626")
    s.put("kakao_results", {(ce.GOLDEN_ID, "Idddde0a626"): {"state": "OK", "units": []}})
    s.scenario("B")
    scenario_b = hand["B"]
    out_b = ce.run_engine(scenario_b, scenario_b.default_query, EngineConfig())
    for key, value in _query_key_defaults(scenario_b).items():
        c.eq(f"② B: {key}", value, s.state(key))
    c.eq("② B: 마감, 선택, 카카오 결과", (False, out_b.best_id, {}),
         (s.state("use_deadline"), s.state("selected_id"), s.state("kakao_results")))
    c.eq("② B: KPI = 엔진", _kpi_expect(out_b), s.kpi())
    c.eq("② 재생 보존 값은 그대로", replay_values,
         tuple(s.state(f"keep_{key}") for key in ("replay_window", "replay_date", "replay_time")))
    s.set("segmented_control", "data_mode", "REPLAY")
    c.eq("② 기록 재생으로 돌리면 재생 값이 그대로", replay_values,
         (s.state("replay_window"), s.state("replay_date"), s.state("replay_time")))


def _ui09(c: _Checker, folder: Path, maps: _MapCalls) -> None:
    golden = ce.golden_scenario()
    config = EngineConfig()
    last = _save_variant(folder, "GV-LAST")
    last_out = ce.run_engine(last, ce.golden_query(), config)
    counter = _Counted(ce.run_engine)
    with _replaced(ce, "run_engine", counter):
        s = _Screen(c, maps).run().scenario(ce.GOLDEN_ID)
        # ③ 찍은 점이 없음
        before = counter.calls
        s.set("segmented_control", "origin_kind", "POINT")
        c.eq("③ 출발 점 없음: 엔진을 부르지 않는다", before, counter.calls)
        c.eq("③ 출발 점 없음: 안내", ["지도를 눌러 출발을 정하세요."], s.main_texts("info"))
        c.eq("③ 출발 점 없음: 비교 패널, KPI, 경로 목록 없음", (0, 0, False),
             (len(s.htmls("mr-compare")), len(s.at.metric), s.has("radio", "selected_id")))
        c.eq("③ 출발 점 없음: 지도는 누르기를 기다린다", ["last_clicked"], maps.calls[-1]["returned_objects"] if maps.calls else None)
        # ① 찍은 점이 길에서 멀다
        s.put("origin_point", (37.51, 127.0))
        c.eq("① SNAP_FAILED 카드", ["찍은 점이 길에서 828 m 떨어져 있습니다(최대 150 m). 길 가까이를 다시 찍으세요."],
             [_plain(value) for value in s.htmls("mr-state")])
        c.eq("① SNAP_FAILED KPI", ["-"] * 4, [value for _, value, _ in s.kpi()])
        s.set("segmented_control", "origin_kind", "PLACE")
        before = counter.calls
        s.set("segmented_control", "dest_kind", "POINT")
        c.eq("③ 목적지 점 없음: 엔진을 부르지 않는다", before, counter.calls)
        c.eq("③ 목적지 점 없음: 안내", ["지도를 눌러 목적지를 정하세요."], s.main_texts("info"))
        s.set("segmented_control", "dest_kind", "PLACE")
        # ④ GV-LAST 에서 Ifbf4ec4c04
        s.scenario("GV-LAST")
        s.set("radio", "selected_id", "Ifbf4ec4c04")
    it = _items_of(last_out)["Ifbf4ec4c04"]
    timeline = s.htmls("mr-tl")
    c.eq("④ 시간 막대 구간 수 = legs 수", len(it.legs), timeline[0].count('class="mr-seg ') if timeline else None)
    lines = ("걷기 170 m · 2분 16초 → 정류장1",
             "가상1번 1번째 차 · 정류장1 08:03:20 → 정류장2 08:05:50 · 탈 확률 95.2% · 1분 04초 기다림",
             "걷기 60 m · 1분 22초 → 정류장4 (신호 1개, 대기 34초)",
             "가상2번 막차를 놓쳐 정류장4에서 도착지까지 걷습니다 · 840 m · 11분 46초",
             "도착 도착지 · 평균 08:20:27, 90% 08:22:16")
    c.eq("④ 여정 안내", lines, guide_lines(it, last_out, last, config))
    steps = s.html_text("mr-steps")
    c.eq("④ 화면의 여정 안내", [], [line for line in lines if line not in steps])
    # ② NO_ROUTE
    narrow = EngineConfig(gamma=1.0)
    no_route = ce.run_engine(golden, ce.golden_query(), narrow)
    c.eq("② NO_ROUTE 문장", ("NO_ROUTE", "경로가 없습니다. 세부 조건에서 탐색 타원 계수(지금 1.00)를 키우거나 수단을 켜 보세요."),
         (no_route.status.value, _plain(compare_panel_html(no_route, narrow))))


def _ui10(c: _Checker, folder: Path, maps: _MapCalls) -> None:
    cases = (
        ("fmt_clock(28,800, 673.8259)", fmt_clock(28_800, 673.8259), "08:11:14"),
        ("fmt_clock(28,800, 1,318.2926)", fmt_clock(28_800, 1_318.2926), "08:21:58"),
        ("fmt_clock(84,000, 3,000)", fmt_clock(84_000, 3_000), "00:10:00 (다음 날)"),
        ("fmt_clock(86,399, 0.6)", fmt_clock(86_399, 0.6), "00:00:00 (다음 날)"),
        ("fmt_dur(1,132)", fmt_dur(1_132), "18분 52초"),
        ("fmt_dur(45.4)", fmt_dur(45.4), "45초"),
        ("fmt_dur(59.5)", fmt_dur(59.5), "1분 00초"),
        ("fmt_dur(5)", fmt_dur(5), "5초"),
        ("fmt_dur(0)", fmt_dur(0), "0초"),
        ("fmt_dur(4,521.5)", fmt_dur(4_521.5), "75분 22초"),
        ("fmt_delta_dur(-644.4667)", fmt_delta_dur(-644.4667), "-10분 44초"),
        ("fmt_delta_dur(20.6697)", fmt_delta_dur(20.6697), "+21초"),
        ("fmt_delta_dur(0.3)", fmt_delta_dur(0.3), "0초"),
        ("fmt_won(2,550)", fmt_won(2_550), "2,550원"),
        ("fmt_won(0)", fmt_won(0), "0원"),
        ("fmt_delta_won(-500)", fmt_delta_won(-500), "-500원"),
        ("fmt_delta_won(1,000)", fmt_delta_won(1_000), "+1,000원"),
        ("fmt_delta_won(0)", fmt_delta_won(0), "변동 없음"),
        ("fmt_pct(0.192228)", fmt_pct(0.192228), "19.2%"),
        ("fmt_pct(0.8125)", fmt_pct(0.8125), "81.2%"),
        ("fmt_pct(0.99996)", fmt_pct(0.99996), "100.0%"),
        ("fmt_pct(0.0004)", fmt_pct(0.0004), "0.0%"),
        ("fmt_dist(880)", fmt_dist(880), "880 m"),
        ("fmt_dist(999.4)", fmt_dist(999.4), "999 m"),
        ("fmt_dist(999.6)", fmt_dist(999.6), "1.00 km"),
        ("fmt_dist(1,250)", fmt_dist(1_250), "1.25 km"),
        ("fmt_dist(12,345.6)", fmt_dist(12_345.6), "12.35 km"),
        ("fmt_mult(1.152)", fmt_mult(1.152), "1.15배"),
        ("fmt_mult(0.846214)", fmt_mult(0.846214), "0.85배"),
        ("fmt_speed(1.25)", fmt_speed(1.25), "1.25 m/s"),
        ("fmt_rate(6)", fmt_rate(6), "6.0건/시"),
        ("fmt_date('2026-11-02')", fmt_date("2026-11-02"), "2026-11-02(월)"),
    )
    for label, actual, expected in cases:
        c.eq(label, expected, actual)
    _clear_caches()
    s = _Screen(c, maps)
    started = time.perf_counter()
    s.run("첫 실행")
    first = time.perf_counter() - started
    started = time.perf_counter()
    s.run("다시 실행")
    again = time.perf_counter() - started
    c.true(f"성능: 시나리오 A 첫 실행 5초 이내 ({first:.2f}초)", first <= 5.0)
    c.true(f"성능: 같은 상태의 다시 실행 2초 이내 ({again:.2f}초)", again <= 2.0)
    print(f"    (A 첫 실행 {first:.2f}초, 다시 실행 {again:.2f}초)")


def _ui11(c: _Checker, folder: Path, maps: _MapCalls) -> None:
    hand = ce.build_scenarios()
    golden = ce.golden_scenario()
    config = EngineConfig()
    for variant_id in ("GV-LATE", "GV-NOSUB"):
        _save_variant(folder, variant_id)
    train_query = ce.golden_train_query()
    bus_query = ce.golden_bus_query()
    train_out = ce.run_engine(golden, train_query, config)
    shifted_300 = ce.advance_clock(golden, 300.0, config)
    train_moved = ce.shift_origin(golden, shifted_300, train_query, 300.0, config)
    train_out_300 = ce.run_engine(shifted_300, train_moved, config) if train_moved else None
    bus_out = ce.run_engine(golden, bus_query, config)
    shifted_600 = ce.advance_clock(golden, 600.0, config)
    bus_moved = ce.shift_origin(golden, shifted_600, bus_query, 600.0, config)
    bus_out_600 = ce.run_engine(shifted_600, bus_moved, config) if bus_moved else None
    shifted_1200 = ce.advance_clock(golden, 1200.0, config)
    far_query = bus_query.model_copy(update={"origin": bus_query.origin.model_copy(update={"prior_distance_m": 12_000.0})})
    far_out = ce.run_engine(golden, far_query, config)
    a = hand["A"]
    a_out = ce.run_engine(a, a.default_query, config)
    a_shifted = ce.advance_clock(a, 120.0, config)
    a_moved = ce.shift_origin(a, a_shifted, a.default_query, 120.0, config)
    a_out_120 = ce.run_engine(a_shifted, a_moved, config) if a_moved else None
    c.eq("늦추기 300 의 열차", "1002", train_moved.origin.trip_id if train_moved else None)
    c.eq("늦추기 600 의 버스", "G1:g1b", bus_moved.origin.trip_id if bus_moved else None)
    c.eq("늦추기 1,200 의 버스", None, ce.shift_origin(golden, shifted_1200, bus_query, 1200.0, config))
    counter = _Counted(ce.run_engine)
    with _replaced(ce, "run_engine", counter):
        s = _Screen(c, maps).run().scenario(ce.GOLDEN_ID)
        # 열차
        s.set("segmented_control", "origin_kind", "TRAIN")
        c.eq("열차: 다음에 설 역 선택지", ["역1 (가상선)", "역2 (가상선)", "역3 (가상선)"], s.options("selectbox", "train_station"))
        s.set("selectbox", "train_station", "M2")
        trains = s.options("selectbox", "train_key")
        c.eq("열차: 역2 의 탄 열차 선택지 7개",
             (7, "08:02:50 도착 · 가상선 하행 · 역3행 · 1000", "08:26:50 도착 · 가상선 하행 · 역3행 · 1006"),
             (len(trains), trains[0] if trains else None, trains[-1] if trains else None))
        s.set("selectbox", "train_key", f"{ce.GOLDEN_PATTERN_ID}|1000|1")
        c.eq("열차 1000: KPI = V12f 열차 질의", _kpi_expect(train_out), s.kpi())
        c.eq("열차 1000: 값", ["08:07:57", "08:08:27", "100.0%", "1,550원"], [value for _, value, _ in s.kpi()])
        c.eq("열차 1000: 출발 표시", "출발: 가상선 하행 1000 열차 안, 다음 역 역2 08:02:50 · 기준 시각 08:00:00 · 목적지: 도착지",
             s.description())
        s.set("select_slider", "depart_offset_s", 300)
        c.eq("열차 늦추기 300: KPI", _kpi_expect(train_out_300) if train_out_300 else None, s.kpi())
        c.eq("열차 늦추기 300: 평균", "08:15:57", s.kpi()[0][1] if s.kpi() else None)
        c.true("열차 늦추기 300: 출발 표시", "가상선 하행 1002 열차 안, 다음 역 역2 08:10:50" in s.description(), s.description())
        s.set("select_slider", "depart_offset_s", 0)
        # GV-LATE
        s.scenario("GV-LATE")
        before = counter.calls
        s.set("segmented_control", "origin_kind", "TRAIN")
        s.set("selectbox", "train_station", "M2")
        note = "기준 시각부터 30분 안에 이 역에 닿는 열차가 없습니다."
        c.true("GV-LATE: 탄 열차 선택 상자가 비활성", s.at.selectbox(key="train_key").disabled)
        c.true("GV-LATE: 안내", note in s.side_captions() and note in s.main_texts("info"), (s.side_captions(), s.main_texts("info")))
        c.eq("GV-LATE: 엔진을 부르지 않는다", before, counter.calls)
        # GV-NOSUB
        s.scenario("GV-NOSUB")
        c.true("GV-NOSUB: 출발 선택지에 '지금 탄 열차' 없음", "지금 탄 열차" not in s.options("segmented_control", "origin_kind"),
               s.options("segmented_control", "origin_kind"))
        # 버스
        s.scenario(ce.GOLDEN_ID)
        s.set("segmented_control", "origin_kind", "BUS")
        c.eq("버스: 노선 선택지", ["가상1 (간선)", "가상2 (지선)"], s.options("selectbox", "bus_line"))
        c.eq("버스: 가상1 의 정류장 선택지", ["1. 정류장1", "2. 정류장2", "3. 정류장3"], s.options("selectbox", "bus_stop_index"))
        s.set("selectbox", "bus_stop_index", 1)
        c.eq("버스: 정류장2 의 탄 버스 앞 셋",
             ["1번째 차 · 08:05:50 도착 · 차량 g1a", "2번째 차 · 08:15:50 도착 · 차량 g1b", "3번째 차 · 08:25:50 도착 · 배차 간격으로 이은 차"],
             s.options("selectbox", "bus_vehicle")[:3])
        s.set("selectbox", "bus_vehicle", "G1:g1a")
        c.eq("버스 g1a: KPI = V12f 버스 질의", _kpi_expect(bus_out), s.kpi())
        c.eq("버스 g1a: 출발 표시", "출발: 가상1번 버스 안, 다음 정류장 정류장2 08:05:50 · 기준 시각 08:00:00 · 목적지: 도착지",
             s.description())
        s.set("select_slider", "depart_offset_s", 600)
        c.eq("버스 늦추기 600: KPI", _kpi_expect(bus_out_600) if bus_out_600 else None, s.kpi())
        c.true("버스 늦추기 600: 출발 표시", "가상1번 버스 안, 다음 정류장 정류장2 08:15:50" in s.description(), s.description())
        before = counter.calls
        s.set("select_slider", "depart_offset_s", 1200)
        c.eq("버스 늦추기 1,200: 안내", ["20분 늦추면 이 역(정류장)에 닿는 차가 없습니다. 출발 늦추기를 줄이거나 출발을 다시 고르세요."],
             s.main_texts("info"))
        c.eq("버스 늦추기 1,200: 엔진을 부르지 않는다", before, counter.calls)
        s.set("select_slider", "depart_offset_s", 0)
        s.set("number_input", "prior_km", 12.0)
        c.eq("이미 탄 거리 12.0: KPI = prior_distance_m 12,000", _kpi_expect(far_out), s.kpi())
        # A
        s.scenario("A")
        c.eq("A: 기본 KPI = 엔진", _kpi_expect(a_out), s.kpi())
        s.set("select_slider", "depart_offset_s", 120)
        c.eq("A: 늦추기 120 KPI = shift_origin 결과", _kpi_expect(a_out_120) if a_out_120 else None, s.kpi())


def _ui12(c: _Checker, folder: Path, maps: _MapCalls) -> None:
    golden = ce.golden_scenario()
    config = EngineConfig()
    click = {"lat": 37.5, "lng": 127.0015}
    state: dict[str, Any] = {"origin_kind": "POINT", "dest_kind": "PLACE", "last_map_click": None}
    c.eq("직접: 처음 누름", True, apply_map_click(state, click))
    c.eq("직접: origin_point 와 last_map_click", ((37.5, 127.0015), click), (state.get("origin_point"), state.get("last_map_click")))
    c.eq("직접: 같은 값을 다시 주면 거짓", False, apply_map_click(state, dict(click)))
    c.eq("직접: None 이면 거짓", False, apply_map_click(state, None))
    c.eq("직접: 둘 다 장소면 거짓", False, apply_map_click({"origin_kind": "PLACE", "dest_kind": "PLACE", "last_map_click": None}, click))
    both: dict[str, Any] = {"origin_kind": "POINT", "dest_kind": "POINT", "map_pick": "DESTINATION", "last_map_click": None,
                            "origin_point": None, "dest_point": None}
    c.eq("직접: 둘 다 지도에서, DESTINATION", (True, None, (37.5, 127.0015)),
         (apply_map_click(both, click), both.get("origin_point"), both.get("dest_point")))
    point_query = Query(origin=OriginState(kind=OriginKind.AT_POINT, lat=37.5, lon=127.0015), destination_node_id="D")
    expected = ce.run_engine(golden, point_query, config)
    s = _Screen(c, maps).run().scenario(ce.GOLDEN_ID)
    s.set("segmented_control", "origin_kind", "POINT")
    s.put("origin_point", (37.5, 127.0015))
    c.eq("화면: KPI = AT_POINT (37.5, 127.0015) → D", _kpi_expect(expected), s.kpi())
    c.true("화면: 출발 표시", s.description().startswith("출발: 지도에서 찍은 점(가장 가까운 교차로1까지 18 m)"), s.description())
    c.eq("화면: 한쪽만 지도에서면 map_pick 이 없다", False, s.has("segmented_control", "map_pick"))
    s.set("segmented_control", "dest_kind", "POINT")
    c.eq("화면: 둘 다 지도에서면 map_pick", True, s.has("segmented_control", "map_pick"))
    c.eq("화면: 지도의 returned_objects", ["last_clicked"], maps.calls[-1]["returned_objects"] if maps.calls else None)
    # 지도 대역이 누른 좌표를 돌려주면 main 이 상태를 고치고 한 번 다시 실행한다
    s.set("segmented_control", "map_pick", "DESTINATION")
    maps.click = {"lat": 37.5, "lng": 127.0181}
    s.run("지도 누름")
    c.eq("화면: 누른 좌표가 목적지가 된다", ((37.5, 127.0181), {"lat": 37.5, "lng": 127.0181}),
         (s.state("dest_point"), s.state("last_map_click")))
    c.true("화면: 그 점으로 계산했다", len(s.kpi()) == 4 and s.kpi()[0][1] != "-", s.kpi())
    maps.click = None


# --- UI-21, UI-22, UI-26, UI-27 ---


def _ui21(c: _Checker, folder: Path, maps: _MapCalls) -> None:
    hand = ce.build_scenarios()
    (folder / "scenarios").mkdir(parents=True, exist_ok=True)
    (folder / "scenarios" / "bad.json").write_text("{ 깨진 JSON", encoding="utf-8")
    ce.save_scenario_json(hand["A"], folder / "scenarios" / "dupA.json")
    simulated = _kpi_expect(ce.run_engine(hand["A"], hand["A"].default_query, EngineConfig()))
    s = _Screen(c, maps).run()
    c.true("⑤ 읽지 못한 파일 안내", "읽지 못한 시나리오 파일 2개: bad.json, dupA.json" in s.side_captions(), s.side_captions())
    c.eq("⑤ 두 파일은 목록에 없다", [hand["A"].title, hand["B"].title, _GOLDEN_LABEL], s.options("selectbox", "scenario_id"))
    captions = s.side_captions()
    c.true("③ 키 줄", any("열린데이터광장 없음 · 공공데이터포털 없음 · 카카오 없음 · 서울 신호 없음" in text for text in captions), captions)
    c.true("③ 기록 저장소 줄", "기록 저장소 없음" in captions, captions)
    c.true("③ 모델 줄", any("신호 없음 · 따릉이 없음" in text for text in captions), captions)
    s.set("segmented_control", "data_mode", "REPLAY")
    store = folder.resolve() / "records.sqlite"
    c.eq("① 기록 재생 안내", [f"기록 재생을 할 수 없습니다: {store}에 기록이 없습니다. 시뮬레이션 값으로 보여 줍니다."], s.main_texts("warning"))
    c.true("① 배지 '시뮬레이션 값 (기록 재생 불가)'", "시뮬레이션 값 (기록 재생 불가)" in s.chips(), s.chips())
    c.true("① 재생 묶음 자리 '기록이 없습니다'", "기록이 없습니다" in s.side_captions(), s.side_captions())
    c.eq("① KPI = 시뮬레이션", simulated, s.kpi())
    s.set("segmented_control", "data_mode", "LIVE")
    c.eq("② 실시간 안내", ["실시간 조회를 할 수 없습니다: 키가 없습니다. 시뮬레이션 값으로 보여 줍니다."], s.main_texts("warning"))
    c.true("② 배지 '시뮬레이션 값 (실시간 불가)'", "시뮬레이션 값 (실시간 불가)" in s.chips(), s.chips())
    c.eq("② '지금 다시 조회' 버튼 없음", False, s.has("button", "live_refresh_button"))
    c.eq("② KPI = 시뮬레이션", simulated, s.kpi())
    for args, expected in ((("REPLAY", False, True), ("SIMULATION", "기록 재생 불가")), (("LIVE", True, False), ("SIMULATION", "실시간 불가")),
                           (("LIVE", False, True), ("LIVE", None)), (("SIMULATION", True, True), ("SIMULATION", None))):
        c.eq(f"④ effective_mode{args}", expected, effective_mode(*args))


def _ui22(c: _Checker, folder: Path, maps: _MapCalls) -> None:
    truth, syn, config, models = _synthetic(folder)
    query = syn.default_query
    moments = {name: _kst_unix(2026, 11, 2, *clock) for name, clock in
               (("08:00", (8, 0)), ("08:01", (8, 1)), ("12:00", (12, 0)), ("08:20", (8, 20)))}
    replays = {name: _replayed(truth, syn, config, models, at) for name, at in moments.items()}
    expect = {name: ce.run_engine(scenario, query, config, sources) for name, (scenario, sources) in replays.items()}
    trains_0800 = ce.train_candidates(replays["08:00"][0], "M2", config)
    trains_0820 = ce.train_candidates(replays["08:20"][0], "M2", config)
    counter = _Counted(ce.replay_scenario)
    with _replaced(ce, "replay_scenario", counter):
        s = _Screen(c, maps).run()
        c.true("① 시나리오 이름", "합성 기록 시험 세계 (생성)" in s.options("selectbox", "scenario_id"), s.options("selectbox", "scenario_id"))
        s.scenario(syn.id)
        _clear_caches()
        started = time.perf_counter()
        s.set("segmented_control", "data_mode", "REPLAY")
        first = time.perf_counter() - started
        c.true(f"⑧ 캐시를 비운 첫 재생 실행 8초 이내 ({first:.2f}초)", first <= 8.0)
        print(f"    (첫 재생 실행 {first:.2f}초)")
        windows = s.options("selectbox", "replay_window")
        c.eq("① 첫 선택지", "2026-11-04(수) 평일 아침 07:30 ~ 08:59 · 조회 720회", windows[0] if windows else None)
        c.true("① 나머지 선택지", len(windows) == 3 and windows[1].startswith("2026-11-03(화) 평일 아침 ")
               and windows[2].startswith("2026-11-02(월) 평일 아침 "), windows)
        value = str(s.state("replay_window"))
        c.true("① 기본 구간은 첫째", value.startswith("2026-11-04|"), value)
        c.eq("① 재생 날짜와 시각", (datetime.date(2026, 11, 4), datetime.time(7, 31)), (s.state("replay_date"), s.state("replay_time")))
        day = s.at.date_input(key="replay_date")
        c.eq("① 날짜 범위", (datetime.date(2026, 11, 2), datetime.date(2026, 11, 4)), (day.min, day.max))
        window = value.split("|", 1)[-1]
        s.set("selectbox", "replay_window", f"2026-11-02|{window}")
        c.eq("② 구간을 고르면 날짜와 시각", (datetime.date(2026, 11, 2), datetime.time(7, 31)),
             (s.state("replay_date"), s.state("replay_time")))
        s.set("time_input", "replay_time", datetime.time(8, 0))
        c.true("② 배지", "2026-11-02(월) 08:00:00 기록 재생" in s.chips(), s.chips())
        c.eq("② KPI = 골든 기본 (RP2)", _GOLDEN_KPI, s.kpi())
        c.eq("② KPI = 엔진", _kpi_expect(expect["08:00"]), s.kpi())
        before = counter.calls
        s.set("select_slider", "depart_offset_s", 60)
        c.eq("③ 늦추기 60: KPI = 08:01:00 재생", _kpi_expect(expect["08:01"]), s.kpi())
        c.true("③ 늦추기 60: 기록을 다시 재생했다(advance_clock 이 아니다)", counter.calls > before, counter.calls - before)
        c.true("③ 배지 끝 ' · 1분 뒤 출발'", "기록 재생 · 1분 뒤 출발" in s.chips(), s.chips())
        s.set("select_slider", "depart_offset_s", 0)
        s.set("segmented_control", "data_mode", "SIMULATION")
        s.set("segmented_control", "data_mode", "REPLAY")
        c.eq("④ 모드를 바꿨다 돌려도 재생 값 그대로", (f"2026-11-02|{window}", datetime.date(2026, 11, 2), datetime.time(8, 0)),
             (s.state("replay_window"), s.state("replay_date"), s.state("replay_time")))
        s.set("time_input", "replay_time", datetime.time(12, 0))
        c.true("⑤ 사이드바 안내", "이 시각 앞뒤에 기록이 없습니다. 기록 구간에서 고르세요." in s.side_texts("warning"), s.side_texts("warning"))
        c.true("⑤ 배지 '원천 일부 건너뜀'", "원천 일부 건너뜀" in s.chips(), s.chips())
        c.true("⑤ 엔진 경고 REPLAY_DATA_GAP", "REPLAY_DATA_GAP" in s.html_text("mr-warnlist"))
        c.eq("⑤ KPI = RP4 의 12:00 결과", _kpi_expect(expect["12:00"]), s.kpi())
        c.eq("⑥ 출발 선택지", ["장소", "지도에서"], s.options("segmented_control", "origin_kind"))
        s.set("time_input", "replay_time", datetime.time(8, 0))
        s.set("segmented_control", "origin_kind", "TRAIN")
        s.set("selectbox", "train_station", "M2")
        pick = next((choice for choice in trains_0800 if choice.train_no == "1003"), None)
        c.true("⑦ 08:00 후보에 1003", pick is not None, [choice.train_no for choice in trains_0800])
        if pick is not None:
            s.set("selectbox", "train_key", f"{pick.pattern_id}|{pick.trip_id}|{pick.index}")
            s.set("time_input", "replay_time", datetime.time(8, 20))
            c.true("⑦ 안내", "고른 열차(1003)가 지금 후보에 없어 첫 열차로 바꿨습니다." in s.side_texts("info"), s.side_texts("info"))
            head = trains_0820[0] if trains_0820 else None
            c.eq("⑦ 새 후보의 첫째", "1005", head.train_no if head else None)
            c.eq("⑦ train_key", f"{head.pattern_id}|{head.trip_id}|{head.index}" if head else None, s.state("train_key"))


def _ui26(c: _Checker, folder: Path, maps: _MapCalls) -> None:
    truth, syn, config, models = _synthetic(folder)
    real = ce.apply_live_overrides
    rp5_now = 1_794_870_010.0  # RP5 의 조회 시각(§9.7)
    calls: list[float] = []

    def fake(scenario: Scenario, config: EngineConfig, client: Any = None, now: Any = None, models: Any = None, **kwargs: Any):
        del client, now
        calls.append(time.time())
        with ce._rp5_router().client() as http:
            return real(scenario, config, http, now=rp5_now, models=models, **kwargs)

    secrets = [value for _, value in ce._FAKE_KEYS]
    for name, value in ce._FAKE_KEYS:
        os.environ[name] = value
    try:
        with ce._rp5_router().client() as http:
            live, sources = real(syn, config, http, now=rp5_now, models=models)
        expected = ce.run_engine(live, syn.default_query, config, sources)
        shifted = ce.advance_clock(live, 120.0, config)
        moved = ce.shift_origin(live, shifted, syn.default_query, 120.0, config)
        expected_120 = ce.run_engine(shifted, moved, config, sources)
        with _replaced(ce, "apply_live_overrides", fake):
            s = _Screen(c, maps).run().scenario(syn.id)
            s.set("segmented_control", "data_mode", "LIVE")
            c.true("① 배지 '실시간 · 08:00:05 조회'", "실시간 · 08:00:05 조회" in s.chips(), s.chips())
            c.true("① 배지 '원천 일부 실패'", "원천 일부 실패" in s.chips(), s.chips())
            c.eq("① KPI = run_engine(RP5 시나리오, 기본 질의, 설정, RP5 원천 상태)", _kpi_expect(expected), s.kpi())
            c.eq("① 가짜 함수 1회", 1, len(calls))
            s.run("같은 조건으로 다시 실행")
            c.eq("② 다시 실행해도 1회", 1, len(calls))
            s.set("select_slider", "depart_offset_s", 120)
            c.eq("③ 늦추기 120: KPI = advance_clock(RP5 시나리오, 120)", _kpi_expect(expected_120), s.kpi())
            c.eq("③ 늦추기 120: 다시 부르지 않는다", 1, len(calls))
            c.true("③ 배지 끝 ' · 2분 뒤 출발 (받은 값을 옮김)'", "· 2분 뒤 출발 (받은 값을 옮김)" in s.chips(), s.chips())
            s.set("select_slider", "depart_offset_s", 0)
            c.eq("④ 30초 안이면 비활성", True, s.at.button(key="live_refresh_button").disabled)
            s.put("live_fetched_at", time.time() - 31.0)
            c.eq("④ 31초 전이면 활성", False, s.at.button(key="live_refresh_button").disabled)
            s.click("live_refresh_button")
            c.eq("④ 누르면 한 번 더 부른다", (2, 1), (len(calls), s.state("live_refresh")))
            leaks = sorted({secret for secret in secrets for text in s.strings() if secret in text})
            c.eq("⑤ 화면 글자에 가짜 키 없음", [], leaks)
    finally:
        for name, _ in ce._FAKE_KEYS:
            os.environ.pop(name, None)


def _ui27(c: _Checker, folder: Path, maps: _MapCalls) -> None:
    truth, syn, config, models = _synthetic(folder)
    golden = ce.golden_scenario()
    out = ce.run_engine(golden, ce.golden_query(), EngineConfig())
    replayed, replay_sources = _replayed(truth, syn, config, models, _kst_unix(2026, 11, 4, 7, 31))
    replay_out = ce.run_engine(replayed, syn.default_query, config, replay_sources)
    counter = _Counted(ce.run_engine)
    with _replaced(ce, "run_engine", counter):
        s = _Screen(c, maps).run()
        counter.calls = 0
        s.scenario(ce.GOLDEN_ID)
        c.eq("골든 첫 실행 1회", 1, counter.calls)
        other = next(itinerary_id for itinerary_id in out.ranking if itinerary_id != out.best_id)
        s.set("radio", "selected_id", other)
        s.set("toggle", "show_variants", True)
        s.set("toggle", "show_variants", False)
        c.eq("선택 여정과 '다른 걷는 길도 보기'를 바꿔도 1회", 1, counter.calls)
        s.put("tabs", "② 탑승별 확률")
        c.eq("탭을 바꾸면 그 탭이 열린다", "② 탑승별 확률", _open_tab(s))
        s.set("selectbox", "trace_run", "NAIVE")
        s.set("selectbox", "trace_line", "G2")
        c.eq("탭, ⑥ 탭의 실행과 노선 선택을 바꿔도 1회", 1, counter.calls)
        s.set("toggle", "climate_card", True)
        c.eq("기후동행카드를 켜면 2회", 2, counter.calls)
        s.set("toggle", "climate_card", False)
        c.eq("끄면 2회 그대로(캐시)", 2, counter.calls)
        s.set("select_slider", "depart_offset_s", 60)
        c.eq("늦추기 60 이면 3회", 3, counter.calls)
        s.set("select_slider", "depart_offset_s", 0)
        c.eq("0 으로 돌리면 3회 그대로", 3, counter.calls)
    replays = _Counted(ce.replay_scenario)
    with _replaced(ce, "replay_scenario", replays):
        s.scenario(syn.id)
        s.set("segmented_control", "data_mode", "REPLAY")
        made = replays.calls
        c.true("기록 재생: 재생을 만든다", made >= 1, made)
        alternative = next((itinerary_id for itinerary_id in replay_out.ranking if itinerary_id != replay_out.best_id), None)
        if alternative is not None:
            s.set("radio", "selected_id", alternative)
        s.set("toggle", "show_variants", True)
        c.eq("기록 재생: 선택 여정을 바꿔도 그대로", made, replays.calls)
        s.set("time_input", "replay_time", datetime.time(8, 0))
        c.eq("기록 재생: 재생 시각을 바꾸면 1회 는다", made + 1, replays.calls)


# --- 9단계 화면 검사 (UI-13 ~ UI-20, UI-23 ~ UI-25, §9.9.3) ---
#
# 탭 안의 요소는 AppTest 의 탭 블록 아래에서 요소 종류(클래스 이름)로 찾는다. 차트는 AppTest 가 요소로 풀지 않으므로 원형 메시지의
# 데이터셋(Arrow)을 읽거나, 명세대로 차트 함수를 직접 부른다(§9.9.1). 기대값은 엔진을 직접 불러 얻거나 명세의 문구를 그대로 쓴다.

_TAB_SPEC = ("① 경로 비교", "② 탑승별 확률", "③ 신호", "④ 따릉이", "⑤ 요금", "⑥ 탐색 과정", "⑦ 데이터·기록")
_TAB_KINDS_TEXT = ("Markdown", "Caption", "Latex", "Info", "Warning", "Error", "Success")


def _nodes(node: Any) -> Iterable[Any]:
    """AppTest 노드와 그 아래 모든 노드(문서 순서)."""
    yield node
    children = getattr(node, "children", None)
    if isinstance(children, dict):
        for child in children.values():
            yield from _nodes(child)


def _open_tab(s: _Screen) -> str | None:
    """열려 있는 탭의 이름. AppTest 는 탭 묶음의 `default_tab_index` 에 지금 탭을 둔다."""
    for node in _nodes(s.at._tree):
        proto = getattr(node, "proto", None)
        try:
            if not proto.HasField("tab_container"):
                continue
        except (AttributeError, ValueError, TypeError):
            continue
        labels = [child.label for child in node.children.values() if type(child).__name__ == "Tab"]
        index = proto.tab_container.default_tab_index
        return labels[index] if 0 <= index < len(labels) else None
    return None


class _Tab:
    """탭 하나의 요소. 실행마다 요소 나무가 바뀌므로 부를 때마다 탭을 다시 찾는다."""

    def __init__(self, s: _Screen, name: str) -> None:
        self.s = s
        self.name = name

    @property
    def node(self) -> Any:
        return next((tab for tab in self.s.at.tabs if tab.label == self.name), None)

    def all(self, kind: str) -> list[Any]:
        node = self.node
        return [] if node is None else [item for item in _nodes(node) if type(item).__name__ == kind]

    def first(self) -> Any:
        node = self.node
        children = list(node.children.values()) if node is not None else []
        return children[0] if children else None

    def values(self, kind: str) -> list[str]:
        return [item.value for item in self.all(kind)]

    def latex(self) -> list[str]:
        return [value.strip().removeprefix("$$").removesuffix("$$").strip() for value in self.values("Latex")]

    def frames(self) -> list[pd.DataFrame]:
        return [item.value for item in self.all("Dataframe")]

    def frame(self, column: str, index: int = 0) -> pd.DataFrame | None:
        """`column` 열이 있는 표 가운데 `index` 번째(문서 순서)."""
        found = [frame for frame in self.frames() if column in frame.columns]
        return found[index] if index < len(found) else None

    def column_types(self, column: str, index: int = 0) -> dict[str, Any]:
        """`column` 열이 있는 표의 열 설정(`column_config` 의 type_config)."""
        found = [item for item in self.all("Dataframe") if column in item.value.columns]
        if index >= len(found):
            return {}
        config = json.loads(found[index].proto.columns or "{}")
        return {name: value.get("type_config", {}) for name, value in config.items()}

    def htmls(self, css: str) -> list[str]:
        return [value for value in self.values("Html") if f'class="{css}' in value]

    def charts(self) -> list[pd.DataFrame]:
        """탭 안 차트마다 본 데이터(차트 순서). 원형 메시지의 Arrow 데이터셋 가운데 맨 위 명세의 `data.name` 이 가리키는 것이다.
        층마다 따로 둔 작은 데이터(문턱값 선과 라벨의 자리)는 빼고, 차트 함수의 `.data` 와 같은 표를 돌려준다."""
        import pyarrow as pa

        frames = []
        for item in self.all("UnknownElement"):
            datasets = list(getattr(item.proto, "datasets", ()))
            if not datasets:
                continue
            name = (json.loads(item.proto.spec or "{}").get("data") or {}).get("name")
            main = next((dataset for dataset in datasets if dataset.name == name), datasets[0])
            frames.append(pa.ipc.open_stream(main.data.data).read_all().to_pandas())
        return frames

    def text(self) -> str:
        node = self.node
        parts: list[str] = []
        for item in (_nodes(node) if node is not None else ()):
            kind = type(item).__name__
            if kind in _TAB_KINDS_TEXT:
                parts.append(item.value)
            elif kind == "Html":
                parts.append(_plain(item.value))
        return "\n".join(parts)


def _cell(value: Any) -> Any:
    if hasattr(value, "item") and not isinstance(value, str):
        value = value.item()
    if isinstance(value, float):
        return round(value, 6)
    return value


def _rows(frame: pd.DataFrame | None, columns: Sequence[str] | None = None) -> list[tuple[Any, ...]]:
    if frame is None:
        return []
    names = list(columns) if columns is not None else list(frame.columns)
    return [tuple(_cell(row[name]) if name in frame.columns else _MISSING for name in names) for _, row in frame.iterrows()]


def _column(frame: pd.DataFrame | None, name: str) -> list[Any]:
    return [] if frame is None or name not in frame.columns else [_cell(value) for value in frame[name]]


def _paragraphs(markup: str) -> list[str]:
    return [_plain(part) for part in re.findall(r"<p>(.*?)</p>", markup, re.S)]


def _list_items(markup: str) -> list[str]:
    return [html.unescape(re.sub(r"<[^>]+>", "", part)) for part in re.findall(r"<li>(.*?)</li>", markup, re.S)]


def _clock_text(c0: float, t: float) -> str:
    """§6.5 의 시계 형식을 검사 쪽에서 다시 적은 것(기대값에 화면 함수를 쓰지 않는다, §9.9.1)."""
    total = math.floor(c0 + t + 0.5)
    text = f"{total % 86_400 // 3600:02d}:{total % 3600 // 60:02d}:{total % 60:02d}"
    return text + (" (다음 날)" if total >= 86_400 else "")


def _plan_events(it: ItineraryResult) -> list[Any]:
    """계획이 지나는 신호 이벤트(§6.3 ③ 탭): 이동(따릉이는 ①③⑤)의 이벤트, 계획이 막차를 놓친 탑승이 있으면 그 대체 보행의 이벤트까지."""
    moves = {move.index: move for move in it.moves}
    events: list[Any] = []
    for k in range(len(it.rides) + 1):
        move = moves.get(k)
        if move is not None:
            paths = (move.bike.walk_in, move.bike.ride, move.bike.walk_out) if move.bike is not None else (move.walk,)
            for path in paths:
                if path is not None:
                    events.extend(path.events)
        if k == len(it.rides):
            break
        ride = it.rides[k]
        if ride.board_index is not None and ride.plan_dep_s is None:
            if ride.fallback is not None:
                events.extend(ride.fallback.events)
            break
    return events


def _select(s: _Screen, itinerary_id: str, output: EngineOutput) -> _Screen:
    """경로 목록에서 여정을 고른다. 다른 걷는 길이면 "다른 걷는 길도 보기"를 먼저 켠다."""
    variants = {variant for it in output.itineraries for variant in it.variant_ids}
    if itinerary_id in variants and not s.state("show_variants", False):
        s.set("toggle", "show_variants", True)
    return s.set("radio", "selected_id", itinerary_id)


def _replay_at(s: _Screen, syn: Scenario, day: int, clock: datetime.time) -> None:
    """합성 기록 시나리오, 기록 재생, 2026-11-{day} 구간, 재생 시각."""
    if s.state("scenario_id") != syn.id:
        s.scenario(syn.id)
    s.set("segmented_control", "data_mode", "REPLAY")
    window = str(s.state("replay_window")).split("|", 1)[-1]
    s.set("selectbox", "replay_window", f"2026-11-{day:02d}|{window}")
    s.set("time_input", "replay_time", clock)


class _FakeKakao:
    """`core_engine.kakao_walk_compare` 의 대역(UI-25): 불린 횟수를 세고, 전송 처리기(`httpx.MockTransport`)로 진짜 함수를 부른다.
    `mode` 가 "ok" 면 표본 5 (기본 352 m · 290 s, SHORTEST 300 m · 240 s), "429" 면 늘 429, "500" 이면 늘 500."""

    def __init__(self) -> None:
        self.real = ce.kakao_walk_compare
        self.calls = 0
        self.mode = "ok"

    def handler(self, request: Any) -> Any:
        import httpx

        if self.mode == "429":
            return httpx.Response(429, json={"errorType": "RequestThrottled"})
        if self.mode == "500":
            return httpx.Response(500, text="server error")
        if request.url.params.get("route_mode") == "SHORTEST":
            return httpx.Response(200, json=ce._sample_kakao(300, 240))
        return httpx.Response(200, json=ce._sample_kakao())

    def __call__(self, origin: Any, destination: Any, our_shortest_m: float, config: EngineConfig, client: Any = None) -> Any:
        import httpx

        del client
        self.calls += 1
        with httpx.Client(transport=httpx.MockTransport(self.handler)) as http:
            return self.real(origin, destination, our_shortest_m, config, http)


@contextlib.contextmanager
def _env_values(values: Mapping[str, str | None]):
    """환경변수를 잠시 바꾸고(None 은 지운다) 되돌린다."""
    saved = {name: os.environ.get(name) for name in values}
    try:
        for name, value in values.items():
            if value is None:
                os.environ.pop(name, None)
            else:
                os.environ[name] = value
        yield
    finally:
        for name, value in saved.items():
            if value is None:
                os.environ.pop(name, None)
            else:
                os.environ[name] = value


def _folder_files(folder: Path) -> dict[str, int]:
    return {str(path.relative_to(folder)): path.stat().st_size for path in sorted(folder.rglob("*")) if path.is_file()}


# --- UI-13 ~ UI-20 ---


def _ui13(c: _Checker, folder: Path, maps: _MapCalls) -> None:
    truth, syn, syn_config, models = _synthetic(folder)
    config = EngineConfig()
    hand = ce.build_scenarios()
    golden = ce.golden_scenario()
    s = _Screen(c, maps).run()
    c.eq("① 탭 이름", list(_TAB_SPEC), [tab.label for tab in s.at.tabs])
    # ② 대표 여정(걸러진 여정 포함)을 하나씩 모두 고른다
    for scenario_id, scenario, query in (("A", hand["A"], hand["A"].default_query), ("B", hand["B"], hand["B"].default_query),
                                         (ce.GOLDEN_ID, golden, ce.golden_query())):
        out = ce.run_engine(scenario, query, config)
        if s.state("scenario_id") != scenario_id:
            s.scenario(scenario_id)
        for itinerary_id in (*out.ranking, *out.pruned_ids):
            s.set("radio", "selected_id", itinerary_id)
            c.eq(f"② {scenario_id}: {itinerary_id} 를 고름", itinerary_id, s.state("selected_id"))
    _replay_at(s, syn, 2, datetime.time(8, 0))
    replayed, sources = _replayed(truth, syn, syn_config, models, _kst_unix(2026, 11, 2, 8, 0))
    replay_out = ce.run_engine(replayed, syn.default_query, syn_config, sources)
    c.true("② 합성 기록 재생 08:00: 대표 여정이 있다", len(replay_out.ranking) > 0, replay_out.ranking)
    for itinerary_id in (*replay_out.ranking, *replay_out.pruned_ids):
        s.set("radio", "selected_id", itinerary_id)
        c.eq(f"② 합성 기록 재생: {itinerary_id} 를 고름", itinerary_id, s.state("selected_id"))
    s.set("segmented_control", "data_mode", "SIMULATION")
    s.scenario(ce.GOLDEN_ID)
    # ③ 도보
    s.set("radio", "selected_id", "If1e99436b8")
    boarding = _Tab(s, "② 탑승별 확률")
    c.eq("③ 도보: ② 탭 안내", ["이 여정은 차량을 타지 않습니다."], boarding.values("Info"))
    c.true("③ 도보: ② 탭 여정 전체 줄(P* 식과 도착 통계)",
           any(text.startswith("P^{*}") for text in boarding.latex()) and boarding.frame("도착하지 못할 확률") is not None, boarding.text())
    bike = _Tab(s, "④ 따릉이")
    c.eq("③ 도보: ④ 탭 안내", ["이 여정에는 따릉이 구간이 없습니다."], bike.values("Info"))
    c.eq("③ 도보: ④ 탭 대여소 상태 표 5행", 5, len(bike.frame("대여소")) if bike.frame("대여소") is not None else None)
    # ④ 신호 없음, 신호 피하기만 찾은 여정
    s.set("radio", "selected_id", "I3a248c7d10")
    signal = _Tab(s, "③ 신호")
    c.eq("④ 신호 없음", ["이 여정에는 신호가 없습니다."], signal.values("Info"))
    c.true("④ 신호 피하기 안내", "이 여정은 '신호 피하기' 탐색이 찾았습니다. 위상을 모르는 신호를 가장 오래 기다린다고 보고 찾은 길입니다."
           in signal.text(), signal.text())
    # ⑤ SNAP_FAILED
    s.set("segmented_control", "origin_kind", "POINT")
    s.put("origin_point", (37.51, 127.0))
    c.eq("⑤ SNAP_FAILED: ⑥ 탭", ["찍은 점을 길에 붙이지 못해 탐색하지 않았습니다."], _Tab(s, "⑥ 탐색 과정").values("Info"))
    data = _Tab(s, "⑦ 데이터·기록")
    c.true("⑤ SNAP_FAILED: ⑦ 탭은 내용이 있다", "데이터 모드 시뮬레이션 · 기준 시각 08:00:00" in data.text() and data.frames(), data.text())
    for name in _TAB_SPEC[:5]:
        tab = _Tab(s, name)
        c.eq(f"⑤ SNAP_FAILED: {name}", (["계산된 여정이 없습니다."], 0, 0), (tab.values("Info"), len(tab.frames()), len(tab.charts())))


def _ui14(c: _Checker, folder: Path, maps: _MapCalls) -> None:
    golden = ce.golden_scenario()
    config = EngineConfig()
    out = ce.run_engine(golden, ce.golden_query(), config)
    items = _items_of(out)
    last = _save_variant(folder, "GV-LAST")
    last_out = ce.run_engine(last, ce.golden_query(), config)
    s = _Screen(c, maps).run().scenario(ce.GOLDEN_ID)
    compare = _Tab(s, "① 경로 비교")
    table = compare.frame("찾은 탐색")
    c.eq("① (순위, 여정)", [("1", "따릉이"), ("2", "지하철 가상선"), ("", "↳ 지하철 가상선"), ("3", "가상1번"),
                          ("4", "가상1번 → 가상2번 (기존 앱 1위)"), ("5", "도보")], _rows(table, ("순위", "여정")))
    c.eq("① 찾은 탐색", ["기본 탐색 · 느린 걸음 기준 · 신호 피하기", "신호 피하기", "기본 탐색 · 따릉이 없이 · 지하철만 · 기존 앱 방식",
                       "버스만 · 느린 걸음 기준", "기존 앱 방식",
                       "기본 탐색 · 따릉이 없이 · 버스만 · 지하철만 · 느린 걸음 기준 · 신호 피하기 · 기존 앱 방식"], _column(table, "찾은 탐색"))
    c.eq("① 계획 도착", ["08:09:06", "08:15:54", "08:15:54", "08:16:46", "08:21:53", "08:21:20"], _column(table, "계획 도착"))
    c.eq("① 상태", ["순위"] * 6, _column(table, "상태"))
    c.true("① 마감이 없으면 마감 열이 없다", table is not None and "마감 확률" not in table.columns, None if table is None else list(table.columns))
    s.set("toggle", "use_deadline", True)
    s.set("time_input", "deadline_time", datetime.time(8, 16, 40))
    table = compare.frame("찾은 탐색")
    c.true("① 마감이 있으면 마감 열", table is not None and "마감 확률" in table.columns, None if table is None else list(table.columns))
    s.set("toggle", "use_deadline", False)
    s.scenario("GV-LAST")
    rows = _rows(compare.frame("찾은 탐색"), ("순위", "여정", "상태"))
    last_items = _items_of(last_out)
    c.eq("① GV-LAST: 맨 아래 행은 Ifbf4ec4c04, 순위 '–', 상태", ("–", last_items["Ifbf4ec4c04"].label, "걸러짐 · 막차 위험 · 확률 낮음"),
         (rows[-1][0], rows[-1][1].removesuffix(" (기존 앱 1위)"), rows[-1][2]) if rows else None)
    s.scenario(ce.GOLDEN_ID)
    # ② 도착 분포 데이터
    ids = list(out.ranking)
    frame = arrival_chart(out, ids, TOKENS_LIGHT).data
    c.eq("② 대표 5개의 5행(순위 순)", ids, list(frame["id"]))
    for row in frame.itertuples():
        it = items[row.id]
        expected = (28_800 + it.arrival.mean_s, 28_800 + it.arrival.p10_s, 28_800 + it.arrival.p50_s, 28_800 + it.arrival.p90_s,
                    28_800 + it.naive_promised_s)
        actual = (row.mean, row.p10, row.p50, row.p90, row.promised)
        c.true(f"② {row.id}: 평균, 10%, 50%, 90%, 약속 도착 = 28,800 + 엔진 값 (10^-6)",
               all(abs(a - b) <= 1e-6 for a, b in zip(actual, expected)), (actual, expected))
    with_variant = [it.itinerary_id for it in (items[rep] for rep in out.ranking) for _ in (0,)]
    with_variant.insert(with_variant.index("I3a248c7d10") + 1, "I469424fb69")
    frame = arrival_chart(out, with_variant, TOKENS_LIGHT, "I469424fb69").data
    c.eq("② I469424fb69 를 고르면 6행", with_variant, list(frame["id"]))
    c.eq("② 그 행의 이름", "↳ 지하철 가상선", next((row.label for row in frame.itertuples() if row.id == "I469424fb69"), None))
    _select(s, "I469424fb69", out)
    shown = compare.charts()
    c.true("② 화면의 도착 분포에도 6행과 그 행", bool(shown) and len(shown[0]) == 6 and "↳ 지하철 가상선" in list(shown[0]["label"]),
           None if not shown else list(shown[0]["label"]))
    s.set("toggle", "show_variants", False)
    s.set("radio", "selected_id", "Ic5c1b22780")
    # ③ 순위 기준 문단과 종합 점수
    text = compare.text()
    c.true("③ 순위 기준 문단: 기준 이름과 같을 때 비교 순서",
           "**순위 기준: 평균 도착**" in text and "값이 같으면 계획대로 갈 확률이 큰 쪽, 요금이 싼 쪽, 탑승이 적은 쪽, 계획의 걷는 거리"
           "(따릉이 구간의 걷기 포함)가 짧은 쪽, 여정 ID 순으로 정합니다." in text, text)
    s.set("selectbox", "rank_criterion", RankCriterion.UTILITY.value)
    s.set("radio", "selected_id", "Ic5c1b22780")
    c.true("③ 종합 점수: J 대입식",
           r"J = 0.5 \cdot \frac{673.83}{1319.86} + 0.2 \cdot \frac{1000}{1550} + 0.3 \cdot (1 - 0.8752) = 0.4217" in compare.latex(),
           compare.latex())
    c.true("③ 종합 점수: T_max, Cost_max 줄", "T_max 1,319.86초 (도보) · Cost_max 1,550원 (지하철 가상선)" in compare.values("Caption"),
           compare.values("Caption"))
    types = compare.column_types("찾은 탐색")
    terms = [types.get(name, {}) for name in ("시간 항", "요금 항", "위험 항")]
    c.eq("③ 세 항 칸은 ProgressColumn 이고 최댓값이 같은 값 0.5",
         [("progress", 0.5)] * 3, [(term.get("type"), term.get("max_value")) for term in terms])
    s.set("selectbox", "rank_criterion", RankCriterion.MEAN_ARRIVAL.value)
    # ④ 카카오 비교 (키 없음)
    button = s.at.button(key="kakao_button") if s.has("button", "kakao_button") else None
    c.eq("④ 키가 없으면 버튼 비활성", True, None if button is None else button.disabled)
    captions = compare.values("Caption")
    c.true("④ '비교 불가(키 없음)' 과 늘 보이는 안내",
           "비교 불가(키 없음)" in captions and captions[-1:] == ["카카오 응답은 이 화면에만 잠시 보이고 저장하지 않습니다."], captions)


def _ui15(c: _Checker, folder: Path, maps: _MapCalls) -> None:
    golden = ce.golden_scenario()
    config = EngineConfig()
    out = ce.run_engine(golden, ce.golden_query(), config)
    items = _items_of(out)
    last = _save_variant(folder, "GV-LAST")
    s = _Screen(c, maps).run().scenario(ce.GOLDEN_ID)
    s.set("radio", "selected_id", "Ifbf4ec4c04")
    tab = _Tab(s, "② 탑승별 확률")
    heads = [_plain(value) for value in tab.htmls("mr-bhead")]
    c.true("① 머리글과 배지",
           len(heads) == 2 and heads[0].startswith("탑승 1: 가상1번 · 정류장1 승차 → 정류장2 하차") and "기존 앱과 같은 차" in heads[0]
           and heads[1].startswith("탑승 2: 가상2번 · 정류장4 승차 → 정류장5 하차") and "유령 환승" in heads[1], heads)
    columns = ("표시", "몇 번째 차", "차량", "출발 시각", "하차 시각", "시각 출처", "만차", "막차", "탈 확률")
    c.eq("② 탑승 1 차량 표", [("★◆", "1번째 차", "차량 g1a", "08:03:20", "08:05:50", "도착 예측", "아니오", "아니오", 0.95221),
                            ("", "2번째 차", "차량 g1b", "08:13:20", "08:15:50", "도착 예측", "아니오", "아니오", 1.0)],
         _rows(tab.frame("표시", 0), columns))
    c.eq("② 탑승 2 차량 표", [("◆", "1번째 차", "차량 g2a", "08:07:00", "08:10:00", "도착 예측", "아니오", "아니오", 0.012551),
                            ("★", "2번째 차", "차량 g2b", "08:17:00", "08:20:00", "도착 예측", "아니오", "아니오", 0.95221),
                            ("", "3번째 차", "배차 간격으로 이은 차", "08:27:00", "08:30:00", "배차 간격으로 이음", "아니오", "아니오", 1.0)],
         _rows(tab.frame("표시", 1), columns))
    kind = tab.column_types("표시").get("탈 확률", {})
    c.eq("② 탈 확률 열은 ProgressColumn (0 ~ 1)", ("progress", 0.0, 1.0), (kind.get("type"), kind.get("min_value"), kind.get("max_value")))
    verdicts = [_paragraphs(value) for value in tab.htmls("mr-verdict")]
    c.eq("③ 판정 문장 (탑승 2)", ["기존 앱: 가상2번 1번째 차(지금부터 7분 00초 뒤 출발)를 탈 수 있다고 안내 → 실제로 탈 확률 1.3% (유령 환승, 기준 40.0%). "
                                "이 앱의 안내: 2번째 차(17분 00초 뒤 출발, 탈 확률 95.2%).",
                                "이 앱은 앞 탑승까지 함께 따져 2번째 차를 안내합니다.",
                                "기존 앱 방식으로는 08:06:38에 정류장에 닿아 22초 여유가 있다고 봅니다."], verdicts[1] if len(verdicts) > 1 else None)
    c.eq("③ 판정 문장 (탑승 1)", ["기존 앱이 안내하는 1번째 차를 탈 확률은 95.2%입니다.",
                                "기존 앱 방식으로는 08:02:16에 정류장에 닿아 1분 04초 여유가 있다고 봅니다."], verdicts[0] if verdicts else None)
    c.true("④ 함께 갈 확률 (탑승 2)", "여기까지 모든 탑승에서 안내 차량(또는 더 이른 차)을 탈 확률 $Q_l$ = 95.2%, 앞 탑승을 계획대로 했을 때 "
           "이 탑승만의 확률 100.0%" in tab.values("Markdown"), tab.values("Markdown"))
    it = items["Ifbf4ec4c04"]
    rides = {ride.index: ride for ride in it.rides}
    for boarding, bins, points in zip(it.boardings, (20, 22), (4096, 3900)):
        chart = histogram_chart(boarding, rides[boarding.ride_index], config, TOKENS_LIGHT)
        frame = chart.data if chart is not None else pd.DataFrame()
        c.eq(f"⑤ 탑승 {boarding.ride_index} 막대그래프 행 수", bins, len(frame))
        c.true(f"⑤ 탑승 {boarding.ride_index} 비율 = 점 수 / {points:,}",
               len(frame) > 0 and all(abs(row.ratio - row.count / points) <= 1e-12 for row in frame.itertuples()))
        c.true(f"⑤ 탑승 {boarding.ride_index} 탈 수 있는 쪽은 왼쪽 경계 ≥ 30 인 칸에만",
               len(frame) > 0 and all((row.side == "탈 수 있음") == (row.left >= 30) for row in frame.itertuples()))
        if boarding.ride_index == 2:
            spec_text = json.dumps(chart.to_dict(), ensure_ascii=False) if chart is not None else ""
            c.true("⑤ 직접 라벨", "승차 여유 30초 이상이면 탐 · 이 탑승만의 확률 100.0%" in spec_text)
    captions = tab.values("Caption")
    c.true("⑤ 그림 아래 (탑승 2)", "막대는 준난수 3,900점의 분포입니다. 판정은 이 그림이 아니라 문턱값 계산을 씁니다(그림 기준 100.0%)." in captions
           and "그림 밖: 왼쪽 9점 · 오른쪽 1점 · 정류장에 닿지 못함 0점" in captions, captions)
    c.eq("⑤ 실제로 탄 차량 표 (탑승 2)", [("차량 g2a", 0.012695), ("차량 g2b", 0.939453), ("배차 간격으로 이은 차", 0.047852)],
         _rows(tab.frame("무게", 1), ("차량", "무게")))
    shown = tab.charts()
    c.eq("⑤ 화면의 막대그래프 데이터 행 수", [20, 22], [len(frame) for frame in shown])
    c.true("⑥ P* 식", "P^{*} = Q_2 = 0.9522" in tab.latex(), tab.latex())
    stats = ("평균", "10%", "50%", "90%", "도착하지 못할 확률", "막차를 놓쳐 걸은 무게")
    c.eq("⑥ 도착 통계", [("08:21:58", "08:20:55", "08:21:53", "08:22:02", "0.0%", "0.0%")], _rows(tab.frame("도착하지 못할 확률"), stats))
    c.true("⑥ 계산 방법", "계산 방법: 탈 확률과 도착 분포: 준난수 4,096점 · 위상을 모르는 신호 1개" in captions, captions)
    s.set("radio", "selected_id", "Ic5c1b22780")
    c.eq("⑥ 따릉이: 안내", ["이 여정은 차량을 타지 않습니다."], tab.values("Info"))
    c.true("⑥ 따릉이: P* 식", "P^{*} = P_{bike,1} = 0.8752" in tab.latex(), tab.latex())
    c.eq("⑥ 따릉이: 자전거가 없어 걸은 무게", ["12.5%"], _column(tab.frame("도착하지 못할 확률"), "자전거가 없어 걸은 무게"))
    c.true("⑥ 따릉이: 계산 방법", "계산 방법: 탈 확률: 문턱값 정확 계산 · 도착 분포: 걷는 속도 점 4,096개" in tab.values("Caption"),
           tab.values("Caption"))
    # ⑦ GV-LAST
    s.scenario(last.id)
    s.set("radio", "selected_id", "Ifbf4ec4c04")
    first = tab.first()
    reasons = _paragraphs(first.value) if type(first).__name__ == "Html" and 'class="mr-callout ghost mr-reasons' in first.value else []
    c.eq("⑦ 맨 위의 사유 문장", ["탑승 2(가상2번)에서 막차까지 따져도 계획대로 탈 확률이 1.3%로 기준 40.0%에 못 미칩니다.",
                              "계획대로 갈 확률 1.3%가 기준 40.0%에 못 미칩니다."], reasons)
    c.eq("⑦ 탑승 2 차량 표 1행", [("차량 g2a (막차)", "예")], _rows(tab.frame("표시", 1), ("차량", "막차")))
    c.true("⑦ 함께 갈 확률 자리", "막차까지 따져도 탈 확률이 40.0%에 못 미칩니다(막차 위험)." in tab.values("Markdown"), tab.values("Markdown"))
    c.eq("⑦ 실제로 탄 차량 표 (탑승 2)", [("차량 g2a", 0.012695), ("막차 놓침", 0.987305)], _rows(tab.frame("무게", 1), ("차량", "무게")))
    c.eq("⑦ 막차를 놓쳐 걸은 무게", ["98.7%"], _column(tab.frame("도착하지 못할 확률"), "막차를 놓쳐 걸은 무게"))
    # ⑧ "동시 도착" 의 자리(§7.4): x 범위가 더 넓은 쪽
    hand = ce.build_scenarios()
    cases = [(ce.GOLDEN_ID, out)] + [(key, ce.run_engine(hand[key], hand[key].default_query, config)) for key in ("A", "B")]
    wrong, count = [], 0
    for key, result in cases:
        for result_it in sorted(result.itineraries, key=lambda item: item.itinerary_id):
            rides_of = {ride.index: ride for ride in result_it.rides}
            for boarding in result_it.boardings:
                if boarding.histogram is None:
                    continue
                aligns, domain = _zero_label(histogram_chart(boarding, rides_of[boarding.ride_index], result.config, TOKENS_LIGHT))
                count += 1
                if aligns != {_wider_side(domain)}:
                    wrong.append((key, result_it.itinerary_id, boarding.ride_index, sorted(aligns), domain))
    c.true("⑧ 골든, A, B 에 막대그래프가 있다", count > 0, count)
    c.eq("⑧ 골든, A, B 의 모든 막대그래프에서 \"동시 도착\" 이 넓은 쪽", [], wrong)
    golden_it = items["Ifbf4ec4c04"]
    base = next(boarding for boarding in golden_it.boardings if boarding.ride_index == 2)
    ride2 = next(ride for ride in golden_it.rides if ride.index == 2)
    for shift, expected, span in ((0.0, "left", [-19.05, 654.05]), (-700.0, "right", [-181.15, 36.15])):
        moved = base.histogram.model_copy(update={"bins": tuple((left + shift, n) for left, n in base.histogram.bins)})
        aligns, domain = _zero_label(histogram_chart(base.model_copy(update={"histogram": moved}), ride2, config, TOKENS_LIGHT))
        which = "그대로" if not shift else f"칸을 {shift:+.0f}초 옮김"
        c.eq(f"⑧ Ifbf4ec4c04 탑승 2 막대그래프({which})의 (\"동시 도착\" 맞춤, x 범위)",
             ({expected}, span), (aligns, [round(value, 2) for value in domain] if domain else domain))


def _zero_label(chart: alt.LayerChart | None) -> tuple[set[str], list[float] | None]:
    """막대그래프의 "동시 도착" 글자 층들(바탕 테두리 층과 글자 층)의 맞춤과 x 범위(§7.4)."""
    layers = chart.to_dict().get("layer", []) if chart is not None else []
    aligns = {layer["mark"].get("align") for layer in layers
              if isinstance(layer.get("mark"), dict) and layer["mark"].get("text") == "동시 도착"}
    domain = next((layer["encoding"]["x"]["scale"].get("domain") for layer in layers
                   if "scale" in layer.get("encoding", {}).get("x", {})), None)
    return aligns, domain


def _wider_side(domain: list[float] | None) -> str | None:
    """x 범위에서 여유 0 의 오른쪽이 넓거나 같으면 "left" (실선 오른쪽에 왼쪽 맞춤), 아니면 "right"."""
    if not domain:
        return None
    return "left" if domain[1] >= -domain[0] else "right"


def _ui16(c: _Checker, folder: Path, maps: _MapCalls) -> None:
    golden = ce.golden_scenario()
    out = ce.run_engine(golden, ce.golden_query(), EngineConfig())
    s = _Screen(c, maps).run().scenario(ce.GOLDEN_ID)
    s.set("radio", "selected_id", "Ifbf4ec4c04")
    tab = _Tab(s, "③ 신호")
    first = tab.first()
    c.eq("⑤ 표 위 안내 문장", "계획은 평소 속도로 걷고 위상을 모르는 신호는 평균만큼 기다린다고 본 값입니다. 확률은 걷는 속도와 위상 표본마다 다시 계산합니다.",
         getattr(first, "value", None))
    columns = ("ID", "신호", "출처", "계획 도착", "τ", "상태", "대기", "분산")
    c.eq("① 신호 표 2행(지나는 순서)", [("SG1", "교차로3 남북", "위상 모름 · 설계 현시", "08:06:06", "-", "위상 모름", "34초", "885.94"),
                                    ("SG3", "교차로4 남북", "실시간 개방 · 설계 현시", "08:20:16", "41초", "적색", "49초", "0.00")],
         _rows(tab.frame("계획 도착"), columns))
    phases = tab.htmls("mr-phase")
    c.eq("① 위상 막대 2개, SG1 만 unknown", [True, False], ['class="mr-phase unknown"' in value for value in phases])
    formulas = tab.latex()
    c.eq("① 대입식 (SG1, SG3 순서)", [r"E[W] = T_{red}^2 / 2C = 90^2 / (2 \times 120) = 33.75",
                                    r"Var = T_{red}^3 / 3C - E[W]^2 = 90^3 / (3 \times 120) - 33.75^2 = 885.94",
                                    r"\tau = (\theta + t_{arr}) \bmod C = (85 + 1216) \bmod 90 = 41", r"W = C - \tau = 90 - 41 = 49"],
         formulas)
    _select(s, "I469424fb69", out)
    rows = _rows(tab.frame("계획 도착"), ("ID", "출처"))
    c.eq("② I469424fb69: SG2 출처", [("SG2", "위상 모름 · 감응 · 설계 현시")], rows)
    c.eq("② 감응 위상 막대", [True], ['class="mr-phase actuated"' in value for value in tab.htmls("mr-phase")])
    c.true("② 감응 대입식", r"E[W] = \sum_i \rho_i^2 / 2 \,/\, \sum_i c_i = 32250 / 700 = 46.07" in tab.latex(), tab.latex())
    c.true("② 표본 5개를 식에 모두 적는다", any("100, 120, 140, 160, 180" in text for text in tab.latex()), tab.latex())
    s.set("toggle", "show_variants", False)
    s.set("radio", "selected_id", "Ic5c1b22780")
    c.true("③ 따릉이 ③ 의 SG4", r"\tau = (\theta + t_{arr}) \bmod C = (0 + 277.5) \bmod 120 = 37.5" in tab.latex(), tab.latex())
    c.eq("③ SG4 상태와 대기", [("SG4", "녹색", "0초")], _rows(tab.frame("계획 도착"), ("ID", "상태", "대기")))
    every = tab.frame("교차로")
    c.eq("④ 시나리오의 모든 신호 4행 (ID 순)", ["SG1", "SG2", "SG3", "SG4"], _column(every, "ID"))
    c.eq("④ SG3, SG4 의 θ 와 지금 상태", [("SG3", "85", "적색"), ("SG4", "0", "녹색")],
         [row for row in _rows(every, ("ID", "θ", "지금 상태")) if row[0] in ("SG3", "SG4")])
    expanders = [node.label for node in tab.all("Expander")]
    c.true("④ 접힌 '시나리오의 모든 신호'", "시나리오의 모든 신호" in expanders, expanders)
    s.set("select_slider", "depart_offset_s", 300)
    c.eq("④ 출발 늦추기 300: SG3 θ 25, SG4 60 (V12g)", [("SG3", "25"), ("SG4", "60")],
         [row for row in _rows(tab.frame("교차로"), ("ID", "θ")) if row[0] in ("SG3", "SG4")])


def _ui17(c: _Checker, folder: Path, maps: _MapCalls) -> None:
    config = EngineConfig()
    norate = _save_variant(folder, "GV-NORATE")
    norate_out = ce.run_engine(norate, ce.golden_query(), config)
    s = _Screen(c, maps).run().scenario(ce.GOLDEN_ID)
    s.set("radio", "selected_id", "Ic5c1b22780")
    tab = _Tab(s, "④ 따릉이")
    stages = tab.htmls("mr-stages")
    c.eq("① 5단계 막대의 구간 5개", (1, 5), (len(stages), stages[0].count('class="mr-seg ') if stages else 0))
    c.eq("① 단계 표", [("① 걷기", "08:00:00", "08:00:40", "40초", "50 m", "0초"), ("② 대여", "08:00:40", "08:01:05", "25초", "", ""),
                       ("③ 따릉이", "08:01:05", "08:07:55", "6분 50초", "1.64 km", "0초"), ("④ 반납", "08:07:55", "08:08:10", "15초", "", ""),
                       ("⑤ 걷기", "08:08:10", "08:09:06", "56초", "70 m", "0초")],
         _rows(tab.frame("단계"), ("단계", "시작", "끝", "시간", "거리", "신호 대기")))
    c.true("① T_pm 대입식", "T_{pm} = 40 + 25 + 410 + 15 + 56 = 546" in tab.latex(), tab.latex())
    pieces = ("n_0 = 1", r"\lambda_h = 12", "g = 0", "a = 40", "P_{bike} = 0.8752")
    c.true("② P_bike 대입식", any(all(piece in text for piece in pieces) for text in tab.latex()), tab.latex())
    c.true("② 자전거가 없을 때 문장", "자전거가 없으면 대여소1에서 도착지까지 1.65 km를 걷습니다(평소 속도 22분 00초, 이 경우의 무게 12.5%)."
           in tab.values("Markdown"), tab.values("Markdown"))
    c.eq("③ 대여소 상태 표", [("대여소1", "이 여정의 대여소", 1, 10, "12.0건/시", "08:00:40", "87.5%"),
                            ("대여소2", "이 여정의 반납소", 2, 10, "6.0건/시", "08:21:12", "37.4%"),
                            ("대여소3", "자전거 없음", 0, 10, "6.0건/시", "08:11:36", "0.0%"),
                            ("대여소4", "남을 확률 낮음", 1, 10, "60.0건/시", "08:04:24", "1.2%"),
                            ("대여소5", "빌릴 수 있음", 3, 10, "-", "08:05:38", "100.0%")],
         _rows(tab.frame("대여소"), ("대여소", "상태", "자전거 수", "거치대", "시간당 대여", "계획 도착", "P_bike")))
    bike_it = next((it for it in norate_out.itineraries if it.status == RouteStatus.RANKED and any(move.bike for move in it.moves)), None)
    c.true("④ GV-NORATE 에 따릉이 여정이 있다", bike_it is not None)
    if bike_it is not None:
        s.scenario(norate.id)
        s.set("radio", "selected_id", bike_it.itinerary_id)
        text = tab.text()
        c.true("④ GV-NORATE: 대여 속도 정보 없음", "대여 속도 정보 없음, 자전거 수만 확인" in text, text)
        c.true("④ GV-NORATE: P_bike 100.0%", "자전거가 남아 있을 확률 100.0%" in text, text)
        c.eq("④ GV-NORATE: 대여소1 행", [("대여소1", "-", "100.0%")],
             [row for row in _rows(tab.frame("대여소"), ("대여소", "시간당 대여", "P_bike")) if row[0] == "대여소1"])


def _ui18(c: _Checker, folder: Path, maps: _MapCalls) -> None:
    config = EngineConfig()
    wide = _save_variant(folder, "GV-WIDE")
    wide_out = ce.run_engine(wide, ce.golden_query(), config.model_copy(update={"climate_card": True}))
    s = _Screen(c, maps).run().scenario(ce.GOLDEN_ID)
    tab = _Tab(s, "⑤ 요금")
    columns = ("여정", "묶음 수", "대중교통", "따릉이", "마일리지", "기후동행카드", "합계", "탑승 거리")
    c.eq("① 여정별 표 6행", [("따릉이", 0, "0원", "1,000원", "0원", "아니오", "1,000원", "0.00 km"),
                           ("지하철 가상선", 1, "1,550원", "0원", "0원", "아니오", "1,550원", "1.37 km"),
                           ("지하철 가상선", 1, "1,550원", "0원", "0원", "아니오", "1,550원", "1.37 km"),
                           ("가상1번", 1, "1,500원", "0원", "0원", "아니오", "1,500원", "0.65 km"),
                           ("가상1번 → 가상2번", 1, "1,500원", "0원", "0원", "아니오", "1,500원", "1.39 km"),
                           ("도보", 0, "0원", "0원", "0원", "아니오", "0원", "0.00 km")], _rows(tab.frame("묶음 수"), columns))
    s.set("radio", "selected_id", "Ifbf4ec4c04")
    c.eq("② Ifbf4ec4c04 의 묶음 표", [(1, "1, 2", "1,500원", "1.39 km", "0원", "-")],
         _rows(tab.frame("앞 묶음과 끊긴 이유"), ("묶음", "탑승", "기본요금", "거리", "거리 추가요금", "앞 묶음과 끊긴 이유")))
    s.set("toggle", "climate_card", True)
    c.eq("③ 기후동행카드: 합계 (V12c)", [("따릉이", "1,000원"), ("지하철 가상선", "0원"), ("지하철 가상선", "0원"), ("가상1번", "0원"),
                                       ("가상1번 → 가상2번", "0원"), ("도보", "0원")], _rows(tab.frame("묶음 수"), ("여정", "합계")))
    s.set("toggle", "bike_mileage", True)
    c.eq("③ 마일리지까지: 따릉이 행", [("따릉이", "500원", "500원")],
         [row for row in _rows(tab.frame("묶음 수"), ("여정", "마일리지", "합계")) if row[0] == "따릉이"])
    s.set("toggle", "bike_mileage", False)
    notes = [_list_items(value) for value in tab.htmls("mr-notes")]
    expected_notes = list(ce.fare_notes(EngineConfig(climate_card=True)))
    c.eq("⑤ 맨 아래 목록 = fare_notes(config) (순서까지)", expected_notes, notes[-1] if notes else None)
    c.true("⑤ 어떤 항목에도 '{' 가 없다", bool(notes) and not any("{" in item for item in notes[-1]), notes)
    s.scenario(wide.id)
    if not s.state("climate_card"):
        s.set("toggle", "climate_card", True)
    target = next((it for it in wide_out.itineraries if it.label == "가상1번 → 가상2번"), None)
    c.true("④ GV-WIDE 에 가상1번 → 가상2번 여정이 있다", target is not None)
    if target is not None:
        s.set("radio", "selected_id", target.itinerary_id)
        c.true("④ GV-WIDE: 광역버스 안내", "광역버스가 있어 기후동행카드 단기권을 적용하지 않았습니다" in tab.text(), tab.text())


def _ui19(c: _Checker, folder: Path, maps: _MapCalls) -> None:
    golden = ce.golden_scenario()
    out = ce.run_engine(golden, ce.golden_query(), EngineConfig())
    s = _Screen(c, maps).run().scenario(ce.GOLDEN_ID)
    tab = _Tab(s, "⑥ 탐색 과정")
    c.true("① 요약", "실행 7개(건너뜀 0개) · 찾은 여정 18개 → 합친 뒤 6개 → 평가 6개(버림 0개)" in tab.values("Markdown"), tab.values("Markdown"))
    runs = tab.frame("건너뛴 이유")
    c.eq("② 실행 이름", ["기본 탐색", "따릉이 없이", "버스만", "지하철만", "느린 걸음 기준", "신호 피하기", "기존 앱 방식"], _column(runs, "실행"))
    c.eq("② 속도 배수", ["1.00배"] * 4 + ["0.85배", "1.00배", "1.00배"], _column(runs, "걷는 속도 배수"))
    c.eq("② 대기 규칙", ["평균 대기"] * 5 + ["가장 긴 대기", "신호 무시"], _column(runs, "신호 대기 규칙"))
    c.eq("② 따릉이 상한", [1, 0, 0, 0, 1, 1, 0], _column(runs, "따릉이 상한"))
    c.eq("② 승차 여유", [30] * 6 + [0], _column(runs, "승차 여유(초)"))
    c.eq("② 라운드 수", [3] * 6 + [4], _column(runs, "라운드 수"))
    c.eq("② D 의 파레토 라벨 수", [3, 2, 2, 2, 3, 3, 3], _column(runs, "D 의 파레토 라벨 수"))
    c.eq("② 찾은 여정 수", [3, 2, 2, 2, 3, 3, 3], _column(runs, "찾은 여정 수"))
    c.eq("② 건너뛴 이유 빈칸", [""] * 7, _column(runs, "건너뛴 이유"))
    c.eq("③ 기본 실행", "FULL", s.state("trace_run"))
    c.eq("③ 라운드 표", [(0, 38, 0, 0, "08:09:06"), (1, 14, 4, 6, "08:09:06"), (2, 0, 6, 3, "08:09:06")],
         _rows(tab.frame("새 걷기 라벨"), ("라운드", "새 걷기 라벨", "표시된 정류장", "훑은 노선", "가장 이른 D 도착")))
    labels = ("도착 시각", "탑승 수", "따릉이 수", "여정")
    c.eq("③ D 의 파레토 라벨 표", [("08:09:06", 0, 1, "따릉이"), ("08:15:54", 1, 0, "지하철 가상선"), ("08:21:20", 0, 0, "도보")],
         _rows(tab.frame("따릉이 수"), labels))
    s.set("selectbox", "trace_run", "NAIVE")
    c.eq("③ 기존 앱 방식: 라운드 4행", 4, len(tab.frame("새 걷기 라벨")) if tab.frame("새 걷기 라벨") is not None else None)
    c.eq("③ 기존 앱 방식: 첫 라벨", ("08:10:42", 2, 0, "가상1번 → 가상2번"), (_rows(tab.frame("따릉이 수"), labels) or [None])[0])
    s.set("selectbox", "trace_run", "FULL")
    lines = tab.frame("구간 운행시간 출처")
    c.eq("④ 노선별 차량 표 3행", ["G1", "G2", "가상선:하행:M1-M3:3"], _column(lines, "노선"))
    c.eq("④ 쓸 수 있음", ["✓"] * 3, _column(lines, "쓸 수 있음"))
    c.eq("④ 구간 운행시간 출처", ["예측 1구간 · 설계 속도 1구간", "예측 1구간 · 설계 속도 0구간", "-"], _column(lines, "구간 운행시간 출처"))
    c.eq("④ 알려진 차량 수와 합성 차량 수 = line_times", [(times.n_known, times.n_synthetic) for times in out.line_times],
         _rows(lines, ("알려진 차량 수", "합성 차량 수")))
    s.set("selectbox", "trace_line", "G1")
    c.eq("④ G1 의 구간 표", [(1, "정류장1 → 정류장2", "2분 30초", "예측에서"), (2, "정류장2 → 정류장3", "2분 48초", "설계 속도")],
         _rows(tab.frame("정류장 → 정류장"), ("구간", "정류장 → 정류장", "운행시간", "출처")))
    c.true("⑤ 타원 가지치기 요약", "유지 28 / 29 · d(S, D) 1.60 km · 임계값 2.08 km · a 1.04 km · b 665 m · 환승용 유지 1개" in tab.values("Markdown"),
           tab.values("Markdown"))
    pruning = tab.frame("환승용 유지")
    sums = [float(str(value).replace(",", "").removesuffix(" m")) for value in _column(pruning, "합")]
    c.eq("⑤ 표 29행", 29, len(sums))
    c.true("⑤ 합 오름차순", sums == sorted(sums), sums)
    c.eq("⑤ 마지막 두 행", [("B3", "2,125.93 m", "✓", "✓"), ("W9", "2,408.27 m", "✕", "")],
         _rows(pruning, ("노드", "합", "유지", "환승용 유지"))[-2:])


def _ui20(c: _Checker, folder: Path, maps: _MapCalls) -> None:
    # 빈 폴더, 골든
    s = _Screen(c, maps).run().scenario(ce.GOLDEN_ID)
    tab = _Tab(s, "⑦ 데이터·기록")
    text = tab.text()
    c.true("① 빈 폴더: 데이터 모드와 기준 시각", "데이터 모드 시뮬레이션 · 기준 시각 08:00:00" in text, text)
    c.true("① 빈 폴더: 시뮬레이션 문장", "시나리오에 적힌 값으로 계산했습니다. 평일 08:00 가정" in tab.values("Caption"), tab.values("Caption"))
    infos = tab.values("Info")
    c.true("② 빈 폴더: 저장소 안내", "기록 저장소가 없습니다. 수집을 시작하려면 키가 있는 컴퓨터에서 `python core_engine.py --collect` 를 "
           "실행하세요(시연 시간대에만 부릅니다)." in infos, infos)
    c.eq("③ 빈 폴더: 역 표", [("역1", "M1", "없음", "-", 1), ("역2", "M2", "없음", "-", 1), ("역3", "M3", "없음", "-", 1)],
         _rows(tab.frame("지나는 정차 패턴"), ("역", "역코드", "시각표", "출처", "지나는 정차 패턴")))
    captions = tab.values("Caption")
    c.true("③ 빈 폴더: 시각표 받기와 역간 거리", "시각표 받기: `python core_engine.py --fetch-timetable M1 M2 M3`" in captions
           and any("없음(직선거리로 둠)" in caption for caption in captions), captions)
    c.true("④ 빈 폴더: 모델 안내", "학습 모델이 없습니다. 신호 기록이 쌓이면 `python core_engine.py --fit`, 따릉이 대여 이력을 받으면 "
           "`--fit-bike` 를 실행하세요." in infos, infos)
    c.true("⑤ 빈 폴더: 키", all(piece in text for piece in ("열린데이터광장 키 없음", "공공데이터포털 키 없음", "카카오 키 없음", "서울 신호 키 없음",
                                                       "키는 환경변수로만 넣습니다.")), text)
    # 학습한 따릉이 속도 (가짜 load_models)
    with tempfile.TemporaryDirectory(prefix="mobility-router-rp6-") as temp:
        pair = [ce._rp6_station("A", "102. 테스트 대여소 A", "ST-102"), ce._rp6_station("B", "205. 테스트 대여소 B", "ST-205")]
        bike = ce.fit_bike_model(ce._rp6_history(Path(temp)), ce._rp6_targets(), pair, EngineConfig())
    with_speed = ce.Models(signal=None, bike=bike, summaries=(), files=())
    without_speed = ce.Models(signal=None, bike=dataclasses.replace(bike, speed=None), summaries=(), files=())
    golden = ce.golden_scenario()
    c.true("RP6 속도 통계", bike.speed is not None and abs(bike.speed.median_mps - 3.666667) < 1e-6 and abs(bike.speed.k - 0.185322) < 1e-6,
           None if bike.speed is None else (bike.speed.median_mps, bike.speed.k))
    with _replaced(ce, "load_models", lambda *args, **kwargs: with_speed):
        _clear_caches()
        learned = _Screen(c, maps).run().scenario(ce.GOLDEN_ID)
        c.eq("학습한 따릉이 속도: 버튼 활성", False, learned.at.button(key="apply_bike_speed").disabled)
        learned.click("apply_bike_speed")
        c.eq("학습한 따릉이 속도: v_pm 3.7, k_pm 0.185322", (3.7, 0.185322), (learned.state("v_pm"), round(float(learned.state("k_pm")), 6)))
        expected = ce.run_engine(golden, ce.golden_query(), EngineConfig(v_pm_mps=3.7, k_pm=float(bike.speed.k)))
        c.eq("학습한 따릉이 속도: KPI", _kpi_expect(expected), learned.kpi())
    with _replaced(ce, "load_models", lambda *args, **kwargs: without_speed):
        _clear_caches()
        plain = _Screen(c, maps).run().scenario(ce.GOLDEN_ID)
        c.eq("속도 통계가 없는 모델: 버튼 비활성", True, plain.at.button(key="apply_bike_speed").disabled)
    _clear_caches()
    # 합성 기록 재생 (UI-22 의 폴더, 2026-11-02 08:00)
    truth, syn, syn_config, models = _synthetic(folder)
    s = _Screen(c, maps).run()
    _replay_at(s, syn, 2, datetime.time(8, 0))
    tab = _Tab(s, "⑦ 데이터·기록")
    sources = tab.frame("관측 시각")
    c.eq("① 원천 표 5행 (원천, 대상)", [("버스 도착", "SYN-G1"), ("버스 도착", "SYN-G2"), ("따릉이", "합성"), ("신호", "합성"), ("지하철 시각표", "")],
         _rows(sources, ("원천", "대상")))
    status = _column(sources, "상태")
    c.eq("① 상태 (첫 행, 마지막 행)과 첫 행 관측 시각", ("✓ 성공", "✓ 성공", "08:00:00"),
         (status[0] if status else None, status[-1] if status else None, (_column(sources, "관측 시각") or [None])[0]))
    oldest = min(path.stat().st_mtime for path in (truth.store_path.parent / "timetables").glob("*.csv"))
    stamp = datetime.datetime.fromtimestamp(oldest, KST)
    c.eq("① 지하철 시각표의 관측 시각은 다른 날이라 날짜를 붙인다(가장 오래된 파일의 수정 시각)",
         stamp.strftime("%H:%M:%S") if stamp.date() == datetime.date(2026, 11, 2) else stamp.strftime("%Y-%m-%d %H:%M:%S"),
         (_column(sources, "관측 시각") or [None])[-1])
    store = tab.frame("조회 주기")
    c.eq("② 저장소 표 3행", [("버스 도착", 2, 1080, "99.7%", "2026-11-02(월) 07:30:00", "2026-11-04(수) 08:59:30", "30초"),
                           ("따릉이", 1, 540, "100.0%", "2026-11-02(월) 07:30:00", "2026-11-04(수) 08:59:30", "30초"),
                           ("신호", 1, 540, "100.0%", "2026-11-02(월) 07:30:00", "2026-11-04(수) 08:59:30", "30초")],
         _rows(store, ("원천", "대상 수", "조회 수", "성공률", "첫 조회", "마지막 조회", "조회 주기")))
    chips = " ".join(_plain(value) for value in tab.htmls("mr-chiprow"))
    c.true("② 수집 상태 배지 '멈춤 · 마지막 조회'", "멈춤 · 마지막 조회" in chips, chips)
    c.eq("② 시연 시간대별 기록 표", [("2026-11-04(수)", "평일 아침", 720, "100.0%"), ("2026-11-03(화)", "평일 아침", 720, "99.6%"),
                                  ("2026-11-02(월)", "평일 아침", 720, "100.0%")],
         _rows(tab.frame("시간대"), ("날짜", "시간대", "조회 수", "성공률")))
    c.eq("② 실패 사유 (저장소 표의 원천별 열, 많은 순 3개)", ["HTTP 500 · 3회", "", ""], _column(store, "실패 사유"))
    stations = tab.frame("지나는 정차 패턴")
    c.eq("③ 시각표 칸이 모두 '있음', 지나는 패턴 1", [("있음", 1)] * 3, _rows(stations, ("시각표", "지나는 정차 패턴")))
    source = (_column(stations, "출처") or [""])[0]
    c.true("③ 출처에 'M1.csv' 와 수정 날짜", "M1.csv" in str(source) and re.search(r"\d{4}-\d{2}-\d{2}", str(source)) is not None, source)
    c.true("③ 역간 거리 '있음 · 확인된 구간 2 / 2'", any("있음 · 확인된 구간 2 / 2" in caption for caption in tab.values("Caption")),
           tab.values("Caption"))
    with contextlib.redirect_stdout(io.StringIO()), contextlib.redirect_stderr(io.StringIO()):
        code = ce.main(["--fit", "--store", str(truth.store_path), "--out", str(folder)])
    c.eq("④ --fit 종료 코드", 0, code)
    s.run("학습 뒤 다시 실행")
    c.true("④ 모델 표에 종류 '신호' 행(대상 2)", ("신호", 2) in _rows(tab.frame("종류"), ("종류", "대상 수")), _rows(tab.frame("종류")))
    every = _Tab(s, "③ 신호").frame("교차로")
    c.eq("④ ③ 탭 모든 신호: SG3, SG4 출처 '기록 학습' (RP6)", [("SG3", "기록 학습"), ("SG4", "기록 학습")],
         [row for row in _rows(every, ("ID", "출처")) if row[0] in ("SG3", "SG4")])


# --- UI-23 ~ UI-25 ---


def _ui23(c: _Checker, folder: Path, maps: _MapCalls) -> None:
    config = EngineConfig()
    hand = ce.build_scenarios()
    b, a = hand["B"], hand["A"]
    out = ce.run_engine(b, b.default_query, config)
    items = _items_of(out)
    s = _Screen(c, maps).run().scenario("B")
    # ① 비교 패널
    panel = (s.htmls("mr-compare") or [""])[0]
    naive_card = panel[panel.find('class="mr-card naive'):panel.find('class="mr-card app')]
    c.true("① 비교 패널 왼쪽에 '유령 환승' 배지", "유령 환승" in _plain(naive_card), _plain(naive_card))
    naive = items[out.comparison.naive_best_id]
    promised = _clock_text(b.clock_s, naive.naive_promised_s)
    conclusion = _plain(panel[panel.find('class="mr-conclusion"'):])
    c.true(f"① 결론 문장에 기존 방식 1위의 약속 도착 {promised}", promised in conclusion, conclusion)
    c.eq("① KPI = 엔진", _kpi_expect(out), s.kpi())
    # ② 기존 방식 1위의 ② 탭
    s.set("radio", "selected_id", naive.itinerary_id)
    tab = _Tab(s, "② 탑승별 확률")
    tables = [frame for frame in tab.frames() if "표시" in frame.columns]
    with_tables = [boarding for boarding in naive.boardings if boarding.vehicles]
    pairs = [(boarding, frame) for boarding, frame in zip(with_tables, tables) if boarding.ghost]
    c.true("② 기존 방식 1위에 유령 환승인 탑승이 있다", bool(pairs), [boarding.ghost for boarding in naive.boardings])
    for boarding, frame in pairs:
        marks = [str(mark) for mark in frame["표시"]]
        label = f"② 탑승 {boarding.ride_index}"
        if any(option.trip_id == boarding.naive_trip_id for option in boarding.vehicles):
            c.true(f"{label}: ◆ 행", any("◆" in mark for mark in marks), marks)
        else:
            c.true(f"{label}: ◆ 차량이 표(끝에서 6대) 밖이면 안내", "기존 앱이 안내하는 차(◆)는 표에 보인 차량보다 앞 차량이라 표에 없습니다."
                   in tab.values("Caption"), tab.values("Caption"))
        if boarding.guided_found:
            c.true(f"{label}: ◆ 와 다른 ★ 행", "★" in marks, marks)
        else:
            c.true(f"{label}: 안내 차량을 정하지 못했으면 ★ 없이 막차 위험 문장",
                   not any("★" in mark for mark in marks)
                   and "막차까지 따져도 탈 확률이 40.0%에 못 미칩니다(막차 위험)." in tab.values("Markdown"), (marks, tab.values("Markdown")))
    rides = {ride.index: ride for ride in naive.rides}
    ghost = next((boarding for boarding in naive.boardings if boarding.ghost and boarding.histogram is not None), None)
    if ghost is not None:
        chart = histogram_chart(ghost, rides[ghost.ride_index], out.config, TOKENS_LIGHT)
        c.eq("② 막대그래프 데이터 행 수 = 칸 수", len(ghost.histogram.bins), len(chart.data) if chart is not None else None)
    guided = next((it for it in out.itineraries if any(boarding.ghost and boarding.guided_found and boarding.guided_trip_id != boarding.naive_trip_id
                                                       for boarding in it.boardings)), None)
    c.true("② 안내 차량을 정한 유령 환승 탑승이 있는 여정이 있다", guided is not None)
    if guided is not None:
        _select(s, guided.itinerary_id, out)
        index = next(i for i, boarding in enumerate(boarding for boarding in guided.boardings if boarding.vehicles)
                     if boarding.ghost and boarding.guided_found)
        marks = _column(_Tab(s, "② 탑승별 확률").frame("표시", index), "표시")
        c.true(f"② {guided.itinerary_id}: ◆ 행과 다른 ★ 행", "◆" in marks and "★" in marks, marks)
        s.set("toggle", "show_variants", False)
        s.set("radio", "selected_id", naive.itinerary_id)
    # ③ 신호 위상 막대 수
    c.eq("③ mr-phase 수 = 신호 이벤트 수", len(_plan_events(naive)), len(_Tab(s, "③ 신호").htmls("mr-phase")))
    # ④ 지하철만, 따릉이, 신호 피하기만 찾은 대표
    reps = [items[rep] for rep in out.ranking]
    subway = next((it for it in reps if it.rides and all(ride.mode == TravelMode.SUBWAY for ride in it.rides)
                   and not any(move.bike for move in it.moves)), None)
    bike = next((it for it in reps if any(move.bike for move in it.moves)), None)
    averse_all = [it for it in reps if SearchRun.AVERSE in it.found_by and SearchRun.FULL not in it.found_by]
    averse = next((it for it in averse_all if it not in (subway, bike)), averse_all[0] if averse_all else None)
    c.true("④ 세 대표가 있다", None not in (subway, bike, averse), (subway, bike, averse))
    for it in (subway, bike, averse):
        if it is None:
            continue
        s.set("radio", "selected_id", it.itinerary_id)
        timeline = s.htmls("mr-tl")
        c.eq(f"④ {it.itinerary_id}: 시간 막대 구간 수 = legs 수", len(it.legs), timeline[0].count('class="mr-seg ') if timeline else None)
        shown = _Tab(s, "① 경로 비교").charts()
        c.true(f"④ {it.itinerary_id}: 도착 분포에 그 여정의 행", bool(shown) and it.itinerary_id in list(shown[0]["id"]))
        c.eq(f"④ {it.itinerary_id}: KPI = 엔진", _kpi_expect(out), s.kpi())
    # ⑤ 출발 늦추기 0 ~ 600
    s.set("radio", "selected_id", out.best_id)
    structures = []
    for dt in range(0, 601, 60):
        expected = ce.run_engine(ce.advance_clock(b, float(dt), config), b.default_query, config)
        s.set("select_slider", "depart_offset_s", dt)
        c.eq(f"⑤ Δt {dt}: KPI", _kpi_expect(expected), s.kpi())
        c.eq(f"⑤ Δt {dt}: 선택이 최선 여정", expected.best_id, s.state("selected_id"))
        best = _items_of(expected)[expected.best_id]
        structures.append((tuple(tuple((line.route_id, line.board_index, line.alight_index) for line in ride.bundle) if ride.bundle
                                 else (ride.route_id, ride.board_index, ride.alight_index) for ride in best.rides),
                           tuple((move.bike.pick_id, move.bike.drop_id) for move in best.moves if move.bike)))
    c.true("⑤ 최선 여정의 탑승 구조가 한 번 이상 바뀐다", len(set(structures)) > 1, structures)
    s.set("select_slider", "depart_offset_s", 0)
    # ⑥ 시나리오 A
    s.scenario("A")
    c.eq("⑥ A: 출발 종류 '지금 탄 열차'", "TRAIN", s.state("origin_kind"))
    a_out = ce.run_engine(a, a.default_query, config)
    c.eq("⑥ A: KPI = 기본 질의", _kpi_expect(a_out), s.kpi())
    s.set("segmented_control", "walk_preset", "느리게")
    c.eq("⑥ A: 느리게 = v_walk 1.0", _kpi_expect(ce.run_engine(a, a.default_query, EngineConfig(v_walk_mps=1.0))), s.kpi())
    s.set("segmented_control", "walk_preset", "보통")
    # ⑦ ⑥ 탭과 탐색 라운드
    c.eq("⑦ ⑥ 탭 실행 표 7행", 7, len(_Tab(s, "⑥ 탐색 과정").frame("건너뛴 이유")) if _Tab(s, "⑥ 탐색 과정").frame("건너뛴 이유") is not None else None)
    rounds = _group_markers(feature_groups(build_map(a, a_out, a_out.best_id))["탐색 라운드"])
    c.eq("⑦ 탐색 라운드 표지 수 = reach 수", len(a_out.search.reach), len(rounds))
    # ⑧ 기후동행카드
    s.set("toggle", "climate_card", True)
    card = ce.run_engine(a, a.default_query, EngineConfig(climate_card=True))
    c.eq("⑧ KPI = 기후동행카드 결과", _kpi_expect(card), s.kpi())
    best = _items_of(card)[card.best_id]
    fare = dict((label, value) for label, value, _ in s.kpi()).get("요금")
    c.eq("⑧ 요금 KPI: 최선 여정의 따릉이 요금 또는 0원", f"{best.fare.bike_krw:,}원" if any(move.bike for move in best.moves) else "0원", fare)
    rows = _rows(_Tab(s, "⑤ 요금").frame("묶음 수"), ("따릉이", "합계"))
    c.true("⑧ ⑤ 탭: 따릉이가 없는 여정의 합계가 모두 '0원'", bool(rows) and all(total == "0원" for bike_fare, total in rows if bike_fare == "0원"), rows)
    c.eq("⑧ ⑤ 탭: 따릉이 요금이 있는 행 수 = 따릉이 구간이 있는 여정 수",
         sum(1 for it in card.itineraries if any(move.bike for move in it.moves)), sum(1 for bike_fare, _ in rows if bike_fare != "0원"))
    s.set("toggle", "climate_card", False)


def _ui24(c: _Checker, folder: Path, maps: _MapCalls) -> None:
    truth, syn, syn_config, models = _synthetic(folder)
    fake = _FakeKakao()
    keys = {name: value for name, value in ce._FAKE_KEYS}
    with _env_values(keys), _replaced(ce, "kakao_walk_compare", fake):
        s = _Screen(c, maps).run()
        s.scenario(syn.id)
        _replay_at(s, syn, 2, datetime.time(8, 0))
        c.true("머리말 배지 '2026-11-02(월) 08:00:00 기록 재생'", "2026-11-02(월) 08:00:00 기록 재생" in s.chips(), s.chips())
        s.set("radio", "selected_id", "Ifbf4ec4c04")
        tab = _Tab(s, "② 탑승별 확률")
        marked = [row for frame in tab.frames() if "표시" in frame.columns for row in _rows(frame, ("표시", "시각 출처")) if row[0]]
        c.true("② 탭: Ifbf4ec4c04 의 안내·기존 앱 차량 시각 출처가 '도착 예측'", bool(marked) and all(source == "도착 예측" for _, source in marked),
               marked)
        data = _Tab(s, "⑦ 데이터·기록")
        c.eq("⑦ 탭: 원천 표 5행, 시연 시간대별 기록 표 3행", (5, 3),
             (len(data.frame("관측 시각")) if data.frame("관측 시각") is not None else None,
              len(data.frame("시간대")) if data.frame("시간대") is not None else None))
        s.set("radio", "selected_id", "If1e99436b8")
        s.click("kakao_button")
        rows = _rows(_Tab(s, "① 경로 비교").frame("카카오 최단"), ("이동", "우리 최단거리", "카카오 기본", "카카오 최단", "차이"))
        c.eq("① 탭: If1e99436b8 카카오 비교 결과 한 줄", [("이동 1: 출발지 → 도착지", "1.60 km", "352 m · 4분 50초", "300 m · 4분 00초", "81.2%")],
             rows)
        c.eq("가짜 카카오 함수 1회", 1, fake.calls)


def _ui25(c: _Checker, folder: Path, maps: _MapCalls) -> None:
    golden = ce.golden_scenario()
    config = EngineConfig()
    out = ce.run_engine(golden, ce.golden_query(), config)
    kakao_key = config.env_kakao_key
    fake = _FakeKakao()
    columns = ("이동", "우리 최단거리", "카카오 기본", "카카오 최단", "차이")
    with _env_values({kakao_key: dict(ce._FAKE_KEYS)[kakao_key]}), _replaced(ce, "kakao_walk_compare", fake):
        s = _Screen(c, maps).run().scenario(ce.GOLDEN_ID)
        before_files = _folder_files(folder)
        compare = _Tab(s, "① 경로 비교")
        # ①
        s.set("radio", "selected_id", "If1e99436b8")
        c.eq("① 버튼 활성", False, s.at.button(key="kakao_button").disabled)
        s.click("kakao_button")
        results = s.state("kakao_results", {})
        c.true("① kakao_results 에 (시나리오 키, 'If1e99436b8')", (ce.GOLDEN_ID, "If1e99436b8") in results, list(results))
        c.eq("① kakao_calls 2", 2, s.state("kakao_calls"))
        c.eq("① 결과 한 줄", [("이동 1: 출발지 → 도착지", "1.60 km", "352 m · 4분 50초", "300 m · 4분 00초", "81.2%")],
             _rows(compare.frame("카카오 최단"), columns))
        c.eq("① 주의 상자", ["우리 보행망과 카카오 최단 거리가 15% 넘게 다릅니다. 보행망을 확인하세요"],
             [_plain(value) for value in compare.htmls("mr-callout warn")])
        # ②
        layers = list(maps.calls[-1]["layers"]) if maps.calls else []
        c.true("② 지도에 '카카오 도보 경로(비교)' 레이어", "카카오 도보 경로(비교)" in layers, layers)
        result = results.get((ce.GOLDEN_ID, "If1e99436b8"))
        direct = feature_groups(build_map(golden, out, "If1e99436b8", kakao=result)) if result else {}
        c.true("② build_map(..., kakao=그 결과) 에 그 레이어", "카카오 도보 경로(비교)" in direct, list(direct))
        captions = s.main_texts("caption")
        c.true("② 바닥글과 지도 범례 아래 글씨에 '· 경로 비교: 카카오'",
               any(text.startswith(_FOOTER) and "· 경로 비교: 카카오" in text for text in captions)
               and any(text.startswith("지도 타일") and "· 경로 비교: 카카오" in text for text in captions), captions)
        # ③
        s.run("다시 실행")
        c.eq("③ 다시 실행하면 버튼 대신 결과, 가짜 함수는 다시 불리지 않는다", (False, 1, 1),
             (s.has("button", "kakao_button"), len(_rows(compare.frame("카카오 최단"))), fake.calls))
        # ④ 따릉이
        s.set("radio", "selected_id", "Ic5c1b22780")
        s.click("kakao_button")
        c.eq("④ kakao_calls 6", 6, s.state("kakao_calls"))
        c.eq("④ 결과 두 줄", [("이동 1 ①: 출발지 → 대여소1", "50 m", "500.0%"), ("이동 1 ⑤: 대여소2 → 도착지", "70 m", "328.6%")],
             _rows(compare.frame("카카오 최단"), ("이동", "우리 최단거리", "차이")))
        # ⑨ (세션 상태) 카카오 결과가 있는 키는 kakao_results 뿐
        holders = sorted(key for key, value in s.at.session_state.items() if "127.0034" in repr(value))
        c.eq("⑨ 카카오 결과가 있는 세션 키", ["kakao_results"], holders)
        leaks = sorted({text for text in s.strings() if dict(ce._FAKE_KEYS)[kakao_key] in text})
        c.eq("⑨ 화면 글자에 가짜 키 없음", [], leaks)
        # ⑦ 키를 지우면
        calls = fake.calls
        os.environ.pop(kakao_key, None)
        s.set("radio", "selected_id", "Idddde0a626")
        button = s.at.button(key="kakao_button") if s.has("button", "kakao_button") else None
        c.eq("⑦ 키를 지우면 버튼 비활성", True, None if button is None else button.disabled)
        c.true("⑦ '비교 불가(키 없음)'", "비교 불가(키 없음)" in compare.values("Caption"), compare.values("Caption"))
        c.eq("⑦ 가짜 함수가 불리지 않는다", calls, fake.calls)
        os.environ[kakao_key] = dict(ce._FAKE_KEYS)[kakao_key]
        # ⑧ 시나리오를 바꾸면
        s.scenario("A")
        c.eq("⑧ 시나리오를 바꾸면 kakao_results 가 {}", {}, s.state("kakao_results"))
        layers = list(maps.calls[-1]["layers"]) if maps.calls else []
        c.true("⑧ 지도에 카카오 레이어가 없다", "카카오 도보 경로(비교)" not in layers, layers)
        c.true("⑧ 바닥글의 '· 경로 비교: 카카오' 는 남는다",
               any(text.startswith(_FOOTER) and "· 경로 비교: 카카오" in text for text in s.main_texts("caption")), s.main_texts("caption"))
        c.eq("⑨ 데이터 폴더의 파일 목록과 크기", before_files, _folder_files(folder))
        # ⑤ 새 세션, kakao_calls 48
        limit = _Screen(c, maps).run().scenario(ce.GOLDEN_ID)
        limit.put("kakao_calls", 48)
        limit.set("radio", "selected_id", "Idddde0a626")
        c.eq("⑤ 48회: 4회 필요한 Idddde0a626 은 비활성", True, limit.at.button(key="kakao_button").disabled)
        c.true("⑤ 한도 안내", "이 세션의 비교 한도(호출 50회)를 다 썼습니다" in _Tab(limit, "① 경로 비교").values("Caption"),
               _Tab(limit, "① 경로 비교").values("Caption"))
        limit.set("radio", "selected_id", "If1e99436b8")
        c.eq("⑤ 48회: 2회 필요한 If1e99436b8 은 활성", False, limit.at.button(key="kakao_button").disabled)
        # ⑥ 429, 늘 500
        for mode, text, added in (("429", "비교 불가(무료 한도 초과 또는 결제 수단 없음)", 1), ("500", "비교 불가(오류)", 3)):
            fake.mode = mode
            failed = _Screen(c, maps).run().scenario(ce.GOLDEN_ID)
            kpi, options = failed.kpi(), failed.options("radio", "selected_id")
            failed.set("radio", "selected_id", "If1e99436b8")
            failed.click("kakao_button")
            c.true(f"⑥ {mode}: '{text}'", text in _Tab(failed, "① 경로 비교").values("Caption"), _Tab(failed, "① 경로 비교").values("Caption"))
            c.eq(f"⑥ {mode}: kakao_calls {added} 증가", added, failed.state("kakao_calls"))
            c.eq(f"⑥ {mode}: 순위와 KPI 는 그대로", (kpi, options), (failed.kpi(), failed.options("radio", "selected_id")))
        fake.mode = "ok"
        c.eq("⑨ 데이터 폴더의 파일 목록과 크기 (끝)", before_files, _folder_files(folder))
# --- UI-28 ---


def _save_bundle(folder: Path) -> Scenario:
    """UI-28 의 시나리오 BUNDLE: §9.5.3 의 묶음 세계에 제목 "묶음 세계", 장소 S "출발지" 와 D "도착지", 기본 질의 S → D 를 붙여
    데이터 폴더의 `scenarios/BUNDLE.json` 에 저장한다. 기준 시각과 나머지 값은 §9.5 의 작은 시나리오 규칙 그대로다."""
    data = ce._bundle_world().model_dump()
    data.update(
        id="BUNDLE",
        title="묶음 세계",
        places=({"name": "출발지", "node_id": "S"}, {"name": "도착지", "node_id": "D"}),
        default_query=Query(origin=OriginState(kind=OriginKind.AT_NODE, node_id="S"), destination_node_id="D").model_dump(),
    )
    scenario = Scenario.model_validate(data)
    ce.save_scenario_json(scenario, folder / "scenarios" / "BUNDLE.json")
    return scenario


def _ui28(c: _Checker, folder: Path, maps: _MapCalls) -> None:
    bundle = _save_bundle(folder)
    config = EngineConfig()
    out = ce.run_engine(bundle, bundle.default_query, config)
    s = _Screen(c, maps).run()
    c.true("시나리오 선택지 '묶음 세계 (생성)'", "묶음 세계 (생성)" in s.options("selectbox", "scenario_id"), s.options("selectbox", "scenario_id"))
    s.scenario("BUNDLE")
    # ① 여정 목록
    c.eq("① 여정 목록", ["**1위** 가상7·가상8번"], s.options("radio", "selected_id"))
    # ② 여정 안내
    ride_line = ("가상7·가상8번 가운데 가상8번 1번째 차 · 정류장P 08:05:30 → 정류장Q 08:09:00 · 탈 확률 95.2% · 1분 30초 기다림\n"
                 "가상7·가상8번 가운데 하차 정류장에 먼저 닿는 차를 탑니다.")
    it = _items_of(out).get(out.best_id) if out.best_id else None
    lines = guide_lines(it, out, bundle, config) if it is not None else ()
    c.true("② 여정 안내의 탑승 줄과 둘째 줄", ride_line in lines, lines)
    steps = s.html_text("mr-steps")
    c.eq("② 화면의 여정 안내에 두 줄", [], [line for line in ride_line.split("\n") if line not in steps])
    # ③ ② 탭 머리글, 차량 표, 표 아래 문장
    tab = _Tab(s, "② 탑승별 확률")
    heads = [_plain(value) for value in tab.htmls("mr-bhead")]
    c.true("③ 머리글과 배지", len(heads) == 1 and heads[0].startswith("탑승 1: 가상7·가상8번 · 정류장P 승차 → 정류장Q 하차")
           and "기존 앱과 같은 차" in heads[0], heads)
    frame = tab.frame("표시", 0)
    columns = ("표시", "노선", "몇 번째 차", "차량", "출발 시각", "하차 시각", "시각 출처", "만차", "막차", "탈 확률")
    c.eq("③ 차량 표의 열", list(columns), list(frame.columns) if frame is not None else None)
    c.eq("③ 차량 표 2행", [("★◆", "가상8번", "1번째 차", "차량 y1", "08:05:30", "08:09:00", "도착 예측", "아니오", "아니오", 0.95221),
                         ("", "가상7번", "2번째 차", "차량 x2", "08:08:20", "08:13:20", "도착 예측", "아니오", "아니오", 0.999977)],
         _rows(frame, columns))
    note = "가상7·가상8번 가운데 하차 정류장에 먼저 닿는 차를 보입니다. 먼저 와도 더 늦게 닿는 차는 표에서 뺍니다."
    c.true("③ 표 아래 묶음 문장", note in tab.values("Caption"), tab.values("Caption"))
    # ④ 판정 문장
    verdicts = [_paragraphs(value) for value in tab.htmls("mr-verdict")]
    c.eq("④ 판정 문장", [["기존 앱이 안내하는 가상8번 1번째 차를 탈 확률은 95.2%입니다.",
                        "기존 앱 방식으로는 08:04:00에 정류장에 닿아 1분 30초 여유가 있다고 봅니다."]], verdicts)
    # ⑤ 골든의 차량 표에는 노선 열이 없다
    s.scenario(ce.GOLDEN_ID)
    s.set("radio", "selected_id", "Ifbf4ec4c04")
    golden = _Tab(s, "② 탑승별 확률")
    c.eq("⑤ 골든 ② 탭 차량 표의 열 (노선 없음)", [["표시", "몇 번째 차", "차량", "출발 시각", "하차 시각", "시각 출처", "만차", "막차", "탈 확률"]] * 2,
         [list(frame.columns) for frame in golden.frames() if "표시" in frame.columns])


# --- UI-29 (13단계) ---

_GPS_POINTS: Mapping[str, tuple[float, float]] = {
    "G1": (37.5095, 127.06281), "G2": (37.498747, 127.028791), "G3": (37.566295, 126.977945),
    "G4": (37.5, 127.0015), "G5": (37.523975, 127.05494), "G6": (37.523993, 127.05494),
}
_GPS_OTHER = "지금 위치는 다른 시나리오의 지역 안입니다. 아래에서 고르면 그 시나리오로 바꿔 지금 위치에서 출발합니다."
_GPS_TAIL = " 지도에서 출발을 찍거나 장소를 고르세요."
_GPS_ERRORS = {
    "PERMISSION_DENIED": "위치 권한이 없어 지금 위치를 받지 못했습니다. 브라우저의 사이트 설정에서 위치를 허용한 뒤 다시 누르세요.",
    "POSITION_UNAVAILABLE": "기기가 지금 위치를 찾지 못했습니다. 잠시 뒤 다시 누르거나 지도에서 출발을 찍으세요.",
    "TIMEOUT": "15초 안에 위치를 받지 못했습니다. 다시 누르거나 지도에서 출발을 찍으세요.",
    "UNSUPPORTED": "이 브라우저는 위치 기능을 지원하지 않습니다. 지도에서 출발을 찍으세요.",
    "INSECURE": "브라우저는 https 주소나 이 컴퓨터의 localhost 주소에서만 위치를 줍니다. 지금 주소에서는 지도에서 출발을 찍으세요.",
}


def _gps_fix(name: str, accuracy: float = 12.0) -> dict[str, float]:
    lat, lon = _GPS_POINTS[name]
    return {"lat": lat, "lon": lon, "accuracy": accuracy}


def _gps_snap(scenario: Scenario, name: str) -> tuple[str, float]:
    """기대값: 엔진의 `snap_point` 를 거리 한도 없이 불러 붙는 노드의 이름과 거리(§9.9.1)."""
    lat, lon = _GPS_POINTS[name]
    unlimited = EngineConfig().model_copy(update={"snap_max_m": 1e12})
    joined, distance = ce.snap_point(scenario, lat, lon, ce.ORIGIN_POINT_ID, unlimited)
    names = {node.id: node.name for node in scenario.nodes}
    names.update({station.id: station.name for station in scenario.bike_stations})
    return names[joined.edges[-1].target], distance


def _gps_outside(scenario: Scenario, label: str, name: str) -> str:
    node, distance = _gps_snap(scenario, name)
    return f"지금 위치는 데이터가 준비된 지역 밖입니다(가장 가까운 곳: {label}, {node}까지 {fmt_dist(distance)}).{_GPS_TAIL}"


def _gps_point_query(scenario: Scenario, name: str) -> Query:
    lat, lon = _GPS_POINTS[name]
    return Query(origin=OriginState(kind=OriginKind.AT_POINT, lat=lat, lon=lon),
                 destination_node_id=scenario.default_query.destination_node_id)


def _folder_names(folder: Path) -> list[str]:
    return sorted(str(path.relative_to(folder)) for path in folder.rglob("*"))


def _ui29(c: _Checker, folder: Path, maps: _MapCalls) -> None:
    hand = ce.build_scenarios()
    a, b, golden = hand["A"], hand["B"], ce.golden_scenario()
    config = EngineConfig()
    listed = [(a.id, a.title, a), (b.id, b.title, b), (golden.id, _GOLDEN_LABEL, golden)]
    g1 = {"lat": 37.5095, "lon": 127.06281, "accuracy_m": 12.0}
    # ① locate_fix 직접 호출
    here = locate_fix(_gps_fix("G1"), a.id, listed, config)
    c.eq("① (G1, A) → HERE", ("HERE", None, "", g1, []), (here["kind"], here["code"], here["text"], here["fix"], here["choices"]))
    for name, current in (("G2", b.id), ("G5", a.id)):
        c.eq(f"① ({name}, {current}) → HERE", "HERE", locate_fix(_gps_fix(name), current, listed, config)["kind"])
    other = locate_fix(_gps_fix("G2"), a.id, listed, config)
    c.eq("① (G2, A) → OTHER, 선택 [B]", ("OTHER", [(b.id, b.title)], _GPS_OTHER), (other["kind"], other["choices"], other["text"]))
    g5b = locate_fix(_gps_fix("G5"), b.id, listed, config)
    c.eq("① (G5, B) → OTHER, 선택 [A]", ("OTHER", [(a.id, a.title)]), (g5b["kind"], g5b["choices"]))
    with_copy = listed + [("A-COPY", f"{a.title} (생성)", a.model_copy(update={"id": "A-COPY"}))]
    c.eq("① 사본을 더하면 (G5, B) 의 선택이 [A, A-COPY]", [a.id, "A-COPY"],
         [scenario_id for scenario_id, _ in locate_fix(_gps_fix("G5"), b.id, with_copy, config)["choices"]])
    g3 = locate_fix(_gps_fix("G3"), a.id, listed, config)
    c.eq("① (G3, A) → OUTSIDE, 가장 가까운 곳 B", ("OUTSIDE", _gps_outside(b, b.title, "G3")), (g3["kind"], g3["text"]))
    g6 = locate_fix(_gps_fix("G6"), a.id, listed, config)
    c.eq("① (G6, A) → OUTSIDE, 가장 가까운 곳 A", ("OUTSIDE", _gps_outside(a, a.title, "G6")), (g6["kind"], g6["text"]))
    prefix = "지금 시나리오는 가상 노선이라 지금 위치를 출발로 쓰지 않습니다. "
    g4 = locate_fix(_gps_fix("G4"), golden.id, listed, config)
    c.eq("① (G4, 골든) → 앞 문장이 붙은 OUTSIDE", ("OUTSIDE", prefix + _gps_outside(b, b.title, "G4")), (g4["kind"], g4["text"]))
    g4a = locate_fix(_gps_fix("G4"), a.id, listed, config)
    c.eq("① (G4, A) → 앞 문장 없는 OUTSIDE", ("OUTSIDE", _gps_outside(b, b.title, "G4")), (g4a["kind"], g4a["text"]))
    lonely = locate_fix(_gps_fix("G3"), golden.id, [(golden.id, _GOLDEN_LABEL, golden)], config)
    c.eq("① 가상 아닌 시나리오가 없으면 괄호 없는 OUTSIDE", ("OUTSIDE", f"지금 위치는 데이터가 준비된 지역 밖입니다.{_GPS_TAIL}"),
         (lonely["kind"], lonely["text"]))
    for code, text in _GPS_ERRORS.items():
        result = locate_fix({"error": code}, a.id, listed, config)
        c.eq(f"① 오류 {code}", ("ERROR", code, text, None, []),
             (result["kind"], result["code"], result["text"], result["fix"], result["choices"]))
    bad_text = "받은 위치 값이 올바르지 않습니다. 다시 누르거나 지도에서 출발을 찍으세요."
    for value in ({"error": "FOO"}, {"error": ["X"]}, None, [37.5, 127.0], {"lat": 91, "lon": 127, "accuracy": 5},
                  {"lat": True, "lon": 127, "accuracy": 5}, {"lat": "37.5", "lon": 127, "accuracy": 5},
                  {"lat": float("nan"), "lon": 127, "accuracy": 5}, {"lat": 37.5, "lon": 127.0},
                  {"lat": 37.5, "lon": 127.0, "accuracy": -1}):
        result = locate_fix(value, a.id, listed, config)
        c.eq(f"① BAD_FIX: {value!r}", ("ERROR", "BAD_FIX", bad_text), (result["kind"], result["code"], result["text"]))
    # ② apply_gps_result 직접 호출과 지도 표지 이름
    state: dict[str, Any] = {"origin_kind": "PLACE", "gps_note": {"kind": "OUTSIDE"}}
    apply_gps_result(state, here)
    c.eq("② HERE → 출발 상태", ("POINT", (37.5095, 127.06281), g1, False),
         (state["origin_kind"], state["origin_point"], state["origin_gps"], "gps_note" in state))
    c.eq("② 지도의 출발 표지 이름", (37.5095, 127.06281, "지금 위치"),
         map_pick_of({**state, "dest_kind": "PLACE"}, a)[1])
    c.eq("② origin_gps 가 없으면 '찍은 출발점'", "찍은 출발점",
         map_pick_of({"origin_kind": "POINT", "origin_point": (37.5095, 127.06281), "dest_kind": "PLACE"}, a)[1][2])
    state = {"origin_kind": "PLACE"}
    apply_gps_result(state, other)
    c.eq("② OTHER → gps_note", ({"kind": "OTHER", "code": None, "text": _GPS_OTHER, "choices": [(b.id, b.title)],
                                  "fix": {"lat": 37.498747, "lon": 127.028791, "accuracy_m": 12.0}}, "PLACE", False),
         (state["gps_note"], state["origin_kind"], "origin_point" in state))
    state = {"origin_kind": "PLACE"}
    apply_gps_result(state, g3)
    c.eq("② OUTSIDE → gps_note 만", ({"kind": "OUTSIDE", "code": None, "text": g3["text"]}, "PLACE"),
         (state["gps_note"], state["origin_kind"]))
    # ③ AppTest: A 에서 G1
    s = _Screen(c, maps).run()
    found = s.at.sidebar.get("bidi_component")
    data = json.loads(found[0].proto.json) if found else {}
    c.eq("③ 사이드바의 위치 단추 요소", (1, GPS_COMPONENT_NAME, True),
         (len(found), found[0].proto.component_name if found else None,
          bool(found) and "지금 위치에서 출발" in found[0].proto.html_content))
    c.eq("③ 위치 단추의 data", {"label": "지금 위치에서 출발", "busy_label": "위치를 찾는 중입니다",
                               "title": "기기 위치는 이 계산에만 쓰고 파일에 남기지 않습니다.", "timeout_ms": 15000,
                               "max_age_ms": 30000}, data)
    files = _folder_names(folder)
    s.put("gps_pending", _gps_fix("G1"))
    node, distance = _gps_snap(a, "G1")
    c.eq("③ G1 → 출발 상태", ("POINT", (37.5095, 127.06281), g1, False),
         (s.state("origin_kind"), tuple(s.state("origin_point")), s.state("origin_gps"), "gps_pending" in s.at.session_state))
    captions = s.side_captions()
    for text in ("지금 위치 37.50950, 127.06281 · 정확도 ±12 m", f"가장 가까운 {node}까지 {fmt_dist(distance)}",
                 "기기 위치는 이 계산에만 쓰고 파일에 남기지 않습니다."):
        c.true(f"③ 사이드바 '{text}'", text in captions, captions)
    c.eq("③ 경고 없음", [], s.side_texts("warning"))
    c.true("③ 머리말", s.description().startswith(f"출발: 지금 위치(가장 가까운 {node}까지 {fmt_dist(distance)})"), s.description())
    c.eq("③ KPI = AT_POINT G1 → A 의 목적지", _kpi_expect(ce.run_engine(a, _gps_point_query(a, "G1"), config)), s.kpi())
    c.eq("③ 데이터 폴더의 파일 목록이 그대로", files, _folder_names(folder))
    s.put("gps_pending", _gps_fix("G1", 350.0))
    c.eq("③ 정확도 350 → 경고", ["위치 정확도가 ±350 m입니다. 실제 위치와 다르면 지도를 눌러 고쳐 찍으세요."], s.side_texts("warning"))
    s.put("origin_point", (37.5096, 127.0628))
    c.eq("③ 지도 누르기 → origin_gps 지움", False, "origin_gps" in s.at.session_state)
    c.true("③ '찍은 점 37.50960, 127.06280'", "찍은 점 37.50960, 127.06280" in s.side_captions(), s.side_captions())
    c.true("③ 머리말 '지도에서 찍은 점'", s.description().startswith("출발: 지도에서 찍은 점("), s.description())
    # ④ AppTest: A 에서 G2 → 바꿔 출발
    s = _Screen(c, maps).run()
    s.put("gps_pending", _gps_fix("G2"))
    switch = f"gps_switch_{b.id}"
    c.true("④ OTHER 안내", _GPS_OTHER in s.side_texts("info"), s.side_texts("info"))
    c.eq("④ 바꿔 출발 단추", f"바꿔 출발: {b.title}", s.at.button(key=switch).label if s.has("button", switch) else None)
    if s.has("button", switch):
        s.click(switch)
    c.eq("④ 바꾼 뒤 상태", (b.id, "POINT", (37.498747, 127.028791), False),
         (s.state("scenario_id"), s.state("origin_kind"), tuple(s.state("origin_point", ())), "gps_note" in s.at.session_state))
    c.eq("④ KPI = B 의 AT_POINT G2 → B 의 목적지", _kpi_expect(ce.run_engine(b, _gps_point_query(b, "G2"), config)), s.kpi())
    # ⑤ AppTest: A 에서 G3, ⑥ 권한 거부
    s = _Screen(c, maps).run()
    kind, kpi = s.state("origin_kind"), s.kpi()
    s.put("gps_pending", _gps_fix("G3"))
    c.eq("⑤ OUTSIDE 안내", [g3["text"]], s.side_texts("warning"))
    c.eq("⑤ 출발 종류와 KPI 그대로", (kind, kpi), (s.state("origin_kind"), s.kpi()))
    s.set("segmented_control", "origin_kind", "POINT")
    c.eq("⑤ 출발 종류를 바꾸면 안내가 사라진다", (False, False), (g3["text"] in s.side_texts("warning"), "gps_note" in s.at.session_state))
    s.put("gps_pending", {"error": "PERMISSION_DENIED"})
    c.true("⑥ 권한 거부 안내", _GPS_ERRORS["PERMISSION_DENIED"] in s.side_texts("warning"), s.side_texts("warning"))
    # ⑦ AppTest: 골든에서 G4
    s = _Screen(c, maps).run().scenario(ce.GOLDEN_ID)
    kind = s.state("origin_kind")
    s.put("gps_pending", _gps_fix("G4"))
    c.eq("⑦ 골든 G4 → 앞 문장이 붙은 OUTSIDE", [g4["text"]], s.side_texts("warning"))
    c.eq("⑦ 출발 그대로", kind, s.state("origin_kind"))


# --- UI-30 (14단계) ---

_SIDE_OF_SHIFT = {shift: side for side, shift in _SIDE_SHIFT.items()}
_SNAP_TEXT = "찍은 점이 길에서 828 m 떨어져 있습니다(최대 150 m). 길 가까이를 다시 찍으세요."


def _simple_badges(fmap: folium.Map) -> list[str]:
    """간단히 보기 지도의 단계 번호 표지(19단계)의 번호, 그린 차례대로."""
    found = []
    for group in feature_groups(fmap).values():
        for marker in _group_markers(group):
            markup = marker.icon.options.get("html", "") if marker.icon is not None else ""
            if "mr-map-badge" in markup:
                found.append(_plain(markup))
    return found


def _simple_labels(fmap: folium.Map) -> list[tuple[str, str]]:
    """간단히 보기 지도의 라벨 (글자, 자리). 자리는 알약의 transform 으로 읽는다."""
    found = []
    for group in feature_groups(fmap).values():
        for marker in _group_markers(group):
            markup = marker.icon.options.get("html", "") if marker.icon is not None else ""
            shift = re.search(r"transform:([^;]+);", markup)
            if shift is not None and shift.group(1) in _SIDE_OF_SHIFT:
                found.append((_plain(markup), _SIDE_OF_SHIFT[shift.group(1)]))
    return found


def _fit_padding(fmap: folium.Map) -> list[tuple[Any, Any]]:
    return [(child.options.get("paddingTopLeft"), child.options.get("paddingBottomRight"))
            for child in fmap._children.values() if type(child).__name__ == "FitBounds"]


def _steps_of(steps: Sequence[GuideStep]) -> list[tuple[str, str, tuple[str, ...]]]:
    return [(step.kind, step.main, step.subs) for step in steps]


def _alts_of(output: EngineOutput, scenario: Scenario) -> list[tuple[str, Grade, str]]:
    return [(row.title, row.grade, row.detail) for row in easy_alternatives(output, scenario)]


def _best_of(output: EngineOutput) -> ItineraryResult:
    return _items_of(output)[output.comparison.best_id]


def _no_banned(c: _Checker, label: str, s: _Screen) -> None:
    strings = s.strings()
    for word in _BANNED_WORDS:
        hits = [text for text in strings if word in text]
        c.true(f"{label}: 화면 글자에 '{word}' 없음", not hits, hits[:2])


def _trip_box(s: _Screen) -> list[tuple[str, str]]:
    """접힘 "출발·목적지 바꾸기"를 담은 블록(출발·도착 상자)의 요소 (종류, 글자)를 차례로. 안쪽 블록은 펼치고 빈 자리와 접힘 안은 뺀다."""
    def holder(node: Any) -> Any:
        children = getattr(node, "children", None)
        if not isinstance(children, dict):
            return None
        for index in sorted(children):
            child = children[index]
            if getattr(child, "type", None) == "expander" and getattr(child, "label", None) == TRIP_EDIT_LABEL:
                return node
            found = holder(child)
            if found is not None:
                return found
        return None

    def flat(node: Any) -> list[tuple[str, str]]:
        rows: list[tuple[str, str]] = []
        for index in sorted(node.children):
            child = node.children[index]
            kind = getattr(child, "type", "")
            if kind == "expander":
                rows.append((kind, child.label))
            elif isinstance(getattr(child, "children", None), dict):
                rows.extend(flat(child))
            elif kind == "toggle":
                rows.append((kind, child.label))
            elif kind != "empty":
                rows.append((kind, child.value if kind in ("caption", "warning") else ""))
        return rows

    box = holder(s.at.main)
    return flat(box) if box is not None else []


def _leave_expect(scenario: Scenario, query: Query, config: EngineConfig) -> str | None:
    """출발 여유의 기대값(19단계): 엔진을 직접 불러 d = 60, 120, …, `LEAVE_SCAN_MAX_S` 초 늦춘 시나리오(`advance_clock`)로 계산한다.
    장소·지점 출발만(차량 안 출발은 None). 문장 규칙은 `check/simple19.py` 가 따로 검산한다."""
    if query.origin.kind not in LEAVE_ORIGIN_KINDS:
        return None
    first = ce.run_engine(scenario, query, config)
    step = int(PARAM_RANGES["depart_offset_s"][2])
    later = ((d, ce.run_engine(ce.advance_clock(scenario, float(d), config), leave_query(query, d), config))
             for d in range(step, min(LEAVE_SCAN_MAX_S, int(config.depart_offset_max_s)) + 1, step))
    return easy_leave(first, later)


def _trip_texts(s: _Screen) -> list[str]:
    return [html.unescape(text) for value in s.htmls("mr-trip") for text in re.findall(r'<span class="mr-tv">(.*?)</span>', value)]


def _ui31(c: _Checker, folder: Path, maps: _MapCalls) -> None:
    """예시 경로 버튼(§6.3, §9.9.6)."""
    hand = ce.build_scenarios()
    a = hand["A"]
    config = EngineConfig()
    name_of = {place.node_id: place.name for place in a.places}

    def at_node(example: Any) -> Query:
        return Query(origin=OriginState(kind=OriginKind.AT_NODE, node_id=example.origin_node_id),
                     destination_node_id=example.destination_node_id)

    e1, e2 = a.examples
    out1, out2 = ce.run_engine(a, at_node(e1), config), ce.run_engine(a, at_node(e2), config)
    # ① ② 간단히 보기, 접힘 안
    s = _Screen(c, maps, view=None).run("간단히 보기 첫 실행 (UI-31)")
    c.eq("⓪ 첫 화면은 첫 예시 경로 E1 (30단계): 시나리오, 출발·목적지 상태", ("A", "PLACE", name_of[e1.origin_node_id], "PLACE",
                                                              name_of[e1.destination_node_id]),
         (s.state("scenario_id"), s.state("origin_kind"), s.state("origin_place"), s.state("dest_kind"), s.state("dest_place")))
    c.eq("⓪ 첫 화면 답 카드 = E1 엔진 결과", [easy_answer_html(out1, a, None, _leave_expect(a, at_node(e1), config))],
         s.htmls("mr-answer"))
    c.eq("⓪ 첫 화면 경로 비교 표 = E1 엔진 결과 (32단계)", compare_htmls(out1, a), s.compare())
    c.eq("⓪ 표의 줄: 공통 앞부분, 뒷부분, 분, 도착, 요금, 추천, 기존 앱 1위, 설명",
         [("지하철 2호선 → ", "지하철 9호선 → 따릉이", "24분", "19:44", "2,550원", True, False, ()),
          ("지하철 2호선 → ", "지하철 9호선 → 143·146·345번", "27분", "19:47", "1,550원", False, True,
           ("기존 길찾기 앱 안내 19:40 도착 → 이 앱 계산 19:47 도착 (7분 늦음)",)),
          ("지하철 2호선 → ", "지하철 9호선", "26분", "19:46", "1,550원", False, False, ())],
         [(r.common, r.tail, r.minutes, r.arrive, r.fare, r.recommended, r.naive, r.notes) for r in compare_rows(out1, a)])
    c.eq("⓪ 주의 카드는 없다(표의 줄로 옮김)", [], s.htmls("mr-caution"))
    first = _Screen(c, maps).run("자세히 보기 첫 실행 (UI-31 ⓪)")
    c.eq("⓪ 자세히 보기로 시작하면 시나리오 기본 질의 그대로", (query_defaults(a)["origin_kind"], query_defaults(a)["dest_place"]),
         (first.state("origin_kind"), first.state("dest_place")))
    s.put("trip_edit", True)
    inside = [item for item in s.at.main.expander if item.label == TRIP_EDIT_LABEL]
    buttons = [(item.key, item.label) for item in inside[0].button if str(item.key).startswith("example_")] if inside else []
    c.eq("① 접힘 안의 예시 버튼 (키, 글자)", [("example_1", e1.name), ("example_2", e2.name)], buttons)
    s.click("example_1")
    c.eq("① E1: 출발·목적지 상태, 접힘은 닫힘 (19단계)", ("PLACE", "선릉역 북쪽 출구", "PLACE", "청담역·경기고교 정류장 근처", False),
         (s.state("origin_kind"), s.state("origin_place"), s.state("dest_kind"), s.state("dest_place"), s.state("trip_edit")))
    c.eq("① E1: 답 카드", [easy_answer_html(out1, a, None, _leave_expect(a, at_node(e1), config))], s.htmls("mr-answer"))
    _no_banned(c, "①", s)
    s.click("example_2")
    c.eq("② E2: 출발·목적지 장소", (name_of[e2.origin_node_id], name_of[e2.destination_node_id]),
         (s.state("origin_place"), s.state("dest_place")))
    c.eq("② E2: 장소 이름", ("청담역·경기고교 정류장", "종합운동장역 북쪽 출구"), (s.state("origin_place"), s.state("dest_place")))
    c.eq("② E2: 경로 비교 표", compare_htmls(out2, a), s.compare())
    c.eq("② E2: 기존 앱 1위 줄의 설명", ("기존 길찾기 앱 안내 19:44 도착 → 이 앱 계산 19:47 도착 (3분 늦음)",
                                   "기존 앱이 타라는 2호선 외선 종합운동장행 열차(19:39 출발)는 놓치기 쉽습니다."),
         next((r.notes for r in compare_rows(out2, a) if r.naive), None))
    naive2 = next((it for it in out2.itineraries if it.itinerary_id == out2.comparison.naive_best_id), None)
    c.eq("② E2: 기존 앱 1위 줄 배지는 놓치기 쉬움, 그 경로의 자체 등급은 그대로(35단계: 설명 줄과 같은 말)",
         (Grade.GHOST, True, True),
         (next((r.grade for r in compare_rows(out2, a) if r.naive), None), naive2 is not None and _ghost_boarding(naive2) is not None,
          "놓치기 쉬움" in _plain(next((h for h in s.compare() if "기존 앱 1위" in h), ""))))
    _no_banned(c, "②", s)
    # ③ 자세히 보기, 사이드바
    s = _Screen(c, maps).run("자세히 보기 첫 실행 (UI-31)")
    side = [item.key for item in s.at.sidebar.button if str(item.key).startswith("example_")]
    c.eq("③ 사이드바의 예시 버튼", ["example_1", "example_2"], side)
    s.set("select_slider", "depart_offset_s", 120)
    shifted = ce.advance_clock(a, 120.0, config)
    s.click("example_2")
    c.eq("③ 출발 늦추기는 그대로", 120, s.state("depart_offset_s"))
    expected = ce.run_engine(shifted, at_node(e2), config)
    c.eq("③ E2: KPI", _kpi_expect(expected), s.kpi())
    c.true("③ E2: 한 줄 설명의 출발·목적지", s.description().startswith(f"출발: {name_of[e2.origin_node_id]} · 기준 시각 ")
           and s.description().endswith(f" · 목적지: {name_of[e2.destination_node_id]}"), s.description())
    _no_banned(c, "③", s)
    # ④ B 와 골든에는 예시 버튼이 없다
    for sid in ("B", ce.GOLDEN_ID):
        s = _Screen(c, maps).run(f"자세히 보기 첫 실행 (UI-31, {sid})").scenario(sid)
        keys = [item.key for item in s.at.button if str(item.key).startswith("example_")]
        c.eq(f"④ {sid}: 예시 버튼 없음", [], keys)


_UI34_EXPECT: dict[str, tuple[str | None, str | None, str | None, str | None, tuple[tuple[str, tuple[str, ...]], ...]]] = {
    'A': ('지금 할 일: 삼성역 2호선 승강장에서 내리기 (19:21 도착), 이어서 삼성역 북쪽 대여소까지 걷기', None, None, '2호선 외선 열차 안 · 다음 역 삼성 19:21 도착',
           (('따릉이 타기: 삼성역 북쪽 대여소 → 경기고교 남쪽 대여소', ('자전거가 없으면 청담역·경기고교 정류장 근처까지 걸어야 합니다(12분 · 923 m).',)),)),
    'A-E1': ('지금 할 일: 선릉역 2호선 승강장까지 걷기, 이어서 2호선 외선 종합운동장행 타기 (19:24 출발)', '19:21까지 나서도 19:44 도착은 같고, 19:22에 나서면 19:45 도착입니다.', None, None,
           (('2호선 외선 종합운동장행 타기', ('이 차는 탈 수 있습니다.', '놓치면 다음 열차(19:27 출발)를 타면 되고, 종합운동장역에서 약 3분 늦게 내립니다.')), ('9호선 상행 삼성중앙행 타기', ('이 차는 탈 수 있습니다.', '놓치면 다음 열차(19:38 출발)를 타면 되고, 봉은사역에서 약 4분 늦게 내립니다.')), ('따릉이 타기: 봉은사역 북쪽 대여소 → 경기고교 남쪽 대여소', ('자전거가 없으면 청담역·경기고교 정류장 근처까지 걸어야 합니다(6분 · 463 m).',)))),
    'A-E2': ('지금 할 일: 경기고교 남쪽 대여소까지 걷기, 이어서 따릉이 타기: 경기고교 남쪽 대여소 → 삼성역 북쪽 대여소', '지금 나서면 19:40 도착, 19:21에 나서면 19:41 도착입니다.', None, None,
           (('따릉이 타기: 경기고교 남쪽 대여소 → 삼성역 북쪽 대여소', ('자전거가 없으면 삼성역까지 걸어야 합니다(16분 · 1.21 km).',)), ('2호선 외선 종합운동장행 타기', ('이 차는 탈 수 있습니다.', '놓치면 다음 열차(19:39 출발)를 타면 되고, 종합운동장역에서 약 3분 늦게 내립니다.')))),
    'A-G1': ('지금 할 일: 삼성역 북쪽 대여소까지 걷기, 이어서 따릉이 타기: 삼성역 북쪽 대여소 → 경기고교 남쪽 대여소', '19:21까지 나서도 19:30 도착은 같고, 19:22에 나서면 143·146·345번으로 19:31 도착입니다.', None, None,
           (('따릉이 타기: 삼성역 북쪽 대여소 → 경기고교 남쪽 대여소', ('자전거가 없으면 청담역·경기고교 정류장 근처까지 걸어야 합니다(13분 · 923 m).',)),)),
    'B': ('지금 할 일: 지하철2호선강남역 정류장까지 걷기, 이어서 140·470번 타기 (23:25 출발)', '지금 나서면 23:33 도착, 23:21에 나서면 따릉이로 23:35 도착입니다.', None, None,
           (('140·470번 타기', ('이 차는 탈 수 있습니다.', '놓치면 470번(23:32 출발)을 타면 되고, 신사역 정류장에서 약 8분 늦게 내립니다.')),)),
    'GOLDEN': ('지금 할 일: 대여소1까지 걷기, 이어서 따릉이 타기: 대여소1 → 대여소2', '지금 나서면 08:11 도착, 08:01에 나서면 08:15 도착입니다.', None, None,
           (('따릉이 타기: 대여소1 → 대여소2', ('자전거가 없으면 도착지까지 걸어야 합니다(22분 · 1.65 km).',)),)),
    'GOLDEN-BUS': ('지금 할 일: 정류장2에서 내리기 (08:06 도착), 이어서 도착지까지 걷기', None, None, None,
           ()),
    'GOLDEN-DL': ('지금 할 일: 대여소1까지 걷기, 이어서 따릉이 타기: 대여소1 → 대여소2', '지금 나서면 08:11 도착, 08:01에 나서면 08:15 도착입니다.', '08:16:40까지 늦을 수 있습니다.', None,
           (('따릉이 타기: 대여소1 → 대여소2', ('자전거가 없으면 도착지까지 걸어야 합니다(22분 · 1.65 km).',)),)),
    'GOLDEN-TRAIN': ('지금 할 일: 역3 승강장에서 내리기 (08:05 도착), 이어서 도착지까지 걷기', None, None, '가상선 하행 열차 안 · 다음 역 역2 08:03 도착',
           ()),
}

_UI34_MAP: dict[str, tuple[list[tuple[str, str]], list[str], tuple[tuple[int, int], tuple[int, int]]]] = {
    'A-E1': ([('출발', 'up'), ('도착', 'up')], ['2 2호선', '4 9호선', '6 따릉이'], ((36, 36), (63, 60))),
    'A-E2': ([('출발', 'up'), ('도착', 'right')], ['2 따릉이', '4 2호선'], ((36, 36), (57, 60))),
    'B': ([('출발', 'left'), ('도착', 'up')], ['2 140·470번'], ((36, 36), (98, 60))),
    'GOLDEN': ([('출발', 'left'), ('도착', 'right')], ['2 따릉이'], ((57, 36), (57, 60))),
    'GOLDEN-DL': ([('출발', 'left'), ('도착', 'right')], ['2 따릉이'], ((57, 36), (57, 60))),
}


def _ui34_cases() -> dict[str, tuple[Scenario, Query, EngineConfig]]:
    """UI-34 ② 의 아홉 경우(§9.9.9, `check/simple19.py` 와 같은 입력)."""
    hand = ce.build_scenarios()
    a, b, golden = hand["A"], hand["B"], ce.golden_scenario()

    def at_node(example: Any) -> Query:
        return Query(origin=OriginState(kind=OriginKind.AT_NODE, node_id=example.origin_node_id),
                     destination_node_id=example.destination_node_id)

    gps = Query(origin=OriginState(kind=OriginKind.AT_POINT, lat=37.5095, lon=127.06281),
                destination_node_id=a.default_query.destination_node_id)
    return {
        "GOLDEN": (golden, ce.golden_query(), EngineConfig()),
        "GOLDEN-TRAIN": (golden, ce.golden_train_query(), EngineConfig()),
        "GOLDEN-BUS": (golden, ce.golden_bus_query(), EngineConfig()),
        "GOLDEN-DL": (golden, ce.golden_query().model_copy(update={"deadline_s": 1000.0}),
                      EngineConfig(rank_criterion=RankCriterion.ON_TIME)),
        "A": (a, a.default_query, EngineConfig()), "A-E1": (a, at_node(a.examples[0]), EngineConfig()),
        "A-E2": (a, at_node(a.examples[1]), EngineConfig()), "A-G1": (a, gps, EngineConfig()),
        "B": (b, b.default_query, EngineConfig()),
    }


def _ui34(c: _Checker, folder: Path, maps: _MapCalls) -> None:
    """길에 선 사람의 세 질문(§6.9 19단계, §9.9.9): 출발 여유, 놓치면 줄, 상자의 마감과 마감 줄, 지금 할 일 잇기, 간단한 출발 표시."""
    a, golden = ce.build_scenarios()["A"], ce.golden_scenario()
    config = EngineConfig()
    # ① 순수 함수
    c.eq("① josa_ro", ["로", "으로", "으로", "로", "로"], [josa_ro(w) for w in ("따릉이", "143·146·345번", "지하철 2호선", "서울", "A")])
    c.eq("① deadline_clock", ("08:16:40", "08:16"), (deadline_clock(28800.0, 1000.0), deadline_clock(28800.0, 960.0)))
    base_q = ce.golden_query()
    c.eq("① leave_query (마감 1,000, 200, 없음 → 300초 늦춤)", (700.0, None, None),
         (leave_query(base_q.model_copy(update={"deadline_s": 1000.0}), 300).deadline_s,
          leave_query(base_q.model_copy(update={"deadline_s": 200.0}), 300).deadline_s, leave_query(base_q, 300).deadline_s))
    gold = ce.run_engine(golden, base_q, config)
    empty = gold.model_copy(update={"ranking": (), "comparison": gold.comparison.model_copy(update={"best_id": None})})
    c.eq("① easy_leave: 늦춘 결과 없음 / 첫 늦춤에 최선 없음", (None, "지금 나서면 08:11 도착, 08:01에 나서면 갈 수 있는 경로가 없습니다."),
         (easy_leave(gold, []), easy_leave(gold, [(60, empty)])))
    # ② 아홉 경우
    for key, (scenario, query, cfg) in _ui34_cases().items():
        out = ce.run_engine(scenario, query, cfg)
        best = _best_of(out)
        rows = easy_answer(out, scenario).rows
        origin = None
        if query.origin.kind == OriginKind.ON_TRAIN:
            origin = _origin_display(_OriginOnly(scenario, query), {"origin_kind": "TRAIN"}, out, None, simple=True)
        backups = tuple((step.main, step.backup) for step in easy_steps(best, out, scenario)
                        if step.kind == "bike" or (step.kind in ("bus", "subway") and step.main.endswith(" 타기")))
        actual = (easy_next(best, out, scenario), _leave_expect(scenario, query, cfg),
                  next((row for row in rows if "까지 늦" in row), None), origin, backups)
        c.eq(f"② {key}: 지금 할 일, 출발 여유, 마감 줄, 출발 표시, 놓치면 줄", _UI34_EXPECT[key], actual)
    # ③ AppTest B 기본
    s = _Screen(c, maps, view=None).run("간단히 보기 첫 실행 (UI-34)").scenario("B")
    answer = s.html_text("mr-answer")
    c.true("③ B: 출발 여유", "지금 나서면 23:33 도착, 23:21에 나서면 따릉이로 23:35 도착입니다." in answer
           and s.htmls("mr-answer")[0].count('class="mr-arow mr-aleave"') == 1, answer)
    steps = " ".join(s.htmls("mr-easy"))
    c.true("③ B: 쉬운 단계의 놓치면 묶음", 'class="mr-backup"' in steps and "놓치면 470번" in _plain(steps), _plain(steps))
    order = [i for i, item in enumerate(s.at.html) if 'class="mr-easy' in item.value or 'class="mr-alts-h' in item.value]
    kinds = ["easy" if 'class="mr-easy' in s.at.html[i].value else "compare" for i in order]
    c.eq("③ B: 경로 비교 표가 쉬운 단계보다 앞(33단계)", ["compare", "easy"], kinds)
    # ④ 마감
    s.set("toggle", "use_deadline", True)
    s.set("time_input", "deadline_time", datetime.time(23, 40, 0))
    c.true("④ B 마감 23:40: 늦는다는 말은 마감 여유 줄에 한 번만(28단계)",
           s.html_text("mr-answer").count("23:40까지 늦을 수 있습니다.") == 1, s.html_text("mr-answer"))
    side_deadline = [item.label for item in s.at.sidebar.toggle if item.key == "use_deadline"]
    c.eq("④ 마감 켜기는 상자 안, 사이드바에는 없음", (True, []), (("toggle", DEADLINE_EASY_LABEL) in _trip_box(s), side_deadline))
    _no_banned(c, "③ ④", s)
    s.set("segmented_control", "view_mode", "DETAIL")
    c.eq("④ 자세히 보기: 사이드바의 마감 켜기", ["도착 마감 시각"], [item.label for item in s.at.sidebar.toggle if item.key == "use_deadline"])
    # ⑤ 출발 여유가 없는 때
    s = _Screen(c, maps, view=None, scenario="A").run("간단히 보기, 시나리오 기본 질의 (UI-34 ⑤)")
    c.eq("⑤ A 기본(차량 안 출발): 출발 여유 없음", 0, s.htmls("mr-answer")[0].count("mr-aleave") if s.htmls("mr-answer") else None)
    s.scenario("B").click("alt_pick_3")  # 32단계: 1번 줄은 지금 보는 추천, 2번 줄은 걸러진 기존 앱 1위라 단추가 없다
    picked = s.htmls("mr-answer")
    c.eq("⑤ B 고른 경로: 출발 여유 없음 (mr-aleave 수, 머리)", (0, True),
         (picked[0].count("mr-aleave") if picked else None, bool(picked) and "<span>고른 경로</span>" in picked[0]))
    _no_banned(c, "⑤", s)
    # ⑥ 라벨 맞춤
    e1 = a.examples[0]
    out = ce.run_engine(a, Query(origin=OriginState(kind=OriginKind.AT_NODE, node_id=e1.origin_node_id),
                                 destination_node_id=e1.destination_node_id), config)
    fmap = build_simple_map(a, out, out.comparison.best_id)
    fits = [child for child in fmap._children.values() if isinstance(child, LabelFit)]
    c.eq("⑥ E1 간단한 지도: 라벨 맞춤 하나 (간격, 아래)", [(6.0, 24.0)], [(child.gap, child.foot) for child in fits])
    rows = fits[0].extents if fits else []
    c.true("⑥ 라벨마다 (위도, 경도, 왼쪽, 오른쪽, 위, 아래) 이고 하나는 출발 라벨의 label_extents",
           len(rows) >= 4 and all(len(row) == 6 for row in rows) and any(row[2:] == label_extents("출발", side) for row in rows
                                                                          for side in ("up", "down", "left", "right")), rows)
    c.true("⑥ 지도 HTML 에 라벨 맞춤 스크립트 (가장 큰 확대 단계 17)", "fitLabels" in fmap.get_root().render() and fits and fits[0].zmax == 17.0, "")
    c.eq("⑥ 번호 표지 줄의 (왼쪽, 오른쪽, 위, 아래): 원 반지름 11, 오른쪽은 11 + 노선 알약 - 3 (2호선 51, 9호선 51, 따릉이 56; 33단계)",
         [(11.0, 59.0, 11.0, 11.0), (11.0, 59.0, 11.0, 11.0), (11.0, 64.0, 11.0, 11.0)], [row[2:] for row in rows if row[4:] == (11.0, 11.0)])
    cases = _ui34_cases()
    for key, expected in _UI34_MAP.items():
        scenario, query, cfg = cases[key]
        result = ce.run_engine(scenario, query, cfg)
        smap = build_simple_map(scenario, result, result.comparison.best_id)
        c.eq(f"⑥ {key}: 간단한 지도의 (알약과 자리, 번호 표지, 맞춤 여백) = check/simple19.txt", expected,
             (_simple_labels(smap), _simple_badges(smap), _fit_padding(smap)[0]))


def _ui35(c: _Checker, folder: Path, maps: _MapCalls) -> None:
    """정류장 이름과 번호(§6.9 20단계, §9.9.10). 리터럴은 `check/simple14.txt`, `simple17.txt`, `simple19.txt` 의 값이다."""
    scenarios = ce.build_scenarios()
    a, b, golden = scenarios["A"], scenarios["B"], ce.golden_scenario()
    config = EngineConfig()
    # ① 순수 함수
    names_b, names_a, names_g = easy_names(b), easy_names(a), easy_names(golden)
    c.eq("① easy_names: B 정류장 둘, B 승강장, A 정류장, 골든 정류장",
         ("지하철2호선강남역 정류장", "신사역 정류장", "강남역 2호선 승강장", "청담역·경기고교 정류장", "정류장1"),
         (names_b["ST22012"], names_b["ST22016"], names_b["G_P2"], names_a["ST23188"], names_g["B1"]))
    c.eq("① easy_names 는 정류장이 아닌 이름을 node_names 그대로 둔다",
         True, all(names_b[key] == value for key, value in node_names(b).items()
                   if not any(node.id == key and node.node_type == NodeType.BUS_STOP for node in b.nodes)))
    c.eq("① stop_number: B 22012, 승강장, 골든 정류장, 없음", ("22012", None, None, None),
         (stop_number("ST22012", b), stop_number("G_P2", b), stop_number("B1", golden), stop_number(None, b)))
    # ② B 기본의 쉬운 단계 (check/simple14.txt)
    out = ce.run_engine(b, b.default_query, config)
    best = _best_of(out)
    steps = easy_steps(best, out, b)
    c.eq("② B 쉬운 단계 1, 2",
         [("walk", "지하철2호선강남역 정류장까지 걷기", ("4분 · 225 m · 신호 1개",)),
          ("bus", "140·470번 타기", ("140번 · 지하철2호선강남역 정류장 23:25 출발 → 신사역 정류장 23:31 하차", "정류장 번호 22012",
                                     "140·470번 가운데 신사역 정류장에 먼저 닿는 차를 타면 됩니다."))],
         [(step.kind, step.main, step.subs) for step in steps[:2]])
    # ③ 자세히 보기의 여정 안내는 노드 이름 그대로
    guide = " ".join(" ".join((step.main, *step.subs)) for step in guide_steps(best, out, b, config))
    c.true("③ 자세히 보기 여정 안내에는 붙인 이름이 없다", "지하철2호선강남역" in guide and "지하철2호선강남역 정류장" not in guide, guide)
    # ④ 아홉 경우에 "정류장 정류장" 이 없다
    doubled = []
    for key, (scenario, query, cfg) in _ui34_cases().items():
        result = ce.run_engine(scenario, query, cfg)
        texts = [easy_answer_html(result, scenario), easy_steps_html(_best_of(result), result, scenario),
                 *(row.title + row.detail for row in easy_alternatives(result, scenario))]
        if any("정류장 정류장" in text for text in texts):
            doubled.append(key)
    c.eq("④ 아홉 경우의 답 카드, 단계, 다른 경로에 \"정류장 정류장\" 없음", [], doubled)
    # ⑤ AppTest B
    s = _Screen(c, maps, view=None).run("간단히 보기 첫 실행 (UI-35)").scenario("B")
    steps_text = _plain(" ".join(s.htmls("mr-easy")))
    c.true("⑤ B 화면: 답 카드 제목(노드 이름 그대로)과 단계의 정류장 번호",
           "140·470번 · 지하철2호선강남역 승차" in s.html_text("mr-answer") and "정류장 번호 22012" in steps_text, steps_text)
    _no_banned(c, "⑤", s)


def _ui36(c: _Checker, folder: Path, maps: _MapCalls) -> None:
    """내 걸음 빠르기(§6.9 22단계, §9.9.11): 간단히 보기는 걷는 속도를 답 카드 아래 본문에 그린다."""
    b = ce.build_scenarios()["B"]

    def walk_widgets(block: Any) -> list[tuple[str, str]]:
        return [(getattr(item, "key", ""), getattr(item, "label", "")) for item in block.get("button_group")
                if getattr(item, "key", "") == "walk_preset"]

    s = _Screen(c, maps, view=None).run("간단히 보기 첫 실행 (UI-36)").scenario("B")
    c.eq("① 간단히 보기: 본문에 걷는 속도, 사이드바에는 없음", ([("walk_preset", WALK_EASY_LABEL)], []),
         (walk_widgets(s.at.main), walk_widgets(s.at.sidebar)))
    c.eq("① 선택지", [*WALK_SPEED_PRESETS, WALK_CUSTOM], s.options("segmented_control", "walk_preset"))
    s.set("segmented_control", "walk_preset", "느리게")
    slow = ce.run_engine(b, b.default_query, EngineConfig(v_walk_mps=WALK_SPEED_PRESETS["느리게"]))
    want = easy_answer(slow, b)
    answer = s.html_text("mr-answer")
    c.true("② 느리게: 답 카드의 걸리는 시간·시각과 90% 줄이 느린 걸음의 결과",
           want is not None and want.span in answer and want.rows[0] in answer and f">{want.minutes}<" in s.htmls("mr-answer")[0],
           (answer, want))
    s.set("segmented_control", "walk_preset", "직접")
    c.eq("③ 직접: 본문에 속도 막대", True, s.has("slider", "v_walk"))
    s.set("segmented_control", "walk_preset", "보통")
    _no_banned(c, "① ~ ③", s)
    s.set("segmented_control", "view_mode", "DETAIL")
    c.eq("④ 자세히 보기: 사이드바에 걷는 속도", [("walk_preset", "걷는 속도")], walk_widgets(s.at.sidebar))


_UI37_EXPECT = {  # check/simple23.txt
    'A-E1-DL-1950': '19:50까지 늦지 않으려면 늦어도 19:24에는 나서세요.',
    'B-DL-2333': '지금 나서도 23:33까지 늦을 수 있습니다.',
    'B-DL-2336': '추천 경로로는 23:36까지 늦을 수 있습니다. 따릉이로 가면 늦지 않습니다.',
    'B-DL-2340': '추천 경로로는 23:40까지 늦을 수 있습니다. 따릉이로 가면 늦지 않습니다.',
    'GOLDEN-DL': '지금 나서도 08:16:40까지 늦을 수 있습니다.',
}


def _ui37_cases() -> dict[str, tuple[Scenario, Query, EngineConfig]]:
    """UI-37 의 다섯 경우(§9.9.12, `check/simple23.py` 와 같은 입력). 골든은 마감 확률 기준, 나머지는 평균 도착 기준(간단히 보기의 기본)."""
    scenarios = ce.build_scenarios()
    a, b = scenarios["A"], scenarios["B"]
    e1 = a.examples[0]
    e1_query = Query(origin=OriginState(kind=OriginKind.AT_NODE, node_id=e1.origin_node_id), destination_node_id=e1.destination_node_id)
    on, mean = EngineConfig(rank_criterion=RankCriterion.ON_TIME), EngineConfig()
    return {"GOLDEN-DL": (ce.golden_scenario(), ce.golden_query().model_copy(update={"deadline_s": 1000.0}), on),
            "B-DL-2340": (b, b.default_query.model_copy(update={"deadline_s": 1200.0}), mean),
            "B-DL-2336": (b, b.default_query.model_copy(update={"deadline_s": 960.0}), mean),
            "B-DL-2333": (b, b.default_query.model_copy(update={"deadline_s": 780.0}), mean),
            "A-E1-DL-1950": (a, e1_query.model_copy(update={"deadline_s": 1800.0}), mean)}


def _deadline_leave_expect(scenario: Scenario, query: Query, config: EngineConfig) -> str | None:
    first = ce.run_engine(scenario, query, config)
    step = int(PARAM_RANGES["depart_offset_s"][2])
    later = ((d, ce.run_engine(ce.advance_clock(scenario, float(d), config), leave_query(query, d), config))
             for d in range(step, min(LEAVE_SCAN_MAX_S, int(config.depart_offset_max_s)) + 1, step))
    return easy_deadline_leave(first, later, scenario)


def _ui37(c: _Checker, folder: Path, maps: _MapCalls) -> None:
    """약속 시각이 있으면(§6.9 23단계, §9.9.12): 마감 여유 문장."""
    golden = ce.golden_scenario()
    gold = ce.run_engine(golden, ce.golden_query(), EngineConfig())
    c.eq("① 마감 없음 → None, 늦춘 결과 없음 → None", (None, None),
         (easy_deadline_leave(gold, []), easy_deadline_leave(ce.run_engine(
             golden, ce.golden_query().model_copy(update={"deadline_s": 2000.0}), EngineConfig()), [])))
    for key, (scenario, query, cfg) in _ui37_cases().items():
        c.eq(f"② {key}: 마감 여유 = check/simple23.txt", _UI37_EXPECT[key], _deadline_leave_expect(scenario, query, cfg))
    s = _Screen(c, maps, view=None).run("간단히 보기 첫 실행 (UI-37)").scenario("B")
    s.set("toggle", "use_deadline", True)
    c.eq("③ 마감을 켜도 순위 기준은 평균 도착", RankCriterion.MEAN_ARRIVAL.value, s.state("rank_criterion"))
    s.set("time_input", "deadline_time", datetime.time(23, 40, 0))
    answer = s.html_text("mr-answer")
    c.true("③ B 23:40: 답 카드에 마감 여유, 출발 여유 문장은 없음",
           _UI37_EXPECT["B-DL-2340"] in answer and "도착은 같" not in answer, answer)
    s.set("toggle", "use_deadline", False)
    c.true("④ 마감을 끄면 출발 여유가 돌아옴", "지금 나서면 23:33 도착" in s.html_text("mr-answer"), s.html_text("mr-answer"))
    _no_banned(c, "③ ④", s)

_UI41_EXPECT = [  # check/simple27.txt (§9.9.16)
    ('walk 0', 'safe', '계획대로 가세요.', '140번(23:25 출발)은 탈 수 있습니다. 23:33 도착 예상입니다.', '140:111014009', False),
    ('walk 60', 'ghost', '140번(23:25 출발)은 이제 타기 어렵습니다.', '따릉이로 바꾸면 23:35 도착합니다(지금 경로는 23:41).', '470:111047023', True),
    ('walk 120', 'warn', '더 빠른 길이 생겼습니다.', '따릉이로 바꾸면 23:37 도착합니다(지금 경로는 23:41).', '470:111047023', True),
    ('walk 180', 'warn', '이번 계산에서 지금 경로를 찾지 못했습니다.', '따릉이로 바꾸면 23:38 도착합니다.', '470:111047023', True),
    ('walk 300', 'safe', '계획대로 가세요.', '470번(23:32 출발)은 탈 수 있습니다. 23:41 도착 예상입니다.', '470:111047023', False),
    ('ride 0', 'safe', '계획대로 가세요.', '지금 경로로 가면 23:32 도착 예상입니다.', None, False),
    ('ride 300', 'safe', '계획대로 가세요.', '지금 경로로 가면 23:32 도착 예상입니다.', None, False),
]


def _ui41_cards() -> list[tuple[str, str, str, str, str | None, bool]]:
    """UI-41 ① (§9.9.16, `check/simple27.py` 와 같은 입력): B 기본의 걷는 중 0·60·120·180·300 초, 140번 차 안 0·300 초."""
    config = EngineConfig()
    b = ce.build_scenarios()["B"]
    query = b.default_query
    start = ce.run_engine(b, query, config)
    best = _items(start)[start.comparison.best_id]
    guide: dict[str, Any] = {"plan": guide_plan(best), "k": 0, "on": False, "bike": _bike_used(best), "kept": None}
    first = _next_ride(best)
    guide["kept"] = _boardings(best)[first].guided_trip_id if first is not None else None
    rows = []
    for dt in (0, 60, 120, 180, 300):
        scenario = ce.advance_clock(b, float(dt), config) if dt else b
        status = guide_status(ce.run_engine(scenario, query, config), scenario, guide)
        guide["kept"] = status.kept
        rows.append((f"walk {dt}", status.tone, status.head, " / ".join(status.lines), status.kept, status.switch_id is not None))
    trip_id = best.rides[0].plan_trip_id
    line = next(item for item in b.bus_lines if trip_id.startswith(f"{item.id}:"))
    board = next((item.board_index for item in best.rides[0].bundle if item.route_id == line.id), best.rides[0].board_index)
    guide.update({"on": True, "kept": None})
    for dt in (0, 300):
        scenario = ce.advance_clock(b, float(dt), config) if dt else b
        index = vehicle_next_index(scenario, TravelMode.BUS, line.id, trip_id, board + 1, config)
        q = Query(origin=OriginState(kind=OriginKind.ON_BUS, line_id=line.id, trip_id=trip_id, next_index=index),
                  destination_node_id=query.destination_node_id)
        status = guide_status(ce.run_engine(scenario, q, config), scenario, guide)
        guide["kept"] = status.kept
        rows.append((f"ride {dt}", status.tone, status.head, " / ".join(status.lines), status.kept, status.switch_id is not None))
    return rows


def _guide_head(s: "_Screen") -> str:
    found = [_plain(value) for value in s.htmls("mr-guide")]
    return found[0] if found else ""


def _ui41(c: _Checker, folder: Path, maps: _MapCalls) -> None:
    """안내 모드(§6.10 27단계, §9.9.16)."""
    got = _ui41_cards()
    for want, row in zip(_UI41_EXPECT, got):
        c.eq(f"① {want[0]}: 안내 카드 = check/simple27.txt", want, row)
    c.eq("① 경우 수", len(_UI41_EXPECT), len(got))
    state: dict[str, Any] = {"guide": {"t0": 1000.0, "last_tick": 1000.0, "skip": 0, "elapsed": 0, "mode": DataMode.LIVE.value},
                             "live_refresh": 3}
    c.eq("② 59 초: 그대로", (False, 0, 3), (guide_tick(state, 1059.0), state["guide"]["elapsed"], state["live_refresh"]))
    c.eq("② 60 초: 지난 시간 60, 실시간 조회 번호 + 1", (True, 60, 4),
         (guide_tick(state, 1060.0), state["guide"]["elapsed"], state["live_refresh"]))
    replay = {"at0": 5000, "elapsed": 120}
    c.eq("② guide_clock: 기록 재생, 시뮬레이션, 실시간, 안내 없음",
         [(5120, 0), (7, 0), (7, 0), (7, 300)],
         [guide_clock(replay, DataMode.REPLAY.value, 7, 300), guide_clock(replay, DataMode.SIMULATION.value, 7, 300),
          guide_clock(replay, DataMode.LIVE.value, 7, 300), guide_clock(None, DataMode.REPLAY.value, 7, 300)])
    s = _Screen(c, maps, view=None).run("간단히 보기 첫 실행 (UI-41)").scenario("B")
    c.true("③ 답 카드 아래 안내 시작 단추", s.has("button", "guide_start"), [b.key for b in s.at.button])
    s.set("select_slider", "depart_offset_s", 300)
    c.true("③ 출발 늦추기 300: 단추 대신 안내 문장", not s.has("button", "guide_start") and GUIDE_DT_BLOCK in s.main_texts("caption"),
           s.main_texts("caption"))
    s.set("select_slider", "depart_offset_s", 0)
    s.click("guide_start")
    head = _guide_head(s)
    c.true("④ 시작: 머리 '계획대로 가세요.'", head.startswith("계획대로 가세요."), head)
    c.eq("④ 단추: 탔어요, 1분 지난 것으로 보기, 끝내기", (True, True, True),
         (s.has("button", "guide_board"), s.has("button", "guide_skip"), s.has("button", "guide_stop")))
    c.true("④ 다른 경로 목록 없음", not s.has("button", "alt_pick_1"), [b.key for b in s.at.button])
    s.click("guide_skip")
    head = _guide_head(s)
    c.true("④ 1분 지난 것으로 보기: ① 의 60 초 머리와 바꾸기 단추", head.startswith(_UI41_EXPECT[1][2]) and s.has("button", "guide_switch"), head)
    _no_banned(c, "④", s)
    s.click("guide_stop")
    s.click("guide_start")
    s.click("guide_board")
    vehicle = s.state("guide")["vehicle"]
    c.eq("⑤ 탔어요: 출발 BUS, 노선과 차량", ("BUS", vehicle[1], vehicle[2]),
         (s.state("origin_kind"), s.state("bus_line"), s.state("bus_vehicle")))
    c.true("⑤ 차 안 문장과 내렸어요 단추", GUIDE_ON_VEHICLE_TEXT in _guide_head(s) and s.has("button", "guide_alight")
           and s.at.button(key="guide_alight").label == "신사역 정류장에서 내렸어요", _guide_head(s))
    _no_banned(c, "⑤", s)
    s.click("guide_alight")
    c.eq("⑤ 내렸어요: 출발 POINT", "POINT", s.state("origin_kind"))
    s.click("guide_stop")
    c.true("⑥ 끝내기: 안내 상태 없음, 시작 단추 다시", "guide" not in s.at.session_state and s.has("button", "guide_start"),
           [b.key for b in s.at.button])
    s.click("guide_start")
    s.click("view_detail")
    c.true("⑥ 자세히 보기로 바꾸면 안내 상태 없음", "guide" not in s.at.session_state, "")
    _no_banned(c, "⑥", s)


_UI42_EXPECT = [  # check/simple28.txt (§9.9.17): (초, 여정, 탑승, 안내 차량, 빠른 걸음 판정, 놓치면 줄 ①)
    (0, 'Ic89b1218f8', 1, '140:111014009', True, '이 차는 탈 수 있습니다.'),
    (0, 'I9f0b076ffe', 1, '2340', True, '이 차는 탈 수 있습니다.'),
    (0, 'I9f0b076ffe', 2, '3170', True, '이 차는 탈 수 있습니다.'),
    (0, 'Ibbcf8eb931', 1, '470:111047023', False, '이 차는 탈 수 있습니다.'),
    (15, 'Ic89b1218f8', 1, '140:111014009', True, '이 차는 탈 수 있습니다.'),
    (15, 'I15a8a5dafb', 1, '470:111047023', True, '이 차는 탈 수 있습니다.'),
    (15, 'I9f0b076ffe', 1, '2340', True, '이 차는 빠른 걸음이면 탈 수 있습니다.'),
    (15, 'I9f0b076ffe', 2, '3170', True, '이 차는 탈 수 있습니다.'),
    (25, 'Ic89b1218f8', 1, '140:111014009', True, '이 차는 빠른 걸음이면 탈 수 있습니다.'),
    (25, 'I15a8a5dafb', 1, '470:111047023', True, '이 차는 탈 수 있습니다.'),
    (25, 'I9f0b076ffe', 1, '2342', True, '이 차는 탈 수 있습니다.'),
    (25, 'I9f0b076ffe', 2, '3172', True, '이 차는 탈 수 있습니다.'),
    (30, 'Ic89b1218f8', 1, '140:111014009', True, '이 차는 빠른 걸음이면 탈 수 있습니다.'),
    (30, 'I15a8a5dafb', 1, '470:111047023', True, '이 차는 탈 수 있습니다.'),
    (30, 'I9f0b076ffe', 1, '2342', True, '이 차는 탈 수 있습니다.'),
    (30, 'I9f0b076ffe', 2, '3172', True, '이 차는 탈 수 있습니다.'),
    (40, 'Ic89b1218f8', 1, '140:111014009', True, '이 차는 빠른 걸음이면 탈 수 있습니다.'),
    (40, 'I15a8a5dafb', 1, '470:111047023', True, '이 차는 탈 수 있습니다.'),
    (40, 'I9f0b076ffe', 1, '2342', False, '이 차는 탈 수 있습니다.'),
    (40, 'I9f0b076ffe', 2, '3172', True, '이 차는 탈 수 있습니다.'),
]
_UI42_BANNED = ("%", "확률", "열 번 중")


def _ui42_rows() -> list[tuple[int, str, int, str, bool, str]]:
    """UI-42 ② (§9.9.16, `check/simple28.py` 와 같은 입력): B 기본의 시계를 옮긴 결과마다 순위 여정의 탑승별 판정과 놓치면 줄 ①."""
    config = EngineConfig()
    fast = fast_config(config)
    b = ce.build_scenarios()["B"]
    rows = []
    for dt in (0, 15, 25, 30, 40):
        scenario = ce.advance_clock(b, float(dt), config) if dt else b
        output = ce.run_engine(scenario, b.default_query, config)
        fast_output = ce.run_engine(scenario, b.default_query, fast) if fast is not None else None
        items = _items(output)
        for rid in output.ranking:
            it = items[rid]
            flags = fast_map(it, output, fast_output)
            backups = {step.main: step.backup for step in easy_steps(it, output, scenario, flags) if step.kind in ("bus", "subway")}
            for boarding in it.boardings:
                if _vehicle(boarding, boarding.guided_trip_id) is None:
                    continue
                ride = it.rides[boarding.ride_index - 1]
                line = backups.get(f"{ride_name(ride)} 타기", ("",))[0]
                rows.append((dt, rid, boarding.ride_index, boarding.guided_trip_id, flags[boarding.ride_index], line))
    return rows


def _main_strings(s: "_Screen") -> list[str]:
    """본문(사이드바 밖)의 글자. 지도 컴포넌트의 그림 자료는 뺀다."""
    found: list[str] = []

    def walk(node: Any) -> None:
        if getattr(node, "type", None) in ("custom_component", "iframe", "components_v2"):
            return
        proto = getattr(node, "proto", None)
        if proto is not None and hasattr(proto, "ListFields"):
            found.extend(text for text in _proto_strings(proto)  # CSS 와 위젯의 숫자 형식("%.1f")은 보이는 글자가 아니다
                         if not ("{" in text and "}" in text and ";" in text) and not re.fullmatch(r"%[0-9.]*[dfs]", text))
        children = getattr(node, "children", None)
        if isinstance(children, dict):
            for child in children.values():
                walk(child)

    walk(s.at.main)
    return found


def _ui42(c: _Checker, folder: Path, maps: _MapCalls) -> None:
    """확률 대신 결정(§6.9 결정 문장 28단계, §6.10, §9.9.17)."""
    c.eq("① catch_text", ["탈 수 있습니다", "빠른 걸음이면 탈 수 있습니다", "놓칠 수 있습니다", "탈 수 있습니다"],
         [catch_text(0.75, 0.75), catch_text(0.7499, 0.75, True), catch_text(0.7499, 0.75), catch_text(1.0, 0.75, True)])
    base = EngineConfig()
    got = fast_config(base)
    c.eq("① fast_config: 보통 → 1.5, 빠르게·직접 1.6 → None", (1.5, None, None),
         (None if got is None else got.v_walk_mps, fast_config(base.model_copy(update={"v_walk_mps": 1.5})),
          fast_config(base.model_copy(update={"v_walk_mps": 1.6}))))
    rows = _ui42_rows()
    for want, row in zip(_UI42_EXPECT, rows):
        c.eq(f"② {want[0]}초 {want[1]} 탑승 {want[2]} = check/simple28.txt", want, row)
    c.eq("② 줄 수", len(_UI42_EXPECT), len(rows))
    b = ce.build_scenarios()["B"]
    answer = easy_answer(ce.run_engine(b, b.default_query, base), b)
    c.eq("③ B 기본 답 카드: 줄과 사실 줄", (("늦어도 23:41에는 도착합니다.",), "1,500원 · 걷기 310 m"),
         (answer.rows, answer.facts) if answer else None)
    for sid in ("A", "B"):
        s = _Screen(c, maps, view=None).run(f"간단히 보기 첫 실행 (UI-42 {sid})").scenario(sid)
        strings = _main_strings(s)
        for word in _UI42_BANNED:
            hits = [text for text in strings if word in text]
            c.true(f"④ {sid} 간단히 보기 본문에 '{word}' 없음", not hits, hits[:3])
        if sid == "B":
            s.click("guide_start")
            strings = _main_strings(s)
            for word in _UI42_BANNED:
                hits = [text for text in strings if word in text]
                c.true(f"④ B 안내 중 본문에 '{word}' 없음", not hits, hits[:3])
            s.click("guide_stop")
            s.set("segmented_control", "walk_preset", "빠르게")
            c.eq("⑤ 걷기 '빠르게': 빠른 걸음 결과를 계산하지 않음", None, fast_config(EngineConfig(v_walk_mps=1.5)))
        _no_banned(c, f"④ {sid}", s)


def _ui43(c: _Checker, folder: Path, maps: _MapCalls) -> None:
    """소개 페이지와 실제 기록 장면(§6.11, §6.12 34단계, §9.9.17): 합성 기록(§9.7.4)으로 소개의 장면 단추를 그리고 눌러 본다."""
    truth, syn, config, models = _synthetic(folder)
    intro_keys = lambda screen: [b.key for b in screen.at.button if str(b.key or "").startswith("intro_")]
    s = _Screen(c, maps, view=None, page=None).run("첫 실행, 장면 파일 없음 (UI-43)")
    c.eq("① 첫 화면은 소개: 길찾기 시작 단추 둘, 장면 단추 없음, 출발·도착 상자와 답 카드 없음, 상태 intro",
         (["intro_start", "intro_start2"], False, [], PAGE_INTRO),
         (intro_keys(s), s.has("button", "to_intro") or bool(s.htmls("mr-answer")), [k for k in intro_keys(s) if "scene" in k],
          s.state(PAGE_KEY)))
    page_text = " ".join(s.strings())
    c.true("① 소개 글: 제목, 대표 장면 세 줄(16:23 안내, 16:41 실제, 16:28 추천), 숫자 셋, 기능 넷, 계산 네 단계",
           all(t in page_text for t in (APP_TITLE, "16:23 도착", "16:41 도착 · 18분 늦음", "16:28 도착 · 13분 빠름", "46~57%",
                                         "최대 21분", "94%", "59번 중 안내보다 2분 넘게", "기존 앱 1위와 나란히 비교", "확률 계산")), page_text[:400])
    _no_banned(c, "①", s)
    scenes = {"scenes": [{"at": "2026-11-02 08:00:00", "name": "시험 장면", "scenario": syn.id},
                         {"at": "2026-11-02 08:20:00", "name": "없는 시나리오", "scenario": "NOPE"},
                         {"at": "2026-12-01 08:00:00", "name": "기록 없는 날", "scenario": syn.id},
                         {"name": "시각 없는 항목", "scenario": syn.id}]}
    (folder / DEMO_SCENES_FILE).write_text(json.dumps(scenes, ensure_ascii=False), encoding="utf-8")
    loaded = load_scenes(folder)
    c.eq("② load_scenes: 형식이 틀린 항목은 건너뜀, 글자", ["11/2(월) 08:00 시험 장면", "11/2(월) 08:20 없는 시나리오",
                                                     "12/1(화) 08:00 기록 없는 날"], [scene.label for scene in loaded])
    (folder / "broken").mkdir()
    (folder / "broken" / DEMO_SCENES_FILE).write_text("{ 깨진", encoding="utf-8")
    c.eq("② 깨진 파일은 빈 튜플", (), load_scenes(folder / "broken"))
    s = _Screen(c, maps, view=None, page=None).run("첫 실행, 장면 파일 있음 (UI-43)")
    shown = [(b.key, b.label) for b in s.at.button if str(b.key or "").startswith("intro_scene_")]
    c.eq("③ 소개의 장면 단추: 시나리오가 있고 기록 날짜 안인 것만", [("intro_scene_0", "11/2(월) 08:00 시험 장면")], shown)
    c.true("③ 머리와 안내", INTRO_SCENES_HEAD in " ".join(s.strings()) and INTRO_SCENES_NOTE in " ".join(s.strings()))
    want_state = (syn.id, "REPLAY", datetime.date(2026, 11, 2), datetime.time(8, 0), 0)
    got_state = lambda: (s.state("scenario_id"), s.state("data_mode"), s.state("replay_date"), s.state("replay_time"),
                         s.state("depart_offset_s"))
    c.eq("④ 장면을 누르기 전: 첫 시나리오(A), 시뮬레이션", ("A", "SIMULATION"), (s.state("scenario_id"), s.state("data_mode")))
    if shown:
        s.click("intro_scene_0")
    c.eq("④ 장면을 누르면: 길찾기 화면, 시나리오, 기록 재생, 날짜와 시각, 출발 늦추기 0", (PAGE_APP, want_state),
         (s.state(PAGE_KEY), got_state()))
    c.true("④ 배지 '2026-11-02(월) 08:00:00 기록 재생'", "2026-11-02(월) 08:00:00 기록 재생" in s.chips(), s.chips())
    scenario, sources = _replayed(truth, syn, config, models, _kst_unix(2026, 11, 2, 8, 0))
    want = easy_answer(ce.run_engine(scenario, syn.default_query, config, sources), scenario)
    answer = s.html_text("mr-answer")
    c.true("④ 답 카드 = 그 시각 기록 재생의 엔진 결과(제목, 시각)", want is not None and want.title in answer and want.span in answer,
           (answer, want))
    c.true("④ 길찾기 화면에는 장면 단추가 없음(34단계)", not intro_keys(s) and not s.has("button_group", "scene_pick"),
           [b.key for b in s.at.button])
    _no_banned(c, "④", s)
    s.click("to_intro")
    c.eq("⑤ 소개 단추: 소개로, 고른 장면 상태는 그대로", (PAGE_INTRO, want_state, True), (s.state(PAGE_KEY), got_state(),
                                                                         s.has("button", "intro_start")))
    s.click("intro_start")
    c.eq("⑤ 길찾기 시작: 길찾기 화면, 장면 상태 그대로, 답 카드", (PAGE_APP, want_state, True),
         (s.state(PAGE_KEY), got_state(), bool(s.htmls("mr-answer"))))
    if s.has("button", "guide_start"):
        s.click("guide_start")
        s.put(PAGE_KEY, PAGE_INTRO)
        c.eq("⑥ 안내 중에는 소개로 가지 않음(상태가 소개여도 길찾기, 소개 단추 없음)", (PAGE_APP, False),
             (s.state(PAGE_KEY), s.has("button", "intro_start")))
        s.click("guide_stop")
    else:
        c.true("⑥ 안내 시작 단추가 있어야 함", False, [b.key for b in s.at.button])
    q = _Screen(c, maps, view=None, page=None)
    q.at.query_params["page"] = "app"
    q.run("주소 ?page=app (UI-43)")
    c.eq("⑦ 주소에 page=app 이면 소개를 건너뜀", (PAGE_APP, False, True),
         (q.state(PAGE_KEY), q.has("button", "intro_start"), q.has("button", "to_intro")))
    d = _Screen(c, maps, view="DETAIL", page=None).run("자세히 보기 첫 실행 (UI-43)")
    c.eq("⑧ 자세히 보기는 소개 없이 길찾기", (PAGE_APP, False), (d.state(PAGE_KEY), d.has("button", "intro_start")))


def _ui38(c: _Checker, folder: Path, maps: _MapCalls) -> None:
    """타는 것(§6.9 24단계, §9.9.13): 간단히 보기는 수단 켜기를 내 걸음 빠르기 아래 본문에 그린다."""
    a = ce.build_scenarios()["A"]
    keys = ["use_bus", "use_subway", "use_bike"]

    def toggles(block: Any) -> list[str]:
        return [getattr(item, "key", "") for item in block.get("toggle") if getattr(item, "key", "") in keys]

    s = _Screen(c, maps, view=None, scenario="A").run("간단히 보기, 시나리오 기본 질의 (UI-38)")
    c.eq("① 간단히 보기: 본문에 버스·지하철·따릉이, 사이드바에는 없음", (keys, []), (toggles(s.at.main), toggles(s.at.sidebar)))
    c.eq("① 이름표", MODES_EASY_LABEL, s.html_text("mr-ctl-label"))
    c.true("① A 기본의 추천은 따릉이를 씀", "따릉이" in s.html_text("mr-answer"), s.html_text("mr-answer"))
    s.set("toggle", "use_bike", False)
    no_bike = ce.run_engine(a, a.default_query, EngineConfig(modes_enabled=(TravelMode.BUS, TravelMode.SUBWAY)))
    want = easy_answer(no_bike, a)
    answer = s.html_text("mr-answer")
    c.true("② 따릉이를 끄면 답 카드가 따릉이 없는 엔진 결과(제목·시각·90% 줄)이고 따릉이가 없음",
           want is not None and want.title in answer and want.span in answer and want.rows[0] in answer
           and "따릉이" not in answer, (answer, want))
    s.set("toggle", "use_bus", False).set("toggle", "use_subway", False)
    captions = [item.value for item in s.at.main.caption]
    c.true("③ 모두 끄면 본문에 걷기만 안내", WALK_ONLY_TEXT in captions, captions)
    for key in keys:
        s.set("toggle", key, True)
    _no_banned(c, "① ~ ③", s)
    s.set("segmented_control", "view_mode", "DETAIL")
    c.eq("④ 자세히 보기: 사이드바에 수단 켜기", (keys, []), (toggles(s.at.sidebar), toggles(s.at.main)))

def _ui39(c: _Checker, folder: Path, maps: _MapCalls) -> None:
    """꺼진 토글의 테두리(§7.5 25단계, §9.9.14): 테두리 색과 바탕의 대비가 두 테마에서 3:1 이상."""
    def lum(hex_color: str) -> float:
        def ch(v: int) -> float:
            x = v / 255
            return x / 12.92 if x <= 0.03928 else ((x + 0.055) / 1.055) ** 2.4
        r, g, b = (int(hex_color[i:i + 2], 16) for i in (1, 3, 5))
        return 0.2126 * ch(r) + 0.7152 * ch(g) + 0.0722 * ch(b)

    def ratio(a: str, b: str) -> float:
        hi, lo = sorted((lum(a), lum(b)), reverse=True)
        return (hi + 0.05) / (lo + 0.05)

    rule = ('[data-testid="stCheckbox"] label:has(input[role="switch"]:not(:checked)) > span + div '
            '{ box-shadow: inset 0 0 0 1.5px var(--mr-muted); }')
    for name, tokens in (("밝은", TOKENS_LIGHT), ("어두운", TOKENS_DARK)):
        c.true(f"① {name}: page_css 에 꺼진 토글 테두리 규칙", rule in page_css(tokens), name)
        c.true(f"② {name}: muted 와 바탕(bg)의 대비 ≥ 3", ratio(tokens["muted"], tokens["bg"]) >= 3.0,
               round(ratio(tokens["muted"], tokens["bg"]), 2))

def _ui40(c: _Checker, folder: Path, maps: _MapCalls) -> None:
    """출발 늦추기의 글자(§6.3 26단계, §9.9.15): 초 대신 나설 시각과 몇 분 뒤."""
    b = ce.build_scenarios()["B"]
    c.eq("① depart_label: 0, 60, 300, 1800 (B 23:20)", ["지금", "23:21 (1분 뒤)", "23:25 (5분 뒤)", "23:50 (30분 뒤)"],
         [depart_label(b.clock_s, d) for d in (0, 60, 300, 1800)])
    s = _Screen(c, maps, view=None).run("간단히 보기 첫 실행 (UI-40)").scenario("B")
    w = s.at.select_slider(key="depart_offset_s")
    c.eq("② 선택지는 0 ~ 1,800 초를 60 초 간격(31개), 처음 값은 지금", (31, "지금"),
         (len(w.options), w.format_func(w.value) if callable(getattr(w, "format_func", None)) else w.options[0]))
    s.set("select_slider", "depart_offset_s", 300)
    c.eq("③ 300 을 고르면 상태 300, 아래 글씨 5분 뒤 출발", (300, True),
         (s.state("depart_offset_s"), any("5분 뒤 출발" in text for text in s.side_captions())))
    c.true("③ 화면 글자에 초 단위 막대 글자가 없음", "300초" not in " ".join(w.options), w.options[:3])


class _OriginOnly:
    """`_origin_display` 가 읽는 `Prepared` 의 칸(display, base, query)만 가진 값(UI-34)."""

    def __init__(self, scenario: Scenario, query: Query) -> None:
        self.display = self.base = scenario
        self.query = query


def _ui33(c: _Checker, folder: Path, maps: _MapCalls) -> None:
    """지도와 지금 할 일 줄의 화면 결함 고침(§6.9, §7.5, §7.6 18단계, §9.9.8)."""
    hand = ce.build_scenarios()
    a, b = hand["A"], hand["B"]
    config = EngineConfig()
    e1 = a.examples[0]
    out = ce.run_engine(a, Query(origin=OriginState(kind=OriginKind.AT_NODE, node_id=e1.origin_node_id),
                                 destination_node_id=e1.destination_node_id), config)
    fmap = build_simple_map(a, out, out.comparison.best_id)
    clamps = [child for child in fmap._children.values() if isinstance(child, FitClamp)]
    fits = _fit_padding(fmap)
    c.eq("① E1 간단한 지도: 맞춤 여백과 줄이기 요소 (여백, 줄이기의 여백, 기준 길이)",
         ([((36, 36), (63, 60))], [("[36.0, 36.0]", "[63.0, 60.0]", 200.0)]),
         (fits, [(clamp.top_left, clamp.bottom_right, clamp.span) for clamp in clamps]))
    html = fmap.get_root().render()
    c.true("① E1 간단한 지도: 축척은 미터만, Leaflet 머리글 없음", SCALE_METRIC_CSS in html and "attributionControl.setPrefix(false)" in html, "")
    detail = build_map(a, out, out.comparison.best_id).get_root().render()
    c.true("② 자세히 보기 지도: 축척은 미터만", SCALE_METRIC_CSS in detail, "")
    exp_b = ce.run_engine(b, b.default_query, config)
    c.true("③ 지금 할 일의 괄호는 한 덩어리",
           '<span class="mr-nb">(23:25 출발)</span>' in easy_answer_html(exp_b, b), easy_answer_html(exp_b, b))
    c.eq("③ _nowrap_parens", 'a <span class="mr-nb">(1)</span> b <span class="mr-nb">(2 x)</span>', _nowrap_parens("a (1) b (2 x)"))


def _ui32(c: _Checker, folder: Path, maps: _MapCalls) -> None:
    """간단히 보기 고침(§6.9 17단계, §9.9.7): 보는 경로와 다른 경로 고르기, 지금 할 일, 같은 이름, 기존 1위 덧말, 사이드바 접힘."""
    hand = ce.build_scenarios()
    a, b, golden = hand["A"], hand["B"], ce.golden_scenario()
    config = EngineConfig()
    # ① 순수 함수
    gold = ce.run_engine(golden, ce.golden_query(), config)
    c.eq("① 골든: 지금 할 일", "지금 할 일: 대여소1까지 걷기, 이어서 따릉이 타기: 대여소1 → 대여소2",
         easy_next(_best_of(gold), gold, golden))
    c.eq("① 골든: 덧말 (셋째 줄만)", ["", "", "기존 길찾기 방식이 타라는 차는 놓치기 쉬워, 이 앱은 탈 수 있는 차로 다시 계산했습니다."],
         [row.note for row in easy_alternatives(gold, golden)])
    train = ce.run_engine(golden, ce.golden_train_query(), config)
    c.eq("① 골든 열차 질의: 지금 할 일", "지금 할 일: 역3 승강장에서 내리기 (08:05 도착), 이어서 도착지까지 걷기",
         easy_next(_best_of(train), train, golden))
    second = gold.ranking[1]
    picked = easy_answer(gold, golden, second)
    c.eq("① 골든: 둘째 순위를 고른 답 카드 (머리, 제목, 마지막 줄)", ("고른 경로", "지하철 가상선", "추천 경로보다 평균 약 6분 늦게 도착합니다."),
         (picked.head, picked.title, picked.rows[-1]) if picked else None)
    c.eq("① 골든: 둘째를 고른 다른 경로 (제목, 앱 추천)", [("따릉이", True), ("가상1번", False), ("가상1번 → 가상2번", False)],
         [(row.title, row.recommended) for row in easy_alternatives(gold, golden, second)])
    # ② AppTest B 기본(간단히 보기)
    exp_b = ce.run_engine(b, b.default_query, config)
    best_b = exp_b.comparison.best_id
    s = _Screen(c, maps, view=None).run("간단히 보기 첫 실행 (UI-32)").scenario("B")
    leave_b = _leave_expect(b, b.default_query, config)
    c.eq("② B: 답 카드", [easy_answer_html(exp_b, b, None, leave_b)], s.htmls("mr-answer"))
    c.true("② B: 지금 할 일과 같은 이름 구분",
           "지금 할 일: 지하철2호선강남역 정류장까지 걷기, 이어서 140·470번 타기 (23:25 출발)" in s.html_text("mr-answer")
           and "140·470번 · 지하철2호선강남역 승차" in s.html_text("mr-answer"), s.html_text("mr-answer"))
    rows_b = compare_rows(exp_b, b)
    c.eq("② B: 경로 비교 표", compare_htmls(exp_b, b), s.compare())
    c.eq("② B: 표의 줄 (이름, 분, 도착, 요금, 추천, 기존 앱 1위, 단추)",
         [("140·470번 · 지하철2호선강남역 승차", "13분", "23:33", "1,500원", True, False, True),
          ("360번 → 140번", "34분", "23:54", "0원 (막차 놓쳐 걷기)", False, True, False),
          ("따릉이", "14분", "23:34", "1,000원", False, False, True),
          ("지하철 2호선 → 지하철 3호선", "19분", "23:39", "1,550원", False, False, True),
          ("140·470번 · 신분당선강남역 승차", "21분", "23:41", "1,500원", False, False, True)],
         [(r.common + r.tail, r.minutes, r.arrive, r.fare, r.recommended, r.naive, r.pickable) for r in rows_b])
    c.eq("② B: 기존 앱 1위(걸러짐) 줄의 설명", ("기존 길찾기 앱 안내 23:30 도착 → 이 앱 계산 23:54 도착 (24분 늦음)",
                                         "기존 앱이 타라는 360번 막차(23:22 출발)는 놓치기 쉽습니다."), rows_b[1].notes)
    c.eq("② B: 줄 단추 (보는 줄과 걸러진 줄에는 없음)", [(f"alt_pick_{n}", ALT_PICK_LABEL) for n in (3, 4, 5)],
         [(item.key, item.label) for item in s.at.main.button if str(item.key).startswith("alt_pick_")])
    c.eq("② B: 돌아가기 단추 없음", False, s.has("button", "pick_best"))
    side_more = [item for item in s.at.sidebar.expander if item.label == SIDE_MORE_LABEL]
    inside = {str(getattr(item, "key", "")) for item in side_more[0].selectbox} | {str(item.key) for item in side_more[0].button} if side_more else set()
    c.eq("② 사이드바 접힘과 그 안의 순위 기준·되돌리기", (1, True, True), (len(side_more), "rank_criterion" in inside, "reset_button" in inside))
    # ③ 따릉이를 고른다
    bike = rows_b[2].itinerary_id
    s.click("alt_pick_3")
    c.eq("③ 고른 여정", bike, s.state("selected_id"))
    c.eq("③ 답 카드", [easy_answer_html(exp_b, b, bike)], s.htmls("mr-answer"))
    picked = easy_answer(exp_b, b, bike)
    c.eq("③ 머리와 비교 줄", ("고른 경로", "추천 경로보다 평균 약 1분 늦게 도착합니다."), (picked.head, picked.rows[-1]) if picked else None)
    c.eq("③ 경로 비교 표 (따릉이 줄이 보는 중)", compare_htmls(exp_b, b, bike), s.compare())
    c.eq("③ 쉬운 단계", [easy_steps_html(_items(exp_b)[bike], exp_b, b)], s.htmls("mr-easy"))
    rows_pick = compare_rows(exp_b, b, bike)
    c.eq("③ 표 첫 줄은 앱 추천, 셋째 줄(따릉이)이 보는 중", (best_b, True, True), (rows_pick[0].itinerary_id, rows_pick[0].recommended,
                                                                      rows_pick[2].shown))
    c.eq("③ 줄 단추 글자", [BACK_TO_BEST_LABEL, ALT_PICK_LABEL, ALT_PICK_LABEL],
         [item.label for item in s.at.main.button if str(item.key).startswith("alt_pick_")])
    c.eq("③ 답 카드 아래 돌아가기 단추", BACK_TO_BEST_LABEL, s.at.button(key="pick_best").label if s.has("button", "pick_best") else None)
    # ④ 자세히 보기로 가도 같은 여정, 돌아와도 같은 여정
    s.click("view_detail")
    c.eq("④ 자세히 보기의 고른 여정", ("DETAIL", bike), (s.state("view_mode"), s.at.radio(key="selected_id").value))
    c.eq("④ 자세히 보기 사이드바에는 접힘 없음", [], [item.label for item in s.at.sidebar.expander if item.label == SIDE_MORE_LABEL])
    s.set("segmented_control", "view_mode", "SIMPLE")
    c.eq("④ 간단히 보기로 돌아와도 고른 경로", [easy_answer_html(exp_b, b, bike)], s.htmls("mr-answer"))
    # ⑤ 추천 경로로 돌아가기
    s.click("pick_best")
    c.eq("⑤ 돌아가기", (best_b, [easy_answer_html(exp_b, b, None, leave_b)], False),
         (s.state("selected_id"), s.htmls("mr-answer"), s.has("button", "pick_best")))
    _no_banned(c, "②~⑤", s)
    # ⑥ B 를 1분 늦추면 같은 이름 둘과 기존 1위 덧말
    shifted = ce.advance_clock(b, 60.0, config)
    exp_60 = ce.run_engine(shifted, b.default_query, config)
    s = _Screen(c, maps, view=None).run("간단히 보기 첫 실행 (⑥)").scenario("B")
    s.set("select_slider", "depart_offset_s", 60)
    rows_60 = compare_rows(exp_60, shifted)
    c.eq("⑥ 경로 비교 표", compare_htmls(exp_60, shifted), s.compare())
    c.eq("⑥ 이름과 설명", [("따릉이", ()), ("140·470번 · 지하철2호선강남역 승차", ("기존 길찾기 앱 안내 23:32 도착 → 이 앱 계산 23:41 도착 (9분 늦음)",
                                                                   "기존 앱이 타라는 140번(23:25 출발)은 놓치기 쉽습니다.")),
                        ("140·470번 · 신분당선강남역 승차", ()), ("지하철 2호선 → 지하철 3호선", ()), ("도보", ())],
         [(row.common + row.tail, row.notes) for row in rows_60])
    # ⑦ A 기본: 지금 할 일과 기존 1위 덧말
    exp_a = ce.run_engine(a, a.default_query, config)
    s = _Screen(c, maps, view=None, scenario="A").run("간단히 보기, 시나리오 기본 질의 (⑦)")
    c.eq("⑦ A 답 카드", [easy_answer_html(exp_a, a)], s.htmls("mr-answer"))
    c.true("⑦ A 지금 할 일", "지금 할 일: 삼성역 2호선 승강장에서 내리기 (19:21 도착)" in s.html_text("mr-answer"), s.html_text("mr-answer"))
    c.eq("⑦ A 기존 앱 1위 줄의 설명", ("기존 길찾기 앱 안내 19:29 도착 → 이 앱 계산 19:34 도착 (5분 늦음)",
                                 "기존 앱이 타라는 146번(19:24 출발)은 놓치기 쉽습니다."),
         next((r.notes for r in compare_rows(exp_a, a) if r.naive), None))
    _no_banned(c, "⑦", s)


def _ui30(c: _Checker, folder: Path, maps: _MapCalls) -> None:
    hand = ce.build_scenarios()
    a, b, golden = hand["A"], hand["B"], ce.golden_scenario()
    config = EngineConfig()
    # ① 순수 함수
    for seconds, expected in ((0, (0, 0, 0)), (29.999, (0, 0, 1)), (30, (1, 0, 1)), (89.9, (1, 1, 2)), (90, (2, 1, 2)),
                              (3599.6, (60, 59, 60)), (-30, (0, -1, 0)), (-30.01, (-1, -1, 0))):
        c.eq(f"① minute_of({seconds}) (nearest, floor, ceil)", expected,
             tuple(minute_of(seconds, rounding) for rounding in ("nearest", "floor", "ceil")))
    for args, expected in (((28800, 673.8259), "08:11"), ((28800, 1301.0603, "ceil"), "08:22"), ((28800, 420, "floor"), "08:07"),
                           ((84000, 2399), "00:00 (다음 날)"), ((86340, 59.9, "floor"), "23:59"), ((86340, 30), "00:00 (다음 날)"),
                           ((28800, 29.99), "08:00")):
        c.eq(f"① fmt_hm{args}", expected, fmt_hm(*args))
    for n, expected in ((0, "1분 미만"), (1, "1분"), (59, "59분"), (60, "1시간"), (61, "1시간 1분"), (125, "2시간 5분")):
        c.eq(f"① fmt_minutes({n})", expected, fmt_minutes(n))
    for p, expected in ((0.0, "거의 매번"), (0.012551, "거의 매번"), (0.0539, "열 번 중 아홉 번은"), (0.0875, "열 번 중 아홉 번은"),
                        (0.35, "열 번 중 일곱 번은"), (0.5, "열 번 중 다섯 번은"), (0.94, "열 번 중 한 번은"), (0.951, "드물게"),
                        (1.0, "드물게")):
        c.eq(f"① miss_text({p})", f"{expected} 놓칩니다", miss_text(p, "놓칩니다"))
    for word, expected in (("146번", "은"), ("360번 막차", "는"), ("지하철 2호선 열차", "는"), ("", "는"), ("A", "는")):
        c.eq(f"① josa({word!r})", expected, josa(word, "은", "는"))
    for text, expected in (("출발", (44, 22)), ("따릉이 대여", (87, 22)), ("140·470번 승차", (117, 22))):
        c.eq(f"① pill_size({text!r})", expected, pill_size(text))
    c.eq("① label_sides 네 점", ["up", "up", "right", "up"],
         label_sides([(37.5, 127.0), (37.5009, 127.0), (37.5, 127.0011), (37.5, 127.0)]))
    c.eq("① label_sides 한 점", ["up"], label_sides([(37.5, 127.0)]))
    c.eq("① map_padding 세 라벨", ((107, 36), (36, 60)),
         map_padding([(37.5, 127.0), (37.51, 127.01)], [((37.5, 127.0), "출발", "down"), ((37.51, 127.01), "도착", "up"),
                                                         ((37.505, 127.0), "가상1번 승차", "left")]))
    c.eq("① map_padding 한 점", ((36, 36), (36, 60)), map_padding([(37.5, 127.0)], [((37.5, 127.0), "출발", "up")]))
    # ② 골든 기본
    out = ce.run_engine(golden, ce.golden_query(), config)
    c.eq("② 답 카드", EasyAnswer("추천 경로", "따릉이", Grade.SAFE, "11분", "08:00 → 08:11 도착",
                                ("늦어도 08:22에는 도착합니다.",), "1,000원 · 걷기 120 m"),
         easy_answer(out))
    c.eq("② 주의 카드", EasyCaution("warn", "기존 길찾기 방식의 1위: 가상1번 → 가상2번", (
        "08:11 도착이라고 안내합니다.", "하지만 타라는 가상2번(08:07 출발)은 놓치기 쉽습니다.",
        "이 앱이 계산한 평균 도착은 08:22이고, 추천 경로보다 약 11분 늦습니다.")), easy_caution(out, golden))
    c.eq("② 쉬운 단계", [("walk", "대여소1까지 걷기", ("1분 · 50 m",)),
                       ("bike", "따릉이 타기: 대여소1 → 대여소2", ("8분 · 1.64 km · 빌리고 반납하는 시간 포함", "자전거를 빌릴 수 있습니다")),
                       ("walk", "도착지까지 걷기", ("1분 · 70 m",)), ("arrive", "도착지 도착", ("평균 08:11 도착",))],
         _steps_of(easy_steps(_best_of(out), out, golden)))
    c.eq("② 다른 경로", [("지하철 가상선", Grade.SAFE, "17분 · 08:17 도착 · 1,550원 · 역1 승강장에서 승차"),
                       ("가상1번", Grade.SAFE, "17분 · 08:17 도착 · 1,500원 · 정류장1에서 승차"),
                       ("가상1번 → 가상2번", Grade.SAFE, "22분 · 08:22 도착 · 1,500원 · 정류장1에서 승차 · 기존 길찾기 방식의 1위")],
         _alts_of(out, golden))
    caution = caution_html(out, golden)
    c.true("② 답 카드 HTML 의 등급", 'class="mr-answer safe"' in easy_answer_html(out, golden), easy_answer_html(out, golden))
    c.true("② 주의 카드 HTML 의 분위기와 가정 문장", 'class="mr-caution warn"' in caution and NAIVE_EASY_NOTE in caution, caution)
    c.eq("② 단계 번호", ["1", "2", "3", ""],
         re.findall(r'<span class="mr-n [a-z]+">(\d*)</span>', easy_steps_html(_best_of(out), out, golden)))
    c.eq("② 다른 경로 줄 수와 단추 글자", [(False, ALT_PICK_LABEL)] * 3,
         [(row.recommended, BACK_TO_BEST_LABEL if row.recommended else ALT_PICK_LABEL) for row in easy_alternatives(out, golden)])
    # ③ 골든 변형
    p90 = ce.run_engine(golden, ce.golden_query(), EngineConfig(rank_criterion=RankCriterion.P90_ARRIVAL))
    c.eq("③ 90% 도착 기준: 답 카드", EasyAnswer("추천 경로 · 90% 도착 기준", "가상1번", Grade.SAFE, "17분", "08:00 → 08:17 도착",
                                         ("늦어도 08:19에는 도착합니다.",), "1,500원 · 걷기 990 m"),
         easy_answer(p90))
    found = easy_caution(p90, golden)
    c.eq("③ 90% 도착 기준: 주의 카드 끝 문장", "이 앱이 계산한 평균 도착은 08:22이고, 추천 경로보다 약 5분 늦습니다.",
         found.lines[-1] if found else None)
    c.eq("③ 90% 도착 기준: 쉬운 단계", [("walk", "정류장1까지 걷기", ("2분 · 170 m",)),
                                   ("bus", "가상1번 타기", ("정류장1 08:03 출발 → 정류장2 08:06 하차",)),
                                   ("walk", "도착지까지 걷기", ("11분 · 820 m · 신호 1개",)), ("arrive", "도착지 도착", ("평균 08:17 도착",))],
         _steps_of(easy_steps(_best_of(p90), p90, golden)))
    c.eq("③ 90% 도착 기준: 다른 경로 둘째", ("따릉이", Grade.SAFE, "11분 · 08:11 도착 · 1,000원"), _alts_of(p90, golden)[1])
    ontime = ce.run_engine(golden, ce.golden_query().model_copy(update={"deadline_s": 1000.0}),
                           EngineConfig(rank_criterion=RankCriterion.ON_TIME))
    answer = easy_answer(ontime)
    c.eq("③ 마감 확률 기준, 마감 1,000: 머리와 줄", ("추천 경로 · 마감 확률 기준", ("늦어도 08:22에는 도착합니다.", "08:16:40까지 늦을 수 있습니다.")),
         (answer.head, answer.rows) if answer else None)
    answer = easy_answer(ce.run_engine(golden, ce.golden_query(), EngineConfig(rank_criterion=RankCriterion.ON_TIME)))
    c.eq("③ 마감 없이 마감 확률 기준: 머리와 줄", ("추천 경로", ("늦어도 08:22에는 도착합니다.",)),
         (answer.head, answer.rows) if answer else None)
    train = ce.run_engine(golden, ce.golden_train_query(), config)
    c.eq("③ 열차 질의: 주의 카드", EasyCaution("plain", "기존 길찾기 방식의 1위도 이 경로입니다", ("08:08 도착이라고 안내합니다.",)),
         easy_caution(train, golden))
    c.eq("③ 열차 질의: 쉬운 단계", [("subway", "역3 승강장에서 내리기", ("지금 탄 열차 · 08:05 도착",)),
                               ("walk", "도착지까지 걷기", ("3분 · 230 m",)), ("arrive", "도착지 도착", ("평균 08:08 도착",))],
         _steps_of(easy_steps(_best_of(train), train, golden)))
    c.eq("③ 열차 질의: 다른 경로 없음", [], _alts_of(train, golden))
    bus = ce.run_engine(golden, ce.golden_bus_query(), config)
    c.eq("③ 버스 질의: 첫 단계", ("bus", "정류장2에서 내리기", ("지금 탄 버스 · 08:06 도착",)),
         _steps_of(easy_steps(_best_of(bus), bus, golden))[0])
    c.eq("③ 버스 질의: 다른 경로", [("가상1번 → 가상2번", Grade.SAFE, "22분 · 08:22 도착 · 1,500원 · 정류장4에서 승차 · 기존 길찾기 방식의 1위")],
         _alts_of(bus, golden))
    last_scenario = ce.golden_last_vehicle_scenario()
    last = ce.run_engine(last_scenario, ce.golden_query(), config)
    found = easy_caution(last, last_scenario)
    c.eq("③ 막차 변형: 주의 카드", ("ghost", "하지만 타라는 가상2번 막차(08:07 출발)는 놓치기 쉽습니다.",
                                "이 앱이 계산한 평균 도착은 08:20이고, 추천 경로보다 약 9분 늦습니다."),
         (found.tone, found.lines[1], found.lines[2]) if found else None)
    c.eq("③ 막차 변형: 다른 경로 셋째", ("도보", Grade.SAFE, "22분 · 08:22 도착 · 0원"), _alts_of(last, last_scenario)[2])
    same = out.model_copy(update={"comparison": out.comparison.model_copy(update={"best_id": out.comparison.naive_best_id, "same": True})})
    answer = easy_answer(same)
    c.eq("③ 같은 경로: 답 카드", ("가상1번 → 가상2번", "22분", ("늦어도 08:23에는 도착합니다.",)),
         (answer.title, answer.minutes, answer.rows) if answer else None)
    c.eq("③ 같은 경로: 주의 카드", EasyCaution("warn", "기존 길찾기 방식의 1위도 이 경로입니다", (
        "08:11 도착이라고 안내합니다.", "하지만 타라는 가상2번(08:07 출발)은 놓치기 쉽습니다.",
        "이 앱은 가상2번(08:17 출발)을 안내합니다.")), easy_caution(same, golden))
    fourth = easy_steps(_best_of(same), same, golden)[3]
    c.eq("③ 같은 경로: 넷째 단계", ("bus", True, "가상2번 타기", ("정류장4 08:17 출발 → 정류장5 08:20 하차",
                                                         "가상2번(08:07 출발)은 놓치기 쉬워 이 차를 안내합니다. 더 일찍 닿으면 앞차를 타도 됩니다.")),
         (fourth.kind, fourth.ghost, fourth.main, fourth.subs))
    c.eq("③ 같은 경로: 다른 경로", ["따릉이", "지하철 가상선", "가상1번"], [row[0] for row in _alts_of(same, golden)])
    none = out.model_copy(update={"ranking": (), "comparison": out.comparison.model_copy(update={"best_id": None})})
    nothing = easy_answer_html(none, golden)
    c.eq("③ 최선 없음: 답 카드 None", None, easy_answer(none))
    c.true("③ 최선 없음: 상태 카드", 'class="mr-state ghost"' in nothing and NO_PLAN_EASY_TEXT in nothing, nothing)
    c.eq("③ 최선 없음: 주의 카드와 다른 경로 없음", (None, "", ()),
         (easy_caution(none, golden), caution_html(none, golden), easy_alternatives(none, golden)))
    lonely = out.model_copy(update={"comparison": out.comparison.model_copy(update={"naive_best_id": None})})
    c.eq("③ 기존 방식 없음: 주의 카드 None", None, easy_caution(lonely, golden))
    c.eq("③ 기존 방식 없음: 다른 경로 셋째", "22분 · 08:22 도착 · 1,500원 · 정류장1에서 승차", _alts_of(lonely, golden)[2][2])
    # ④ 지도
    fmap = build_simple_map(golden, out, out.comparison.best_id)
    c.eq("④ 레이어", ["추천 경로", "출발·도착"], list(feature_groups(fmap)))
    c.eq("④ 레이어 선택 창 없음, 확대 단추 꺼짐", (False, False),
         (any(isinstance(child, folium.LayerControl) for child in fmap._children.values()), fmap.options.get("zoom_control")))
    c.true("④ 휴대폰 끌기 스크립트", "L.Browser.mobile" in fmap.get_root().render())
    c.eq("④ 알약과 자리, 번호 표지 (19단계, 33단계부터 노선 이름)", ([("출발", "left"), ("도착", "right")], ["2 따릉이"]), (_simple_labels(fmap), _simple_badges(fmap)))
    c.eq("④ 맞춤 여백", [((57, 36), (57, 60))], _fit_padding(fmap))
    expected_a = ce.run_engine(a, a.default_query, config)
    names_a = {node.id: node.name for node in a.nodes}
    first_alight = _best_of(expected_a).rides[0].alight_node_id
    map_a = build_simple_map(a, expected_a, expected_a.comparison.best_id)
    c.eq("④ A: 알약은 출발·도착, 첫 하차(삼성역 2호선 승강장, 출발 자리)에는 번호가 없고 따릉이 타기에 3",
         (["출발", "도착"], ["3 따릉이"], "삼성역 2호선 승강장"), ([text for text, _ in _simple_labels(map_a)], _simple_badges(map_a), names_a[first_alight]))
    waiting = build_simple_map(golden, None, None, pick=("ORIGIN", (37.5, 127.0, "x"), None))
    c.eq("④ 찍기를 기다리는 지도: 레이어", ["출발·도착"], list(feature_groups(waiting)))
    c.true("④ 찍기를 기다리는 지도: 십자 커서", "cursor: crosshair" in waiting.get_root().render())
    # ⑤ AppTest A 기본(보기 기본값), ⑦ 자세히와 되돌아오기: 같은 AppTest 이고 run_engine 은 한 번
    expected_b = ce.run_engine(b, b.default_query, config)
    place = next(item for item in a.places if item.node_id != a.default_query.destination_node_id)
    moved_a = ce.run_engine(a, Query(origin=OriginState(kind=OriginKind.AT_NODE, node_id=place.node_id),
                                     destination_node_id=a.default_query.destination_node_id, deadline_s=a.default_query.deadline_s),
                            config)
    counter = _Counted(ce.run_engine)
    with _replaced(ce, "run_engine", counter):
        s = _Screen(c, maps, view=None, scenario="A").run("간단히 보기, 시나리오 기본 질의")
        c.eq("⑤ 보기 기본값", "SIMPLE", s.state("view_mode"))
        c.eq("⑤ 보기 선택지", ["간단히", "자세히"], s.options("segmented_control", "view_mode"))
        c.eq("⑤ 비교 패널, KPI, 탭, 경로 목록 없음", (0, 0, 0, False),
             (len(s.htmls("mr-compare")), len(s.at.metric), len(s.at.tabs), s.has("radio", "selected_id")))
        main_keys = [item.key for item in s.at.main.segmented_control]
        side_keys = [item.key for item in s.at.sidebar.segmented_control]
        c.eq("⑤ 본문에 출발·도착 상자와 출발·목적지 구간 선택", (1, True, True),
             (len(s.htmls("mr-trip")), "origin_kind" in main_keys, "dest_kind" in main_keys))
        c.eq("⑤ 위치 단추 요소는 본문에 하나, 사이드바에 없음", (1, 0),
             (len(s.at.main.get("bidi_component")), len(s.at.sidebar.get("bidi_component"))))
        c.eq("⑤ 접힘 '출발·목적지 바꾸기'", [TRIP_EDIT_LABEL], [item.label for item in s.at.main.expander if item.label == TRIP_EDIT_LABEL])
        c.eq("⑤ 사이드바에 출발·목적지 구간 선택 없음", (False, False), ("origin_kind" in side_keys, "dest_kind" in side_keys))
        c.true("⑤ 사이드바 안내", TRIP_SIDEBAR_NOTE in s.side_captions(), s.side_captions())
        best_a = _best_of(expected_a)
        answer_a = [easy_answer_html(expected_a, a)]
        c.eq("⑤ 답 카드", answer_a, s.htmls("mr-answer"))
        c.eq("⑤ 주의 카드는 없다(32단계)", [], s.htmls("mr-caution"))
        c.eq("⑤ 쉬운 단계", [easy_steps_html(best_a, expected_a, a)], s.htmls("mr-easy"))
        c.eq("⑤ 경로 비교 표", compare_htmls(expected_a, a), s.compare())
        call = maps.calls[-1] if maps.calls else {}
        c.eq("⑤ 지도 호출: 높이와 레이어", (380, {"추천 경로", "출발·도착"}), (call.get("height"), set(call.get("layers", ()))))
        c.true("⑤ 단추 '자세한 분석 보기'", s.has("button", "view_detail"))
        c.true("⑤ 경고 안내", f"계산 경고 {len(expected_a.warnings)}건은 자세히 보기에서 볼 수 있습니다." in s.main_texts("caption"),
               s.main_texts("caption"))
        _no_banned(c, "⑤", s)
        trip = _trip_texts(s)
        s.click("view_detail")
        c.eq("⑦ 자세히: 보기", "DETAIL", s.state("view_mode"))
        c.eq("⑦ 자세히: 비교 패널, KPI, 탭", (1, _kpi_expect(expected_a), True),
             (len(s.htmls("mr-compare")), s.kpi(), len(s.at.tabs) > 0))
        c.true("⑦ 자세히: 사이드바에 출발 구간 선택", "origin_kind" in [item.key for item in s.at.sidebar.segmented_control])
        description = s.description()
        c.eq("⑦ 상자의 출발은 간단한 말, 한 줄 설명은 열차 번호와 초까지 (19단계)",
             ("2호선 외선 열차 안 · 다음 역 삼성 19:21 도착", True, True),
             ((trip or [None])[0], description.startswith("출발: 2호선 외선 2209 열차 안, 다음 역 삼성 19:21:15 · 기준 시각 "),
              len(trip) == 2 and description.endswith(f" · 목적지: {trip[1]}")))
        _no_banned(c, "⑦", s)
        s.set("segmented_control", "view_mode", "SIMPLE")
        c.eq("⑦ 간단히로 돌아오면 답 카드가 ⑤ 와 같다", answer_a, s.htmls("mr-answer"))
        c.eq("⑤ ~ ⑦ run_engine 1회(캐시)", 1, counter.calls)
    # ⑥ 상자 안에서 출발을 바꾼다
    s = _Screen(c, maps, view=None).run("간단히 보기 첫 실행 (⑥)")
    s.put("trip_edit", True)
    s.set("segmented_control", "origin_kind", "PLACE")
    s.set("selectbox", "origin_place", place.name)
    c.eq("⑥ 장소 출발의 답 카드", [easy_answer_html(moved_a, a, None, _leave_expect(a, moved_a.query, config))], s.htmls("mr-answer"))
    c.eq("⑥ 접힘은 열린 채", True, s.state("trip_edit"))
    _no_banned(c, "⑥", s)
    # ⑧ B: 기존 방식 1위가 걸러짐
    s = _Screen(c, maps, view=None).run("간단히 보기 첫 실행 (⑧)").scenario("B")
    cards = [item for item in s.compare() if 'class="mr-cmp naive"' in item]
    c.eq("⑧ B 경로 비교 표", compare_htmls(expected_b, b), s.compare())
    c.true("⑧ B 기존 앱 1위 줄은 놓치기 쉬움 배지와 설명", len(cards) == 1 and 'class="mr-badge ghost"' in cards[0]
           and "기존 길찾기 앱 안내 23:30 도착 → 이 앱 계산 23:54 도착" in cards[0], cards)
    _no_banned(c, "⑧", s)
    # ⑨ 골든: 찍기를 기다림, 찍은 점이 길에서 멀다
    s = _Screen(c, maps, view=None).run("간단히 보기 첫 실행 (⑨)").scenario(ce.GOLDEN_ID)
    s.set("segmented_control", "origin_kind", "POINT")
    c.eq("⑨ 찍은 점 없음: 안내", ["지도를 눌러 출발을 정하세요."], s.main_texts("info"))
    c.eq("⑨ 찍은 점 없음: 지도는 누르기를 기다린다", ["last_clicked"], maps.calls[-1]["returned_objects"] if maps.calls else None)
    _no_banned(c, "⑨ 찍은 점 없음", s)
    s.put("origin_point", (37.51, 127.0))
    c.eq("⑨ SNAP_FAILED 카드", [_SNAP_TEXT], [_plain(value) for value in s.htmls("mr-state")])
    c.eq("⑨ SNAP_FAILED 지도: 찍은 점의 출발·도착 레이어", ("출발·도착",), maps.calls[-1]["layers"] if maps.calls else None)
    _no_banned(c, "⑨ SNAP_FAILED", s)
    # ⑩ A: 지금 위치에서 출발. 개인정보 문장과 정확도 경고는 상자의 위치 단추 아래(접힘 밖)
    node, distance = _gps_snap(a, "G1")
    answer_g1 = [easy_answer_html(ce.run_engine(a, _gps_point_query(a, "G1"), config), a, None,
                                  _leave_expect(a, _gps_point_query(a, "G1"), config))]
    warn = gps_accuracy_text(350.0)
    s = _Screen(c, maps, view=None).run("간단히 보기 첫 실행 (⑩)")
    for accuracy, middle in ((12.0, []), (350.0, [("warning", warn)])):
        tag = f"⑩ 반경 {accuracy:g}"
        s.put("gps_pending", _gps_fix("G1", accuracy))
        c.eq(f"{tag}: 출발 상태", ("POINT", (37.5095, 127.06281), {"lat": 37.5095, "lon": 127.06281, "accuracy_m": accuracy}),
             (s.state("origin_kind"), tuple(s.state("origin_point", ())), s.state("origin_gps")))
        c.eq(f"{tag}: 상자의 출발 표시", f"지금 위치(가장 가까운 {node}까지 {fmt_dist(distance)})", (_trip_texts(s) or [None])[0])
        c.eq(f"{tag}: 상자의 차례 (위치 단추, 개인정보 문장, 경고, 접힘)",
             [("bidi_component", ""), ("caption", GPS_PRIVACY_NOTE), *middle, ("expander", TRIP_EDIT_LABEL),
              ("toggle", DEADLINE_EASY_LABEL)], _trip_box(s))
        inside = [item for item in s.at.main.expander if item.label == TRIP_EDIT_LABEL]
        captions = [item.value for item in inside[0].caption] if inside else []
        c.eq(f"{tag}: 접힘 안에는 지금 위치 줄만 (개인정보 문장과 경고 없음)", (True, False, []),
             (f"지금 위치 37.50950, 127.06281 · 정확도 ±{fmt_dist(accuracy)}" in captions, GPS_PRIVACY_NOTE in captions,
              [item.value for item in inside[0].warning] if inside else None))
        c.eq(f"{tag}: 사이드바에는 개인정보 문장과 경고 없음", (False, []), (GPS_PRIVACY_NOTE in s.side_captions(), s.side_texts("warning")))
        c.eq(f"{tag}: 접힘은 접힌 채", False, bool(s.state("trip_edit", False)))
        c.eq(f"{tag}: 답 카드 = AT_POINT G1 → A 의 목적지", answer_g1, s.htmls("mr-answer"))
        _no_banned(c, tag, s)


_UI_CHECKS: tuple[tuple[str, str, Callable[[_Checker, Path, _MapCalls], None]], ...] = (
    ("UI-01", "기본 실행과 시나리오 목록", _ui01),
    ("UI-02", "위젯, 기본값, 보존 키", _ui02),
    ("UI-03", "비교 패널과 결론 문장", _ui03),
    ("UI-04", "KPI", _ui04),
    ("UI-05", "지도 (build_map)", _ui05),
    ("UI-06", "경로 목록, 시간 막대, 여정 안내", _ui06),
    ("UI-07", "조건 변경과 선택 유지", _ui07),
    ("UI-08", "되돌리기와 시나리오 전환", _ui08),
    ("UI-09", "상태 화면", _ui09),
    ("UI-10", "형식 함수와 성능", _ui10),
    ("UI-11", "출발 상태: 지금 탄 열차·버스", _ui11),
    ("UI-12", "지도에서 고르기", _ui12),
    ("UI-13", "탭 구성과 빈 상태", _ui13),
    ("UI-14", "① 경로 비교", _ui14),
    ("UI-15", "② 탑승별 확률", _ui15),
    ("UI-16", "③ 신호", _ui16),
    ("UI-17", "④ 따릉이", _ui17),
    ("UI-18", "⑤ 요금", _ui18),
    ("UI-19", "⑥ 탐색 과정", _ui19),
    ("UI-20", "⑦ 데이터·기록", _ui20),
    ("UI-21", "데이터 모드 대체와 시나리오 파일 오류", _ui21),
    ("UI-22", "기록 재생", _ui22),
    ("UI-23", "시연 흐름 기본", _ui23),
    ("UI-24", "시연 흐름 기록", _ui24),
    ("UI-25", "카카오 비교", _ui25),
    ("UI-26", "실시간", _ui26),
    ("UI-27", "캐시와 엔진 호출 수", _ui27),
    ("UI-28", "묶음 탑승의 안내와 차량 표", _ui28),
    ("UI-29", "지금 위치에서 출발", _ui29),
    ("UI-30", "간단히 보기", _ui30),
    ("UI-31", "예시 경로", _ui31),
    ("UI-32", "간단히 보기 고침", _ui32),
    ("UI-33", "지도와 지금 할 일 줄 고침", _ui33),
    ("UI-34", "길에 선 사람의 세 질문", _ui34),
    ("UI-35", "정류장 이름과 번호", _ui35),
    ("UI-36", "내 걸음 빠르기", _ui36),
    ("UI-37", "약속 시각이 있으면", _ui37),
    ("UI-38", "타는 것", _ui38),
    ("UI-39", "꺼진 토글의 테두리", _ui39),
    ("UI-40", "출발 늦추기의 글자", _ui40),
    ("UI-41", "안내 모드", _ui41),
    ("UI-42", "확률 대신 결정", _ui42),
    ("UI-43", "소개 페이지와 실제 기록 장면", _ui43),
)


def run_ui_tests(selected: Sequence[str] = ()) -> int:
    """화면 검사(§8.7, §9.9). 검사마다 임시 데이터 폴더와 빈 캐시에서 시작하고, 키와 데이터 폴더 환경변수를 비운 채 실행한다.
    `selected` 에 검사 ID 를 주면 그 검사만 실행한다. 모두 통과하면 0, 아니면 1."""
    import streamlit_folium
    config = EngineConfig()
    names = (config.env_seoul_key, config.env_data_go_kr_key, config.env_kakao_key, config.env_tdata_key, DATA_DIR_ENV)
    saved = {name: os.environ.get(name) for name in names}
    checks = [item for item in _UI_CHECKS if not selected or item[0] in selected]
    unknown = sorted(set(selected) - {item[0] for item in _UI_CHECKS})
    if unknown:
        print(f"알 수 없는 검사: {', '.join(unknown)}")
        return 1
    passed = 0
    started_all = time.perf_counter()
    try:
        for check_id, title, func in checks:
            for name in names:
                os.environ.pop(name, None)
            checker = _Checker()
            maps = _MapCalls()
            started = time.perf_counter()
            with tempfile.TemporaryDirectory(prefix="mobility-router-uitest-") as temp:
                folder = Path(temp)
                os.environ[DATA_DIR_ENV] = str(folder)
                _clear_caches()
                try:
                    with _replaced(streamlit_folium, "st_folium", maps):
                        func(checker, folder, maps)
                except Exception as error:  # noqa: BLE001 - 검사 하나의 실패로 보인다
                    checker.failures.append(f"예외 {type(error).__name__}: {error}\n" + "".join(traceback.format_exc(limit=6)))
            elapsed = time.perf_counter() - started
            if checker.failures:
                print(f"FAIL {check_id} {title} ({checker.count - len(checker.failures)}/{checker.count}, {elapsed:.1f}초)")
                for failure in checker.failures:
                    print("    - " + failure.replace("\n", "\n      "))
            else:
                passed += 1
                print(f"PASS {check_id} {title} ({checker.count}개 판정, {elapsed:.1f}초)")
    finally:
        for name, value in saved.items():
            if value is None:
                os.environ.pop(name, None)
            else:
                os.environ[name] = value
        _clear_caches()
    print(f"통과 {passed}/{len(checks)} ({time.perf_counter() - started_all:.1f}초)")
    return 0 if passed == len(checks) else 1


if __name__ == "__main__":
    if runtime.exists():  # streamlit run app.py, AppTest
        main()
    elif "--uitest" in sys.argv:  # python app.py --uitest [검사 ID ...]
        raise SystemExit(run_ui_tests(tuple(arg for arg in sys.argv[sys.argv.index("--uitest") + 1:] if not arg.startswith("-"))))
    else:  # python app.py [streamlit 옵션]
        command = [sys.executable, "-m", "streamlit", "run", str(Path(__file__).resolve()), *THEME_FLAGS, *sys.argv[1:]]
        raise SystemExit(subprocess.call(command))
