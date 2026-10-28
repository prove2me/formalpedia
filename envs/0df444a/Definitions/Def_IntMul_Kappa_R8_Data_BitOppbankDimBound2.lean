-- Prove2me | Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankDimBound2
-- name    : IntMul_Kappa_R8_Data_BitOppbankDimBound2
-- status  : Definition
-- author  : @Ethan Cheung Wang
-- created : 2026-10-28T18:03:15.205922+00:00
-- url     : https://prove2.me/theorems/1071827c-11ee-41cf-bfe8-f55cefc412e0
-- title:
--   Densified dimF $\le 22$ pack 2 ($[10000,15000)$)
-- statement:
--   Pack 2 of the densified dimension-field bound.
--
--   For every densified node index $n$ with $10000\le n<15000$, the 5-bit field $\mathrm{dimF}(n)$ extracted from $\mathrm{DIMT}$ satisfies
--   $$1\le \mathrm{dimF}(n)\le 22.$$
--   Proved by `decide` on successive `Fin 50` windows (no `native_decide`).
-- source:
--   R8 BitNB densified DIMT field bound; Fin-window decide packs

-- DimBound pack 2: dimF bounds on n ∈ [10000, 15000)

import Definitions.Def_IntMul_Kappa_R6_Defs4
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankPnd
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankSupG
import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 1000000

open IntMul.Kappa.R8.Bit.Oppbank.Pnd
open IntMul.Kappa.R8.Bit.Oppbank.ChkBitArg
open IntMul.Kappa.R8.Bit.Oppbank.SupG

namespace IntMul.Kappa.R8.Bit.Oppbank.DimBound2

private theorem le_w200 : ∀ n : Fin 50, dimF (n.val + 10000) ≤ 22 := by decide
private theorem pos_w200 : ∀ n : Fin 50, 0 < dimF (n.val + 10000) := by decide
private theorem le_w201 : ∀ n : Fin 50, dimF (n.val + 10050) ≤ 22 := by decide
private theorem pos_w201 : ∀ n : Fin 50, 0 < dimF (n.val + 10050) := by decide
private theorem le_w202 : ∀ n : Fin 50, dimF (n.val + 10100) ≤ 22 := by decide
private theorem pos_w202 : ∀ n : Fin 50, 0 < dimF (n.val + 10100) := by decide
private theorem le_w203 : ∀ n : Fin 50, dimF (n.val + 10150) ≤ 22 := by decide
private theorem pos_w203 : ∀ n : Fin 50, 0 < dimF (n.val + 10150) := by decide
private theorem le_w204 : ∀ n : Fin 50, dimF (n.val + 10200) ≤ 22 := by decide
private theorem pos_w204 : ∀ n : Fin 50, 0 < dimF (n.val + 10200) := by decide
private theorem le_w205 : ∀ n : Fin 50, dimF (n.val + 10250) ≤ 22 := by decide
private theorem pos_w205 : ∀ n : Fin 50, 0 < dimF (n.val + 10250) := by decide
private theorem le_w206 : ∀ n : Fin 50, dimF (n.val + 10300) ≤ 22 := by decide
private theorem pos_w206 : ∀ n : Fin 50, 0 < dimF (n.val + 10300) := by decide
private theorem le_w207 : ∀ n : Fin 50, dimF (n.val + 10350) ≤ 22 := by decide
private theorem pos_w207 : ∀ n : Fin 50, 0 < dimF (n.val + 10350) := by decide
private theorem le_w208 : ∀ n : Fin 50, dimF (n.val + 10400) ≤ 22 := by decide
private theorem pos_w208 : ∀ n : Fin 50, 0 < dimF (n.val + 10400) := by decide
private theorem le_w209 : ∀ n : Fin 50, dimF (n.val + 10450) ≤ 22 := by decide
private theorem pos_w209 : ∀ n : Fin 50, 0 < dimF (n.val + 10450) := by decide
private theorem le_w210 : ∀ n : Fin 50, dimF (n.val + 10500) ≤ 22 := by decide
private theorem pos_w210 : ∀ n : Fin 50, 0 < dimF (n.val + 10500) := by decide
private theorem le_w211 : ∀ n : Fin 50, dimF (n.val + 10550) ≤ 22 := by decide
private theorem pos_w211 : ∀ n : Fin 50, 0 < dimF (n.val + 10550) := by decide
private theorem le_w212 : ∀ n : Fin 50, dimF (n.val + 10600) ≤ 22 := by decide
private theorem pos_w212 : ∀ n : Fin 50, 0 < dimF (n.val + 10600) := by decide
private theorem le_w213 : ∀ n : Fin 50, dimF (n.val + 10650) ≤ 22 := by decide
private theorem pos_w213 : ∀ n : Fin 50, 0 < dimF (n.val + 10650) := by decide
private theorem le_w214 : ∀ n : Fin 50, dimF (n.val + 10700) ≤ 22 := by decide
private theorem pos_w214 : ∀ n : Fin 50, 0 < dimF (n.val + 10700) := by decide
private theorem le_w215 : ∀ n : Fin 50, dimF (n.val + 10750) ≤ 22 := by decide
private theorem pos_w215 : ∀ n : Fin 50, 0 < dimF (n.val + 10750) := by decide
private theorem le_w216 : ∀ n : Fin 50, dimF (n.val + 10800) ≤ 22 := by decide
private theorem pos_w216 : ∀ n : Fin 50, 0 < dimF (n.val + 10800) := by decide
private theorem le_w217 : ∀ n : Fin 50, dimF (n.val + 10850) ≤ 22 := by decide
private theorem pos_w217 : ∀ n : Fin 50, 0 < dimF (n.val + 10850) := by decide
private theorem le_w218 : ∀ n : Fin 50, dimF (n.val + 10900) ≤ 22 := by decide
private theorem pos_w218 : ∀ n : Fin 50, 0 < dimF (n.val + 10900) := by decide
private theorem le_w219 : ∀ n : Fin 50, dimF (n.val + 10950) ≤ 22 := by decide
private theorem pos_w219 : ∀ n : Fin 50, 0 < dimF (n.val + 10950) := by decide
private theorem le_w220 : ∀ n : Fin 50, dimF (n.val + 11000) ≤ 22 := by decide
private theorem pos_w220 : ∀ n : Fin 50, 0 < dimF (n.val + 11000) := by decide
private theorem le_w221 : ∀ n : Fin 50, dimF (n.val + 11050) ≤ 22 := by decide
private theorem pos_w221 : ∀ n : Fin 50, 0 < dimF (n.val + 11050) := by decide
private theorem le_w222 : ∀ n : Fin 50, dimF (n.val + 11100) ≤ 22 := by decide
private theorem pos_w222 : ∀ n : Fin 50, 0 < dimF (n.val + 11100) := by decide
private theorem le_w223 : ∀ n : Fin 50, dimF (n.val + 11150) ≤ 22 := by decide
private theorem pos_w223 : ∀ n : Fin 50, 0 < dimF (n.val + 11150) := by decide
private theorem le_w224 : ∀ n : Fin 50, dimF (n.val + 11200) ≤ 22 := by decide
private theorem pos_w224 : ∀ n : Fin 50, 0 < dimF (n.val + 11200) := by decide
private theorem le_w225 : ∀ n : Fin 50, dimF (n.val + 11250) ≤ 22 := by decide
private theorem pos_w225 : ∀ n : Fin 50, 0 < dimF (n.val + 11250) := by decide
private theorem le_w226 : ∀ n : Fin 50, dimF (n.val + 11300) ≤ 22 := by decide
private theorem pos_w226 : ∀ n : Fin 50, 0 < dimF (n.val + 11300) := by decide
private theorem le_w227 : ∀ n : Fin 50, dimF (n.val + 11350) ≤ 22 := by decide
private theorem pos_w227 : ∀ n : Fin 50, 0 < dimF (n.val + 11350) := by decide
private theorem le_w228 : ∀ n : Fin 50, dimF (n.val + 11400) ≤ 22 := by decide
private theorem pos_w228 : ∀ n : Fin 50, 0 < dimF (n.val + 11400) := by decide
private theorem le_w229 : ∀ n : Fin 50, dimF (n.val + 11450) ≤ 22 := by decide
private theorem pos_w229 : ∀ n : Fin 50, 0 < dimF (n.val + 11450) := by decide
private theorem le_w230 : ∀ n : Fin 50, dimF (n.val + 11500) ≤ 22 := by decide
private theorem pos_w230 : ∀ n : Fin 50, 0 < dimF (n.val + 11500) := by decide
private theorem le_w231 : ∀ n : Fin 50, dimF (n.val + 11550) ≤ 22 := by decide
private theorem pos_w231 : ∀ n : Fin 50, 0 < dimF (n.val + 11550) := by decide
private theorem le_w232 : ∀ n : Fin 50, dimF (n.val + 11600) ≤ 22 := by decide
private theorem pos_w232 : ∀ n : Fin 50, 0 < dimF (n.val + 11600) := by decide
private theorem le_w233 : ∀ n : Fin 50, dimF (n.val + 11650) ≤ 22 := by decide
private theorem pos_w233 : ∀ n : Fin 50, 0 < dimF (n.val + 11650) := by decide
private theorem le_w234 : ∀ n : Fin 50, dimF (n.val + 11700) ≤ 22 := by decide
private theorem pos_w234 : ∀ n : Fin 50, 0 < dimF (n.val + 11700) := by decide
private theorem le_w235 : ∀ n : Fin 50, dimF (n.val + 11750) ≤ 22 := by decide
private theorem pos_w235 : ∀ n : Fin 50, 0 < dimF (n.val + 11750) := by decide
private theorem le_w236 : ∀ n : Fin 50, dimF (n.val + 11800) ≤ 22 := by decide
private theorem pos_w236 : ∀ n : Fin 50, 0 < dimF (n.val + 11800) := by decide
private theorem le_w237 : ∀ n : Fin 50, dimF (n.val + 11850) ≤ 22 := by decide
private theorem pos_w237 : ∀ n : Fin 50, 0 < dimF (n.val + 11850) := by decide
private theorem le_w238 : ∀ n : Fin 50, dimF (n.val + 11900) ≤ 22 := by decide
private theorem pos_w238 : ∀ n : Fin 50, 0 < dimF (n.val + 11900) := by decide
private theorem le_w239 : ∀ n : Fin 50, dimF (n.val + 11950) ≤ 22 := by decide
private theorem pos_w239 : ∀ n : Fin 50, 0 < dimF (n.val + 11950) := by decide
private theorem le_w240 : ∀ n : Fin 50, dimF (n.val + 12000) ≤ 22 := by decide
private theorem pos_w240 : ∀ n : Fin 50, 0 < dimF (n.val + 12000) := by decide
private theorem le_w241 : ∀ n : Fin 50, dimF (n.val + 12050) ≤ 22 := by decide
private theorem pos_w241 : ∀ n : Fin 50, 0 < dimF (n.val + 12050) := by decide
private theorem le_w242 : ∀ n : Fin 50, dimF (n.val + 12100) ≤ 22 := by decide
private theorem pos_w242 : ∀ n : Fin 50, 0 < dimF (n.val + 12100) := by decide
private theorem le_w243 : ∀ n : Fin 50, dimF (n.val + 12150) ≤ 22 := by decide
private theorem pos_w243 : ∀ n : Fin 50, 0 < dimF (n.val + 12150) := by decide
private theorem le_w244 : ∀ n : Fin 50, dimF (n.val + 12200) ≤ 22 := by decide
private theorem pos_w244 : ∀ n : Fin 50, 0 < dimF (n.val + 12200) := by decide
private theorem le_w245 : ∀ n : Fin 50, dimF (n.val + 12250) ≤ 22 := by decide
private theorem pos_w245 : ∀ n : Fin 50, 0 < dimF (n.val + 12250) := by decide
private theorem le_w246 : ∀ n : Fin 50, dimF (n.val + 12300) ≤ 22 := by decide
private theorem pos_w246 : ∀ n : Fin 50, 0 < dimF (n.val + 12300) := by decide
private theorem le_w247 : ∀ n : Fin 50, dimF (n.val + 12350) ≤ 22 := by decide
private theorem pos_w247 : ∀ n : Fin 50, 0 < dimF (n.val + 12350) := by decide
private theorem le_w248 : ∀ n : Fin 50, dimF (n.val + 12400) ≤ 22 := by decide
private theorem pos_w248 : ∀ n : Fin 50, 0 < dimF (n.val + 12400) := by decide
private theorem le_w249 : ∀ n : Fin 50, dimF (n.val + 12450) ≤ 22 := by decide
private theorem pos_w249 : ∀ n : Fin 50, 0 < dimF (n.val + 12450) := by decide
private theorem le_w250 : ∀ n : Fin 50, dimF (n.val + 12500) ≤ 22 := by decide
private theorem pos_w250 : ∀ n : Fin 50, 0 < dimF (n.val + 12500) := by decide
private theorem le_w251 : ∀ n : Fin 50, dimF (n.val + 12550) ≤ 22 := by decide
private theorem pos_w251 : ∀ n : Fin 50, 0 < dimF (n.val + 12550) := by decide
private theorem le_w252 : ∀ n : Fin 50, dimF (n.val + 12600) ≤ 22 := by decide
private theorem pos_w252 : ∀ n : Fin 50, 0 < dimF (n.val + 12600) := by decide
private theorem le_w253 : ∀ n : Fin 50, dimF (n.val + 12650) ≤ 22 := by decide
private theorem pos_w253 : ∀ n : Fin 50, 0 < dimF (n.val + 12650) := by decide
private theorem le_w254 : ∀ n : Fin 50, dimF (n.val + 12700) ≤ 22 := by decide
private theorem pos_w254 : ∀ n : Fin 50, 0 < dimF (n.val + 12700) := by decide
private theorem le_w255 : ∀ n : Fin 50, dimF (n.val + 12750) ≤ 22 := by decide
private theorem pos_w255 : ∀ n : Fin 50, 0 < dimF (n.val + 12750) := by decide
private theorem le_w256 : ∀ n : Fin 50, dimF (n.val + 12800) ≤ 22 := by decide
private theorem pos_w256 : ∀ n : Fin 50, 0 < dimF (n.val + 12800) := by decide
private theorem le_w257 : ∀ n : Fin 50, dimF (n.val + 12850) ≤ 22 := by decide
private theorem pos_w257 : ∀ n : Fin 50, 0 < dimF (n.val + 12850) := by decide
private theorem le_w258 : ∀ n : Fin 50, dimF (n.val + 12900) ≤ 22 := by decide
private theorem pos_w258 : ∀ n : Fin 50, 0 < dimF (n.val + 12900) := by decide
private theorem le_w259 : ∀ n : Fin 50, dimF (n.val + 12950) ≤ 22 := by decide
private theorem pos_w259 : ∀ n : Fin 50, 0 < dimF (n.val + 12950) := by decide
private theorem le_w260 : ∀ n : Fin 50, dimF (n.val + 13000) ≤ 22 := by decide
private theorem pos_w260 : ∀ n : Fin 50, 0 < dimF (n.val + 13000) := by decide
private theorem le_w261 : ∀ n : Fin 50, dimF (n.val + 13050) ≤ 22 := by decide
private theorem pos_w261 : ∀ n : Fin 50, 0 < dimF (n.val + 13050) := by decide
private theorem le_w262 : ∀ n : Fin 50, dimF (n.val + 13100) ≤ 22 := by decide
private theorem pos_w262 : ∀ n : Fin 50, 0 < dimF (n.val + 13100) := by decide
private theorem le_w263 : ∀ n : Fin 50, dimF (n.val + 13150) ≤ 22 := by decide
private theorem pos_w263 : ∀ n : Fin 50, 0 < dimF (n.val + 13150) := by decide
private theorem le_w264 : ∀ n : Fin 50, dimF (n.val + 13200) ≤ 22 := by decide
private theorem pos_w264 : ∀ n : Fin 50, 0 < dimF (n.val + 13200) := by decide
private theorem le_w265 : ∀ n : Fin 50, dimF (n.val + 13250) ≤ 22 := by decide
private theorem pos_w265 : ∀ n : Fin 50, 0 < dimF (n.val + 13250) := by decide
private theorem le_w266 : ∀ n : Fin 50, dimF (n.val + 13300) ≤ 22 := by decide
private theorem pos_w266 : ∀ n : Fin 50, 0 < dimF (n.val + 13300) := by decide
private theorem le_w267 : ∀ n : Fin 50, dimF (n.val + 13350) ≤ 22 := by decide
private theorem pos_w267 : ∀ n : Fin 50, 0 < dimF (n.val + 13350) := by decide
private theorem le_w268 : ∀ n : Fin 50, dimF (n.val + 13400) ≤ 22 := by decide
private theorem pos_w268 : ∀ n : Fin 50, 0 < dimF (n.val + 13400) := by decide
private theorem le_w269 : ∀ n : Fin 50, dimF (n.val + 13450) ≤ 22 := by decide
private theorem pos_w269 : ∀ n : Fin 50, 0 < dimF (n.val + 13450) := by decide
private theorem le_w270 : ∀ n : Fin 50, dimF (n.val + 13500) ≤ 22 := by decide
private theorem pos_w270 : ∀ n : Fin 50, 0 < dimF (n.val + 13500) := by decide
private theorem le_w271 : ∀ n : Fin 50, dimF (n.val + 13550) ≤ 22 := by decide
private theorem pos_w271 : ∀ n : Fin 50, 0 < dimF (n.val + 13550) := by decide
private theorem le_w272 : ∀ n : Fin 50, dimF (n.val + 13600) ≤ 22 := by decide
private theorem pos_w272 : ∀ n : Fin 50, 0 < dimF (n.val + 13600) := by decide
private theorem le_w273 : ∀ n : Fin 50, dimF (n.val + 13650) ≤ 22 := by decide
private theorem pos_w273 : ∀ n : Fin 50, 0 < dimF (n.val + 13650) := by decide
private theorem le_w274 : ∀ n : Fin 50, dimF (n.val + 13700) ≤ 22 := by decide
private theorem pos_w274 : ∀ n : Fin 50, 0 < dimF (n.val + 13700) := by decide
private theorem le_w275 : ∀ n : Fin 50, dimF (n.val + 13750) ≤ 22 := by decide
private theorem pos_w275 : ∀ n : Fin 50, 0 < dimF (n.val + 13750) := by decide
private theorem le_w276 : ∀ n : Fin 50, dimF (n.val + 13800) ≤ 22 := by decide
private theorem pos_w276 : ∀ n : Fin 50, 0 < dimF (n.val + 13800) := by decide
private theorem le_w277 : ∀ n : Fin 50, dimF (n.val + 13850) ≤ 22 := by decide
private theorem pos_w277 : ∀ n : Fin 50, 0 < dimF (n.val + 13850) := by decide
private theorem le_w278 : ∀ n : Fin 50, dimF (n.val + 13900) ≤ 22 := by decide
private theorem pos_w278 : ∀ n : Fin 50, 0 < dimF (n.val + 13900) := by decide
private theorem le_w279 : ∀ n : Fin 50, dimF (n.val + 13950) ≤ 22 := by decide
private theorem pos_w279 : ∀ n : Fin 50, 0 < dimF (n.val + 13950) := by decide
private theorem le_w280 : ∀ n : Fin 50, dimF (n.val + 14000) ≤ 22 := by decide
private theorem pos_w280 : ∀ n : Fin 50, 0 < dimF (n.val + 14000) := by decide
private theorem le_w281 : ∀ n : Fin 50, dimF (n.val + 14050) ≤ 22 := by decide
private theorem pos_w281 : ∀ n : Fin 50, 0 < dimF (n.val + 14050) := by decide
private theorem le_w282 : ∀ n : Fin 50, dimF (n.val + 14100) ≤ 22 := by decide
private theorem pos_w282 : ∀ n : Fin 50, 0 < dimF (n.val + 14100) := by decide
private theorem le_w283 : ∀ n : Fin 50, dimF (n.val + 14150) ≤ 22 := by decide
private theorem pos_w283 : ∀ n : Fin 50, 0 < dimF (n.val + 14150) := by decide
private theorem le_w284 : ∀ n : Fin 50, dimF (n.val + 14200) ≤ 22 := by decide
private theorem pos_w284 : ∀ n : Fin 50, 0 < dimF (n.val + 14200) := by decide
private theorem le_w285 : ∀ n : Fin 50, dimF (n.val + 14250) ≤ 22 := by decide
private theorem pos_w285 : ∀ n : Fin 50, 0 < dimF (n.val + 14250) := by decide
private theorem le_w286 : ∀ n : Fin 50, dimF (n.val + 14300) ≤ 22 := by decide
private theorem pos_w286 : ∀ n : Fin 50, 0 < dimF (n.val + 14300) := by decide
private theorem le_w287 : ∀ n : Fin 50, dimF (n.val + 14350) ≤ 22 := by decide
private theorem pos_w287 : ∀ n : Fin 50, 0 < dimF (n.val + 14350) := by decide
private theorem le_w288 : ∀ n : Fin 50, dimF (n.val + 14400) ≤ 22 := by decide
private theorem pos_w288 : ∀ n : Fin 50, 0 < dimF (n.val + 14400) := by decide
private theorem le_w289 : ∀ n : Fin 50, dimF (n.val + 14450) ≤ 22 := by decide
private theorem pos_w289 : ∀ n : Fin 50, 0 < dimF (n.val + 14450) := by decide
private theorem le_w290 : ∀ n : Fin 50, dimF (n.val + 14500) ≤ 22 := by decide
private theorem pos_w290 : ∀ n : Fin 50, 0 < dimF (n.val + 14500) := by decide
private theorem le_w291 : ∀ n : Fin 50, dimF (n.val + 14550) ≤ 22 := by decide
private theorem pos_w291 : ∀ n : Fin 50, 0 < dimF (n.val + 14550) := by decide
private theorem le_w292 : ∀ n : Fin 50, dimF (n.val + 14600) ≤ 22 := by decide
private theorem pos_w292 : ∀ n : Fin 50, 0 < dimF (n.val + 14600) := by decide
private theorem le_w293 : ∀ n : Fin 50, dimF (n.val + 14650) ≤ 22 := by decide
private theorem pos_w293 : ∀ n : Fin 50, 0 < dimF (n.val + 14650) := by decide
private theorem le_w294 : ∀ n : Fin 50, dimF (n.val + 14700) ≤ 22 := by decide
private theorem pos_w294 : ∀ n : Fin 50, 0 < dimF (n.val + 14700) := by decide
private theorem le_w295 : ∀ n : Fin 50, dimF (n.val + 14750) ≤ 22 := by decide
private theorem pos_w295 : ∀ n : Fin 50, 0 < dimF (n.val + 14750) := by decide
private theorem le_w296 : ∀ n : Fin 50, dimF (n.val + 14800) ≤ 22 := by decide
private theorem pos_w296 : ∀ n : Fin 50, 0 < dimF (n.val + 14800) := by decide
private theorem le_w297 : ∀ n : Fin 50, dimF (n.val + 14850) ≤ 22 := by decide
private theorem pos_w297 : ∀ n : Fin 50, 0 < dimF (n.val + 14850) := by decide
private theorem le_w298 : ∀ n : Fin 50, dimF (n.val + 14900) ≤ 22 := by decide
private theorem pos_w298 : ∀ n : Fin 50, 0 < dimF (n.val + 14900) := by decide
private theorem le_w299 : ∀ n : Fin 50, dimF (n.val + 14950) ≤ 22 := by decide
private theorem pos_w299 : ∀ n : Fin 50, 0 < dimF (n.val + 14950) := by decide

theorem dimF_le_22_range : ∀ n, 10000 ≤ n → n < 15000 → dimF n ≤ 22 := by
  intro n hlo hhi
  by_cases h0 : n < 10050
  · have hr : n - 10000 < 50 := by omega
    have heq : n = (n - 10000) + 10000 := by omega
    rw [heq]
    exact le_w200 ⟨n - 10000, hr⟩
  · by_cases h1 : n < 10100
    · have hr : n - 10050 < 50 := by omega
      have heq : n = (n - 10050) + 10050 := by omega
      rw [heq]
      exact le_w201 ⟨n - 10050, hr⟩
    · by_cases h2 : n < 10150
      · have hr : n - 10100 < 50 := by omega
        have heq : n = (n - 10100) + 10100 := by omega
        rw [heq]
        exact le_w202 ⟨n - 10100, hr⟩
      · by_cases h3 : n < 10200
        · have hr : n - 10150 < 50 := by omega
          have heq : n = (n - 10150) + 10150 := by omega
          rw [heq]
          exact le_w203 ⟨n - 10150, hr⟩
        · by_cases h4 : n < 10250
          · have hr : n - 10200 < 50 := by omega
            have heq : n = (n - 10200) + 10200 := by omega
            rw [heq]
            exact le_w204 ⟨n - 10200, hr⟩
          · by_cases h5 : n < 10300
            · have hr : n - 10250 < 50 := by omega
              have heq : n = (n - 10250) + 10250 := by omega
              rw [heq]
              exact le_w205 ⟨n - 10250, hr⟩
            · by_cases h6 : n < 10350
              · have hr : n - 10300 < 50 := by omega
                have heq : n = (n - 10300) + 10300 := by omega
                rw [heq]
                exact le_w206 ⟨n - 10300, hr⟩
              · by_cases h7 : n < 10400
                · have hr : n - 10350 < 50 := by omega
                  have heq : n = (n - 10350) + 10350 := by omega
                  rw [heq]
                  exact le_w207 ⟨n - 10350, hr⟩
                · by_cases h8 : n < 10450
                  · have hr : n - 10400 < 50 := by omega
                    have heq : n = (n - 10400) + 10400 := by omega
                    rw [heq]
                    exact le_w208 ⟨n - 10400, hr⟩
                  · by_cases h9 : n < 10500
                    · have hr : n - 10450 < 50 := by omega
                      have heq : n = (n - 10450) + 10450 := by omega
                      rw [heq]
                      exact le_w209 ⟨n - 10450, hr⟩
                    · by_cases h10 : n < 10550
                      · have hr : n - 10500 < 50 := by omega
                        have heq : n = (n - 10500) + 10500 := by omega
                        rw [heq]
                        exact le_w210 ⟨n - 10500, hr⟩
                      · by_cases h11 : n < 10600
                        · have hr : n - 10550 < 50 := by omega
                          have heq : n = (n - 10550) + 10550 := by omega
                          rw [heq]
                          exact le_w211 ⟨n - 10550, hr⟩
                        · by_cases h12 : n < 10650
                          · have hr : n - 10600 < 50 := by omega
                            have heq : n = (n - 10600) + 10600 := by omega
                            rw [heq]
                            exact le_w212 ⟨n - 10600, hr⟩
                          · by_cases h13 : n < 10700
                            · have hr : n - 10650 < 50 := by omega
                              have heq : n = (n - 10650) + 10650 := by omega
                              rw [heq]
                              exact le_w213 ⟨n - 10650, hr⟩
                            · by_cases h14 : n < 10750
                              · have hr : n - 10700 < 50 := by omega
                                have heq : n = (n - 10700) + 10700 := by omega
                                rw [heq]
                                exact le_w214 ⟨n - 10700, hr⟩
                              · by_cases h15 : n < 10800
                                · have hr : n - 10750 < 50 := by omega
                                  have heq : n = (n - 10750) + 10750 := by omega
                                  rw [heq]
                                  exact le_w215 ⟨n - 10750, hr⟩
                                · by_cases h16 : n < 10850
                                  · have hr : n - 10800 < 50 := by omega
                                    have heq : n = (n - 10800) + 10800 := by omega
                                    rw [heq]
                                    exact le_w216 ⟨n - 10800, hr⟩
                                  · by_cases h17 : n < 10900
                                    · have hr : n - 10850 < 50 := by omega
                                      have heq : n = (n - 10850) + 10850 := by omega
                                      rw [heq]
                                      exact le_w217 ⟨n - 10850, hr⟩
                                    · by_cases h18 : n < 10950
                                      · have hr : n - 10900 < 50 := by omega
                                        have heq : n = (n - 10900) + 10900 := by omega
                                        rw [heq]
                                        exact le_w218 ⟨n - 10900, hr⟩
                                      · by_cases h19 : n < 11000
                                        · have hr : n - 10950 < 50 := by omega
                                          have heq : n = (n - 10950) + 10950 := by omega
                                          rw [heq]
                                          exact le_w219 ⟨n - 10950, hr⟩
                                        · by_cases h20 : n < 11050
                                          · have hr : n - 11000 < 50 := by omega
                                            have heq : n = (n - 11000) + 11000 := by omega
                                            rw [heq]
                                            exact le_w220 ⟨n - 11000, hr⟩
                                          · by_cases h21 : n < 11100
                                            · have hr : n - 11050 < 50 := by omega
                                              have heq : n = (n - 11050) + 11050 := by omega
                                              rw [heq]
                                              exact le_w221 ⟨n - 11050, hr⟩
                                            · by_cases h22 : n < 11150
                                              · have hr : n - 11100 < 50 := by omega
                                                have heq : n = (n - 11100) + 11100 := by omega
                                                rw [heq]
                                                exact le_w222 ⟨n - 11100, hr⟩
                                              · by_cases h23 : n < 11200
                                                · have hr : n - 11150 < 50 := by omega
                                                  have heq : n = (n - 11150) + 11150 := by omega
                                                  rw [heq]
                                                  exact le_w223 ⟨n - 11150, hr⟩
                                                · by_cases h24 : n < 11250
                                                  · have hr : n - 11200 < 50 := by omega
                                                    have heq : n = (n - 11200) + 11200 := by omega
                                                    rw [heq]
                                                    exact le_w224 ⟨n - 11200, hr⟩
                                                  · by_cases h25 : n < 11300
                                                    · have hr : n - 11250 < 50 := by omega
                                                      have heq : n = (n - 11250) + 11250 := by omega
                                                      rw [heq]
                                                      exact le_w225 ⟨n - 11250, hr⟩
                                                    · by_cases h26 : n < 11350
                                                      · have hr : n - 11300 < 50 := by omega
                                                        have heq : n = (n - 11300) + 11300 := by omega
                                                        rw [heq]
                                                        exact le_w226 ⟨n - 11300, hr⟩
                                                      · by_cases h27 : n < 11400
                                                        · have hr : n - 11350 < 50 := by omega
                                                          have heq : n = (n - 11350) + 11350 := by omega
                                                          rw [heq]
                                                          exact le_w227 ⟨n - 11350, hr⟩
                                                        · by_cases h28 : n < 11450
                                                          · have hr : n - 11400 < 50 := by omega
                                                            have heq : n = (n - 11400) + 11400 := by omega
                                                            rw [heq]
                                                            exact le_w228 ⟨n - 11400, hr⟩
                                                          · by_cases h29 : n < 11500
                                                            · have hr : n - 11450 < 50 := by omega
                                                              have heq : n = (n - 11450) + 11450 := by omega
                                                              rw [heq]
                                                              exact le_w229 ⟨n - 11450, hr⟩
                                                            · by_cases h30 : n < 11550
                                                              · have hr : n - 11500 < 50 := by omega
                                                                have heq : n = (n - 11500) + 11500 := by omega
                                                                rw [heq]
                                                                exact le_w230 ⟨n - 11500, hr⟩
                                                              · by_cases h31 : n < 11600
                                                                · have hr : n - 11550 < 50 := by omega
                                                                  have heq : n = (n - 11550) + 11550 := by omega
                                                                  rw [heq]
                                                                  exact le_w231 ⟨n - 11550, hr⟩
                                                                · by_cases h32 : n < 11650
                                                                  · have hr : n - 11600 < 50 := by omega
                                                                    have heq : n = (n - 11600) + 11600 := by omega
                                                                    rw [heq]
                                                                    exact le_w232 ⟨n - 11600, hr⟩
                                                                  · by_cases h33 : n < 11700
                                                                    · have hr : n - 11650 < 50 := by omega
                                                                      have heq : n = (n - 11650) + 11650 := by omega
                                                                      rw [heq]
                                                                      exact le_w233 ⟨n - 11650, hr⟩
                                                                    · by_cases h34 : n < 11750
                                                                      · have hr : n - 11700 < 50 := by omega
                                                                        have heq : n = (n - 11700) + 11700 := by omega
                                                                        rw [heq]
                                                                        exact le_w234 ⟨n - 11700, hr⟩
                                                                      · by_cases h35 : n < 11800
                                                                        · have hr : n - 11750 < 50 := by omega
                                                                          have heq : n = (n - 11750) + 11750 := by omega
                                                                          rw [heq]
                                                                          exact le_w235 ⟨n - 11750, hr⟩
                                                                        · by_cases h36 : n < 11850
                                                                          · have hr : n - 11800 < 50 := by omega
                                                                            have heq : n = (n - 11800) + 11800 := by omega
                                                                            rw [heq]
                                                                            exact le_w236 ⟨n - 11800, hr⟩
                                                                          · by_cases h37 : n < 11900
                                                                            · have hr : n - 11850 < 50 := by omega
                                                                              have heq : n = (n - 11850) + 11850 := by omega
                                                                              rw [heq]
                                                                              exact le_w237 ⟨n - 11850, hr⟩
                                                                            · by_cases h38 : n < 11950
                                                                              · have hr : n - 11900 < 50 := by omega
                                                                                have heq : n = (n - 11900) + 11900 := by omega
                                                                                rw [heq]
                                                                                exact le_w238 ⟨n - 11900, hr⟩
                                                                              · by_cases h39 : n < 12000
                                                                                · have hr : n - 11950 < 50 := by omega
                                                                                  have heq : n = (n - 11950) + 11950 := by omega
                                                                                  rw [heq]
                                                                                  exact le_w239 ⟨n - 11950, hr⟩
                                                                                · by_cases h40 : n < 12050
                                                                                  · have hr : n - 12000 < 50 := by omega
                                                                                    have heq : n = (n - 12000) + 12000 := by omega
                                                                                    rw [heq]
                                                                                    exact le_w240 ⟨n - 12000, hr⟩
                                                                                  · by_cases h41 : n < 12100
                                                                                    · have hr : n - 12050 < 50 := by omega
                                                                                      have heq : n = (n - 12050) + 12050 := by omega
                                                                                      rw [heq]
                                                                                      exact le_w241 ⟨n - 12050, hr⟩
                                                                                    · by_cases h42 : n < 12150
                                                                                      · have hr : n - 12100 < 50 := by omega
                                                                                        have heq : n = (n - 12100) + 12100 := by omega
                                                                                        rw [heq]
                                                                                        exact le_w242 ⟨n - 12100, hr⟩
                                                                                      · by_cases h43 : n < 12200
                                                                                        · have hr : n - 12150 < 50 := by omega
                                                                                          have heq : n = (n - 12150) + 12150 := by omega
                                                                                          rw [heq]
                                                                                          exact le_w243 ⟨n - 12150, hr⟩
                                                                                        · by_cases h44 : n < 12250
                                                                                          · have hr : n - 12200 < 50 := by omega
                                                                                            have heq : n = (n - 12200) + 12200 := by omega
                                                                                            rw [heq]
                                                                                            exact le_w244 ⟨n - 12200, hr⟩
                                                                                          · by_cases h45 : n < 12300
                                                                                            · have hr : n - 12250 < 50 := by omega
                                                                                              have heq : n = (n - 12250) + 12250 := by omega
                                                                                              rw [heq]
                                                                                              exact le_w245 ⟨n - 12250, hr⟩
                                                                                            · by_cases h46 : n < 12350
                                                                                              · have hr : n - 12300 < 50 := by omega
                                                                                                have heq : n = (n - 12300) + 12300 := by omega
                                                                                                rw [heq]
                                                                                                exact le_w246 ⟨n - 12300, hr⟩
                                                                                              · by_cases h47 : n < 12400
                                                                                                · have hr : n - 12350 < 50 := by omega
                                                                                                  have heq : n = (n - 12350) + 12350 := by omega
                                                                                                  rw [heq]
                                                                                                  exact le_w247 ⟨n - 12350, hr⟩
                                                                                                · by_cases h48 : n < 12450
                                                                                                  · have hr : n - 12400 < 50 := by omega
                                                                                                    have heq : n = (n - 12400) + 12400 := by omega
                                                                                                    rw [heq]
                                                                                                    exact le_w248 ⟨n - 12400, hr⟩
                                                                                                  · by_cases h49 : n < 12500
                                                                                                    · have hr : n - 12450 < 50 := by omega
                                                                                                      have heq : n = (n - 12450) + 12450 := by omega
                                                                                                      rw [heq]
                                                                                                      exact le_w249 ⟨n - 12450, hr⟩
                                                                                                    · by_cases h50 : n < 12550
                                                                                                      · have hr : n - 12500 < 50 := by omega
                                                                                                        have heq : n = (n - 12500) + 12500 := by omega
                                                                                                        rw [heq]
                                                                                                        exact le_w250 ⟨n - 12500, hr⟩
                                                                                                      · by_cases h51 : n < 12600
                                                                                                        · have hr : n - 12550 < 50 := by omega
                                                                                                          have heq : n = (n - 12550) + 12550 := by omega
                                                                                                          rw [heq]
                                                                                                          exact le_w251 ⟨n - 12550, hr⟩
                                                                                                        · by_cases h52 : n < 12650
                                                                                                          · have hr : n - 12600 < 50 := by omega
                                                                                                            have heq : n = (n - 12600) + 12600 := by omega
                                                                                                            rw [heq]
                                                                                                            exact le_w252 ⟨n - 12600, hr⟩
                                                                                                          · by_cases h53 : n < 12700
                                                                                                            · have hr : n - 12650 < 50 := by omega
                                                                                                              have heq : n = (n - 12650) + 12650 := by omega
                                                                                                              rw [heq]
                                                                                                              exact le_w253 ⟨n - 12650, hr⟩
                                                                                                            · by_cases h54 : n < 12750
                                                                                                              · have hr : n - 12700 < 50 := by omega
                                                                                                                have heq : n = (n - 12700) + 12700 := by omega
                                                                                                                rw [heq]
                                                                                                                exact le_w254 ⟨n - 12700, hr⟩
                                                                                                              · by_cases h55 : n < 12800
                                                                                                                · have hr : n - 12750 < 50 := by omega
                                                                                                                  have heq : n = (n - 12750) + 12750 := by omega
                                                                                                                  rw [heq]
                                                                                                                  exact le_w255 ⟨n - 12750, hr⟩
                                                                                                                · by_cases h56 : n < 12850
                                                                                                                  · have hr : n - 12800 < 50 := by omega
                                                                                                                    have heq : n = (n - 12800) + 12800 := by omega
                                                                                                                    rw [heq]
                                                                                                                    exact le_w256 ⟨n - 12800, hr⟩
                                                                                                                  · by_cases h57 : n < 12900
                                                                                                                    · have hr : n - 12850 < 50 := by omega
                                                                                                                      have heq : n = (n - 12850) + 12850 := by omega
                                                                                                                      rw [heq]
                                                                                                                      exact le_w257 ⟨n - 12850, hr⟩
                                                                                                                    · by_cases h58 : n < 12950
                                                                                                                      · have hr : n - 12900 < 50 := by omega
                                                                                                                        have heq : n = (n - 12900) + 12900 := by omega
                                                                                                                        rw [heq]
                                                                                                                        exact le_w258 ⟨n - 12900, hr⟩
                                                                                                                      · by_cases h59 : n < 13000
                                                                                                                        · have hr : n - 12950 < 50 := by omega
                                                                                                                          have heq : n = (n - 12950) + 12950 := by omega
                                                                                                                          rw [heq]
                                                                                                                          exact le_w259 ⟨n - 12950, hr⟩
                                                                                                                        · by_cases h60 : n < 13050
                                                                                                                          · have hr : n - 13000 < 50 := by omega
                                                                                                                            have heq : n = (n - 13000) + 13000 := by omega
                                                                                                                            rw [heq]
                                                                                                                            exact le_w260 ⟨n - 13000, hr⟩
                                                                                                                          · by_cases h61 : n < 13100
                                                                                                                            · have hr : n - 13050 < 50 := by omega
                                                                                                                              have heq : n = (n - 13050) + 13050 := by omega
                                                                                                                              rw [heq]
                                                                                                                              exact le_w261 ⟨n - 13050, hr⟩
                                                                                                                            · by_cases h62 : n < 13150
                                                                                                                              · have hr : n - 13100 < 50 := by omega
                                                                                                                                have heq : n = (n - 13100) + 13100 := by omega
                                                                                                                                rw [heq]
                                                                                                                                exact le_w262 ⟨n - 13100, hr⟩
                                                                                                                              · by_cases h63 : n < 13200
                                                                                                                                · have hr : n - 13150 < 50 := by omega
                                                                                                                                  have heq : n = (n - 13150) + 13150 := by omega
                                                                                                                                  rw [heq]
                                                                                                                                  exact le_w263 ⟨n - 13150, hr⟩
                                                                                                                                · by_cases h64 : n < 13250
                                                                                                                                  · have hr : n - 13200 < 50 := by omega
                                                                                                                                    have heq : n = (n - 13200) + 13200 := by omega
                                                                                                                                    rw [heq]
                                                                                                                                    exact le_w264 ⟨n - 13200, hr⟩
                                                                                                                                  · by_cases h65 : n < 13300
                                                                                                                                    · have hr : n - 13250 < 50 := by omega
                                                                                                                                      have heq : n = (n - 13250) + 13250 := by omega
                                                                                                                                      rw [heq]
                                                                                                                                      exact le_w265 ⟨n - 13250, hr⟩
                                                                                                                                    · by_cases h66 : n < 13350
                                                                                                                                      · have hr : n - 13300 < 50 := by omega
                                                                                                                                        have heq : n = (n - 13300) + 13300 := by omega
                                                                                                                                        rw [heq]
                                                                                                                                        exact le_w266 ⟨n - 13300, hr⟩
                                                                                                                                      · by_cases h67 : n < 13400
                                                                                                                                        · have hr : n - 13350 < 50 := by omega
                                                                                                                                          have heq : n = (n - 13350) + 13350 := by omega
                                                                                                                                          rw [heq]
                                                                                                                                          exact le_w267 ⟨n - 13350, hr⟩
                                                                                                                                        · by_cases h68 : n < 13450
                                                                                                                                          · have hr : n - 13400 < 50 := by omega
                                                                                                                                            have heq : n = (n - 13400) + 13400 := by omega
                                                                                                                                            rw [heq]
                                                                                                                                            exact le_w268 ⟨n - 13400, hr⟩
                                                                                                                                          · by_cases h69 : n < 13500
                                                                                                                                            · have hr : n - 13450 < 50 := by omega
                                                                                                                                              have heq : n = (n - 13450) + 13450 := by omega
                                                                                                                                              rw [heq]
                                                                                                                                              exact le_w269 ⟨n - 13450, hr⟩
                                                                                                                                            · by_cases h70 : n < 13550
                                                                                                                                              · have hr : n - 13500 < 50 := by omega
                                                                                                                                                have heq : n = (n - 13500) + 13500 := by omega
                                                                                                                                                rw [heq]
                                                                                                                                                exact le_w270 ⟨n - 13500, hr⟩
                                                                                                                                              · by_cases h71 : n < 13600
                                                                                                                                                · have hr : n - 13550 < 50 := by omega
                                                                                                                                                  have heq : n = (n - 13550) + 13550 := by omega
                                                                                                                                                  rw [heq]
                                                                                                                                                  exact le_w271 ⟨n - 13550, hr⟩
                                                                                                                                                · by_cases h72 : n < 13650
                                                                                                                                                  · have hr : n - 13600 < 50 := by omega
                                                                                                                                                    have heq : n = (n - 13600) + 13600 := by omega
                                                                                                                                                    rw [heq]
                                                                                                                                                    exact le_w272 ⟨n - 13600, hr⟩
                                                                                                                                                  · by_cases h73 : n < 13700
                                                                                                                                                    · have hr : n - 13650 < 50 := by omega
                                                                                                                                                      have heq : n = (n - 13650) + 13650 := by omega
                                                                                                                                                      rw [heq]
                                                                                                                                                      exact le_w273 ⟨n - 13650, hr⟩
                                                                                                                                                    · by_cases h74 : n < 13750
                                                                                                                                                      · have hr : n - 13700 < 50 := by omega
                                                                                                                                                        have heq : n = (n - 13700) + 13700 := by omega
                                                                                                                                                        rw [heq]
                                                                                                                                                        exact le_w274 ⟨n - 13700, hr⟩
                                                                                                                                                      · by_cases h75 : n < 13800
                                                                                                                                                        · have hr : n - 13750 < 50 := by omega
                                                                                                                                                          have heq : n = (n - 13750) + 13750 := by omega
                                                                                                                                                          rw [heq]
                                                                                                                                                          exact le_w275 ⟨n - 13750, hr⟩
                                                                                                                                                        · by_cases h76 : n < 13850
                                                                                                                                                          · have hr : n - 13800 < 50 := by omega
                                                                                                                                                            have heq : n = (n - 13800) + 13800 := by omega
                                                                                                                                                            rw [heq]
                                                                                                                                                            exact le_w276 ⟨n - 13800, hr⟩
                                                                                                                                                          · by_cases h77 : n < 13900
                                                                                                                                                            · have hr : n - 13850 < 50 := by omega
                                                                                                                                                              have heq : n = (n - 13850) + 13850 := by omega
                                                                                                                                                              rw [heq]
                                                                                                                                                              exact le_w277 ⟨n - 13850, hr⟩
                                                                                                                                                            · by_cases h78 : n < 13950
                                                                                                                                                              · have hr : n - 13900 < 50 := by omega
                                                                                                                                                                have heq : n = (n - 13900) + 13900 := by omega
                                                                                                                                                                rw [heq]
                                                                                                                                                                exact le_w278 ⟨n - 13900, hr⟩
                                                                                                                                                              · by_cases h79 : n < 14000
                                                                                                                                                                · have hr : n - 13950 < 50 := by omega
                                                                                                                                                                  have heq : n = (n - 13950) + 13950 := by omega
                                                                                                                                                                  rw [heq]
                                                                                                                                                                  exact le_w279 ⟨n - 13950, hr⟩
                                                                                                                                                                · by_cases h80 : n < 14050
                                                                                                                                                                  · have hr : n - 14000 < 50 := by omega
                                                                                                                                                                    have heq : n = (n - 14000) + 14000 := by omega
                                                                                                                                                                    rw [heq]
                                                                                                                                                                    exact le_w280 ⟨n - 14000, hr⟩
                                                                                                                                                                  · by_cases h81 : n < 14100
                                                                                                                                                                    · have hr : n - 14050 < 50 := by omega
                                                                                                                                                                      have heq : n = (n - 14050) + 14050 := by omega
                                                                                                                                                                      rw [heq]
                                                                                                                                                                      exact le_w281 ⟨n - 14050, hr⟩
                                                                                                                                                                    · by_cases h82 : n < 14150
                                                                                                                                                                      · have hr : n - 14100 < 50 := by omega
                                                                                                                                                                        have heq : n = (n - 14100) + 14100 := by omega
                                                                                                                                                                        rw [heq]
                                                                                                                                                                        exact le_w282 ⟨n - 14100, hr⟩
                                                                                                                                                                      · by_cases h83 : n < 14200
                                                                                                                                                                        · have hr : n - 14150 < 50 := by omega
                                                                                                                                                                          have heq : n = (n - 14150) + 14150 := by omega
                                                                                                                                                                          rw [heq]
                                                                                                                                                                          exact le_w283 ⟨n - 14150, hr⟩
                                                                                                                                                                        · by_cases h84 : n < 14250
                                                                                                                                                                          · have hr : n - 14200 < 50 := by omega
                                                                                                                                                                            have heq : n = (n - 14200) + 14200 := by omega
                                                                                                                                                                            rw [heq]
                                                                                                                                                                            exact le_w284 ⟨n - 14200, hr⟩
                                                                                                                                                                          · by_cases h85 : n < 14300
                                                                                                                                                                            · have hr : n - 14250 < 50 := by omega
                                                                                                                                                                              have heq : n = (n - 14250) + 14250 := by omega
                                                                                                                                                                              rw [heq]
                                                                                                                                                                              exact le_w285 ⟨n - 14250, hr⟩
                                                                                                                                                                            · by_cases h86 : n < 14350
                                                                                                                                                                              · have hr : n - 14300 < 50 := by omega
                                                                                                                                                                                have heq : n = (n - 14300) + 14300 := by omega
                                                                                                                                                                                rw [heq]
                                                                                                                                                                                exact le_w286 ⟨n - 14300, hr⟩
                                                                                                                                                                              · by_cases h87 : n < 14400
                                                                                                                                                                                · have hr : n - 14350 < 50 := by omega
                                                                                                                                                                                  have heq : n = (n - 14350) + 14350 := by omega
                                                                                                                                                                                  rw [heq]
                                                                                                                                                                                  exact le_w287 ⟨n - 14350, hr⟩
                                                                                                                                                                                · by_cases h88 : n < 14450
                                                                                                                                                                                  · have hr : n - 14400 < 50 := by omega
                                                                                                                                                                                    have heq : n = (n - 14400) + 14400 := by omega
                                                                                                                                                                                    rw [heq]
                                                                                                                                                                                    exact le_w288 ⟨n - 14400, hr⟩
                                                                                                                                                                                  · by_cases h89 : n < 14500
                                                                                                                                                                                    · have hr : n - 14450 < 50 := by omega
                                                                                                                                                                                      have heq : n = (n - 14450) + 14450 := by omega
                                                                                                                                                                                      rw [heq]
                                                                                                                                                                                      exact le_w289 ⟨n - 14450, hr⟩
                                                                                                                                                                                    · by_cases h90 : n < 14550
                                                                                                                                                                                      · have hr : n - 14500 < 50 := by omega
                                                                                                                                                                                        have heq : n = (n - 14500) + 14500 := by omega
                                                                                                                                                                                        rw [heq]
                                                                                                                                                                                        exact le_w290 ⟨n - 14500, hr⟩
                                                                                                                                                                                      · by_cases h91 : n < 14600
                                                                                                                                                                                        · have hr : n - 14550 < 50 := by omega
                                                                                                                                                                                          have heq : n = (n - 14550) + 14550 := by omega
                                                                                                                                                                                          rw [heq]
                                                                                                                                                                                          exact le_w291 ⟨n - 14550, hr⟩
                                                                                                                                                                                        · by_cases h92 : n < 14650
                                                                                                                                                                                          · have hr : n - 14600 < 50 := by omega
                                                                                                                                                                                            have heq : n = (n - 14600) + 14600 := by omega
                                                                                                                                                                                            rw [heq]
                                                                                                                                                                                            exact le_w292 ⟨n - 14600, hr⟩
                                                                                                                                                                                          · by_cases h93 : n < 14700
                                                                                                                                                                                            · have hr : n - 14650 < 50 := by omega
                                                                                                                                                                                              have heq : n = (n - 14650) + 14650 := by omega
                                                                                                                                                                                              rw [heq]
                                                                                                                                                                                              exact le_w293 ⟨n - 14650, hr⟩
                                                                                                                                                                                            · by_cases h94 : n < 14750
                                                                                                                                                                                              · have hr : n - 14700 < 50 := by omega
                                                                                                                                                                                                have heq : n = (n - 14700) + 14700 := by omega
                                                                                                                                                                                                rw [heq]
                                                                                                                                                                                                exact le_w294 ⟨n - 14700, hr⟩
                                                                                                                                                                                              · by_cases h95 : n < 14800
                                                                                                                                                                                                · have hr : n - 14750 < 50 := by omega
                                                                                                                                                                                                  have heq : n = (n - 14750) + 14750 := by omega
                                                                                                                                                                                                  rw [heq]
                                                                                                                                                                                                  exact le_w295 ⟨n - 14750, hr⟩
                                                                                                                                                                                                · by_cases h96 : n < 14850
                                                                                                                                                                                                  · have hr : n - 14800 < 50 := by omega
                                                                                                                                                                                                    have heq : n = (n - 14800) + 14800 := by omega
                                                                                                                                                                                                    rw [heq]
                                                                                                                                                                                                    exact le_w296 ⟨n - 14800, hr⟩
                                                                                                                                                                                                  · by_cases h97 : n < 14900
                                                                                                                                                                                                    · have hr : n - 14850 < 50 := by omega
                                                                                                                                                                                                      have heq : n = (n - 14850) + 14850 := by omega
                                                                                                                                                                                                      rw [heq]
                                                                                                                                                                                                      exact le_w297 ⟨n - 14850, hr⟩
                                                                                                                                                                                                    · by_cases h98 : n < 14950
                                                                                                                                                                                                      · have hr : n - 14900 < 50 := by omega
                                                                                                                                                                                                        have heq : n = (n - 14900) + 14900 := by omega
                                                                                                                                                                                                        rw [heq]
                                                                                                                                                                                                        exact le_w298 ⟨n - 14900, hr⟩
                                                                                                                                                                                                      · by_cases h99 : n < 15000
                                                                                                                                                                                                        · have hr : n - 14950 < 50 := by omega
                                                                                                                                                                                                          have heq : n = (n - 14950) + 14950 := by omega
                                                                                                                                                                                                          rw [heq]
                                                                                                                                                                                                          exact le_w299 ⟨n - 14950, hr⟩
                                                                                                                                                                                                        · omega

theorem dimF_pos_range : ∀ n, 10000 ≤ n → n < 15000 → 0 < dimF n := by
  intro n hlo hhi
  by_cases h0 : n < 10050
  · have hr : n - 10000 < 50 := by omega
    have heq : n = (n - 10000) + 10000 := by omega
    rw [heq]
    exact pos_w200 ⟨n - 10000, hr⟩
  · by_cases h1 : n < 10100
    · have hr : n - 10050 < 50 := by omega
      have heq : n = (n - 10050) + 10050 := by omega
      rw [heq]
      exact pos_w201 ⟨n - 10050, hr⟩
    · by_cases h2 : n < 10150
      · have hr : n - 10100 < 50 := by omega
        have heq : n = (n - 10100) + 10100 := by omega
        rw [heq]
        exact pos_w202 ⟨n - 10100, hr⟩
      · by_cases h3 : n < 10200
        · have hr : n - 10150 < 50 := by omega
          have heq : n = (n - 10150) + 10150 := by omega
          rw [heq]
          exact pos_w203 ⟨n - 10150, hr⟩
        · by_cases h4 : n < 10250
          · have hr : n - 10200 < 50 := by omega
            have heq : n = (n - 10200) + 10200 := by omega
            rw [heq]
            exact pos_w204 ⟨n - 10200, hr⟩
          · by_cases h5 : n < 10300
            · have hr : n - 10250 < 50 := by omega
              have heq : n = (n - 10250) + 10250 := by omega
              rw [heq]
              exact pos_w205 ⟨n - 10250, hr⟩
            · by_cases h6 : n < 10350
              · have hr : n - 10300 < 50 := by omega
                have heq : n = (n - 10300) + 10300 := by omega
                rw [heq]
                exact pos_w206 ⟨n - 10300, hr⟩
              · by_cases h7 : n < 10400
                · have hr : n - 10350 < 50 := by omega
                  have heq : n = (n - 10350) + 10350 := by omega
                  rw [heq]
                  exact pos_w207 ⟨n - 10350, hr⟩
                · by_cases h8 : n < 10450
                  · have hr : n - 10400 < 50 := by omega
                    have heq : n = (n - 10400) + 10400 := by omega
                    rw [heq]
                    exact pos_w208 ⟨n - 10400, hr⟩
                  · by_cases h9 : n < 10500
                    · have hr : n - 10450 < 50 := by omega
                      have heq : n = (n - 10450) + 10450 := by omega
                      rw [heq]
                      exact pos_w209 ⟨n - 10450, hr⟩
                    · by_cases h10 : n < 10550
                      · have hr : n - 10500 < 50 := by omega
                        have heq : n = (n - 10500) + 10500 := by omega
                        rw [heq]
                        exact pos_w210 ⟨n - 10500, hr⟩
                      · by_cases h11 : n < 10600
                        · have hr : n - 10550 < 50 := by omega
                          have heq : n = (n - 10550) + 10550 := by omega
                          rw [heq]
                          exact pos_w211 ⟨n - 10550, hr⟩
                        · by_cases h12 : n < 10650
                          · have hr : n - 10600 < 50 := by omega
                            have heq : n = (n - 10600) + 10600 := by omega
                            rw [heq]
                            exact pos_w212 ⟨n - 10600, hr⟩
                          · by_cases h13 : n < 10700
                            · have hr : n - 10650 < 50 := by omega
                              have heq : n = (n - 10650) + 10650 := by omega
                              rw [heq]
                              exact pos_w213 ⟨n - 10650, hr⟩
                            · by_cases h14 : n < 10750
                              · have hr : n - 10700 < 50 := by omega
                                have heq : n = (n - 10700) + 10700 := by omega
                                rw [heq]
                                exact pos_w214 ⟨n - 10700, hr⟩
                              · by_cases h15 : n < 10800
                                · have hr : n - 10750 < 50 := by omega
                                  have heq : n = (n - 10750) + 10750 := by omega
                                  rw [heq]
                                  exact pos_w215 ⟨n - 10750, hr⟩
                                · by_cases h16 : n < 10850
                                  · have hr : n - 10800 < 50 := by omega
                                    have heq : n = (n - 10800) + 10800 := by omega
                                    rw [heq]
                                    exact pos_w216 ⟨n - 10800, hr⟩
                                  · by_cases h17 : n < 10900
                                    · have hr : n - 10850 < 50 := by omega
                                      have heq : n = (n - 10850) + 10850 := by omega
                                      rw [heq]
                                      exact pos_w217 ⟨n - 10850, hr⟩
                                    · by_cases h18 : n < 10950
                                      · have hr : n - 10900 < 50 := by omega
                                        have heq : n = (n - 10900) + 10900 := by omega
                                        rw [heq]
                                        exact pos_w218 ⟨n - 10900, hr⟩
                                      · by_cases h19 : n < 11000
                                        · have hr : n - 10950 < 50 := by omega
                                          have heq : n = (n - 10950) + 10950 := by omega
                                          rw [heq]
                                          exact pos_w219 ⟨n - 10950, hr⟩
                                        · by_cases h20 : n < 11050
                                          · have hr : n - 11000 < 50 := by omega
                                            have heq : n = (n - 11000) + 11000 := by omega
                                            rw [heq]
                                            exact pos_w220 ⟨n - 11000, hr⟩
                                          · by_cases h21 : n < 11100
                                            · have hr : n - 11050 < 50 := by omega
                                              have heq : n = (n - 11050) + 11050 := by omega
                                              rw [heq]
                                              exact pos_w221 ⟨n - 11050, hr⟩
                                            · by_cases h22 : n < 11150
                                              · have hr : n - 11100 < 50 := by omega
                                                have heq : n = (n - 11100) + 11100 := by omega
                                                rw [heq]
                                                exact pos_w222 ⟨n - 11100, hr⟩
                                              · by_cases h23 : n < 11200
                                                · have hr : n - 11150 < 50 := by omega
                                                  have heq : n = (n - 11150) + 11150 := by omega
                                                  rw [heq]
                                                  exact pos_w223 ⟨n - 11150, hr⟩
                                                · by_cases h24 : n < 11250
                                                  · have hr : n - 11200 < 50 := by omega
                                                    have heq : n = (n - 11200) + 11200 := by omega
                                                    rw [heq]
                                                    exact pos_w224 ⟨n - 11200, hr⟩
                                                  · by_cases h25 : n < 11300
                                                    · have hr : n - 11250 < 50 := by omega
                                                      have heq : n = (n - 11250) + 11250 := by omega
                                                      rw [heq]
                                                      exact pos_w225 ⟨n - 11250, hr⟩
                                                    · by_cases h26 : n < 11350
                                                      · have hr : n - 11300 < 50 := by omega
                                                        have heq : n = (n - 11300) + 11300 := by omega
                                                        rw [heq]
                                                        exact pos_w226 ⟨n - 11300, hr⟩
                                                      · by_cases h27 : n < 11400
                                                        · have hr : n - 11350 < 50 := by omega
                                                          have heq : n = (n - 11350) + 11350 := by omega
                                                          rw [heq]
                                                          exact pos_w227 ⟨n - 11350, hr⟩
                                                        · by_cases h28 : n < 11450
                                                          · have hr : n - 11400 < 50 := by omega
                                                            have heq : n = (n - 11400) + 11400 := by omega
                                                            rw [heq]
                                                            exact pos_w228 ⟨n - 11400, hr⟩
                                                          · by_cases h29 : n < 11500
                                                            · have hr : n - 11450 < 50 := by omega
                                                              have heq : n = (n - 11450) + 11450 := by omega
                                                              rw [heq]
                                                              exact pos_w229 ⟨n - 11450, hr⟩
                                                            · by_cases h30 : n < 11550
                                                              · have hr : n - 11500 < 50 := by omega
                                                                have heq : n = (n - 11500) + 11500 := by omega
                                                                rw [heq]
                                                                exact pos_w230 ⟨n - 11500, hr⟩
                                                              · by_cases h31 : n < 11600
                                                                · have hr : n - 11550 < 50 := by omega
                                                                  have heq : n = (n - 11550) + 11550 := by omega
                                                                  rw [heq]
                                                                  exact pos_w231 ⟨n - 11550, hr⟩
                                                                · by_cases h32 : n < 11650
                                                                  · have hr : n - 11600 < 50 := by omega
                                                                    have heq : n = (n - 11600) + 11600 := by omega
                                                                    rw [heq]
                                                                    exact pos_w232 ⟨n - 11600, hr⟩
                                                                  · by_cases h33 : n < 11700
                                                                    · have hr : n - 11650 < 50 := by omega
                                                                      have heq : n = (n - 11650) + 11650 := by omega
                                                                      rw [heq]
                                                                      exact pos_w233 ⟨n - 11650, hr⟩
                                                                    · by_cases h34 : n < 11750
                                                                      · have hr : n - 11700 < 50 := by omega
                                                                        have heq : n = (n - 11700) + 11700 := by omega
                                                                        rw [heq]
                                                                        exact pos_w234 ⟨n - 11700, hr⟩
                                                                      · by_cases h35 : n < 11800
                                                                        · have hr : n - 11750 < 50 := by omega
                                                                          have heq : n = (n - 11750) + 11750 := by omega
                                                                          rw [heq]
                                                                          exact pos_w235 ⟨n - 11750, hr⟩
                                                                        · by_cases h36 : n < 11850
                                                                          · have hr : n - 11800 < 50 := by omega
                                                                            have heq : n = (n - 11800) + 11800 := by omega
                                                                            rw [heq]
                                                                            exact pos_w236 ⟨n - 11800, hr⟩
                                                                          · by_cases h37 : n < 11900
                                                                            · have hr : n - 11850 < 50 := by omega
                                                                              have heq : n = (n - 11850) + 11850 := by omega
                                                                              rw [heq]
                                                                              exact pos_w237 ⟨n - 11850, hr⟩
                                                                            · by_cases h38 : n < 11950
                                                                              · have hr : n - 11900 < 50 := by omega
                                                                                have heq : n = (n - 11900) + 11900 := by omega
                                                                                rw [heq]
                                                                                exact pos_w238 ⟨n - 11900, hr⟩
                                                                              · by_cases h39 : n < 12000
                                                                                · have hr : n - 11950 < 50 := by omega
                                                                                  have heq : n = (n - 11950) + 11950 := by omega
                                                                                  rw [heq]
                                                                                  exact pos_w239 ⟨n - 11950, hr⟩
                                                                                · by_cases h40 : n < 12050
                                                                                  · have hr : n - 12000 < 50 := by omega
                                                                                    have heq : n = (n - 12000) + 12000 := by omega
                                                                                    rw [heq]
                                                                                    exact pos_w240 ⟨n - 12000, hr⟩
                                                                                  · by_cases h41 : n < 12100
                                                                                    · have hr : n - 12050 < 50 := by omega
                                                                                      have heq : n = (n - 12050) + 12050 := by omega
                                                                                      rw [heq]
                                                                                      exact pos_w241 ⟨n - 12050, hr⟩
                                                                                    · by_cases h42 : n < 12150
                                                                                      · have hr : n - 12100 < 50 := by omega
                                                                                        have heq : n = (n - 12100) + 12100 := by omega
                                                                                        rw [heq]
                                                                                        exact pos_w242 ⟨n - 12100, hr⟩
                                                                                      · by_cases h43 : n < 12200
                                                                                        · have hr : n - 12150 < 50 := by omega
                                                                                          have heq : n = (n - 12150) + 12150 := by omega
                                                                                          rw [heq]
                                                                                          exact pos_w243 ⟨n - 12150, hr⟩
                                                                                        · by_cases h44 : n < 12250
                                                                                          · have hr : n - 12200 < 50 := by omega
                                                                                            have heq : n = (n - 12200) + 12200 := by omega
                                                                                            rw [heq]
                                                                                            exact pos_w244 ⟨n - 12200, hr⟩
                                                                                          · by_cases h45 : n < 12300
                                                                                            · have hr : n - 12250 < 50 := by omega
                                                                                              have heq : n = (n - 12250) + 12250 := by omega
                                                                                              rw [heq]
                                                                                              exact pos_w245 ⟨n - 12250, hr⟩
                                                                                            · by_cases h46 : n < 12350
                                                                                              · have hr : n - 12300 < 50 := by omega
                                                                                                have heq : n = (n - 12300) + 12300 := by omega
                                                                                                rw [heq]
                                                                                                exact pos_w246 ⟨n - 12300, hr⟩
                                                                                              · by_cases h47 : n < 12400
                                                                                                · have hr : n - 12350 < 50 := by omega
                                                                                                  have heq : n = (n - 12350) + 12350 := by omega
                                                                                                  rw [heq]
                                                                                                  exact pos_w247 ⟨n - 12350, hr⟩
                                                                                                · by_cases h48 : n < 12450
                                                                                                  · have hr : n - 12400 < 50 := by omega
                                                                                                    have heq : n = (n - 12400) + 12400 := by omega
                                                                                                    rw [heq]
                                                                                                    exact pos_w248 ⟨n - 12400, hr⟩
                                                                                                  · by_cases h49 : n < 12500
                                                                                                    · have hr : n - 12450 < 50 := by omega
                                                                                                      have heq : n = (n - 12450) + 12450 := by omega
                                                                                                      rw [heq]
                                                                                                      exact pos_w249 ⟨n - 12450, hr⟩
                                                                                                    · by_cases h50 : n < 12550
                                                                                                      · have hr : n - 12500 < 50 := by omega
                                                                                                        have heq : n = (n - 12500) + 12500 := by omega
                                                                                                        rw [heq]
                                                                                                        exact pos_w250 ⟨n - 12500, hr⟩
                                                                                                      · by_cases h51 : n < 12600
                                                                                                        · have hr : n - 12550 < 50 := by omega
                                                                                                          have heq : n = (n - 12550) + 12550 := by omega
                                                                                                          rw [heq]
                                                                                                          exact pos_w251 ⟨n - 12550, hr⟩
                                                                                                        · by_cases h52 : n < 12650
                                                                                                          · have hr : n - 12600 < 50 := by omega
                                                                                                            have heq : n = (n - 12600) + 12600 := by omega
                                                                                                            rw [heq]
                                                                                                            exact pos_w252 ⟨n - 12600, hr⟩
                                                                                                          · by_cases h53 : n < 12700
                                                                                                            · have hr : n - 12650 < 50 := by omega
                                                                                                              have heq : n = (n - 12650) + 12650 := by omega
                                                                                                              rw [heq]
                                                                                                              exact pos_w253 ⟨n - 12650, hr⟩
                                                                                                            · by_cases h54 : n < 12750
                                                                                                              · have hr : n - 12700 < 50 := by omega
                                                                                                                have heq : n = (n - 12700) + 12700 := by omega
                                                                                                                rw [heq]
                                                                                                                exact pos_w254 ⟨n - 12700, hr⟩
                                                                                                              · by_cases h55 : n < 12800
                                                                                                                · have hr : n - 12750 < 50 := by omega
                                                                                                                  have heq : n = (n - 12750) + 12750 := by omega
                                                                                                                  rw [heq]
                                                                                                                  exact pos_w255 ⟨n - 12750, hr⟩
                                                                                                                · by_cases h56 : n < 12850
                                                                                                                  · have hr : n - 12800 < 50 := by omega
                                                                                                                    have heq : n = (n - 12800) + 12800 := by omega
                                                                                                                    rw [heq]
                                                                                                                    exact pos_w256 ⟨n - 12800, hr⟩
                                                                                                                  · by_cases h57 : n < 12900
                                                                                                                    · have hr : n - 12850 < 50 := by omega
                                                                                                                      have heq : n = (n - 12850) + 12850 := by omega
                                                                                                                      rw [heq]
                                                                                                                      exact pos_w257 ⟨n - 12850, hr⟩
                                                                                                                    · by_cases h58 : n < 12950
                                                                                                                      · have hr : n - 12900 < 50 := by omega
                                                                                                                        have heq : n = (n - 12900) + 12900 := by omega
                                                                                                                        rw [heq]
                                                                                                                        exact pos_w258 ⟨n - 12900, hr⟩
                                                                                                                      · by_cases h59 : n < 13000
                                                                                                                        · have hr : n - 12950 < 50 := by omega
                                                                                                                          have heq : n = (n - 12950) + 12950 := by omega
                                                                                                                          rw [heq]
                                                                                                                          exact pos_w259 ⟨n - 12950, hr⟩
                                                                                                                        · by_cases h60 : n < 13050
                                                                                                                          · have hr : n - 13000 < 50 := by omega
                                                                                                                            have heq : n = (n - 13000) + 13000 := by omega
                                                                                                                            rw [heq]
                                                                                                                            exact pos_w260 ⟨n - 13000, hr⟩
                                                                                                                          · by_cases h61 : n < 13100
                                                                                                                            · have hr : n - 13050 < 50 := by omega
                                                                                                                              have heq : n = (n - 13050) + 13050 := by omega
                                                                                                                              rw [heq]
                                                                                                                              exact pos_w261 ⟨n - 13050, hr⟩
                                                                                                                            · by_cases h62 : n < 13150
                                                                                                                              · have hr : n - 13100 < 50 := by omega
                                                                                                                                have heq : n = (n - 13100) + 13100 := by omega
                                                                                                                                rw [heq]
                                                                                                                                exact pos_w262 ⟨n - 13100, hr⟩
                                                                                                                              · by_cases h63 : n < 13200
                                                                                                                                · have hr : n - 13150 < 50 := by omega
                                                                                                                                  have heq : n = (n - 13150) + 13150 := by omega
                                                                                                                                  rw [heq]
                                                                                                                                  exact pos_w263 ⟨n - 13150, hr⟩
                                                                                                                                · by_cases h64 : n < 13250
                                                                                                                                  · have hr : n - 13200 < 50 := by omega
                                                                                                                                    have heq : n = (n - 13200) + 13200 := by omega
                                                                                                                                    rw [heq]
                                                                                                                                    exact pos_w264 ⟨n - 13200, hr⟩
                                                                                                                                  · by_cases h65 : n < 13300
                                                                                                                                    · have hr : n - 13250 < 50 := by omega
                                                                                                                                      have heq : n = (n - 13250) + 13250 := by omega
                                                                                                                                      rw [heq]
                                                                                                                                      exact pos_w265 ⟨n - 13250, hr⟩
                                                                                                                                    · by_cases h66 : n < 13350
                                                                                                                                      · have hr : n - 13300 < 50 := by omega
                                                                                                                                        have heq : n = (n - 13300) + 13300 := by omega
                                                                                                                                        rw [heq]
                                                                                                                                        exact pos_w266 ⟨n - 13300, hr⟩
                                                                                                                                      · by_cases h67 : n < 13400
                                                                                                                                        · have hr : n - 13350 < 50 := by omega
                                                                                                                                          have heq : n = (n - 13350) + 13350 := by omega
                                                                                                                                          rw [heq]
                                                                                                                                          exact pos_w267 ⟨n - 13350, hr⟩
                                                                                                                                        · by_cases h68 : n < 13450
                                                                                                                                          · have hr : n - 13400 < 50 := by omega
                                                                                                                                            have heq : n = (n - 13400) + 13400 := by omega
                                                                                                                                            rw [heq]
                                                                                                                                            exact pos_w268 ⟨n - 13400, hr⟩
                                                                                                                                          · by_cases h69 : n < 13500
                                                                                                                                            · have hr : n - 13450 < 50 := by omega
                                                                                                                                              have heq : n = (n - 13450) + 13450 := by omega
                                                                                                                                              rw [heq]
                                                                                                                                              exact pos_w269 ⟨n - 13450, hr⟩
                                                                                                                                            · by_cases h70 : n < 13550
                                                                                                                                              · have hr : n - 13500 < 50 := by omega
                                                                                                                                                have heq : n = (n - 13500) + 13500 := by omega
                                                                                                                                                rw [heq]
                                                                                                                                                exact pos_w270 ⟨n - 13500, hr⟩
                                                                                                                                              · by_cases h71 : n < 13600
                                                                                                                                                · have hr : n - 13550 < 50 := by omega
                                                                                                                                                  have heq : n = (n - 13550) + 13550 := by omega
                                                                                                                                                  rw [heq]
                                                                                                                                                  exact pos_w271 ⟨n - 13550, hr⟩
                                                                                                                                                · by_cases h72 : n < 13650
                                                                                                                                                  · have hr : n - 13600 < 50 := by omega
                                                                                                                                                    have heq : n = (n - 13600) + 13600 := by omega
                                                                                                                                                    rw [heq]
                                                                                                                                                    exact pos_w272 ⟨n - 13600, hr⟩
                                                                                                                                                  · by_cases h73 : n < 13700
                                                                                                                                                    · have hr : n - 13650 < 50 := by omega
                                                                                                                                                      have heq : n = (n - 13650) + 13650 := by omega
                                                                                                                                                      rw [heq]
                                                                                                                                                      exact pos_w273 ⟨n - 13650, hr⟩
                                                                                                                                                    · by_cases h74 : n < 13750
                                                                                                                                                      · have hr : n - 13700 < 50 := by omega
                                                                                                                                                        have heq : n = (n - 13700) + 13700 := by omega
                                                                                                                                                        rw [heq]
                                                                                                                                                        exact pos_w274 ⟨n - 13700, hr⟩
                                                                                                                                                      · by_cases h75 : n < 13800
                                                                                                                                                        · have hr : n - 13750 < 50 := by omega
                                                                                                                                                          have heq : n = (n - 13750) + 13750 := by omega
                                                                                                                                                          rw [heq]
                                                                                                                                                          exact pos_w275 ⟨n - 13750, hr⟩
                                                                                                                                                        · by_cases h76 : n < 13850
                                                                                                                                                          · have hr : n - 13800 < 50 := by omega
                                                                                                                                                            have heq : n = (n - 13800) + 13800 := by omega
                                                                                                                                                            rw [heq]
                                                                                                                                                            exact pos_w276 ⟨n - 13800, hr⟩
                                                                                                                                                          · by_cases h77 : n < 13900
                                                                                                                                                            · have hr : n - 13850 < 50 := by omega
                                                                                                                                                              have heq : n = (n - 13850) + 13850 := by omega
                                                                                                                                                              rw [heq]
                                                                                                                                                              exact pos_w277 ⟨n - 13850, hr⟩
                                                                                                                                                            · by_cases h78 : n < 13950
                                                                                                                                                              · have hr : n - 13900 < 50 := by omega
                                                                                                                                                                have heq : n = (n - 13900) + 13900 := by omega
                                                                                                                                                                rw [heq]
                                                                                                                                                                exact pos_w278 ⟨n - 13900, hr⟩
                                                                                                                                                              · by_cases h79 : n < 14000
                                                                                                                                                                · have hr : n - 13950 < 50 := by omega
                                                                                                                                                                  have heq : n = (n - 13950) + 13950 := by omega
                                                                                                                                                                  rw [heq]
                                                                                                                                                                  exact pos_w279 ⟨n - 13950, hr⟩
                                                                                                                                                                · by_cases h80 : n < 14050
                                                                                                                                                                  · have hr : n - 14000 < 50 := by omega
                                                                                                                                                                    have heq : n = (n - 14000) + 14000 := by omega
                                                                                                                                                                    rw [heq]
                                                                                                                                                                    exact pos_w280 ⟨n - 14000, hr⟩
                                                                                                                                                                  · by_cases h81 : n < 14100
                                                                                                                                                                    · have hr : n - 14050 < 50 := by omega
                                                                                                                                                                      have heq : n = (n - 14050) + 14050 := by omega
                                                                                                                                                                      rw [heq]
                                                                                                                                                                      exact pos_w281 ⟨n - 14050, hr⟩
                                                                                                                                                                    · by_cases h82 : n < 14150
                                                                                                                                                                      · have hr : n - 14100 < 50 := by omega
                                                                                                                                                                        have heq : n = (n - 14100) + 14100 := by omega
                                                                                                                                                                        rw [heq]
                                                                                                                                                                        exact pos_w282 ⟨n - 14100, hr⟩
                                                                                                                                                                      · by_cases h83 : n < 14200
                                                                                                                                                                        · have hr : n - 14150 < 50 := by omega
                                                                                                                                                                          have heq : n = (n - 14150) + 14150 := by omega
                                                                                                                                                                          rw [heq]
                                                                                                                                                                          exact pos_w283 ⟨n - 14150, hr⟩
                                                                                                                                                                        · by_cases h84 : n < 14250
                                                                                                                                                                          · have hr : n - 14200 < 50 := by omega
                                                                                                                                                                            have heq : n = (n - 14200) + 14200 := by omega
                                                                                                                                                                            rw [heq]
                                                                                                                                                                            exact pos_w284 ⟨n - 14200, hr⟩
                                                                                                                                                                          · by_cases h85 : n < 14300
                                                                                                                                                                            · have hr : n - 14250 < 50 := by omega
                                                                                                                                                                              have heq : n = (n - 14250) + 14250 := by omega
                                                                                                                                                                              rw [heq]
                                                                                                                                                                              exact pos_w285 ⟨n - 14250, hr⟩
                                                                                                                                                                            · by_cases h86 : n < 14350
                                                                                                                                                                              · have hr : n - 14300 < 50 := by omega
                                                                                                                                                                                have heq : n = (n - 14300) + 14300 := by omega
                                                                                                                                                                                rw [heq]
                                                                                                                                                                                exact pos_w286 ⟨n - 14300, hr⟩
                                                                                                                                                                              · by_cases h87 : n < 14400
                                                                                                                                                                                · have hr : n - 14350 < 50 := by omega
                                                                                                                                                                                  have heq : n = (n - 14350) + 14350 := by omega
                                                                                                                                                                                  rw [heq]
                                                                                                                                                                                  exact pos_w287 ⟨n - 14350, hr⟩
                                                                                                                                                                                · by_cases h88 : n < 14450
                                                                                                                                                                                  · have hr : n - 14400 < 50 := by omega
                                                                                                                                                                                    have heq : n = (n - 14400) + 14400 := by omega
                                                                                                                                                                                    rw [heq]
                                                                                                                                                                                    exact pos_w288 ⟨n - 14400, hr⟩
                                                                                                                                                                                  · by_cases h89 : n < 14500
                                                                                                                                                                                    · have hr : n - 14450 < 50 := by omega
                                                                                                                                                                                      have heq : n = (n - 14450) + 14450 := by omega
                                                                                                                                                                                      rw [heq]
                                                                                                                                                                                      exact pos_w289 ⟨n - 14450, hr⟩
                                                                                                                                                                                    · by_cases h90 : n < 14550
                                                                                                                                                                                      · have hr : n - 14500 < 50 := by omega
                                                                                                                                                                                        have heq : n = (n - 14500) + 14500 := by omega
                                                                                                                                                                                        rw [heq]
                                                                                                                                                                                        exact pos_w290 ⟨n - 14500, hr⟩
                                                                                                                                                                                      · by_cases h91 : n < 14600
                                                                                                                                                                                        · have hr : n - 14550 < 50 := by omega
                                                                                                                                                                                          have heq : n = (n - 14550) + 14550 := by omega
                                                                                                                                                                                          rw [heq]
                                                                                                                                                                                          exact pos_w291 ⟨n - 14550, hr⟩
                                                                                                                                                                                        · by_cases h92 : n < 14650
                                                                                                                                                                                          · have hr : n - 14600 < 50 := by omega
                                                                                                                                                                                            have heq : n = (n - 14600) + 14600 := by omega
                                                                                                                                                                                            rw [heq]
                                                                                                                                                                                            exact pos_w292 ⟨n - 14600, hr⟩
                                                                                                                                                                                          · by_cases h93 : n < 14700
                                                                                                                                                                                            · have hr : n - 14650 < 50 := by omega
                                                                                                                                                                                              have heq : n = (n - 14650) + 14650 := by omega
                                                                                                                                                                                              rw [heq]
                                                                                                                                                                                              exact pos_w293 ⟨n - 14650, hr⟩
                                                                                                                                                                                            · by_cases h94 : n < 14750
                                                                                                                                                                                              · have hr : n - 14700 < 50 := by omega
                                                                                                                                                                                                have heq : n = (n - 14700) + 14700 := by omega
                                                                                                                                                                                                rw [heq]
                                                                                                                                                                                                exact pos_w294 ⟨n - 14700, hr⟩
                                                                                                                                                                                              · by_cases h95 : n < 14800
                                                                                                                                                                                                · have hr : n - 14750 < 50 := by omega
                                                                                                                                                                                                  have heq : n = (n - 14750) + 14750 := by omega
                                                                                                                                                                                                  rw [heq]
                                                                                                                                                                                                  exact pos_w295 ⟨n - 14750, hr⟩
                                                                                                                                                                                                · by_cases h96 : n < 14850
                                                                                                                                                                                                  · have hr : n - 14800 < 50 := by omega
                                                                                                                                                                                                    have heq : n = (n - 14800) + 14800 := by omega
                                                                                                                                                                                                    rw [heq]
                                                                                                                                                                                                    exact pos_w296 ⟨n - 14800, hr⟩
                                                                                                                                                                                                  · by_cases h97 : n < 14900
                                                                                                                                                                                                    · have hr : n - 14850 < 50 := by omega
                                                                                                                                                                                                      have heq : n = (n - 14850) + 14850 := by omega
                                                                                                                                                                                                      rw [heq]
                                                                                                                                                                                                      exact pos_w297 ⟨n - 14850, hr⟩
                                                                                                                                                                                                    · by_cases h98 : n < 14950
                                                                                                                                                                                                      · have hr : n - 14900 < 50 := by omega
                                                                                                                                                                                                        have heq : n = (n - 14900) + 14900 := by omega
                                                                                                                                                                                                        rw [heq]
                                                                                                                                                                                                        exact pos_w298 ⟨n - 14900, hr⟩
                                                                                                                                                                                                      · by_cases h99 : n < 15000
                                                                                                                                                                                                        · have hr : n - 14950 < 50 := by omega
                                                                                                                                                                                                          have heq : n = (n - 14950) + 14950 := by omega
                                                                                                                                                                                                          rw [heq]
                                                                                                                                                                                                          exact pos_w299 ⟨n - 14950, hr⟩
                                                                                                                                                                                                        · omega

end IntMul.Kappa.R8.Bit.Oppbank.DimBound2


