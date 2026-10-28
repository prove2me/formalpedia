-- Prove2me | Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankDimBound3
-- name    : IntMul_Kappa_R8_Data_BitOppbankDimBound3
-- status  : Definition
-- author  : @Ethan Cheung Wang
-- created : 2026-10-28T18:02:29.700486+00:00
-- url     : https://prove2.me/theorems/d1b3c89f-5b49-485c-86be-4286d71f7d73
-- title:
--   Densified dimF $\le 22$ pack 3 ($[15000,20000)$)
-- statement:
--   Pack 3 of the densified dimension-field bound.
--
--   For every densified node index $n$ with $15000\le n<20000$, the 5-bit field $\mathrm{dimF}(n)$ extracted from $\mathrm{DIMT}$ satisfies
--   $$1\le \mathrm{dimF}(n)\le 22.$$
--   Proved by `decide` on successive `Fin 50` windows (no `native_decide`).
-- source:
--   R8 BitNB densified DIMT field bound; Fin-window decide packs

-- DimBound pack 3: dimF bounds on n ∈ [15000, 20000)

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

namespace IntMul.Kappa.R8.Bit.Oppbank.DimBound3

private theorem le_w300 : ∀ n : Fin 50, dimF (n.val + 15000) ≤ 22 := by decide
private theorem pos_w300 : ∀ n : Fin 50, 0 < dimF (n.val + 15000) := by decide
private theorem le_w301 : ∀ n : Fin 50, dimF (n.val + 15050) ≤ 22 := by decide
private theorem pos_w301 : ∀ n : Fin 50, 0 < dimF (n.val + 15050) := by decide
private theorem le_w302 : ∀ n : Fin 50, dimF (n.val + 15100) ≤ 22 := by decide
private theorem pos_w302 : ∀ n : Fin 50, 0 < dimF (n.val + 15100) := by decide
private theorem le_w303 : ∀ n : Fin 50, dimF (n.val + 15150) ≤ 22 := by decide
private theorem pos_w303 : ∀ n : Fin 50, 0 < dimF (n.val + 15150) := by decide
private theorem le_w304 : ∀ n : Fin 50, dimF (n.val + 15200) ≤ 22 := by decide
private theorem pos_w304 : ∀ n : Fin 50, 0 < dimF (n.val + 15200) := by decide
private theorem le_w305 : ∀ n : Fin 50, dimF (n.val + 15250) ≤ 22 := by decide
private theorem pos_w305 : ∀ n : Fin 50, 0 < dimF (n.val + 15250) := by decide
private theorem le_w306 : ∀ n : Fin 50, dimF (n.val + 15300) ≤ 22 := by decide
private theorem pos_w306 : ∀ n : Fin 50, 0 < dimF (n.val + 15300) := by decide
private theorem le_w307 : ∀ n : Fin 50, dimF (n.val + 15350) ≤ 22 := by decide
private theorem pos_w307 : ∀ n : Fin 50, 0 < dimF (n.val + 15350) := by decide
private theorem le_w308 : ∀ n : Fin 50, dimF (n.val + 15400) ≤ 22 := by decide
private theorem pos_w308 : ∀ n : Fin 50, 0 < dimF (n.val + 15400) := by decide
private theorem le_w309 : ∀ n : Fin 50, dimF (n.val + 15450) ≤ 22 := by decide
private theorem pos_w309 : ∀ n : Fin 50, 0 < dimF (n.val + 15450) := by decide
private theorem le_w310 : ∀ n : Fin 50, dimF (n.val + 15500) ≤ 22 := by decide
private theorem pos_w310 : ∀ n : Fin 50, 0 < dimF (n.val + 15500) := by decide
private theorem le_w311 : ∀ n : Fin 50, dimF (n.val + 15550) ≤ 22 := by decide
private theorem pos_w311 : ∀ n : Fin 50, 0 < dimF (n.val + 15550) := by decide
private theorem le_w312 : ∀ n : Fin 50, dimF (n.val + 15600) ≤ 22 := by decide
private theorem pos_w312 : ∀ n : Fin 50, 0 < dimF (n.val + 15600) := by decide
private theorem le_w313 : ∀ n : Fin 50, dimF (n.val + 15650) ≤ 22 := by decide
private theorem pos_w313 : ∀ n : Fin 50, 0 < dimF (n.val + 15650) := by decide
private theorem le_w314 : ∀ n : Fin 50, dimF (n.val + 15700) ≤ 22 := by decide
private theorem pos_w314 : ∀ n : Fin 50, 0 < dimF (n.val + 15700) := by decide
private theorem le_w315 : ∀ n : Fin 50, dimF (n.val + 15750) ≤ 22 := by decide
private theorem pos_w315 : ∀ n : Fin 50, 0 < dimF (n.val + 15750) := by decide
private theorem le_w316 : ∀ n : Fin 50, dimF (n.val + 15800) ≤ 22 := by decide
private theorem pos_w316 : ∀ n : Fin 50, 0 < dimF (n.val + 15800) := by decide
private theorem le_w317 : ∀ n : Fin 50, dimF (n.val + 15850) ≤ 22 := by decide
private theorem pos_w317 : ∀ n : Fin 50, 0 < dimF (n.val + 15850) := by decide
private theorem le_w318 : ∀ n : Fin 50, dimF (n.val + 15900) ≤ 22 := by decide
private theorem pos_w318 : ∀ n : Fin 50, 0 < dimF (n.val + 15900) := by decide
private theorem le_w319 : ∀ n : Fin 50, dimF (n.val + 15950) ≤ 22 := by decide
private theorem pos_w319 : ∀ n : Fin 50, 0 < dimF (n.val + 15950) := by decide
private theorem le_w320 : ∀ n : Fin 50, dimF (n.val + 16000) ≤ 22 := by decide
private theorem pos_w320 : ∀ n : Fin 50, 0 < dimF (n.val + 16000) := by decide
private theorem le_w321 : ∀ n : Fin 50, dimF (n.val + 16050) ≤ 22 := by decide
private theorem pos_w321 : ∀ n : Fin 50, 0 < dimF (n.val + 16050) := by decide
private theorem le_w322 : ∀ n : Fin 50, dimF (n.val + 16100) ≤ 22 := by decide
private theorem pos_w322 : ∀ n : Fin 50, 0 < dimF (n.val + 16100) := by decide
private theorem le_w323 : ∀ n : Fin 50, dimF (n.val + 16150) ≤ 22 := by decide
private theorem pos_w323 : ∀ n : Fin 50, 0 < dimF (n.val + 16150) := by decide
private theorem le_w324 : ∀ n : Fin 50, dimF (n.val + 16200) ≤ 22 := by decide
private theorem pos_w324 : ∀ n : Fin 50, 0 < dimF (n.val + 16200) := by decide
private theorem le_w325 : ∀ n : Fin 50, dimF (n.val + 16250) ≤ 22 := by decide
private theorem pos_w325 : ∀ n : Fin 50, 0 < dimF (n.val + 16250) := by decide
private theorem le_w326 : ∀ n : Fin 50, dimF (n.val + 16300) ≤ 22 := by decide
private theorem pos_w326 : ∀ n : Fin 50, 0 < dimF (n.val + 16300) := by decide
private theorem le_w327 : ∀ n : Fin 50, dimF (n.val + 16350) ≤ 22 := by decide
private theorem pos_w327 : ∀ n : Fin 50, 0 < dimF (n.val + 16350) := by decide
private theorem le_w328 : ∀ n : Fin 50, dimF (n.val + 16400) ≤ 22 := by decide
private theorem pos_w328 : ∀ n : Fin 50, 0 < dimF (n.val + 16400) := by decide
private theorem le_w329 : ∀ n : Fin 50, dimF (n.val + 16450) ≤ 22 := by decide
private theorem pos_w329 : ∀ n : Fin 50, 0 < dimF (n.val + 16450) := by decide
private theorem le_w330 : ∀ n : Fin 50, dimF (n.val + 16500) ≤ 22 := by decide
private theorem pos_w330 : ∀ n : Fin 50, 0 < dimF (n.val + 16500) := by decide
private theorem le_w331 : ∀ n : Fin 50, dimF (n.val + 16550) ≤ 22 := by decide
private theorem pos_w331 : ∀ n : Fin 50, 0 < dimF (n.val + 16550) := by decide
private theorem le_w332 : ∀ n : Fin 50, dimF (n.val + 16600) ≤ 22 := by decide
private theorem pos_w332 : ∀ n : Fin 50, 0 < dimF (n.val + 16600) := by decide
private theorem le_w333 : ∀ n : Fin 50, dimF (n.val + 16650) ≤ 22 := by decide
private theorem pos_w333 : ∀ n : Fin 50, 0 < dimF (n.val + 16650) := by decide
private theorem le_w334 : ∀ n : Fin 50, dimF (n.val + 16700) ≤ 22 := by decide
private theorem pos_w334 : ∀ n : Fin 50, 0 < dimF (n.val + 16700) := by decide
private theorem le_w335 : ∀ n : Fin 50, dimF (n.val + 16750) ≤ 22 := by decide
private theorem pos_w335 : ∀ n : Fin 50, 0 < dimF (n.val + 16750) := by decide
private theorem le_w336 : ∀ n : Fin 50, dimF (n.val + 16800) ≤ 22 := by decide
private theorem pos_w336 : ∀ n : Fin 50, 0 < dimF (n.val + 16800) := by decide
private theorem le_w337 : ∀ n : Fin 50, dimF (n.val + 16850) ≤ 22 := by decide
private theorem pos_w337 : ∀ n : Fin 50, 0 < dimF (n.val + 16850) := by decide
private theorem le_w338 : ∀ n : Fin 50, dimF (n.val + 16900) ≤ 22 := by decide
private theorem pos_w338 : ∀ n : Fin 50, 0 < dimF (n.val + 16900) := by decide
private theorem le_w339 : ∀ n : Fin 50, dimF (n.val + 16950) ≤ 22 := by decide
private theorem pos_w339 : ∀ n : Fin 50, 0 < dimF (n.val + 16950) := by decide
private theorem le_w340 : ∀ n : Fin 50, dimF (n.val + 17000) ≤ 22 := by decide
private theorem pos_w340 : ∀ n : Fin 50, 0 < dimF (n.val + 17000) := by decide
private theorem le_w341 : ∀ n : Fin 50, dimF (n.val + 17050) ≤ 22 := by decide
private theorem pos_w341 : ∀ n : Fin 50, 0 < dimF (n.val + 17050) := by decide
private theorem le_w342 : ∀ n : Fin 50, dimF (n.val + 17100) ≤ 22 := by decide
private theorem pos_w342 : ∀ n : Fin 50, 0 < dimF (n.val + 17100) := by decide
private theorem le_w343 : ∀ n : Fin 50, dimF (n.val + 17150) ≤ 22 := by decide
private theorem pos_w343 : ∀ n : Fin 50, 0 < dimF (n.val + 17150) := by decide
private theorem le_w344 : ∀ n : Fin 50, dimF (n.val + 17200) ≤ 22 := by decide
private theorem pos_w344 : ∀ n : Fin 50, 0 < dimF (n.val + 17200) := by decide
private theorem le_w345 : ∀ n : Fin 50, dimF (n.val + 17250) ≤ 22 := by decide
private theorem pos_w345 : ∀ n : Fin 50, 0 < dimF (n.val + 17250) := by decide
private theorem le_w346 : ∀ n : Fin 50, dimF (n.val + 17300) ≤ 22 := by decide
private theorem pos_w346 : ∀ n : Fin 50, 0 < dimF (n.val + 17300) := by decide
private theorem le_w347 : ∀ n : Fin 50, dimF (n.val + 17350) ≤ 22 := by decide
private theorem pos_w347 : ∀ n : Fin 50, 0 < dimF (n.val + 17350) := by decide
private theorem le_w348 : ∀ n : Fin 50, dimF (n.val + 17400) ≤ 22 := by decide
private theorem pos_w348 : ∀ n : Fin 50, 0 < dimF (n.val + 17400) := by decide
private theorem le_w349 : ∀ n : Fin 50, dimF (n.val + 17450) ≤ 22 := by decide
private theorem pos_w349 : ∀ n : Fin 50, 0 < dimF (n.val + 17450) := by decide
private theorem le_w350 : ∀ n : Fin 50, dimF (n.val + 17500) ≤ 22 := by decide
private theorem pos_w350 : ∀ n : Fin 50, 0 < dimF (n.val + 17500) := by decide
private theorem le_w351 : ∀ n : Fin 50, dimF (n.val + 17550) ≤ 22 := by decide
private theorem pos_w351 : ∀ n : Fin 50, 0 < dimF (n.val + 17550) := by decide
private theorem le_w352 : ∀ n : Fin 50, dimF (n.val + 17600) ≤ 22 := by decide
private theorem pos_w352 : ∀ n : Fin 50, 0 < dimF (n.val + 17600) := by decide
private theorem le_w353 : ∀ n : Fin 50, dimF (n.val + 17650) ≤ 22 := by decide
private theorem pos_w353 : ∀ n : Fin 50, 0 < dimF (n.val + 17650) := by decide
private theorem le_w354 : ∀ n : Fin 50, dimF (n.val + 17700) ≤ 22 := by decide
private theorem pos_w354 : ∀ n : Fin 50, 0 < dimF (n.val + 17700) := by decide
private theorem le_w355 : ∀ n : Fin 50, dimF (n.val + 17750) ≤ 22 := by decide
private theorem pos_w355 : ∀ n : Fin 50, 0 < dimF (n.val + 17750) := by decide
private theorem le_w356 : ∀ n : Fin 50, dimF (n.val + 17800) ≤ 22 := by decide
private theorem pos_w356 : ∀ n : Fin 50, 0 < dimF (n.val + 17800) := by decide
private theorem le_w357 : ∀ n : Fin 50, dimF (n.val + 17850) ≤ 22 := by decide
private theorem pos_w357 : ∀ n : Fin 50, 0 < dimF (n.val + 17850) := by decide
private theorem le_w358 : ∀ n : Fin 50, dimF (n.val + 17900) ≤ 22 := by decide
private theorem pos_w358 : ∀ n : Fin 50, 0 < dimF (n.val + 17900) := by decide
private theorem le_w359 : ∀ n : Fin 50, dimF (n.val + 17950) ≤ 22 := by decide
private theorem pos_w359 : ∀ n : Fin 50, 0 < dimF (n.val + 17950) := by decide
private theorem le_w360 : ∀ n : Fin 50, dimF (n.val + 18000) ≤ 22 := by decide
private theorem pos_w360 : ∀ n : Fin 50, 0 < dimF (n.val + 18000) := by decide
private theorem le_w361 : ∀ n : Fin 50, dimF (n.val + 18050) ≤ 22 := by decide
private theorem pos_w361 : ∀ n : Fin 50, 0 < dimF (n.val + 18050) := by decide
private theorem le_w362 : ∀ n : Fin 50, dimF (n.val + 18100) ≤ 22 := by decide
private theorem pos_w362 : ∀ n : Fin 50, 0 < dimF (n.val + 18100) := by decide
private theorem le_w363 : ∀ n : Fin 50, dimF (n.val + 18150) ≤ 22 := by decide
private theorem pos_w363 : ∀ n : Fin 50, 0 < dimF (n.val + 18150) := by decide
private theorem le_w364 : ∀ n : Fin 50, dimF (n.val + 18200) ≤ 22 := by decide
private theorem pos_w364 : ∀ n : Fin 50, 0 < dimF (n.val + 18200) := by decide
private theorem le_w365 : ∀ n : Fin 50, dimF (n.val + 18250) ≤ 22 := by decide
private theorem pos_w365 : ∀ n : Fin 50, 0 < dimF (n.val + 18250) := by decide
private theorem le_w366 : ∀ n : Fin 50, dimF (n.val + 18300) ≤ 22 := by decide
private theorem pos_w366 : ∀ n : Fin 50, 0 < dimF (n.val + 18300) := by decide
private theorem le_w367 : ∀ n : Fin 50, dimF (n.val + 18350) ≤ 22 := by decide
private theorem pos_w367 : ∀ n : Fin 50, 0 < dimF (n.val + 18350) := by decide
private theorem le_w368 : ∀ n : Fin 50, dimF (n.val + 18400) ≤ 22 := by decide
private theorem pos_w368 : ∀ n : Fin 50, 0 < dimF (n.val + 18400) := by decide
private theorem le_w369 : ∀ n : Fin 50, dimF (n.val + 18450) ≤ 22 := by decide
private theorem pos_w369 : ∀ n : Fin 50, 0 < dimF (n.val + 18450) := by decide
private theorem le_w370 : ∀ n : Fin 50, dimF (n.val + 18500) ≤ 22 := by decide
private theorem pos_w370 : ∀ n : Fin 50, 0 < dimF (n.val + 18500) := by decide
private theorem le_w371 : ∀ n : Fin 50, dimF (n.val + 18550) ≤ 22 := by decide
private theorem pos_w371 : ∀ n : Fin 50, 0 < dimF (n.val + 18550) := by decide
private theorem le_w372 : ∀ n : Fin 50, dimF (n.val + 18600) ≤ 22 := by decide
private theorem pos_w372 : ∀ n : Fin 50, 0 < dimF (n.val + 18600) := by decide
private theorem le_w373 : ∀ n : Fin 50, dimF (n.val + 18650) ≤ 22 := by decide
private theorem pos_w373 : ∀ n : Fin 50, 0 < dimF (n.val + 18650) := by decide
private theorem le_w374 : ∀ n : Fin 50, dimF (n.val + 18700) ≤ 22 := by decide
private theorem pos_w374 : ∀ n : Fin 50, 0 < dimF (n.val + 18700) := by decide
private theorem le_w375 : ∀ n : Fin 50, dimF (n.val + 18750) ≤ 22 := by decide
private theorem pos_w375 : ∀ n : Fin 50, 0 < dimF (n.val + 18750) := by decide
private theorem le_w376 : ∀ n : Fin 50, dimF (n.val + 18800) ≤ 22 := by decide
private theorem pos_w376 : ∀ n : Fin 50, 0 < dimF (n.val + 18800) := by decide
private theorem le_w377 : ∀ n : Fin 50, dimF (n.val + 18850) ≤ 22 := by decide
private theorem pos_w377 : ∀ n : Fin 50, 0 < dimF (n.val + 18850) := by decide
private theorem le_w378 : ∀ n : Fin 50, dimF (n.val + 18900) ≤ 22 := by decide
private theorem pos_w378 : ∀ n : Fin 50, 0 < dimF (n.val + 18900) := by decide
private theorem le_w379 : ∀ n : Fin 50, dimF (n.val + 18950) ≤ 22 := by decide
private theorem pos_w379 : ∀ n : Fin 50, 0 < dimF (n.val + 18950) := by decide
private theorem le_w380 : ∀ n : Fin 50, dimF (n.val + 19000) ≤ 22 := by decide
private theorem pos_w380 : ∀ n : Fin 50, 0 < dimF (n.val + 19000) := by decide
private theorem le_w381 : ∀ n : Fin 50, dimF (n.val + 19050) ≤ 22 := by decide
private theorem pos_w381 : ∀ n : Fin 50, 0 < dimF (n.val + 19050) := by decide
private theorem le_w382 : ∀ n : Fin 50, dimF (n.val + 19100) ≤ 22 := by decide
private theorem pos_w382 : ∀ n : Fin 50, 0 < dimF (n.val + 19100) := by decide
private theorem le_w383 : ∀ n : Fin 50, dimF (n.val + 19150) ≤ 22 := by decide
private theorem pos_w383 : ∀ n : Fin 50, 0 < dimF (n.val + 19150) := by decide
private theorem le_w384 : ∀ n : Fin 50, dimF (n.val + 19200) ≤ 22 := by decide
private theorem pos_w384 : ∀ n : Fin 50, 0 < dimF (n.val + 19200) := by decide
private theorem le_w385 : ∀ n : Fin 50, dimF (n.val + 19250) ≤ 22 := by decide
private theorem pos_w385 : ∀ n : Fin 50, 0 < dimF (n.val + 19250) := by decide
private theorem le_w386 : ∀ n : Fin 50, dimF (n.val + 19300) ≤ 22 := by decide
private theorem pos_w386 : ∀ n : Fin 50, 0 < dimF (n.val + 19300) := by decide
private theorem le_w387 : ∀ n : Fin 50, dimF (n.val + 19350) ≤ 22 := by decide
private theorem pos_w387 : ∀ n : Fin 50, 0 < dimF (n.val + 19350) := by decide
private theorem le_w388 : ∀ n : Fin 50, dimF (n.val + 19400) ≤ 22 := by decide
private theorem pos_w388 : ∀ n : Fin 50, 0 < dimF (n.val + 19400) := by decide
private theorem le_w389 : ∀ n : Fin 50, dimF (n.val + 19450) ≤ 22 := by decide
private theorem pos_w389 : ∀ n : Fin 50, 0 < dimF (n.val + 19450) := by decide
private theorem le_w390 : ∀ n : Fin 50, dimF (n.val + 19500) ≤ 22 := by decide
private theorem pos_w390 : ∀ n : Fin 50, 0 < dimF (n.val + 19500) := by decide
private theorem le_w391 : ∀ n : Fin 50, dimF (n.val + 19550) ≤ 22 := by decide
private theorem pos_w391 : ∀ n : Fin 50, 0 < dimF (n.val + 19550) := by decide
private theorem le_w392 : ∀ n : Fin 50, dimF (n.val + 19600) ≤ 22 := by decide
private theorem pos_w392 : ∀ n : Fin 50, 0 < dimF (n.val + 19600) := by decide
private theorem le_w393 : ∀ n : Fin 50, dimF (n.val + 19650) ≤ 22 := by decide
private theorem pos_w393 : ∀ n : Fin 50, 0 < dimF (n.val + 19650) := by decide
private theorem le_w394 : ∀ n : Fin 50, dimF (n.val + 19700) ≤ 22 := by decide
private theorem pos_w394 : ∀ n : Fin 50, 0 < dimF (n.val + 19700) := by decide
private theorem le_w395 : ∀ n : Fin 50, dimF (n.val + 19750) ≤ 22 := by decide
private theorem pos_w395 : ∀ n : Fin 50, 0 < dimF (n.val + 19750) := by decide
private theorem le_w396 : ∀ n : Fin 50, dimF (n.val + 19800) ≤ 22 := by decide
private theorem pos_w396 : ∀ n : Fin 50, 0 < dimF (n.val + 19800) := by decide
private theorem le_w397 : ∀ n : Fin 50, dimF (n.val + 19850) ≤ 22 := by decide
private theorem pos_w397 : ∀ n : Fin 50, 0 < dimF (n.val + 19850) := by decide
private theorem le_w398 : ∀ n : Fin 50, dimF (n.val + 19900) ≤ 22 := by decide
private theorem pos_w398 : ∀ n : Fin 50, 0 < dimF (n.val + 19900) := by decide
private theorem le_w399 : ∀ n : Fin 50, dimF (n.val + 19950) ≤ 22 := by decide
private theorem pos_w399 : ∀ n : Fin 50, 0 < dimF (n.val + 19950) := by decide

theorem dimF_le_22_range : ∀ n, 15000 ≤ n → n < 20000 → dimF n ≤ 22 := by
  intro n hlo hhi
  by_cases h0 : n < 15050
  · have hr : n - 15000 < 50 := by omega
    have heq : n = (n - 15000) + 15000 := by omega
    rw [heq]
    exact le_w300 ⟨n - 15000, hr⟩
  · by_cases h1 : n < 15100
    · have hr : n - 15050 < 50 := by omega
      have heq : n = (n - 15050) + 15050 := by omega
      rw [heq]
      exact le_w301 ⟨n - 15050, hr⟩
    · by_cases h2 : n < 15150
      · have hr : n - 15100 < 50 := by omega
        have heq : n = (n - 15100) + 15100 := by omega
        rw [heq]
        exact le_w302 ⟨n - 15100, hr⟩
      · by_cases h3 : n < 15200
        · have hr : n - 15150 < 50 := by omega
          have heq : n = (n - 15150) + 15150 := by omega
          rw [heq]
          exact le_w303 ⟨n - 15150, hr⟩
        · by_cases h4 : n < 15250
          · have hr : n - 15200 < 50 := by omega
            have heq : n = (n - 15200) + 15200 := by omega
            rw [heq]
            exact le_w304 ⟨n - 15200, hr⟩
          · by_cases h5 : n < 15300
            · have hr : n - 15250 < 50 := by omega
              have heq : n = (n - 15250) + 15250 := by omega
              rw [heq]
              exact le_w305 ⟨n - 15250, hr⟩
            · by_cases h6 : n < 15350
              · have hr : n - 15300 < 50 := by omega
                have heq : n = (n - 15300) + 15300 := by omega
                rw [heq]
                exact le_w306 ⟨n - 15300, hr⟩
              · by_cases h7 : n < 15400
                · have hr : n - 15350 < 50 := by omega
                  have heq : n = (n - 15350) + 15350 := by omega
                  rw [heq]
                  exact le_w307 ⟨n - 15350, hr⟩
                · by_cases h8 : n < 15450
                  · have hr : n - 15400 < 50 := by omega
                    have heq : n = (n - 15400) + 15400 := by omega
                    rw [heq]
                    exact le_w308 ⟨n - 15400, hr⟩
                  · by_cases h9 : n < 15500
                    · have hr : n - 15450 < 50 := by omega
                      have heq : n = (n - 15450) + 15450 := by omega
                      rw [heq]
                      exact le_w309 ⟨n - 15450, hr⟩
                    · by_cases h10 : n < 15550
                      · have hr : n - 15500 < 50 := by omega
                        have heq : n = (n - 15500) + 15500 := by omega
                        rw [heq]
                        exact le_w310 ⟨n - 15500, hr⟩
                      · by_cases h11 : n < 15600
                        · have hr : n - 15550 < 50 := by omega
                          have heq : n = (n - 15550) + 15550 := by omega
                          rw [heq]
                          exact le_w311 ⟨n - 15550, hr⟩
                        · by_cases h12 : n < 15650
                          · have hr : n - 15600 < 50 := by omega
                            have heq : n = (n - 15600) + 15600 := by omega
                            rw [heq]
                            exact le_w312 ⟨n - 15600, hr⟩
                          · by_cases h13 : n < 15700
                            · have hr : n - 15650 < 50 := by omega
                              have heq : n = (n - 15650) + 15650 := by omega
                              rw [heq]
                              exact le_w313 ⟨n - 15650, hr⟩
                            · by_cases h14 : n < 15750
                              · have hr : n - 15700 < 50 := by omega
                                have heq : n = (n - 15700) + 15700 := by omega
                                rw [heq]
                                exact le_w314 ⟨n - 15700, hr⟩
                              · by_cases h15 : n < 15800
                                · have hr : n - 15750 < 50 := by omega
                                  have heq : n = (n - 15750) + 15750 := by omega
                                  rw [heq]
                                  exact le_w315 ⟨n - 15750, hr⟩
                                · by_cases h16 : n < 15850
                                  · have hr : n - 15800 < 50 := by omega
                                    have heq : n = (n - 15800) + 15800 := by omega
                                    rw [heq]
                                    exact le_w316 ⟨n - 15800, hr⟩
                                  · by_cases h17 : n < 15900
                                    · have hr : n - 15850 < 50 := by omega
                                      have heq : n = (n - 15850) + 15850 := by omega
                                      rw [heq]
                                      exact le_w317 ⟨n - 15850, hr⟩
                                    · by_cases h18 : n < 15950
                                      · have hr : n - 15900 < 50 := by omega
                                        have heq : n = (n - 15900) + 15900 := by omega
                                        rw [heq]
                                        exact le_w318 ⟨n - 15900, hr⟩
                                      · by_cases h19 : n < 16000
                                        · have hr : n - 15950 < 50 := by omega
                                          have heq : n = (n - 15950) + 15950 := by omega
                                          rw [heq]
                                          exact le_w319 ⟨n - 15950, hr⟩
                                        · by_cases h20 : n < 16050
                                          · have hr : n - 16000 < 50 := by omega
                                            have heq : n = (n - 16000) + 16000 := by omega
                                            rw [heq]
                                            exact le_w320 ⟨n - 16000, hr⟩
                                          · by_cases h21 : n < 16100
                                            · have hr : n - 16050 < 50 := by omega
                                              have heq : n = (n - 16050) + 16050 := by omega
                                              rw [heq]
                                              exact le_w321 ⟨n - 16050, hr⟩
                                            · by_cases h22 : n < 16150
                                              · have hr : n - 16100 < 50 := by omega
                                                have heq : n = (n - 16100) + 16100 := by omega
                                                rw [heq]
                                                exact le_w322 ⟨n - 16100, hr⟩
                                              · by_cases h23 : n < 16200
                                                · have hr : n - 16150 < 50 := by omega
                                                  have heq : n = (n - 16150) + 16150 := by omega
                                                  rw [heq]
                                                  exact le_w323 ⟨n - 16150, hr⟩
                                                · by_cases h24 : n < 16250
                                                  · have hr : n - 16200 < 50 := by omega
                                                    have heq : n = (n - 16200) + 16200 := by omega
                                                    rw [heq]
                                                    exact le_w324 ⟨n - 16200, hr⟩
                                                  · by_cases h25 : n < 16300
                                                    · have hr : n - 16250 < 50 := by omega
                                                      have heq : n = (n - 16250) + 16250 := by omega
                                                      rw [heq]
                                                      exact le_w325 ⟨n - 16250, hr⟩
                                                    · by_cases h26 : n < 16350
                                                      · have hr : n - 16300 < 50 := by omega
                                                        have heq : n = (n - 16300) + 16300 := by omega
                                                        rw [heq]
                                                        exact le_w326 ⟨n - 16300, hr⟩
                                                      · by_cases h27 : n < 16400
                                                        · have hr : n - 16350 < 50 := by omega
                                                          have heq : n = (n - 16350) + 16350 := by omega
                                                          rw [heq]
                                                          exact le_w327 ⟨n - 16350, hr⟩
                                                        · by_cases h28 : n < 16450
                                                          · have hr : n - 16400 < 50 := by omega
                                                            have heq : n = (n - 16400) + 16400 := by omega
                                                            rw [heq]
                                                            exact le_w328 ⟨n - 16400, hr⟩
                                                          · by_cases h29 : n < 16500
                                                            · have hr : n - 16450 < 50 := by omega
                                                              have heq : n = (n - 16450) + 16450 := by omega
                                                              rw [heq]
                                                              exact le_w329 ⟨n - 16450, hr⟩
                                                            · by_cases h30 : n < 16550
                                                              · have hr : n - 16500 < 50 := by omega
                                                                have heq : n = (n - 16500) + 16500 := by omega
                                                                rw [heq]
                                                                exact le_w330 ⟨n - 16500, hr⟩
                                                              · by_cases h31 : n < 16600
                                                                · have hr : n - 16550 < 50 := by omega
                                                                  have heq : n = (n - 16550) + 16550 := by omega
                                                                  rw [heq]
                                                                  exact le_w331 ⟨n - 16550, hr⟩
                                                                · by_cases h32 : n < 16650
                                                                  · have hr : n - 16600 < 50 := by omega
                                                                    have heq : n = (n - 16600) + 16600 := by omega
                                                                    rw [heq]
                                                                    exact le_w332 ⟨n - 16600, hr⟩
                                                                  · by_cases h33 : n < 16700
                                                                    · have hr : n - 16650 < 50 := by omega
                                                                      have heq : n = (n - 16650) + 16650 := by omega
                                                                      rw [heq]
                                                                      exact le_w333 ⟨n - 16650, hr⟩
                                                                    · by_cases h34 : n < 16750
                                                                      · have hr : n - 16700 < 50 := by omega
                                                                        have heq : n = (n - 16700) + 16700 := by omega
                                                                        rw [heq]
                                                                        exact le_w334 ⟨n - 16700, hr⟩
                                                                      · by_cases h35 : n < 16800
                                                                        · have hr : n - 16750 < 50 := by omega
                                                                          have heq : n = (n - 16750) + 16750 := by omega
                                                                          rw [heq]
                                                                          exact le_w335 ⟨n - 16750, hr⟩
                                                                        · by_cases h36 : n < 16850
                                                                          · have hr : n - 16800 < 50 := by omega
                                                                            have heq : n = (n - 16800) + 16800 := by omega
                                                                            rw [heq]
                                                                            exact le_w336 ⟨n - 16800, hr⟩
                                                                          · by_cases h37 : n < 16900
                                                                            · have hr : n - 16850 < 50 := by omega
                                                                              have heq : n = (n - 16850) + 16850 := by omega
                                                                              rw [heq]
                                                                              exact le_w337 ⟨n - 16850, hr⟩
                                                                            · by_cases h38 : n < 16950
                                                                              · have hr : n - 16900 < 50 := by omega
                                                                                have heq : n = (n - 16900) + 16900 := by omega
                                                                                rw [heq]
                                                                                exact le_w338 ⟨n - 16900, hr⟩
                                                                              · by_cases h39 : n < 17000
                                                                                · have hr : n - 16950 < 50 := by omega
                                                                                  have heq : n = (n - 16950) + 16950 := by omega
                                                                                  rw [heq]
                                                                                  exact le_w339 ⟨n - 16950, hr⟩
                                                                                · by_cases h40 : n < 17050
                                                                                  · have hr : n - 17000 < 50 := by omega
                                                                                    have heq : n = (n - 17000) + 17000 := by omega
                                                                                    rw [heq]
                                                                                    exact le_w340 ⟨n - 17000, hr⟩
                                                                                  · by_cases h41 : n < 17100
                                                                                    · have hr : n - 17050 < 50 := by omega
                                                                                      have heq : n = (n - 17050) + 17050 := by omega
                                                                                      rw [heq]
                                                                                      exact le_w341 ⟨n - 17050, hr⟩
                                                                                    · by_cases h42 : n < 17150
                                                                                      · have hr : n - 17100 < 50 := by omega
                                                                                        have heq : n = (n - 17100) + 17100 := by omega
                                                                                        rw [heq]
                                                                                        exact le_w342 ⟨n - 17100, hr⟩
                                                                                      · by_cases h43 : n < 17200
                                                                                        · have hr : n - 17150 < 50 := by omega
                                                                                          have heq : n = (n - 17150) + 17150 := by omega
                                                                                          rw [heq]
                                                                                          exact le_w343 ⟨n - 17150, hr⟩
                                                                                        · by_cases h44 : n < 17250
                                                                                          · have hr : n - 17200 < 50 := by omega
                                                                                            have heq : n = (n - 17200) + 17200 := by omega
                                                                                            rw [heq]
                                                                                            exact le_w344 ⟨n - 17200, hr⟩
                                                                                          · by_cases h45 : n < 17300
                                                                                            · have hr : n - 17250 < 50 := by omega
                                                                                              have heq : n = (n - 17250) + 17250 := by omega
                                                                                              rw [heq]
                                                                                              exact le_w345 ⟨n - 17250, hr⟩
                                                                                            · by_cases h46 : n < 17350
                                                                                              · have hr : n - 17300 < 50 := by omega
                                                                                                have heq : n = (n - 17300) + 17300 := by omega
                                                                                                rw [heq]
                                                                                                exact le_w346 ⟨n - 17300, hr⟩
                                                                                              · by_cases h47 : n < 17400
                                                                                                · have hr : n - 17350 < 50 := by omega
                                                                                                  have heq : n = (n - 17350) + 17350 := by omega
                                                                                                  rw [heq]
                                                                                                  exact le_w347 ⟨n - 17350, hr⟩
                                                                                                · by_cases h48 : n < 17450
                                                                                                  · have hr : n - 17400 < 50 := by omega
                                                                                                    have heq : n = (n - 17400) + 17400 := by omega
                                                                                                    rw [heq]
                                                                                                    exact le_w348 ⟨n - 17400, hr⟩
                                                                                                  · by_cases h49 : n < 17500
                                                                                                    · have hr : n - 17450 < 50 := by omega
                                                                                                      have heq : n = (n - 17450) + 17450 := by omega
                                                                                                      rw [heq]
                                                                                                      exact le_w349 ⟨n - 17450, hr⟩
                                                                                                    · by_cases h50 : n < 17550
                                                                                                      · have hr : n - 17500 < 50 := by omega
                                                                                                        have heq : n = (n - 17500) + 17500 := by omega
                                                                                                        rw [heq]
                                                                                                        exact le_w350 ⟨n - 17500, hr⟩
                                                                                                      · by_cases h51 : n < 17600
                                                                                                        · have hr : n - 17550 < 50 := by omega
                                                                                                          have heq : n = (n - 17550) + 17550 := by omega
                                                                                                          rw [heq]
                                                                                                          exact le_w351 ⟨n - 17550, hr⟩
                                                                                                        · by_cases h52 : n < 17650
                                                                                                          · have hr : n - 17600 < 50 := by omega
                                                                                                            have heq : n = (n - 17600) + 17600 := by omega
                                                                                                            rw [heq]
                                                                                                            exact le_w352 ⟨n - 17600, hr⟩
                                                                                                          · by_cases h53 : n < 17700
                                                                                                            · have hr : n - 17650 < 50 := by omega
                                                                                                              have heq : n = (n - 17650) + 17650 := by omega
                                                                                                              rw [heq]
                                                                                                              exact le_w353 ⟨n - 17650, hr⟩
                                                                                                            · by_cases h54 : n < 17750
                                                                                                              · have hr : n - 17700 < 50 := by omega
                                                                                                                have heq : n = (n - 17700) + 17700 := by omega
                                                                                                                rw [heq]
                                                                                                                exact le_w354 ⟨n - 17700, hr⟩
                                                                                                              · by_cases h55 : n < 17800
                                                                                                                · have hr : n - 17750 < 50 := by omega
                                                                                                                  have heq : n = (n - 17750) + 17750 := by omega
                                                                                                                  rw [heq]
                                                                                                                  exact le_w355 ⟨n - 17750, hr⟩
                                                                                                                · by_cases h56 : n < 17850
                                                                                                                  · have hr : n - 17800 < 50 := by omega
                                                                                                                    have heq : n = (n - 17800) + 17800 := by omega
                                                                                                                    rw [heq]
                                                                                                                    exact le_w356 ⟨n - 17800, hr⟩
                                                                                                                  · by_cases h57 : n < 17900
                                                                                                                    · have hr : n - 17850 < 50 := by omega
                                                                                                                      have heq : n = (n - 17850) + 17850 := by omega
                                                                                                                      rw [heq]
                                                                                                                      exact le_w357 ⟨n - 17850, hr⟩
                                                                                                                    · by_cases h58 : n < 17950
                                                                                                                      · have hr : n - 17900 < 50 := by omega
                                                                                                                        have heq : n = (n - 17900) + 17900 := by omega
                                                                                                                        rw [heq]
                                                                                                                        exact le_w358 ⟨n - 17900, hr⟩
                                                                                                                      · by_cases h59 : n < 18000
                                                                                                                        · have hr : n - 17950 < 50 := by omega
                                                                                                                          have heq : n = (n - 17950) + 17950 := by omega
                                                                                                                          rw [heq]
                                                                                                                          exact le_w359 ⟨n - 17950, hr⟩
                                                                                                                        · by_cases h60 : n < 18050
                                                                                                                          · have hr : n - 18000 < 50 := by omega
                                                                                                                            have heq : n = (n - 18000) + 18000 := by omega
                                                                                                                            rw [heq]
                                                                                                                            exact le_w360 ⟨n - 18000, hr⟩
                                                                                                                          · by_cases h61 : n < 18100
                                                                                                                            · have hr : n - 18050 < 50 := by omega
                                                                                                                              have heq : n = (n - 18050) + 18050 := by omega
                                                                                                                              rw [heq]
                                                                                                                              exact le_w361 ⟨n - 18050, hr⟩
                                                                                                                            · by_cases h62 : n < 18150
                                                                                                                              · have hr : n - 18100 < 50 := by omega
                                                                                                                                have heq : n = (n - 18100) + 18100 := by omega
                                                                                                                                rw [heq]
                                                                                                                                exact le_w362 ⟨n - 18100, hr⟩
                                                                                                                              · by_cases h63 : n < 18200
                                                                                                                                · have hr : n - 18150 < 50 := by omega
                                                                                                                                  have heq : n = (n - 18150) + 18150 := by omega
                                                                                                                                  rw [heq]
                                                                                                                                  exact le_w363 ⟨n - 18150, hr⟩
                                                                                                                                · by_cases h64 : n < 18250
                                                                                                                                  · have hr : n - 18200 < 50 := by omega
                                                                                                                                    have heq : n = (n - 18200) + 18200 := by omega
                                                                                                                                    rw [heq]
                                                                                                                                    exact le_w364 ⟨n - 18200, hr⟩
                                                                                                                                  · by_cases h65 : n < 18300
                                                                                                                                    · have hr : n - 18250 < 50 := by omega
                                                                                                                                      have heq : n = (n - 18250) + 18250 := by omega
                                                                                                                                      rw [heq]
                                                                                                                                      exact le_w365 ⟨n - 18250, hr⟩
                                                                                                                                    · by_cases h66 : n < 18350
                                                                                                                                      · have hr : n - 18300 < 50 := by omega
                                                                                                                                        have heq : n = (n - 18300) + 18300 := by omega
                                                                                                                                        rw [heq]
                                                                                                                                        exact le_w366 ⟨n - 18300, hr⟩
                                                                                                                                      · by_cases h67 : n < 18400
                                                                                                                                        · have hr : n - 18350 < 50 := by omega
                                                                                                                                          have heq : n = (n - 18350) + 18350 := by omega
                                                                                                                                          rw [heq]
                                                                                                                                          exact le_w367 ⟨n - 18350, hr⟩
                                                                                                                                        · by_cases h68 : n < 18450
                                                                                                                                          · have hr : n - 18400 < 50 := by omega
                                                                                                                                            have heq : n = (n - 18400) + 18400 := by omega
                                                                                                                                            rw [heq]
                                                                                                                                            exact le_w368 ⟨n - 18400, hr⟩
                                                                                                                                          · by_cases h69 : n < 18500
                                                                                                                                            · have hr : n - 18450 < 50 := by omega
                                                                                                                                              have heq : n = (n - 18450) + 18450 := by omega
                                                                                                                                              rw [heq]
                                                                                                                                              exact le_w369 ⟨n - 18450, hr⟩
                                                                                                                                            · by_cases h70 : n < 18550
                                                                                                                                              · have hr : n - 18500 < 50 := by omega
                                                                                                                                                have heq : n = (n - 18500) + 18500 := by omega
                                                                                                                                                rw [heq]
                                                                                                                                                exact le_w370 ⟨n - 18500, hr⟩
                                                                                                                                              · by_cases h71 : n < 18600
                                                                                                                                                · have hr : n - 18550 < 50 := by omega
                                                                                                                                                  have heq : n = (n - 18550) + 18550 := by omega
                                                                                                                                                  rw [heq]
                                                                                                                                                  exact le_w371 ⟨n - 18550, hr⟩
                                                                                                                                                · by_cases h72 : n < 18650
                                                                                                                                                  · have hr : n - 18600 < 50 := by omega
                                                                                                                                                    have heq : n = (n - 18600) + 18600 := by omega
                                                                                                                                                    rw [heq]
                                                                                                                                                    exact le_w372 ⟨n - 18600, hr⟩
                                                                                                                                                  · by_cases h73 : n < 18700
                                                                                                                                                    · have hr : n - 18650 < 50 := by omega
                                                                                                                                                      have heq : n = (n - 18650) + 18650 := by omega
                                                                                                                                                      rw [heq]
                                                                                                                                                      exact le_w373 ⟨n - 18650, hr⟩
                                                                                                                                                    · by_cases h74 : n < 18750
                                                                                                                                                      · have hr : n - 18700 < 50 := by omega
                                                                                                                                                        have heq : n = (n - 18700) + 18700 := by omega
                                                                                                                                                        rw [heq]
                                                                                                                                                        exact le_w374 ⟨n - 18700, hr⟩
                                                                                                                                                      · by_cases h75 : n < 18800
                                                                                                                                                        · have hr : n - 18750 < 50 := by omega
                                                                                                                                                          have heq : n = (n - 18750) + 18750 := by omega
                                                                                                                                                          rw [heq]
                                                                                                                                                          exact le_w375 ⟨n - 18750, hr⟩
                                                                                                                                                        · by_cases h76 : n < 18850
                                                                                                                                                          · have hr : n - 18800 < 50 := by omega
                                                                                                                                                            have heq : n = (n - 18800) + 18800 := by omega
                                                                                                                                                            rw [heq]
                                                                                                                                                            exact le_w376 ⟨n - 18800, hr⟩
                                                                                                                                                          · by_cases h77 : n < 18900
                                                                                                                                                            · have hr : n - 18850 < 50 := by omega
                                                                                                                                                              have heq : n = (n - 18850) + 18850 := by omega
                                                                                                                                                              rw [heq]
                                                                                                                                                              exact le_w377 ⟨n - 18850, hr⟩
                                                                                                                                                            · by_cases h78 : n < 18950
                                                                                                                                                              · have hr : n - 18900 < 50 := by omega
                                                                                                                                                                have heq : n = (n - 18900) + 18900 := by omega
                                                                                                                                                                rw [heq]
                                                                                                                                                                exact le_w378 ⟨n - 18900, hr⟩
                                                                                                                                                              · by_cases h79 : n < 19000
                                                                                                                                                                · have hr : n - 18950 < 50 := by omega
                                                                                                                                                                  have heq : n = (n - 18950) + 18950 := by omega
                                                                                                                                                                  rw [heq]
                                                                                                                                                                  exact le_w379 ⟨n - 18950, hr⟩
                                                                                                                                                                · by_cases h80 : n < 19050
                                                                                                                                                                  · have hr : n - 19000 < 50 := by omega
                                                                                                                                                                    have heq : n = (n - 19000) + 19000 := by omega
                                                                                                                                                                    rw [heq]
                                                                                                                                                                    exact le_w380 ⟨n - 19000, hr⟩
                                                                                                                                                                  · by_cases h81 : n < 19100
                                                                                                                                                                    · have hr : n - 19050 < 50 := by omega
                                                                                                                                                                      have heq : n = (n - 19050) + 19050 := by omega
                                                                                                                                                                      rw [heq]
                                                                                                                                                                      exact le_w381 ⟨n - 19050, hr⟩
                                                                                                                                                                    · by_cases h82 : n < 19150
                                                                                                                                                                      · have hr : n - 19100 < 50 := by omega
                                                                                                                                                                        have heq : n = (n - 19100) + 19100 := by omega
                                                                                                                                                                        rw [heq]
                                                                                                                                                                        exact le_w382 ⟨n - 19100, hr⟩
                                                                                                                                                                      · by_cases h83 : n < 19200
                                                                                                                                                                        · have hr : n - 19150 < 50 := by omega
                                                                                                                                                                          have heq : n = (n - 19150) + 19150 := by omega
                                                                                                                                                                          rw [heq]
                                                                                                                                                                          exact le_w383 ⟨n - 19150, hr⟩
                                                                                                                                                                        · by_cases h84 : n < 19250
                                                                                                                                                                          · have hr : n - 19200 < 50 := by omega
                                                                                                                                                                            have heq : n = (n - 19200) + 19200 := by omega
                                                                                                                                                                            rw [heq]
                                                                                                                                                                            exact le_w384 ⟨n - 19200, hr⟩
                                                                                                                                                                          · by_cases h85 : n < 19300
                                                                                                                                                                            · have hr : n - 19250 < 50 := by omega
                                                                                                                                                                              have heq : n = (n - 19250) + 19250 := by omega
                                                                                                                                                                              rw [heq]
                                                                                                                                                                              exact le_w385 ⟨n - 19250, hr⟩
                                                                                                                                                                            · by_cases h86 : n < 19350
                                                                                                                                                                              · have hr : n - 19300 < 50 := by omega
                                                                                                                                                                                have heq : n = (n - 19300) + 19300 := by omega
                                                                                                                                                                                rw [heq]
                                                                                                                                                                                exact le_w386 ⟨n - 19300, hr⟩
                                                                                                                                                                              · by_cases h87 : n < 19400
                                                                                                                                                                                · have hr : n - 19350 < 50 := by omega
                                                                                                                                                                                  have heq : n = (n - 19350) + 19350 := by omega
                                                                                                                                                                                  rw [heq]
                                                                                                                                                                                  exact le_w387 ⟨n - 19350, hr⟩
                                                                                                                                                                                · by_cases h88 : n < 19450
                                                                                                                                                                                  · have hr : n - 19400 < 50 := by omega
                                                                                                                                                                                    have heq : n = (n - 19400) + 19400 := by omega
                                                                                                                                                                                    rw [heq]
                                                                                                                                                                                    exact le_w388 ⟨n - 19400, hr⟩
                                                                                                                                                                                  · by_cases h89 : n < 19500
                                                                                                                                                                                    · have hr : n - 19450 < 50 := by omega
                                                                                                                                                                                      have heq : n = (n - 19450) + 19450 := by omega
                                                                                                                                                                                      rw [heq]
                                                                                                                                                                                      exact le_w389 ⟨n - 19450, hr⟩
                                                                                                                                                                                    · by_cases h90 : n < 19550
                                                                                                                                                                                      · have hr : n - 19500 < 50 := by omega
                                                                                                                                                                                        have heq : n = (n - 19500) + 19500 := by omega
                                                                                                                                                                                        rw [heq]
                                                                                                                                                                                        exact le_w390 ⟨n - 19500, hr⟩
                                                                                                                                                                                      · by_cases h91 : n < 19600
                                                                                                                                                                                        · have hr : n - 19550 < 50 := by omega
                                                                                                                                                                                          have heq : n = (n - 19550) + 19550 := by omega
                                                                                                                                                                                          rw [heq]
                                                                                                                                                                                          exact le_w391 ⟨n - 19550, hr⟩
                                                                                                                                                                                        · by_cases h92 : n < 19650
                                                                                                                                                                                          · have hr : n - 19600 < 50 := by omega
                                                                                                                                                                                            have heq : n = (n - 19600) + 19600 := by omega
                                                                                                                                                                                            rw [heq]
                                                                                                                                                                                            exact le_w392 ⟨n - 19600, hr⟩
                                                                                                                                                                                          · by_cases h93 : n < 19700
                                                                                                                                                                                            · have hr : n - 19650 < 50 := by omega
                                                                                                                                                                                              have heq : n = (n - 19650) + 19650 := by omega
                                                                                                                                                                                              rw [heq]
                                                                                                                                                                                              exact le_w393 ⟨n - 19650, hr⟩
                                                                                                                                                                                            · by_cases h94 : n < 19750
                                                                                                                                                                                              · have hr : n - 19700 < 50 := by omega
                                                                                                                                                                                                have heq : n = (n - 19700) + 19700 := by omega
                                                                                                                                                                                                rw [heq]
                                                                                                                                                                                                exact le_w394 ⟨n - 19700, hr⟩
                                                                                                                                                                                              · by_cases h95 : n < 19800
                                                                                                                                                                                                · have hr : n - 19750 < 50 := by omega
                                                                                                                                                                                                  have heq : n = (n - 19750) + 19750 := by omega
                                                                                                                                                                                                  rw [heq]
                                                                                                                                                                                                  exact le_w395 ⟨n - 19750, hr⟩
                                                                                                                                                                                                · by_cases h96 : n < 19850
                                                                                                                                                                                                  · have hr : n - 19800 < 50 := by omega
                                                                                                                                                                                                    have heq : n = (n - 19800) + 19800 := by omega
                                                                                                                                                                                                    rw [heq]
                                                                                                                                                                                                    exact le_w396 ⟨n - 19800, hr⟩
                                                                                                                                                                                                  · by_cases h97 : n < 19900
                                                                                                                                                                                                    · have hr : n - 19850 < 50 := by omega
                                                                                                                                                                                                      have heq : n = (n - 19850) + 19850 := by omega
                                                                                                                                                                                                      rw [heq]
                                                                                                                                                                                                      exact le_w397 ⟨n - 19850, hr⟩
                                                                                                                                                                                                    · by_cases h98 : n < 19950
                                                                                                                                                                                                      · have hr : n - 19900 < 50 := by omega
                                                                                                                                                                                                        have heq : n = (n - 19900) + 19900 := by omega
                                                                                                                                                                                                        rw [heq]
                                                                                                                                                                                                        exact le_w398 ⟨n - 19900, hr⟩
                                                                                                                                                                                                      · by_cases h99 : n < 20000
                                                                                                                                                                                                        · have hr : n - 19950 < 50 := by omega
                                                                                                                                                                                                          have heq : n = (n - 19950) + 19950 := by omega
                                                                                                                                                                                                          rw [heq]
                                                                                                                                                                                                          exact le_w399 ⟨n - 19950, hr⟩
                                                                                                                                                                                                        · omega

theorem dimF_pos_range : ∀ n, 15000 ≤ n → n < 20000 → 0 < dimF n := by
  intro n hlo hhi
  by_cases h0 : n < 15050
  · have hr : n - 15000 < 50 := by omega
    have heq : n = (n - 15000) + 15000 := by omega
    rw [heq]
    exact pos_w300 ⟨n - 15000, hr⟩
  · by_cases h1 : n < 15100
    · have hr : n - 15050 < 50 := by omega
      have heq : n = (n - 15050) + 15050 := by omega
      rw [heq]
      exact pos_w301 ⟨n - 15050, hr⟩
    · by_cases h2 : n < 15150
      · have hr : n - 15100 < 50 := by omega
        have heq : n = (n - 15100) + 15100 := by omega
        rw [heq]
        exact pos_w302 ⟨n - 15100, hr⟩
      · by_cases h3 : n < 15200
        · have hr : n - 15150 < 50 := by omega
          have heq : n = (n - 15150) + 15150 := by omega
          rw [heq]
          exact pos_w303 ⟨n - 15150, hr⟩
        · by_cases h4 : n < 15250
          · have hr : n - 15200 < 50 := by omega
            have heq : n = (n - 15200) + 15200 := by omega
            rw [heq]
            exact pos_w304 ⟨n - 15200, hr⟩
          · by_cases h5 : n < 15300
            · have hr : n - 15250 < 50 := by omega
              have heq : n = (n - 15250) + 15250 := by omega
              rw [heq]
              exact pos_w305 ⟨n - 15250, hr⟩
            · by_cases h6 : n < 15350
              · have hr : n - 15300 < 50 := by omega
                have heq : n = (n - 15300) + 15300 := by omega
                rw [heq]
                exact pos_w306 ⟨n - 15300, hr⟩
              · by_cases h7 : n < 15400
                · have hr : n - 15350 < 50 := by omega
                  have heq : n = (n - 15350) + 15350 := by omega
                  rw [heq]
                  exact pos_w307 ⟨n - 15350, hr⟩
                · by_cases h8 : n < 15450
                  · have hr : n - 15400 < 50 := by omega
                    have heq : n = (n - 15400) + 15400 := by omega
                    rw [heq]
                    exact pos_w308 ⟨n - 15400, hr⟩
                  · by_cases h9 : n < 15500
                    · have hr : n - 15450 < 50 := by omega
                      have heq : n = (n - 15450) + 15450 := by omega
                      rw [heq]
                      exact pos_w309 ⟨n - 15450, hr⟩
                    · by_cases h10 : n < 15550
                      · have hr : n - 15500 < 50 := by omega
                        have heq : n = (n - 15500) + 15500 := by omega
                        rw [heq]
                        exact pos_w310 ⟨n - 15500, hr⟩
                      · by_cases h11 : n < 15600
                        · have hr : n - 15550 < 50 := by omega
                          have heq : n = (n - 15550) + 15550 := by omega
                          rw [heq]
                          exact pos_w311 ⟨n - 15550, hr⟩
                        · by_cases h12 : n < 15650
                          · have hr : n - 15600 < 50 := by omega
                            have heq : n = (n - 15600) + 15600 := by omega
                            rw [heq]
                            exact pos_w312 ⟨n - 15600, hr⟩
                          · by_cases h13 : n < 15700
                            · have hr : n - 15650 < 50 := by omega
                              have heq : n = (n - 15650) + 15650 := by omega
                              rw [heq]
                              exact pos_w313 ⟨n - 15650, hr⟩
                            · by_cases h14 : n < 15750
                              · have hr : n - 15700 < 50 := by omega
                                have heq : n = (n - 15700) + 15700 := by omega
                                rw [heq]
                                exact pos_w314 ⟨n - 15700, hr⟩
                              · by_cases h15 : n < 15800
                                · have hr : n - 15750 < 50 := by omega
                                  have heq : n = (n - 15750) + 15750 := by omega
                                  rw [heq]
                                  exact pos_w315 ⟨n - 15750, hr⟩
                                · by_cases h16 : n < 15850
                                  · have hr : n - 15800 < 50 := by omega
                                    have heq : n = (n - 15800) + 15800 := by omega
                                    rw [heq]
                                    exact pos_w316 ⟨n - 15800, hr⟩
                                  · by_cases h17 : n < 15900
                                    · have hr : n - 15850 < 50 := by omega
                                      have heq : n = (n - 15850) + 15850 := by omega
                                      rw [heq]
                                      exact pos_w317 ⟨n - 15850, hr⟩
                                    · by_cases h18 : n < 15950
                                      · have hr : n - 15900 < 50 := by omega
                                        have heq : n = (n - 15900) + 15900 := by omega
                                        rw [heq]
                                        exact pos_w318 ⟨n - 15900, hr⟩
                                      · by_cases h19 : n < 16000
                                        · have hr : n - 15950 < 50 := by omega
                                          have heq : n = (n - 15950) + 15950 := by omega
                                          rw [heq]
                                          exact pos_w319 ⟨n - 15950, hr⟩
                                        · by_cases h20 : n < 16050
                                          · have hr : n - 16000 < 50 := by omega
                                            have heq : n = (n - 16000) + 16000 := by omega
                                            rw [heq]
                                            exact pos_w320 ⟨n - 16000, hr⟩
                                          · by_cases h21 : n < 16100
                                            · have hr : n - 16050 < 50 := by omega
                                              have heq : n = (n - 16050) + 16050 := by omega
                                              rw [heq]
                                              exact pos_w321 ⟨n - 16050, hr⟩
                                            · by_cases h22 : n < 16150
                                              · have hr : n - 16100 < 50 := by omega
                                                have heq : n = (n - 16100) + 16100 := by omega
                                                rw [heq]
                                                exact pos_w322 ⟨n - 16100, hr⟩
                                              · by_cases h23 : n < 16200
                                                · have hr : n - 16150 < 50 := by omega
                                                  have heq : n = (n - 16150) + 16150 := by omega
                                                  rw [heq]
                                                  exact pos_w323 ⟨n - 16150, hr⟩
                                                · by_cases h24 : n < 16250
                                                  · have hr : n - 16200 < 50 := by omega
                                                    have heq : n = (n - 16200) + 16200 := by omega
                                                    rw [heq]
                                                    exact pos_w324 ⟨n - 16200, hr⟩
                                                  · by_cases h25 : n < 16300
                                                    · have hr : n - 16250 < 50 := by omega
                                                      have heq : n = (n - 16250) + 16250 := by omega
                                                      rw [heq]
                                                      exact pos_w325 ⟨n - 16250, hr⟩
                                                    · by_cases h26 : n < 16350
                                                      · have hr : n - 16300 < 50 := by omega
                                                        have heq : n = (n - 16300) + 16300 := by omega
                                                        rw [heq]
                                                        exact pos_w326 ⟨n - 16300, hr⟩
                                                      · by_cases h27 : n < 16400
                                                        · have hr : n - 16350 < 50 := by omega
                                                          have heq : n = (n - 16350) + 16350 := by omega
                                                          rw [heq]
                                                          exact pos_w327 ⟨n - 16350, hr⟩
                                                        · by_cases h28 : n < 16450
                                                          · have hr : n - 16400 < 50 := by omega
                                                            have heq : n = (n - 16400) + 16400 := by omega
                                                            rw [heq]
                                                            exact pos_w328 ⟨n - 16400, hr⟩
                                                          · by_cases h29 : n < 16500
                                                            · have hr : n - 16450 < 50 := by omega
                                                              have heq : n = (n - 16450) + 16450 := by omega
                                                              rw [heq]
                                                              exact pos_w329 ⟨n - 16450, hr⟩
                                                            · by_cases h30 : n < 16550
                                                              · have hr : n - 16500 < 50 := by omega
                                                                have heq : n = (n - 16500) + 16500 := by omega
                                                                rw [heq]
                                                                exact pos_w330 ⟨n - 16500, hr⟩
                                                              · by_cases h31 : n < 16600
                                                                · have hr : n - 16550 < 50 := by omega
                                                                  have heq : n = (n - 16550) + 16550 := by omega
                                                                  rw [heq]
                                                                  exact pos_w331 ⟨n - 16550, hr⟩
                                                                · by_cases h32 : n < 16650
                                                                  · have hr : n - 16600 < 50 := by omega
                                                                    have heq : n = (n - 16600) + 16600 := by omega
                                                                    rw [heq]
                                                                    exact pos_w332 ⟨n - 16600, hr⟩
                                                                  · by_cases h33 : n < 16700
                                                                    · have hr : n - 16650 < 50 := by omega
                                                                      have heq : n = (n - 16650) + 16650 := by omega
                                                                      rw [heq]
                                                                      exact pos_w333 ⟨n - 16650, hr⟩
                                                                    · by_cases h34 : n < 16750
                                                                      · have hr : n - 16700 < 50 := by omega
                                                                        have heq : n = (n - 16700) + 16700 := by omega
                                                                        rw [heq]
                                                                        exact pos_w334 ⟨n - 16700, hr⟩
                                                                      · by_cases h35 : n < 16800
                                                                        · have hr : n - 16750 < 50 := by omega
                                                                          have heq : n = (n - 16750) + 16750 := by omega
                                                                          rw [heq]
                                                                          exact pos_w335 ⟨n - 16750, hr⟩
                                                                        · by_cases h36 : n < 16850
                                                                          · have hr : n - 16800 < 50 := by omega
                                                                            have heq : n = (n - 16800) + 16800 := by omega
                                                                            rw [heq]
                                                                            exact pos_w336 ⟨n - 16800, hr⟩
                                                                          · by_cases h37 : n < 16900
                                                                            · have hr : n - 16850 < 50 := by omega
                                                                              have heq : n = (n - 16850) + 16850 := by omega
                                                                              rw [heq]
                                                                              exact pos_w337 ⟨n - 16850, hr⟩
                                                                            · by_cases h38 : n < 16950
                                                                              · have hr : n - 16900 < 50 := by omega
                                                                                have heq : n = (n - 16900) + 16900 := by omega
                                                                                rw [heq]
                                                                                exact pos_w338 ⟨n - 16900, hr⟩
                                                                              · by_cases h39 : n < 17000
                                                                                · have hr : n - 16950 < 50 := by omega
                                                                                  have heq : n = (n - 16950) + 16950 := by omega
                                                                                  rw [heq]
                                                                                  exact pos_w339 ⟨n - 16950, hr⟩
                                                                                · by_cases h40 : n < 17050
                                                                                  · have hr : n - 17000 < 50 := by omega
                                                                                    have heq : n = (n - 17000) + 17000 := by omega
                                                                                    rw [heq]
                                                                                    exact pos_w340 ⟨n - 17000, hr⟩
                                                                                  · by_cases h41 : n < 17100
                                                                                    · have hr : n - 17050 < 50 := by omega
                                                                                      have heq : n = (n - 17050) + 17050 := by omega
                                                                                      rw [heq]
                                                                                      exact pos_w341 ⟨n - 17050, hr⟩
                                                                                    · by_cases h42 : n < 17150
                                                                                      · have hr : n - 17100 < 50 := by omega
                                                                                        have heq : n = (n - 17100) + 17100 := by omega
                                                                                        rw [heq]
                                                                                        exact pos_w342 ⟨n - 17100, hr⟩
                                                                                      · by_cases h43 : n < 17200
                                                                                        · have hr : n - 17150 < 50 := by omega
                                                                                          have heq : n = (n - 17150) + 17150 := by omega
                                                                                          rw [heq]
                                                                                          exact pos_w343 ⟨n - 17150, hr⟩
                                                                                        · by_cases h44 : n < 17250
                                                                                          · have hr : n - 17200 < 50 := by omega
                                                                                            have heq : n = (n - 17200) + 17200 := by omega
                                                                                            rw [heq]
                                                                                            exact pos_w344 ⟨n - 17200, hr⟩
                                                                                          · by_cases h45 : n < 17300
                                                                                            · have hr : n - 17250 < 50 := by omega
                                                                                              have heq : n = (n - 17250) + 17250 := by omega
                                                                                              rw [heq]
                                                                                              exact pos_w345 ⟨n - 17250, hr⟩
                                                                                            · by_cases h46 : n < 17350
                                                                                              · have hr : n - 17300 < 50 := by omega
                                                                                                have heq : n = (n - 17300) + 17300 := by omega
                                                                                                rw [heq]
                                                                                                exact pos_w346 ⟨n - 17300, hr⟩
                                                                                              · by_cases h47 : n < 17400
                                                                                                · have hr : n - 17350 < 50 := by omega
                                                                                                  have heq : n = (n - 17350) + 17350 := by omega
                                                                                                  rw [heq]
                                                                                                  exact pos_w347 ⟨n - 17350, hr⟩
                                                                                                · by_cases h48 : n < 17450
                                                                                                  · have hr : n - 17400 < 50 := by omega
                                                                                                    have heq : n = (n - 17400) + 17400 := by omega
                                                                                                    rw [heq]
                                                                                                    exact pos_w348 ⟨n - 17400, hr⟩
                                                                                                  · by_cases h49 : n < 17500
                                                                                                    · have hr : n - 17450 < 50 := by omega
                                                                                                      have heq : n = (n - 17450) + 17450 := by omega
                                                                                                      rw [heq]
                                                                                                      exact pos_w349 ⟨n - 17450, hr⟩
                                                                                                    · by_cases h50 : n < 17550
                                                                                                      · have hr : n - 17500 < 50 := by omega
                                                                                                        have heq : n = (n - 17500) + 17500 := by omega
                                                                                                        rw [heq]
                                                                                                        exact pos_w350 ⟨n - 17500, hr⟩
                                                                                                      · by_cases h51 : n < 17600
                                                                                                        · have hr : n - 17550 < 50 := by omega
                                                                                                          have heq : n = (n - 17550) + 17550 := by omega
                                                                                                          rw [heq]
                                                                                                          exact pos_w351 ⟨n - 17550, hr⟩
                                                                                                        · by_cases h52 : n < 17650
                                                                                                          · have hr : n - 17600 < 50 := by omega
                                                                                                            have heq : n = (n - 17600) + 17600 := by omega
                                                                                                            rw [heq]
                                                                                                            exact pos_w352 ⟨n - 17600, hr⟩
                                                                                                          · by_cases h53 : n < 17700
                                                                                                            · have hr : n - 17650 < 50 := by omega
                                                                                                              have heq : n = (n - 17650) + 17650 := by omega
                                                                                                              rw [heq]
                                                                                                              exact pos_w353 ⟨n - 17650, hr⟩
                                                                                                            · by_cases h54 : n < 17750
                                                                                                              · have hr : n - 17700 < 50 := by omega
                                                                                                                have heq : n = (n - 17700) + 17700 := by omega
                                                                                                                rw [heq]
                                                                                                                exact pos_w354 ⟨n - 17700, hr⟩
                                                                                                              · by_cases h55 : n < 17800
                                                                                                                · have hr : n - 17750 < 50 := by omega
                                                                                                                  have heq : n = (n - 17750) + 17750 := by omega
                                                                                                                  rw [heq]
                                                                                                                  exact pos_w355 ⟨n - 17750, hr⟩
                                                                                                                · by_cases h56 : n < 17850
                                                                                                                  · have hr : n - 17800 < 50 := by omega
                                                                                                                    have heq : n = (n - 17800) + 17800 := by omega
                                                                                                                    rw [heq]
                                                                                                                    exact pos_w356 ⟨n - 17800, hr⟩
                                                                                                                  · by_cases h57 : n < 17900
                                                                                                                    · have hr : n - 17850 < 50 := by omega
                                                                                                                      have heq : n = (n - 17850) + 17850 := by omega
                                                                                                                      rw [heq]
                                                                                                                      exact pos_w357 ⟨n - 17850, hr⟩
                                                                                                                    · by_cases h58 : n < 17950
                                                                                                                      · have hr : n - 17900 < 50 := by omega
                                                                                                                        have heq : n = (n - 17900) + 17900 := by omega
                                                                                                                        rw [heq]
                                                                                                                        exact pos_w358 ⟨n - 17900, hr⟩
                                                                                                                      · by_cases h59 : n < 18000
                                                                                                                        · have hr : n - 17950 < 50 := by omega
                                                                                                                          have heq : n = (n - 17950) + 17950 := by omega
                                                                                                                          rw [heq]
                                                                                                                          exact pos_w359 ⟨n - 17950, hr⟩
                                                                                                                        · by_cases h60 : n < 18050
                                                                                                                          · have hr : n - 18000 < 50 := by omega
                                                                                                                            have heq : n = (n - 18000) + 18000 := by omega
                                                                                                                            rw [heq]
                                                                                                                            exact pos_w360 ⟨n - 18000, hr⟩
                                                                                                                          · by_cases h61 : n < 18100
                                                                                                                            · have hr : n - 18050 < 50 := by omega
                                                                                                                              have heq : n = (n - 18050) + 18050 := by omega
                                                                                                                              rw [heq]
                                                                                                                              exact pos_w361 ⟨n - 18050, hr⟩
                                                                                                                            · by_cases h62 : n < 18150
                                                                                                                              · have hr : n - 18100 < 50 := by omega
                                                                                                                                have heq : n = (n - 18100) + 18100 := by omega
                                                                                                                                rw [heq]
                                                                                                                                exact pos_w362 ⟨n - 18100, hr⟩
                                                                                                                              · by_cases h63 : n < 18200
                                                                                                                                · have hr : n - 18150 < 50 := by omega
                                                                                                                                  have heq : n = (n - 18150) + 18150 := by omega
                                                                                                                                  rw [heq]
                                                                                                                                  exact pos_w363 ⟨n - 18150, hr⟩
                                                                                                                                · by_cases h64 : n < 18250
                                                                                                                                  · have hr : n - 18200 < 50 := by omega
                                                                                                                                    have heq : n = (n - 18200) + 18200 := by omega
                                                                                                                                    rw [heq]
                                                                                                                                    exact pos_w364 ⟨n - 18200, hr⟩
                                                                                                                                  · by_cases h65 : n < 18300
                                                                                                                                    · have hr : n - 18250 < 50 := by omega
                                                                                                                                      have heq : n = (n - 18250) + 18250 := by omega
                                                                                                                                      rw [heq]
                                                                                                                                      exact pos_w365 ⟨n - 18250, hr⟩
                                                                                                                                    · by_cases h66 : n < 18350
                                                                                                                                      · have hr : n - 18300 < 50 := by omega
                                                                                                                                        have heq : n = (n - 18300) + 18300 := by omega
                                                                                                                                        rw [heq]
                                                                                                                                        exact pos_w366 ⟨n - 18300, hr⟩
                                                                                                                                      · by_cases h67 : n < 18400
                                                                                                                                        · have hr : n - 18350 < 50 := by omega
                                                                                                                                          have heq : n = (n - 18350) + 18350 := by omega
                                                                                                                                          rw [heq]
                                                                                                                                          exact pos_w367 ⟨n - 18350, hr⟩
                                                                                                                                        · by_cases h68 : n < 18450
                                                                                                                                          · have hr : n - 18400 < 50 := by omega
                                                                                                                                            have heq : n = (n - 18400) + 18400 := by omega
                                                                                                                                            rw [heq]
                                                                                                                                            exact pos_w368 ⟨n - 18400, hr⟩
                                                                                                                                          · by_cases h69 : n < 18500
                                                                                                                                            · have hr : n - 18450 < 50 := by omega
                                                                                                                                              have heq : n = (n - 18450) + 18450 := by omega
                                                                                                                                              rw [heq]
                                                                                                                                              exact pos_w369 ⟨n - 18450, hr⟩
                                                                                                                                            · by_cases h70 : n < 18550
                                                                                                                                              · have hr : n - 18500 < 50 := by omega
                                                                                                                                                have heq : n = (n - 18500) + 18500 := by omega
                                                                                                                                                rw [heq]
                                                                                                                                                exact pos_w370 ⟨n - 18500, hr⟩
                                                                                                                                              · by_cases h71 : n < 18600
                                                                                                                                                · have hr : n - 18550 < 50 := by omega
                                                                                                                                                  have heq : n = (n - 18550) + 18550 := by omega
                                                                                                                                                  rw [heq]
                                                                                                                                                  exact pos_w371 ⟨n - 18550, hr⟩
                                                                                                                                                · by_cases h72 : n < 18650
                                                                                                                                                  · have hr : n - 18600 < 50 := by omega
                                                                                                                                                    have heq : n = (n - 18600) + 18600 := by omega
                                                                                                                                                    rw [heq]
                                                                                                                                                    exact pos_w372 ⟨n - 18600, hr⟩
                                                                                                                                                  · by_cases h73 : n < 18700
                                                                                                                                                    · have hr : n - 18650 < 50 := by omega
                                                                                                                                                      have heq : n = (n - 18650) + 18650 := by omega
                                                                                                                                                      rw [heq]
                                                                                                                                                      exact pos_w373 ⟨n - 18650, hr⟩
                                                                                                                                                    · by_cases h74 : n < 18750
                                                                                                                                                      · have hr : n - 18700 < 50 := by omega
                                                                                                                                                        have heq : n = (n - 18700) + 18700 := by omega
                                                                                                                                                        rw [heq]
                                                                                                                                                        exact pos_w374 ⟨n - 18700, hr⟩
                                                                                                                                                      · by_cases h75 : n < 18800
                                                                                                                                                        · have hr : n - 18750 < 50 := by omega
                                                                                                                                                          have heq : n = (n - 18750) + 18750 := by omega
                                                                                                                                                          rw [heq]
                                                                                                                                                          exact pos_w375 ⟨n - 18750, hr⟩
                                                                                                                                                        · by_cases h76 : n < 18850
                                                                                                                                                          · have hr : n - 18800 < 50 := by omega
                                                                                                                                                            have heq : n = (n - 18800) + 18800 := by omega
                                                                                                                                                            rw [heq]
                                                                                                                                                            exact pos_w376 ⟨n - 18800, hr⟩
                                                                                                                                                          · by_cases h77 : n < 18900
                                                                                                                                                            · have hr : n - 18850 < 50 := by omega
                                                                                                                                                              have heq : n = (n - 18850) + 18850 := by omega
                                                                                                                                                              rw [heq]
                                                                                                                                                              exact pos_w377 ⟨n - 18850, hr⟩
                                                                                                                                                            · by_cases h78 : n < 18950
                                                                                                                                                              · have hr : n - 18900 < 50 := by omega
                                                                                                                                                                have heq : n = (n - 18900) + 18900 := by omega
                                                                                                                                                                rw [heq]
                                                                                                                                                                exact pos_w378 ⟨n - 18900, hr⟩
                                                                                                                                                              · by_cases h79 : n < 19000
                                                                                                                                                                · have hr : n - 18950 < 50 := by omega
                                                                                                                                                                  have heq : n = (n - 18950) + 18950 := by omega
                                                                                                                                                                  rw [heq]
                                                                                                                                                                  exact pos_w379 ⟨n - 18950, hr⟩
                                                                                                                                                                · by_cases h80 : n < 19050
                                                                                                                                                                  · have hr : n - 19000 < 50 := by omega
                                                                                                                                                                    have heq : n = (n - 19000) + 19000 := by omega
                                                                                                                                                                    rw [heq]
                                                                                                                                                                    exact pos_w380 ⟨n - 19000, hr⟩
                                                                                                                                                                  · by_cases h81 : n < 19100
                                                                                                                                                                    · have hr : n - 19050 < 50 := by omega
                                                                                                                                                                      have heq : n = (n - 19050) + 19050 := by omega
                                                                                                                                                                      rw [heq]
                                                                                                                                                                      exact pos_w381 ⟨n - 19050, hr⟩
                                                                                                                                                                    · by_cases h82 : n < 19150
                                                                                                                                                                      · have hr : n - 19100 < 50 := by omega
                                                                                                                                                                        have heq : n = (n - 19100) + 19100 := by omega
                                                                                                                                                                        rw [heq]
                                                                                                                                                                        exact pos_w382 ⟨n - 19100, hr⟩
                                                                                                                                                                      · by_cases h83 : n < 19200
                                                                                                                                                                        · have hr : n - 19150 < 50 := by omega
                                                                                                                                                                          have heq : n = (n - 19150) + 19150 := by omega
                                                                                                                                                                          rw [heq]
                                                                                                                                                                          exact pos_w383 ⟨n - 19150, hr⟩
                                                                                                                                                                        · by_cases h84 : n < 19250
                                                                                                                                                                          · have hr : n - 19200 < 50 := by omega
                                                                                                                                                                            have heq : n = (n - 19200) + 19200 := by omega
                                                                                                                                                                            rw [heq]
                                                                                                                                                                            exact pos_w384 ⟨n - 19200, hr⟩
                                                                                                                                                                          · by_cases h85 : n < 19300
                                                                                                                                                                            · have hr : n - 19250 < 50 := by omega
                                                                                                                                                                              have heq : n = (n - 19250) + 19250 := by omega
                                                                                                                                                                              rw [heq]
                                                                                                                                                                              exact pos_w385 ⟨n - 19250, hr⟩
                                                                                                                                                                            · by_cases h86 : n < 19350
                                                                                                                                                                              · have hr : n - 19300 < 50 := by omega
                                                                                                                                                                                have heq : n = (n - 19300) + 19300 := by omega
                                                                                                                                                                                rw [heq]
                                                                                                                                                                                exact pos_w386 ⟨n - 19300, hr⟩
                                                                                                                                                                              · by_cases h87 : n < 19400
                                                                                                                                                                                · have hr : n - 19350 < 50 := by omega
                                                                                                                                                                                  have heq : n = (n - 19350) + 19350 := by omega
                                                                                                                                                                                  rw [heq]
                                                                                                                                                                                  exact pos_w387 ⟨n - 19350, hr⟩
                                                                                                                                                                                · by_cases h88 : n < 19450
                                                                                                                                                                                  · have hr : n - 19400 < 50 := by omega
                                                                                                                                                                                    have heq : n = (n - 19400) + 19400 := by omega
                                                                                                                                                                                    rw [heq]
                                                                                                                                                                                    exact pos_w388 ⟨n - 19400, hr⟩
                                                                                                                                                                                  · by_cases h89 : n < 19500
                                                                                                                                                                                    · have hr : n - 19450 < 50 := by omega
                                                                                                                                                                                      have heq : n = (n - 19450) + 19450 := by omega
                                                                                                                                                                                      rw [heq]
                                                                                                                                                                                      exact pos_w389 ⟨n - 19450, hr⟩
                                                                                                                                                                                    · by_cases h90 : n < 19550
                                                                                                                                                                                      · have hr : n - 19500 < 50 := by omega
                                                                                                                                                                                        have heq : n = (n - 19500) + 19500 := by omega
                                                                                                                                                                                        rw [heq]
                                                                                                                                                                                        exact pos_w390 ⟨n - 19500, hr⟩
                                                                                                                                                                                      · by_cases h91 : n < 19600
                                                                                                                                                                                        · have hr : n - 19550 < 50 := by omega
                                                                                                                                                                                          have heq : n = (n - 19550) + 19550 := by omega
                                                                                                                                                                                          rw [heq]
                                                                                                                                                                                          exact pos_w391 ⟨n - 19550, hr⟩
                                                                                                                                                                                        · by_cases h92 : n < 19650
                                                                                                                                                                                          · have hr : n - 19600 < 50 := by omega
                                                                                                                                                                                            have heq : n = (n - 19600) + 19600 := by omega
                                                                                                                                                                                            rw [heq]
                                                                                                                                                                                            exact pos_w392 ⟨n - 19600, hr⟩
                                                                                                                                                                                          · by_cases h93 : n < 19700
                                                                                                                                                                                            · have hr : n - 19650 < 50 := by omega
                                                                                                                                                                                              have heq : n = (n - 19650) + 19650 := by omega
                                                                                                                                                                                              rw [heq]
                                                                                                                                                                                              exact pos_w393 ⟨n - 19650, hr⟩
                                                                                                                                                                                            · by_cases h94 : n < 19750
                                                                                                                                                                                              · have hr : n - 19700 < 50 := by omega
                                                                                                                                                                                                have heq : n = (n - 19700) + 19700 := by omega
                                                                                                                                                                                                rw [heq]
                                                                                                                                                                                                exact pos_w394 ⟨n - 19700, hr⟩
                                                                                                                                                                                              · by_cases h95 : n < 19800
                                                                                                                                                                                                · have hr : n - 19750 < 50 := by omega
                                                                                                                                                                                                  have heq : n = (n - 19750) + 19750 := by omega
                                                                                                                                                                                                  rw [heq]
                                                                                                                                                                                                  exact pos_w395 ⟨n - 19750, hr⟩
                                                                                                                                                                                                · by_cases h96 : n < 19850
                                                                                                                                                                                                  · have hr : n - 19800 < 50 := by omega
                                                                                                                                                                                                    have heq : n = (n - 19800) + 19800 := by omega
                                                                                                                                                                                                    rw [heq]
                                                                                                                                                                                                    exact pos_w396 ⟨n - 19800, hr⟩
                                                                                                                                                                                                  · by_cases h97 : n < 19900
                                                                                                                                                                                                    · have hr : n - 19850 < 50 := by omega
                                                                                                                                                                                                      have heq : n = (n - 19850) + 19850 := by omega
                                                                                                                                                                                                      rw [heq]
                                                                                                                                                                                                      exact pos_w397 ⟨n - 19850, hr⟩
                                                                                                                                                                                                    · by_cases h98 : n < 19950
                                                                                                                                                                                                      · have hr : n - 19900 < 50 := by omega
                                                                                                                                                                                                        have heq : n = (n - 19900) + 19900 := by omega
                                                                                                                                                                                                        rw [heq]
                                                                                                                                                                                                        exact pos_w398 ⟨n - 19900, hr⟩
                                                                                                                                                                                                      · by_cases h99 : n < 20000
                                                                                                                                                                                                        · have hr : n - 19950 < 50 := by omega
                                                                                                                                                                                                          have heq : n = (n - 19950) + 19950 := by omega
                                                                                                                                                                                                          rw [heq]
                                                                                                                                                                                                          exact pos_w399 ⟨n - 19950, hr⟩
                                                                                                                                                                                                        · omega

end IntMul.Kappa.R8.Bit.Oppbank.DimBound3


