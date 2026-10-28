-- Prove2me | Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankDimBound0
-- name    : IntMul_Kappa_R8_Data_BitOppbankDimBound0
-- status  : Definition
-- author  : @Ethan Cheung Wang
-- created : 2026-10-28T17:59:53.630191+00:00
-- url     : https://prove2.me/theorems/2a53c57d-22aa-4b4b-967b-fb09e756c723
-- title:
--   Densified dimF $\le 22$ pack 0 ($n<5000$)
-- statement:
--   Pack 0 of the densified dimension-field bound.
--
--   For every densified node index $n$ with $0\le n<5000$, the 5-bit field $\mathrm{dimF}(n)$ extracted from $\mathrm{DIMT}$ satisfies
--   $$1\le \mathrm{dimF}(n)\le 22.$$
--   Proved by `decide` on successive `Fin 50` windows (no `native_decide`).
-- source:
--   R8 BitNB densified DIMT field bound; Fin-window decide packs

-- DimBound pack 0: dimF bounds on n ∈ [0, 5000)

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

namespace IntMul.Kappa.R8.Bit.Oppbank.DimBound0

private theorem le_w0 : ∀ n : Fin 50, dimF (n.val + 0) ≤ 22 := by decide
private theorem pos_w0 : ∀ n : Fin 50, 0 < dimF (n.val + 0) := by decide
private theorem le_w1 : ∀ n : Fin 50, dimF (n.val + 50) ≤ 22 := by decide
private theorem pos_w1 : ∀ n : Fin 50, 0 < dimF (n.val + 50) := by decide
private theorem le_w2 : ∀ n : Fin 50, dimF (n.val + 100) ≤ 22 := by decide
private theorem pos_w2 : ∀ n : Fin 50, 0 < dimF (n.val + 100) := by decide
private theorem le_w3 : ∀ n : Fin 50, dimF (n.val + 150) ≤ 22 := by decide
private theorem pos_w3 : ∀ n : Fin 50, 0 < dimF (n.val + 150) := by decide
private theorem le_w4 : ∀ n : Fin 50, dimF (n.val + 200) ≤ 22 := by decide
private theorem pos_w4 : ∀ n : Fin 50, 0 < dimF (n.val + 200) := by decide
private theorem le_w5 : ∀ n : Fin 50, dimF (n.val + 250) ≤ 22 := by decide
private theorem pos_w5 : ∀ n : Fin 50, 0 < dimF (n.val + 250) := by decide
private theorem le_w6 : ∀ n : Fin 50, dimF (n.val + 300) ≤ 22 := by decide
private theorem pos_w6 : ∀ n : Fin 50, 0 < dimF (n.val + 300) := by decide
private theorem le_w7 : ∀ n : Fin 50, dimF (n.val + 350) ≤ 22 := by decide
private theorem pos_w7 : ∀ n : Fin 50, 0 < dimF (n.val + 350) := by decide
private theorem le_w8 : ∀ n : Fin 50, dimF (n.val + 400) ≤ 22 := by decide
private theorem pos_w8 : ∀ n : Fin 50, 0 < dimF (n.val + 400) := by decide
private theorem le_w9 : ∀ n : Fin 50, dimF (n.val + 450) ≤ 22 := by decide
private theorem pos_w9 : ∀ n : Fin 50, 0 < dimF (n.val + 450) := by decide
private theorem le_w10 : ∀ n : Fin 50, dimF (n.val + 500) ≤ 22 := by decide
private theorem pos_w10 : ∀ n : Fin 50, 0 < dimF (n.val + 500) := by decide
private theorem le_w11 : ∀ n : Fin 50, dimF (n.val + 550) ≤ 22 := by decide
private theorem pos_w11 : ∀ n : Fin 50, 0 < dimF (n.val + 550) := by decide
private theorem le_w12 : ∀ n : Fin 50, dimF (n.val + 600) ≤ 22 := by decide
private theorem pos_w12 : ∀ n : Fin 50, 0 < dimF (n.val + 600) := by decide
private theorem le_w13 : ∀ n : Fin 50, dimF (n.val + 650) ≤ 22 := by decide
private theorem pos_w13 : ∀ n : Fin 50, 0 < dimF (n.val + 650) := by decide
private theorem le_w14 : ∀ n : Fin 50, dimF (n.val + 700) ≤ 22 := by decide
private theorem pos_w14 : ∀ n : Fin 50, 0 < dimF (n.val + 700) := by decide
private theorem le_w15 : ∀ n : Fin 50, dimF (n.val + 750) ≤ 22 := by decide
private theorem pos_w15 : ∀ n : Fin 50, 0 < dimF (n.val + 750) := by decide
private theorem le_w16 : ∀ n : Fin 50, dimF (n.val + 800) ≤ 22 := by decide
private theorem pos_w16 : ∀ n : Fin 50, 0 < dimF (n.val + 800) := by decide
private theorem le_w17 : ∀ n : Fin 50, dimF (n.val + 850) ≤ 22 := by decide
private theorem pos_w17 : ∀ n : Fin 50, 0 < dimF (n.val + 850) := by decide
private theorem le_w18 : ∀ n : Fin 50, dimF (n.val + 900) ≤ 22 := by decide
private theorem pos_w18 : ∀ n : Fin 50, 0 < dimF (n.val + 900) := by decide
private theorem le_w19 : ∀ n : Fin 50, dimF (n.val + 950) ≤ 22 := by decide
private theorem pos_w19 : ∀ n : Fin 50, 0 < dimF (n.val + 950) := by decide
private theorem le_w20 : ∀ n : Fin 50, dimF (n.val + 1000) ≤ 22 := by decide
private theorem pos_w20 : ∀ n : Fin 50, 0 < dimF (n.val + 1000) := by decide
private theorem le_w21 : ∀ n : Fin 50, dimF (n.val + 1050) ≤ 22 := by decide
private theorem pos_w21 : ∀ n : Fin 50, 0 < dimF (n.val + 1050) := by decide
private theorem le_w22 : ∀ n : Fin 50, dimF (n.val + 1100) ≤ 22 := by decide
private theorem pos_w22 : ∀ n : Fin 50, 0 < dimF (n.val + 1100) := by decide
private theorem le_w23 : ∀ n : Fin 50, dimF (n.val + 1150) ≤ 22 := by decide
private theorem pos_w23 : ∀ n : Fin 50, 0 < dimF (n.val + 1150) := by decide
private theorem le_w24 : ∀ n : Fin 50, dimF (n.val + 1200) ≤ 22 := by decide
private theorem pos_w24 : ∀ n : Fin 50, 0 < dimF (n.val + 1200) := by decide
private theorem le_w25 : ∀ n : Fin 50, dimF (n.val + 1250) ≤ 22 := by decide
private theorem pos_w25 : ∀ n : Fin 50, 0 < dimF (n.val + 1250) := by decide
private theorem le_w26 : ∀ n : Fin 50, dimF (n.val + 1300) ≤ 22 := by decide
private theorem pos_w26 : ∀ n : Fin 50, 0 < dimF (n.val + 1300) := by decide
private theorem le_w27 : ∀ n : Fin 50, dimF (n.val + 1350) ≤ 22 := by decide
private theorem pos_w27 : ∀ n : Fin 50, 0 < dimF (n.val + 1350) := by decide
private theorem le_w28 : ∀ n : Fin 50, dimF (n.val + 1400) ≤ 22 := by decide
private theorem pos_w28 : ∀ n : Fin 50, 0 < dimF (n.val + 1400) := by decide
private theorem le_w29 : ∀ n : Fin 50, dimF (n.val + 1450) ≤ 22 := by decide
private theorem pos_w29 : ∀ n : Fin 50, 0 < dimF (n.val + 1450) := by decide
private theorem le_w30 : ∀ n : Fin 50, dimF (n.val + 1500) ≤ 22 := by decide
private theorem pos_w30 : ∀ n : Fin 50, 0 < dimF (n.val + 1500) := by decide
private theorem le_w31 : ∀ n : Fin 50, dimF (n.val + 1550) ≤ 22 := by decide
private theorem pos_w31 : ∀ n : Fin 50, 0 < dimF (n.val + 1550) := by decide
private theorem le_w32 : ∀ n : Fin 50, dimF (n.val + 1600) ≤ 22 := by decide
private theorem pos_w32 : ∀ n : Fin 50, 0 < dimF (n.val + 1600) := by decide
private theorem le_w33 : ∀ n : Fin 50, dimF (n.val + 1650) ≤ 22 := by decide
private theorem pos_w33 : ∀ n : Fin 50, 0 < dimF (n.val + 1650) := by decide
private theorem le_w34 : ∀ n : Fin 50, dimF (n.val + 1700) ≤ 22 := by decide
private theorem pos_w34 : ∀ n : Fin 50, 0 < dimF (n.val + 1700) := by decide
private theorem le_w35 : ∀ n : Fin 50, dimF (n.val + 1750) ≤ 22 := by decide
private theorem pos_w35 : ∀ n : Fin 50, 0 < dimF (n.val + 1750) := by decide
private theorem le_w36 : ∀ n : Fin 50, dimF (n.val + 1800) ≤ 22 := by decide
private theorem pos_w36 : ∀ n : Fin 50, 0 < dimF (n.val + 1800) := by decide
private theorem le_w37 : ∀ n : Fin 50, dimF (n.val + 1850) ≤ 22 := by decide
private theorem pos_w37 : ∀ n : Fin 50, 0 < dimF (n.val + 1850) := by decide
private theorem le_w38 : ∀ n : Fin 50, dimF (n.val + 1900) ≤ 22 := by decide
private theorem pos_w38 : ∀ n : Fin 50, 0 < dimF (n.val + 1900) := by decide
private theorem le_w39 : ∀ n : Fin 50, dimF (n.val + 1950) ≤ 22 := by decide
private theorem pos_w39 : ∀ n : Fin 50, 0 < dimF (n.val + 1950) := by decide
private theorem le_w40 : ∀ n : Fin 50, dimF (n.val + 2000) ≤ 22 := by decide
private theorem pos_w40 : ∀ n : Fin 50, 0 < dimF (n.val + 2000) := by decide
private theorem le_w41 : ∀ n : Fin 50, dimF (n.val + 2050) ≤ 22 := by decide
private theorem pos_w41 : ∀ n : Fin 50, 0 < dimF (n.val + 2050) := by decide
private theorem le_w42 : ∀ n : Fin 50, dimF (n.val + 2100) ≤ 22 := by decide
private theorem pos_w42 : ∀ n : Fin 50, 0 < dimF (n.val + 2100) := by decide
private theorem le_w43 : ∀ n : Fin 50, dimF (n.val + 2150) ≤ 22 := by decide
private theorem pos_w43 : ∀ n : Fin 50, 0 < dimF (n.val + 2150) := by decide
private theorem le_w44 : ∀ n : Fin 50, dimF (n.val + 2200) ≤ 22 := by decide
private theorem pos_w44 : ∀ n : Fin 50, 0 < dimF (n.val + 2200) := by decide
private theorem le_w45 : ∀ n : Fin 50, dimF (n.val + 2250) ≤ 22 := by decide
private theorem pos_w45 : ∀ n : Fin 50, 0 < dimF (n.val + 2250) := by decide
private theorem le_w46 : ∀ n : Fin 50, dimF (n.val + 2300) ≤ 22 := by decide
private theorem pos_w46 : ∀ n : Fin 50, 0 < dimF (n.val + 2300) := by decide
private theorem le_w47 : ∀ n : Fin 50, dimF (n.val + 2350) ≤ 22 := by decide
private theorem pos_w47 : ∀ n : Fin 50, 0 < dimF (n.val + 2350) := by decide
private theorem le_w48 : ∀ n : Fin 50, dimF (n.val + 2400) ≤ 22 := by decide
private theorem pos_w48 : ∀ n : Fin 50, 0 < dimF (n.val + 2400) := by decide
private theorem le_w49 : ∀ n : Fin 50, dimF (n.val + 2450) ≤ 22 := by decide
private theorem pos_w49 : ∀ n : Fin 50, 0 < dimF (n.val + 2450) := by decide
private theorem le_w50 : ∀ n : Fin 50, dimF (n.val + 2500) ≤ 22 := by decide
private theorem pos_w50 : ∀ n : Fin 50, 0 < dimF (n.val + 2500) := by decide
private theorem le_w51 : ∀ n : Fin 50, dimF (n.val + 2550) ≤ 22 := by decide
private theorem pos_w51 : ∀ n : Fin 50, 0 < dimF (n.val + 2550) := by decide
private theorem le_w52 : ∀ n : Fin 50, dimF (n.val + 2600) ≤ 22 := by decide
private theorem pos_w52 : ∀ n : Fin 50, 0 < dimF (n.val + 2600) := by decide
private theorem le_w53 : ∀ n : Fin 50, dimF (n.val + 2650) ≤ 22 := by decide
private theorem pos_w53 : ∀ n : Fin 50, 0 < dimF (n.val + 2650) := by decide
private theorem le_w54 : ∀ n : Fin 50, dimF (n.val + 2700) ≤ 22 := by decide
private theorem pos_w54 : ∀ n : Fin 50, 0 < dimF (n.val + 2700) := by decide
private theorem le_w55 : ∀ n : Fin 50, dimF (n.val + 2750) ≤ 22 := by decide
private theorem pos_w55 : ∀ n : Fin 50, 0 < dimF (n.val + 2750) := by decide
private theorem le_w56 : ∀ n : Fin 50, dimF (n.val + 2800) ≤ 22 := by decide
private theorem pos_w56 : ∀ n : Fin 50, 0 < dimF (n.val + 2800) := by decide
private theorem le_w57 : ∀ n : Fin 50, dimF (n.val + 2850) ≤ 22 := by decide
private theorem pos_w57 : ∀ n : Fin 50, 0 < dimF (n.val + 2850) := by decide
private theorem le_w58 : ∀ n : Fin 50, dimF (n.val + 2900) ≤ 22 := by decide
private theorem pos_w58 : ∀ n : Fin 50, 0 < dimF (n.val + 2900) := by decide
private theorem le_w59 : ∀ n : Fin 50, dimF (n.val + 2950) ≤ 22 := by decide
private theorem pos_w59 : ∀ n : Fin 50, 0 < dimF (n.val + 2950) := by decide
private theorem le_w60 : ∀ n : Fin 50, dimF (n.val + 3000) ≤ 22 := by decide
private theorem pos_w60 : ∀ n : Fin 50, 0 < dimF (n.val + 3000) := by decide
private theorem le_w61 : ∀ n : Fin 50, dimF (n.val + 3050) ≤ 22 := by decide
private theorem pos_w61 : ∀ n : Fin 50, 0 < dimF (n.val + 3050) := by decide
private theorem le_w62 : ∀ n : Fin 50, dimF (n.val + 3100) ≤ 22 := by decide
private theorem pos_w62 : ∀ n : Fin 50, 0 < dimF (n.val + 3100) := by decide
private theorem le_w63 : ∀ n : Fin 50, dimF (n.val + 3150) ≤ 22 := by decide
private theorem pos_w63 : ∀ n : Fin 50, 0 < dimF (n.val + 3150) := by decide
private theorem le_w64 : ∀ n : Fin 50, dimF (n.val + 3200) ≤ 22 := by decide
private theorem pos_w64 : ∀ n : Fin 50, 0 < dimF (n.val + 3200) := by decide
private theorem le_w65 : ∀ n : Fin 50, dimF (n.val + 3250) ≤ 22 := by decide
private theorem pos_w65 : ∀ n : Fin 50, 0 < dimF (n.val + 3250) := by decide
private theorem le_w66 : ∀ n : Fin 50, dimF (n.val + 3300) ≤ 22 := by decide
private theorem pos_w66 : ∀ n : Fin 50, 0 < dimF (n.val + 3300) := by decide
private theorem le_w67 : ∀ n : Fin 50, dimF (n.val + 3350) ≤ 22 := by decide
private theorem pos_w67 : ∀ n : Fin 50, 0 < dimF (n.val + 3350) := by decide
private theorem le_w68 : ∀ n : Fin 50, dimF (n.val + 3400) ≤ 22 := by decide
private theorem pos_w68 : ∀ n : Fin 50, 0 < dimF (n.val + 3400) := by decide
private theorem le_w69 : ∀ n : Fin 50, dimF (n.val + 3450) ≤ 22 := by decide
private theorem pos_w69 : ∀ n : Fin 50, 0 < dimF (n.val + 3450) := by decide
private theorem le_w70 : ∀ n : Fin 50, dimF (n.val + 3500) ≤ 22 := by decide
private theorem pos_w70 : ∀ n : Fin 50, 0 < dimF (n.val + 3500) := by decide
private theorem le_w71 : ∀ n : Fin 50, dimF (n.val + 3550) ≤ 22 := by decide
private theorem pos_w71 : ∀ n : Fin 50, 0 < dimF (n.val + 3550) := by decide
private theorem le_w72 : ∀ n : Fin 50, dimF (n.val + 3600) ≤ 22 := by decide
private theorem pos_w72 : ∀ n : Fin 50, 0 < dimF (n.val + 3600) := by decide
private theorem le_w73 : ∀ n : Fin 50, dimF (n.val + 3650) ≤ 22 := by decide
private theorem pos_w73 : ∀ n : Fin 50, 0 < dimF (n.val + 3650) := by decide
private theorem le_w74 : ∀ n : Fin 50, dimF (n.val + 3700) ≤ 22 := by decide
private theorem pos_w74 : ∀ n : Fin 50, 0 < dimF (n.val + 3700) := by decide
private theorem le_w75 : ∀ n : Fin 50, dimF (n.val + 3750) ≤ 22 := by decide
private theorem pos_w75 : ∀ n : Fin 50, 0 < dimF (n.val + 3750) := by decide
private theorem le_w76 : ∀ n : Fin 50, dimF (n.val + 3800) ≤ 22 := by decide
private theorem pos_w76 : ∀ n : Fin 50, 0 < dimF (n.val + 3800) := by decide
private theorem le_w77 : ∀ n : Fin 50, dimF (n.val + 3850) ≤ 22 := by decide
private theorem pos_w77 : ∀ n : Fin 50, 0 < dimF (n.val + 3850) := by decide
private theorem le_w78 : ∀ n : Fin 50, dimF (n.val + 3900) ≤ 22 := by decide
private theorem pos_w78 : ∀ n : Fin 50, 0 < dimF (n.val + 3900) := by decide
private theorem le_w79 : ∀ n : Fin 50, dimF (n.val + 3950) ≤ 22 := by decide
private theorem pos_w79 : ∀ n : Fin 50, 0 < dimF (n.val + 3950) := by decide
private theorem le_w80 : ∀ n : Fin 50, dimF (n.val + 4000) ≤ 22 := by decide
private theorem pos_w80 : ∀ n : Fin 50, 0 < dimF (n.val + 4000) := by decide
private theorem le_w81 : ∀ n : Fin 50, dimF (n.val + 4050) ≤ 22 := by decide
private theorem pos_w81 : ∀ n : Fin 50, 0 < dimF (n.val + 4050) := by decide
private theorem le_w82 : ∀ n : Fin 50, dimF (n.val + 4100) ≤ 22 := by decide
private theorem pos_w82 : ∀ n : Fin 50, 0 < dimF (n.val + 4100) := by decide
private theorem le_w83 : ∀ n : Fin 50, dimF (n.val + 4150) ≤ 22 := by decide
private theorem pos_w83 : ∀ n : Fin 50, 0 < dimF (n.val + 4150) := by decide
private theorem le_w84 : ∀ n : Fin 50, dimF (n.val + 4200) ≤ 22 := by decide
private theorem pos_w84 : ∀ n : Fin 50, 0 < dimF (n.val + 4200) := by decide
private theorem le_w85 : ∀ n : Fin 50, dimF (n.val + 4250) ≤ 22 := by decide
private theorem pos_w85 : ∀ n : Fin 50, 0 < dimF (n.val + 4250) := by decide
private theorem le_w86 : ∀ n : Fin 50, dimF (n.val + 4300) ≤ 22 := by decide
private theorem pos_w86 : ∀ n : Fin 50, 0 < dimF (n.val + 4300) := by decide
private theorem le_w87 : ∀ n : Fin 50, dimF (n.val + 4350) ≤ 22 := by decide
private theorem pos_w87 : ∀ n : Fin 50, 0 < dimF (n.val + 4350) := by decide
private theorem le_w88 : ∀ n : Fin 50, dimF (n.val + 4400) ≤ 22 := by decide
private theorem pos_w88 : ∀ n : Fin 50, 0 < dimF (n.val + 4400) := by decide
private theorem le_w89 : ∀ n : Fin 50, dimF (n.val + 4450) ≤ 22 := by decide
private theorem pos_w89 : ∀ n : Fin 50, 0 < dimF (n.val + 4450) := by decide
private theorem le_w90 : ∀ n : Fin 50, dimF (n.val + 4500) ≤ 22 := by decide
private theorem pos_w90 : ∀ n : Fin 50, 0 < dimF (n.val + 4500) := by decide
private theorem le_w91 : ∀ n : Fin 50, dimF (n.val + 4550) ≤ 22 := by decide
private theorem pos_w91 : ∀ n : Fin 50, 0 < dimF (n.val + 4550) := by decide
private theorem le_w92 : ∀ n : Fin 50, dimF (n.val + 4600) ≤ 22 := by decide
private theorem pos_w92 : ∀ n : Fin 50, 0 < dimF (n.val + 4600) := by decide
private theorem le_w93 : ∀ n : Fin 50, dimF (n.val + 4650) ≤ 22 := by decide
private theorem pos_w93 : ∀ n : Fin 50, 0 < dimF (n.val + 4650) := by decide
private theorem le_w94 : ∀ n : Fin 50, dimF (n.val + 4700) ≤ 22 := by decide
private theorem pos_w94 : ∀ n : Fin 50, 0 < dimF (n.val + 4700) := by decide
private theorem le_w95 : ∀ n : Fin 50, dimF (n.val + 4750) ≤ 22 := by decide
private theorem pos_w95 : ∀ n : Fin 50, 0 < dimF (n.val + 4750) := by decide
private theorem le_w96 : ∀ n : Fin 50, dimF (n.val + 4800) ≤ 22 := by decide
private theorem pos_w96 : ∀ n : Fin 50, 0 < dimF (n.val + 4800) := by decide
private theorem le_w97 : ∀ n : Fin 50, dimF (n.val + 4850) ≤ 22 := by decide
private theorem pos_w97 : ∀ n : Fin 50, 0 < dimF (n.val + 4850) := by decide
private theorem le_w98 : ∀ n : Fin 50, dimF (n.val + 4900) ≤ 22 := by decide
private theorem pos_w98 : ∀ n : Fin 50, 0 < dimF (n.val + 4900) := by decide
private theorem le_w99 : ∀ n : Fin 50, dimF (n.val + 4950) ≤ 22 := by decide
private theorem pos_w99 : ∀ n : Fin 50, 0 < dimF (n.val + 4950) := by decide

theorem dimF_le_22_range : ∀ n, 0 ≤ n → n < 5000 → dimF n ≤ 22 := by
  intro n hlo hhi
  by_cases h0 : n < 50
  · have hr : n - 0 < 50 := by omega
    have heq : n = (n - 0) + 0 := by omega
    rw [heq]
    exact le_w0 ⟨n - 0, hr⟩
  · by_cases h1 : n < 100
    · have hr : n - 50 < 50 := by omega
      have heq : n = (n - 50) + 50 := by omega
      rw [heq]
      exact le_w1 ⟨n - 50, hr⟩
    · by_cases h2 : n < 150
      · have hr : n - 100 < 50 := by omega
        have heq : n = (n - 100) + 100 := by omega
        rw [heq]
        exact le_w2 ⟨n - 100, hr⟩
      · by_cases h3 : n < 200
        · have hr : n - 150 < 50 := by omega
          have heq : n = (n - 150) + 150 := by omega
          rw [heq]
          exact le_w3 ⟨n - 150, hr⟩
        · by_cases h4 : n < 250
          · have hr : n - 200 < 50 := by omega
            have heq : n = (n - 200) + 200 := by omega
            rw [heq]
            exact le_w4 ⟨n - 200, hr⟩
          · by_cases h5 : n < 300
            · have hr : n - 250 < 50 := by omega
              have heq : n = (n - 250) + 250 := by omega
              rw [heq]
              exact le_w5 ⟨n - 250, hr⟩
            · by_cases h6 : n < 350
              · have hr : n - 300 < 50 := by omega
                have heq : n = (n - 300) + 300 := by omega
                rw [heq]
                exact le_w6 ⟨n - 300, hr⟩
              · by_cases h7 : n < 400
                · have hr : n - 350 < 50 := by omega
                  have heq : n = (n - 350) + 350 := by omega
                  rw [heq]
                  exact le_w7 ⟨n - 350, hr⟩
                · by_cases h8 : n < 450
                  · have hr : n - 400 < 50 := by omega
                    have heq : n = (n - 400) + 400 := by omega
                    rw [heq]
                    exact le_w8 ⟨n - 400, hr⟩
                  · by_cases h9 : n < 500
                    · have hr : n - 450 < 50 := by omega
                      have heq : n = (n - 450) + 450 := by omega
                      rw [heq]
                      exact le_w9 ⟨n - 450, hr⟩
                    · by_cases h10 : n < 550
                      · have hr : n - 500 < 50 := by omega
                        have heq : n = (n - 500) + 500 := by omega
                        rw [heq]
                        exact le_w10 ⟨n - 500, hr⟩
                      · by_cases h11 : n < 600
                        · have hr : n - 550 < 50 := by omega
                          have heq : n = (n - 550) + 550 := by omega
                          rw [heq]
                          exact le_w11 ⟨n - 550, hr⟩
                        · by_cases h12 : n < 650
                          · have hr : n - 600 < 50 := by omega
                            have heq : n = (n - 600) + 600 := by omega
                            rw [heq]
                            exact le_w12 ⟨n - 600, hr⟩
                          · by_cases h13 : n < 700
                            · have hr : n - 650 < 50 := by omega
                              have heq : n = (n - 650) + 650 := by omega
                              rw [heq]
                              exact le_w13 ⟨n - 650, hr⟩
                            · by_cases h14 : n < 750
                              · have hr : n - 700 < 50 := by omega
                                have heq : n = (n - 700) + 700 := by omega
                                rw [heq]
                                exact le_w14 ⟨n - 700, hr⟩
                              · by_cases h15 : n < 800
                                · have hr : n - 750 < 50 := by omega
                                  have heq : n = (n - 750) + 750 := by omega
                                  rw [heq]
                                  exact le_w15 ⟨n - 750, hr⟩
                                · by_cases h16 : n < 850
                                  · have hr : n - 800 < 50 := by omega
                                    have heq : n = (n - 800) + 800 := by omega
                                    rw [heq]
                                    exact le_w16 ⟨n - 800, hr⟩
                                  · by_cases h17 : n < 900
                                    · have hr : n - 850 < 50 := by omega
                                      have heq : n = (n - 850) + 850 := by omega
                                      rw [heq]
                                      exact le_w17 ⟨n - 850, hr⟩
                                    · by_cases h18 : n < 950
                                      · have hr : n - 900 < 50 := by omega
                                        have heq : n = (n - 900) + 900 := by omega
                                        rw [heq]
                                        exact le_w18 ⟨n - 900, hr⟩
                                      · by_cases h19 : n < 1000
                                        · have hr : n - 950 < 50 := by omega
                                          have heq : n = (n - 950) + 950 := by omega
                                          rw [heq]
                                          exact le_w19 ⟨n - 950, hr⟩
                                        · by_cases h20 : n < 1050
                                          · have hr : n - 1000 < 50 := by omega
                                            have heq : n = (n - 1000) + 1000 := by omega
                                            rw [heq]
                                            exact le_w20 ⟨n - 1000, hr⟩
                                          · by_cases h21 : n < 1100
                                            · have hr : n - 1050 < 50 := by omega
                                              have heq : n = (n - 1050) + 1050 := by omega
                                              rw [heq]
                                              exact le_w21 ⟨n - 1050, hr⟩
                                            · by_cases h22 : n < 1150
                                              · have hr : n - 1100 < 50 := by omega
                                                have heq : n = (n - 1100) + 1100 := by omega
                                                rw [heq]
                                                exact le_w22 ⟨n - 1100, hr⟩
                                              · by_cases h23 : n < 1200
                                                · have hr : n - 1150 < 50 := by omega
                                                  have heq : n = (n - 1150) + 1150 := by omega
                                                  rw [heq]
                                                  exact le_w23 ⟨n - 1150, hr⟩
                                                · by_cases h24 : n < 1250
                                                  · have hr : n - 1200 < 50 := by omega
                                                    have heq : n = (n - 1200) + 1200 := by omega
                                                    rw [heq]
                                                    exact le_w24 ⟨n - 1200, hr⟩
                                                  · by_cases h25 : n < 1300
                                                    · have hr : n - 1250 < 50 := by omega
                                                      have heq : n = (n - 1250) + 1250 := by omega
                                                      rw [heq]
                                                      exact le_w25 ⟨n - 1250, hr⟩
                                                    · by_cases h26 : n < 1350
                                                      · have hr : n - 1300 < 50 := by omega
                                                        have heq : n = (n - 1300) + 1300 := by omega
                                                        rw [heq]
                                                        exact le_w26 ⟨n - 1300, hr⟩
                                                      · by_cases h27 : n < 1400
                                                        · have hr : n - 1350 < 50 := by omega
                                                          have heq : n = (n - 1350) + 1350 := by omega
                                                          rw [heq]
                                                          exact le_w27 ⟨n - 1350, hr⟩
                                                        · by_cases h28 : n < 1450
                                                          · have hr : n - 1400 < 50 := by omega
                                                            have heq : n = (n - 1400) + 1400 := by omega
                                                            rw [heq]
                                                            exact le_w28 ⟨n - 1400, hr⟩
                                                          · by_cases h29 : n < 1500
                                                            · have hr : n - 1450 < 50 := by omega
                                                              have heq : n = (n - 1450) + 1450 := by omega
                                                              rw [heq]
                                                              exact le_w29 ⟨n - 1450, hr⟩
                                                            · by_cases h30 : n < 1550
                                                              · have hr : n - 1500 < 50 := by omega
                                                                have heq : n = (n - 1500) + 1500 := by omega
                                                                rw [heq]
                                                                exact le_w30 ⟨n - 1500, hr⟩
                                                              · by_cases h31 : n < 1600
                                                                · have hr : n - 1550 < 50 := by omega
                                                                  have heq : n = (n - 1550) + 1550 := by omega
                                                                  rw [heq]
                                                                  exact le_w31 ⟨n - 1550, hr⟩
                                                                · by_cases h32 : n < 1650
                                                                  · have hr : n - 1600 < 50 := by omega
                                                                    have heq : n = (n - 1600) + 1600 := by omega
                                                                    rw [heq]
                                                                    exact le_w32 ⟨n - 1600, hr⟩
                                                                  · by_cases h33 : n < 1700
                                                                    · have hr : n - 1650 < 50 := by omega
                                                                      have heq : n = (n - 1650) + 1650 := by omega
                                                                      rw [heq]
                                                                      exact le_w33 ⟨n - 1650, hr⟩
                                                                    · by_cases h34 : n < 1750
                                                                      · have hr : n - 1700 < 50 := by omega
                                                                        have heq : n = (n - 1700) + 1700 := by omega
                                                                        rw [heq]
                                                                        exact le_w34 ⟨n - 1700, hr⟩
                                                                      · by_cases h35 : n < 1800
                                                                        · have hr : n - 1750 < 50 := by omega
                                                                          have heq : n = (n - 1750) + 1750 := by omega
                                                                          rw [heq]
                                                                          exact le_w35 ⟨n - 1750, hr⟩
                                                                        · by_cases h36 : n < 1850
                                                                          · have hr : n - 1800 < 50 := by omega
                                                                            have heq : n = (n - 1800) + 1800 := by omega
                                                                            rw [heq]
                                                                            exact le_w36 ⟨n - 1800, hr⟩
                                                                          · by_cases h37 : n < 1900
                                                                            · have hr : n - 1850 < 50 := by omega
                                                                              have heq : n = (n - 1850) + 1850 := by omega
                                                                              rw [heq]
                                                                              exact le_w37 ⟨n - 1850, hr⟩
                                                                            · by_cases h38 : n < 1950
                                                                              · have hr : n - 1900 < 50 := by omega
                                                                                have heq : n = (n - 1900) + 1900 := by omega
                                                                                rw [heq]
                                                                                exact le_w38 ⟨n - 1900, hr⟩
                                                                              · by_cases h39 : n < 2000
                                                                                · have hr : n - 1950 < 50 := by omega
                                                                                  have heq : n = (n - 1950) + 1950 := by omega
                                                                                  rw [heq]
                                                                                  exact le_w39 ⟨n - 1950, hr⟩
                                                                                · by_cases h40 : n < 2050
                                                                                  · have hr : n - 2000 < 50 := by omega
                                                                                    have heq : n = (n - 2000) + 2000 := by omega
                                                                                    rw [heq]
                                                                                    exact le_w40 ⟨n - 2000, hr⟩
                                                                                  · by_cases h41 : n < 2100
                                                                                    · have hr : n - 2050 < 50 := by omega
                                                                                      have heq : n = (n - 2050) + 2050 := by omega
                                                                                      rw [heq]
                                                                                      exact le_w41 ⟨n - 2050, hr⟩
                                                                                    · by_cases h42 : n < 2150
                                                                                      · have hr : n - 2100 < 50 := by omega
                                                                                        have heq : n = (n - 2100) + 2100 := by omega
                                                                                        rw [heq]
                                                                                        exact le_w42 ⟨n - 2100, hr⟩
                                                                                      · by_cases h43 : n < 2200
                                                                                        · have hr : n - 2150 < 50 := by omega
                                                                                          have heq : n = (n - 2150) + 2150 := by omega
                                                                                          rw [heq]
                                                                                          exact le_w43 ⟨n - 2150, hr⟩
                                                                                        · by_cases h44 : n < 2250
                                                                                          · have hr : n - 2200 < 50 := by omega
                                                                                            have heq : n = (n - 2200) + 2200 := by omega
                                                                                            rw [heq]
                                                                                            exact le_w44 ⟨n - 2200, hr⟩
                                                                                          · by_cases h45 : n < 2300
                                                                                            · have hr : n - 2250 < 50 := by omega
                                                                                              have heq : n = (n - 2250) + 2250 := by omega
                                                                                              rw [heq]
                                                                                              exact le_w45 ⟨n - 2250, hr⟩
                                                                                            · by_cases h46 : n < 2350
                                                                                              · have hr : n - 2300 < 50 := by omega
                                                                                                have heq : n = (n - 2300) + 2300 := by omega
                                                                                                rw [heq]
                                                                                                exact le_w46 ⟨n - 2300, hr⟩
                                                                                              · by_cases h47 : n < 2400
                                                                                                · have hr : n - 2350 < 50 := by omega
                                                                                                  have heq : n = (n - 2350) + 2350 := by omega
                                                                                                  rw [heq]
                                                                                                  exact le_w47 ⟨n - 2350, hr⟩
                                                                                                · by_cases h48 : n < 2450
                                                                                                  · have hr : n - 2400 < 50 := by omega
                                                                                                    have heq : n = (n - 2400) + 2400 := by omega
                                                                                                    rw [heq]
                                                                                                    exact le_w48 ⟨n - 2400, hr⟩
                                                                                                  · by_cases h49 : n < 2500
                                                                                                    · have hr : n - 2450 < 50 := by omega
                                                                                                      have heq : n = (n - 2450) + 2450 := by omega
                                                                                                      rw [heq]
                                                                                                      exact le_w49 ⟨n - 2450, hr⟩
                                                                                                    · by_cases h50 : n < 2550
                                                                                                      · have hr : n - 2500 < 50 := by omega
                                                                                                        have heq : n = (n - 2500) + 2500 := by omega
                                                                                                        rw [heq]
                                                                                                        exact le_w50 ⟨n - 2500, hr⟩
                                                                                                      · by_cases h51 : n < 2600
                                                                                                        · have hr : n - 2550 < 50 := by omega
                                                                                                          have heq : n = (n - 2550) + 2550 := by omega
                                                                                                          rw [heq]
                                                                                                          exact le_w51 ⟨n - 2550, hr⟩
                                                                                                        · by_cases h52 : n < 2650
                                                                                                          · have hr : n - 2600 < 50 := by omega
                                                                                                            have heq : n = (n - 2600) + 2600 := by omega
                                                                                                            rw [heq]
                                                                                                            exact le_w52 ⟨n - 2600, hr⟩
                                                                                                          · by_cases h53 : n < 2700
                                                                                                            · have hr : n - 2650 < 50 := by omega
                                                                                                              have heq : n = (n - 2650) + 2650 := by omega
                                                                                                              rw [heq]
                                                                                                              exact le_w53 ⟨n - 2650, hr⟩
                                                                                                            · by_cases h54 : n < 2750
                                                                                                              · have hr : n - 2700 < 50 := by omega
                                                                                                                have heq : n = (n - 2700) + 2700 := by omega
                                                                                                                rw [heq]
                                                                                                                exact le_w54 ⟨n - 2700, hr⟩
                                                                                                              · by_cases h55 : n < 2800
                                                                                                                · have hr : n - 2750 < 50 := by omega
                                                                                                                  have heq : n = (n - 2750) + 2750 := by omega
                                                                                                                  rw [heq]
                                                                                                                  exact le_w55 ⟨n - 2750, hr⟩
                                                                                                                · by_cases h56 : n < 2850
                                                                                                                  · have hr : n - 2800 < 50 := by omega
                                                                                                                    have heq : n = (n - 2800) + 2800 := by omega
                                                                                                                    rw [heq]
                                                                                                                    exact le_w56 ⟨n - 2800, hr⟩
                                                                                                                  · by_cases h57 : n < 2900
                                                                                                                    · have hr : n - 2850 < 50 := by omega
                                                                                                                      have heq : n = (n - 2850) + 2850 := by omega
                                                                                                                      rw [heq]
                                                                                                                      exact le_w57 ⟨n - 2850, hr⟩
                                                                                                                    · by_cases h58 : n < 2950
                                                                                                                      · have hr : n - 2900 < 50 := by omega
                                                                                                                        have heq : n = (n - 2900) + 2900 := by omega
                                                                                                                        rw [heq]
                                                                                                                        exact le_w58 ⟨n - 2900, hr⟩
                                                                                                                      · by_cases h59 : n < 3000
                                                                                                                        · have hr : n - 2950 < 50 := by omega
                                                                                                                          have heq : n = (n - 2950) + 2950 := by omega
                                                                                                                          rw [heq]
                                                                                                                          exact le_w59 ⟨n - 2950, hr⟩
                                                                                                                        · by_cases h60 : n < 3050
                                                                                                                          · have hr : n - 3000 < 50 := by omega
                                                                                                                            have heq : n = (n - 3000) + 3000 := by omega
                                                                                                                            rw [heq]
                                                                                                                            exact le_w60 ⟨n - 3000, hr⟩
                                                                                                                          · by_cases h61 : n < 3100
                                                                                                                            · have hr : n - 3050 < 50 := by omega
                                                                                                                              have heq : n = (n - 3050) + 3050 := by omega
                                                                                                                              rw [heq]
                                                                                                                              exact le_w61 ⟨n - 3050, hr⟩
                                                                                                                            · by_cases h62 : n < 3150
                                                                                                                              · have hr : n - 3100 < 50 := by omega
                                                                                                                                have heq : n = (n - 3100) + 3100 := by omega
                                                                                                                                rw [heq]
                                                                                                                                exact le_w62 ⟨n - 3100, hr⟩
                                                                                                                              · by_cases h63 : n < 3200
                                                                                                                                · have hr : n - 3150 < 50 := by omega
                                                                                                                                  have heq : n = (n - 3150) + 3150 := by omega
                                                                                                                                  rw [heq]
                                                                                                                                  exact le_w63 ⟨n - 3150, hr⟩
                                                                                                                                · by_cases h64 : n < 3250
                                                                                                                                  · have hr : n - 3200 < 50 := by omega
                                                                                                                                    have heq : n = (n - 3200) + 3200 := by omega
                                                                                                                                    rw [heq]
                                                                                                                                    exact le_w64 ⟨n - 3200, hr⟩
                                                                                                                                  · by_cases h65 : n < 3300
                                                                                                                                    · have hr : n - 3250 < 50 := by omega
                                                                                                                                      have heq : n = (n - 3250) + 3250 := by omega
                                                                                                                                      rw [heq]
                                                                                                                                      exact le_w65 ⟨n - 3250, hr⟩
                                                                                                                                    · by_cases h66 : n < 3350
                                                                                                                                      · have hr : n - 3300 < 50 := by omega
                                                                                                                                        have heq : n = (n - 3300) + 3300 := by omega
                                                                                                                                        rw [heq]
                                                                                                                                        exact le_w66 ⟨n - 3300, hr⟩
                                                                                                                                      · by_cases h67 : n < 3400
                                                                                                                                        · have hr : n - 3350 < 50 := by omega
                                                                                                                                          have heq : n = (n - 3350) + 3350 := by omega
                                                                                                                                          rw [heq]
                                                                                                                                          exact le_w67 ⟨n - 3350, hr⟩
                                                                                                                                        · by_cases h68 : n < 3450
                                                                                                                                          · have hr : n - 3400 < 50 := by omega
                                                                                                                                            have heq : n = (n - 3400) + 3400 := by omega
                                                                                                                                            rw [heq]
                                                                                                                                            exact le_w68 ⟨n - 3400, hr⟩
                                                                                                                                          · by_cases h69 : n < 3500
                                                                                                                                            · have hr : n - 3450 < 50 := by omega
                                                                                                                                              have heq : n = (n - 3450) + 3450 := by omega
                                                                                                                                              rw [heq]
                                                                                                                                              exact le_w69 ⟨n - 3450, hr⟩
                                                                                                                                            · by_cases h70 : n < 3550
                                                                                                                                              · have hr : n - 3500 < 50 := by omega
                                                                                                                                                have heq : n = (n - 3500) + 3500 := by omega
                                                                                                                                                rw [heq]
                                                                                                                                                exact le_w70 ⟨n - 3500, hr⟩
                                                                                                                                              · by_cases h71 : n < 3600
                                                                                                                                                · have hr : n - 3550 < 50 := by omega
                                                                                                                                                  have heq : n = (n - 3550) + 3550 := by omega
                                                                                                                                                  rw [heq]
                                                                                                                                                  exact le_w71 ⟨n - 3550, hr⟩
                                                                                                                                                · by_cases h72 : n < 3650
                                                                                                                                                  · have hr : n - 3600 < 50 := by omega
                                                                                                                                                    have heq : n = (n - 3600) + 3600 := by omega
                                                                                                                                                    rw [heq]
                                                                                                                                                    exact le_w72 ⟨n - 3600, hr⟩
                                                                                                                                                  · by_cases h73 : n < 3700
                                                                                                                                                    · have hr : n - 3650 < 50 := by omega
                                                                                                                                                      have heq : n = (n - 3650) + 3650 := by omega
                                                                                                                                                      rw [heq]
                                                                                                                                                      exact le_w73 ⟨n - 3650, hr⟩
                                                                                                                                                    · by_cases h74 : n < 3750
                                                                                                                                                      · have hr : n - 3700 < 50 := by omega
                                                                                                                                                        have heq : n = (n - 3700) + 3700 := by omega
                                                                                                                                                        rw [heq]
                                                                                                                                                        exact le_w74 ⟨n - 3700, hr⟩
                                                                                                                                                      · by_cases h75 : n < 3800
                                                                                                                                                        · have hr : n - 3750 < 50 := by omega
                                                                                                                                                          have heq : n = (n - 3750) + 3750 := by omega
                                                                                                                                                          rw [heq]
                                                                                                                                                          exact le_w75 ⟨n - 3750, hr⟩
                                                                                                                                                        · by_cases h76 : n < 3850
                                                                                                                                                          · have hr : n - 3800 < 50 := by omega
                                                                                                                                                            have heq : n = (n - 3800) + 3800 := by omega
                                                                                                                                                            rw [heq]
                                                                                                                                                            exact le_w76 ⟨n - 3800, hr⟩
                                                                                                                                                          · by_cases h77 : n < 3900
                                                                                                                                                            · have hr : n - 3850 < 50 := by omega
                                                                                                                                                              have heq : n = (n - 3850) + 3850 := by omega
                                                                                                                                                              rw [heq]
                                                                                                                                                              exact le_w77 ⟨n - 3850, hr⟩
                                                                                                                                                            · by_cases h78 : n < 3950
                                                                                                                                                              · have hr : n - 3900 < 50 := by omega
                                                                                                                                                                have heq : n = (n - 3900) + 3900 := by omega
                                                                                                                                                                rw [heq]
                                                                                                                                                                exact le_w78 ⟨n - 3900, hr⟩
                                                                                                                                                              · by_cases h79 : n < 4000
                                                                                                                                                                · have hr : n - 3950 < 50 := by omega
                                                                                                                                                                  have heq : n = (n - 3950) + 3950 := by omega
                                                                                                                                                                  rw [heq]
                                                                                                                                                                  exact le_w79 ⟨n - 3950, hr⟩
                                                                                                                                                                · by_cases h80 : n < 4050
                                                                                                                                                                  · have hr : n - 4000 < 50 := by omega
                                                                                                                                                                    have heq : n = (n - 4000) + 4000 := by omega
                                                                                                                                                                    rw [heq]
                                                                                                                                                                    exact le_w80 ⟨n - 4000, hr⟩
                                                                                                                                                                  · by_cases h81 : n < 4100
                                                                                                                                                                    · have hr : n - 4050 < 50 := by omega
                                                                                                                                                                      have heq : n = (n - 4050) + 4050 := by omega
                                                                                                                                                                      rw [heq]
                                                                                                                                                                      exact le_w81 ⟨n - 4050, hr⟩
                                                                                                                                                                    · by_cases h82 : n < 4150
                                                                                                                                                                      · have hr : n - 4100 < 50 := by omega
                                                                                                                                                                        have heq : n = (n - 4100) + 4100 := by omega
                                                                                                                                                                        rw [heq]
                                                                                                                                                                        exact le_w82 ⟨n - 4100, hr⟩
                                                                                                                                                                      · by_cases h83 : n < 4200
                                                                                                                                                                        · have hr : n - 4150 < 50 := by omega
                                                                                                                                                                          have heq : n = (n - 4150) + 4150 := by omega
                                                                                                                                                                          rw [heq]
                                                                                                                                                                          exact le_w83 ⟨n - 4150, hr⟩
                                                                                                                                                                        · by_cases h84 : n < 4250
                                                                                                                                                                          · have hr : n - 4200 < 50 := by omega
                                                                                                                                                                            have heq : n = (n - 4200) + 4200 := by omega
                                                                                                                                                                            rw [heq]
                                                                                                                                                                            exact le_w84 ⟨n - 4200, hr⟩
                                                                                                                                                                          · by_cases h85 : n < 4300
                                                                                                                                                                            · have hr : n - 4250 < 50 := by omega
                                                                                                                                                                              have heq : n = (n - 4250) + 4250 := by omega
                                                                                                                                                                              rw [heq]
                                                                                                                                                                              exact le_w85 ⟨n - 4250, hr⟩
                                                                                                                                                                            · by_cases h86 : n < 4350
                                                                                                                                                                              · have hr : n - 4300 < 50 := by omega
                                                                                                                                                                                have heq : n = (n - 4300) + 4300 := by omega
                                                                                                                                                                                rw [heq]
                                                                                                                                                                                exact le_w86 ⟨n - 4300, hr⟩
                                                                                                                                                                              · by_cases h87 : n < 4400
                                                                                                                                                                                · have hr : n - 4350 < 50 := by omega
                                                                                                                                                                                  have heq : n = (n - 4350) + 4350 := by omega
                                                                                                                                                                                  rw [heq]
                                                                                                                                                                                  exact le_w87 ⟨n - 4350, hr⟩
                                                                                                                                                                                · by_cases h88 : n < 4450
                                                                                                                                                                                  · have hr : n - 4400 < 50 := by omega
                                                                                                                                                                                    have heq : n = (n - 4400) + 4400 := by omega
                                                                                                                                                                                    rw [heq]
                                                                                                                                                                                    exact le_w88 ⟨n - 4400, hr⟩
                                                                                                                                                                                  · by_cases h89 : n < 4500
                                                                                                                                                                                    · have hr : n - 4450 < 50 := by omega
                                                                                                                                                                                      have heq : n = (n - 4450) + 4450 := by omega
                                                                                                                                                                                      rw [heq]
                                                                                                                                                                                      exact le_w89 ⟨n - 4450, hr⟩
                                                                                                                                                                                    · by_cases h90 : n < 4550
                                                                                                                                                                                      · have hr : n - 4500 < 50 := by omega
                                                                                                                                                                                        have heq : n = (n - 4500) + 4500 := by omega
                                                                                                                                                                                        rw [heq]
                                                                                                                                                                                        exact le_w90 ⟨n - 4500, hr⟩
                                                                                                                                                                                      · by_cases h91 : n < 4600
                                                                                                                                                                                        · have hr : n - 4550 < 50 := by omega
                                                                                                                                                                                          have heq : n = (n - 4550) + 4550 := by omega
                                                                                                                                                                                          rw [heq]
                                                                                                                                                                                          exact le_w91 ⟨n - 4550, hr⟩
                                                                                                                                                                                        · by_cases h92 : n < 4650
                                                                                                                                                                                          · have hr : n - 4600 < 50 := by omega
                                                                                                                                                                                            have heq : n = (n - 4600) + 4600 := by omega
                                                                                                                                                                                            rw [heq]
                                                                                                                                                                                            exact le_w92 ⟨n - 4600, hr⟩
                                                                                                                                                                                          · by_cases h93 : n < 4700
                                                                                                                                                                                            · have hr : n - 4650 < 50 := by omega
                                                                                                                                                                                              have heq : n = (n - 4650) + 4650 := by omega
                                                                                                                                                                                              rw [heq]
                                                                                                                                                                                              exact le_w93 ⟨n - 4650, hr⟩
                                                                                                                                                                                            · by_cases h94 : n < 4750
                                                                                                                                                                                              · have hr : n - 4700 < 50 := by omega
                                                                                                                                                                                                have heq : n = (n - 4700) + 4700 := by omega
                                                                                                                                                                                                rw [heq]
                                                                                                                                                                                                exact le_w94 ⟨n - 4700, hr⟩
                                                                                                                                                                                              · by_cases h95 : n < 4800
                                                                                                                                                                                                · have hr : n - 4750 < 50 := by omega
                                                                                                                                                                                                  have heq : n = (n - 4750) + 4750 := by omega
                                                                                                                                                                                                  rw [heq]
                                                                                                                                                                                                  exact le_w95 ⟨n - 4750, hr⟩
                                                                                                                                                                                                · by_cases h96 : n < 4850
                                                                                                                                                                                                  · have hr : n - 4800 < 50 := by omega
                                                                                                                                                                                                    have heq : n = (n - 4800) + 4800 := by omega
                                                                                                                                                                                                    rw [heq]
                                                                                                                                                                                                    exact le_w96 ⟨n - 4800, hr⟩
                                                                                                                                                                                                  · by_cases h97 : n < 4900
                                                                                                                                                                                                    · have hr : n - 4850 < 50 := by omega
                                                                                                                                                                                                      have heq : n = (n - 4850) + 4850 := by omega
                                                                                                                                                                                                      rw [heq]
                                                                                                                                                                                                      exact le_w97 ⟨n - 4850, hr⟩
                                                                                                                                                                                                    · by_cases h98 : n < 4950
                                                                                                                                                                                                      · have hr : n - 4900 < 50 := by omega
                                                                                                                                                                                                        have heq : n = (n - 4900) + 4900 := by omega
                                                                                                                                                                                                        rw [heq]
                                                                                                                                                                                                        exact le_w98 ⟨n - 4900, hr⟩
                                                                                                                                                                                                      · by_cases h99 : n < 5000
                                                                                                                                                                                                        · have hr : n - 4950 < 50 := by omega
                                                                                                                                                                                                          have heq : n = (n - 4950) + 4950 := by omega
                                                                                                                                                                                                          rw [heq]
                                                                                                                                                                                                          exact le_w99 ⟨n - 4950, hr⟩
                                                                                                                                                                                                        · omega

theorem dimF_pos_range : ∀ n, 0 ≤ n → n < 5000 → 0 < dimF n := by
  intro n hlo hhi
  by_cases h0 : n < 50
  · have hr : n - 0 < 50 := by omega
    have heq : n = (n - 0) + 0 := by omega
    rw [heq]
    exact pos_w0 ⟨n - 0, hr⟩
  · by_cases h1 : n < 100
    · have hr : n - 50 < 50 := by omega
      have heq : n = (n - 50) + 50 := by omega
      rw [heq]
      exact pos_w1 ⟨n - 50, hr⟩
    · by_cases h2 : n < 150
      · have hr : n - 100 < 50 := by omega
        have heq : n = (n - 100) + 100 := by omega
        rw [heq]
        exact pos_w2 ⟨n - 100, hr⟩
      · by_cases h3 : n < 200
        · have hr : n - 150 < 50 := by omega
          have heq : n = (n - 150) + 150 := by omega
          rw [heq]
          exact pos_w3 ⟨n - 150, hr⟩
        · by_cases h4 : n < 250
          · have hr : n - 200 < 50 := by omega
            have heq : n = (n - 200) + 200 := by omega
            rw [heq]
            exact pos_w4 ⟨n - 200, hr⟩
          · by_cases h5 : n < 300
            · have hr : n - 250 < 50 := by omega
              have heq : n = (n - 250) + 250 := by omega
              rw [heq]
              exact pos_w5 ⟨n - 250, hr⟩
            · by_cases h6 : n < 350
              · have hr : n - 300 < 50 := by omega
                have heq : n = (n - 300) + 300 := by omega
                rw [heq]
                exact pos_w6 ⟨n - 300, hr⟩
              · by_cases h7 : n < 400
                · have hr : n - 350 < 50 := by omega
                  have heq : n = (n - 350) + 350 := by omega
                  rw [heq]
                  exact pos_w7 ⟨n - 350, hr⟩
                · by_cases h8 : n < 450
                  · have hr : n - 400 < 50 := by omega
                    have heq : n = (n - 400) + 400 := by omega
                    rw [heq]
                    exact pos_w8 ⟨n - 400, hr⟩
                  · by_cases h9 : n < 500
                    · have hr : n - 450 < 50 := by omega
                      have heq : n = (n - 450) + 450 := by omega
                      rw [heq]
                      exact pos_w9 ⟨n - 450, hr⟩
                    · by_cases h10 : n < 550
                      · have hr : n - 500 < 50 := by omega
                        have heq : n = (n - 500) + 500 := by omega
                        rw [heq]
                        exact pos_w10 ⟨n - 500, hr⟩
                      · by_cases h11 : n < 600
                        · have hr : n - 550 < 50 := by omega
                          have heq : n = (n - 550) + 550 := by omega
                          rw [heq]
                          exact pos_w11 ⟨n - 550, hr⟩
                        · by_cases h12 : n < 650
                          · have hr : n - 600 < 50 := by omega
                            have heq : n = (n - 600) + 600 := by omega
                            rw [heq]
                            exact pos_w12 ⟨n - 600, hr⟩
                          · by_cases h13 : n < 700
                            · have hr : n - 650 < 50 := by omega
                              have heq : n = (n - 650) + 650 := by omega
                              rw [heq]
                              exact pos_w13 ⟨n - 650, hr⟩
                            · by_cases h14 : n < 750
                              · have hr : n - 700 < 50 := by omega
                                have heq : n = (n - 700) + 700 := by omega
                                rw [heq]
                                exact pos_w14 ⟨n - 700, hr⟩
                              · by_cases h15 : n < 800
                                · have hr : n - 750 < 50 := by omega
                                  have heq : n = (n - 750) + 750 := by omega
                                  rw [heq]
                                  exact pos_w15 ⟨n - 750, hr⟩
                                · by_cases h16 : n < 850
                                  · have hr : n - 800 < 50 := by omega
                                    have heq : n = (n - 800) + 800 := by omega
                                    rw [heq]
                                    exact pos_w16 ⟨n - 800, hr⟩
                                  · by_cases h17 : n < 900
                                    · have hr : n - 850 < 50 := by omega
                                      have heq : n = (n - 850) + 850 := by omega
                                      rw [heq]
                                      exact pos_w17 ⟨n - 850, hr⟩
                                    · by_cases h18 : n < 950
                                      · have hr : n - 900 < 50 := by omega
                                        have heq : n = (n - 900) + 900 := by omega
                                        rw [heq]
                                        exact pos_w18 ⟨n - 900, hr⟩
                                      · by_cases h19 : n < 1000
                                        · have hr : n - 950 < 50 := by omega
                                          have heq : n = (n - 950) + 950 := by omega
                                          rw [heq]
                                          exact pos_w19 ⟨n - 950, hr⟩
                                        · by_cases h20 : n < 1050
                                          · have hr : n - 1000 < 50 := by omega
                                            have heq : n = (n - 1000) + 1000 := by omega
                                            rw [heq]
                                            exact pos_w20 ⟨n - 1000, hr⟩
                                          · by_cases h21 : n < 1100
                                            · have hr : n - 1050 < 50 := by omega
                                              have heq : n = (n - 1050) + 1050 := by omega
                                              rw [heq]
                                              exact pos_w21 ⟨n - 1050, hr⟩
                                            · by_cases h22 : n < 1150
                                              · have hr : n - 1100 < 50 := by omega
                                                have heq : n = (n - 1100) + 1100 := by omega
                                                rw [heq]
                                                exact pos_w22 ⟨n - 1100, hr⟩
                                              · by_cases h23 : n < 1200
                                                · have hr : n - 1150 < 50 := by omega
                                                  have heq : n = (n - 1150) + 1150 := by omega
                                                  rw [heq]
                                                  exact pos_w23 ⟨n - 1150, hr⟩
                                                · by_cases h24 : n < 1250
                                                  · have hr : n - 1200 < 50 := by omega
                                                    have heq : n = (n - 1200) + 1200 := by omega
                                                    rw [heq]
                                                    exact pos_w24 ⟨n - 1200, hr⟩
                                                  · by_cases h25 : n < 1300
                                                    · have hr : n - 1250 < 50 := by omega
                                                      have heq : n = (n - 1250) + 1250 := by omega
                                                      rw [heq]
                                                      exact pos_w25 ⟨n - 1250, hr⟩
                                                    · by_cases h26 : n < 1350
                                                      · have hr : n - 1300 < 50 := by omega
                                                        have heq : n = (n - 1300) + 1300 := by omega
                                                        rw [heq]
                                                        exact pos_w26 ⟨n - 1300, hr⟩
                                                      · by_cases h27 : n < 1400
                                                        · have hr : n - 1350 < 50 := by omega
                                                          have heq : n = (n - 1350) + 1350 := by omega
                                                          rw [heq]
                                                          exact pos_w27 ⟨n - 1350, hr⟩
                                                        · by_cases h28 : n < 1450
                                                          · have hr : n - 1400 < 50 := by omega
                                                            have heq : n = (n - 1400) + 1400 := by omega
                                                            rw [heq]
                                                            exact pos_w28 ⟨n - 1400, hr⟩
                                                          · by_cases h29 : n < 1500
                                                            · have hr : n - 1450 < 50 := by omega
                                                              have heq : n = (n - 1450) + 1450 := by omega
                                                              rw [heq]
                                                              exact pos_w29 ⟨n - 1450, hr⟩
                                                            · by_cases h30 : n < 1550
                                                              · have hr : n - 1500 < 50 := by omega
                                                                have heq : n = (n - 1500) + 1500 := by omega
                                                                rw [heq]
                                                                exact pos_w30 ⟨n - 1500, hr⟩
                                                              · by_cases h31 : n < 1600
                                                                · have hr : n - 1550 < 50 := by omega
                                                                  have heq : n = (n - 1550) + 1550 := by omega
                                                                  rw [heq]
                                                                  exact pos_w31 ⟨n - 1550, hr⟩
                                                                · by_cases h32 : n < 1650
                                                                  · have hr : n - 1600 < 50 := by omega
                                                                    have heq : n = (n - 1600) + 1600 := by omega
                                                                    rw [heq]
                                                                    exact pos_w32 ⟨n - 1600, hr⟩
                                                                  · by_cases h33 : n < 1700
                                                                    · have hr : n - 1650 < 50 := by omega
                                                                      have heq : n = (n - 1650) + 1650 := by omega
                                                                      rw [heq]
                                                                      exact pos_w33 ⟨n - 1650, hr⟩
                                                                    · by_cases h34 : n < 1750
                                                                      · have hr : n - 1700 < 50 := by omega
                                                                        have heq : n = (n - 1700) + 1700 := by omega
                                                                        rw [heq]
                                                                        exact pos_w34 ⟨n - 1700, hr⟩
                                                                      · by_cases h35 : n < 1800
                                                                        · have hr : n - 1750 < 50 := by omega
                                                                          have heq : n = (n - 1750) + 1750 := by omega
                                                                          rw [heq]
                                                                          exact pos_w35 ⟨n - 1750, hr⟩
                                                                        · by_cases h36 : n < 1850
                                                                          · have hr : n - 1800 < 50 := by omega
                                                                            have heq : n = (n - 1800) + 1800 := by omega
                                                                            rw [heq]
                                                                            exact pos_w36 ⟨n - 1800, hr⟩
                                                                          · by_cases h37 : n < 1900
                                                                            · have hr : n - 1850 < 50 := by omega
                                                                              have heq : n = (n - 1850) + 1850 := by omega
                                                                              rw [heq]
                                                                              exact pos_w37 ⟨n - 1850, hr⟩
                                                                            · by_cases h38 : n < 1950
                                                                              · have hr : n - 1900 < 50 := by omega
                                                                                have heq : n = (n - 1900) + 1900 := by omega
                                                                                rw [heq]
                                                                                exact pos_w38 ⟨n - 1900, hr⟩
                                                                              · by_cases h39 : n < 2000
                                                                                · have hr : n - 1950 < 50 := by omega
                                                                                  have heq : n = (n - 1950) + 1950 := by omega
                                                                                  rw [heq]
                                                                                  exact pos_w39 ⟨n - 1950, hr⟩
                                                                                · by_cases h40 : n < 2050
                                                                                  · have hr : n - 2000 < 50 := by omega
                                                                                    have heq : n = (n - 2000) + 2000 := by omega
                                                                                    rw [heq]
                                                                                    exact pos_w40 ⟨n - 2000, hr⟩
                                                                                  · by_cases h41 : n < 2100
                                                                                    · have hr : n - 2050 < 50 := by omega
                                                                                      have heq : n = (n - 2050) + 2050 := by omega
                                                                                      rw [heq]
                                                                                      exact pos_w41 ⟨n - 2050, hr⟩
                                                                                    · by_cases h42 : n < 2150
                                                                                      · have hr : n - 2100 < 50 := by omega
                                                                                        have heq : n = (n - 2100) + 2100 := by omega
                                                                                        rw [heq]
                                                                                        exact pos_w42 ⟨n - 2100, hr⟩
                                                                                      · by_cases h43 : n < 2200
                                                                                        · have hr : n - 2150 < 50 := by omega
                                                                                          have heq : n = (n - 2150) + 2150 := by omega
                                                                                          rw [heq]
                                                                                          exact pos_w43 ⟨n - 2150, hr⟩
                                                                                        · by_cases h44 : n < 2250
                                                                                          · have hr : n - 2200 < 50 := by omega
                                                                                            have heq : n = (n - 2200) + 2200 := by omega
                                                                                            rw [heq]
                                                                                            exact pos_w44 ⟨n - 2200, hr⟩
                                                                                          · by_cases h45 : n < 2300
                                                                                            · have hr : n - 2250 < 50 := by omega
                                                                                              have heq : n = (n - 2250) + 2250 := by omega
                                                                                              rw [heq]
                                                                                              exact pos_w45 ⟨n - 2250, hr⟩
                                                                                            · by_cases h46 : n < 2350
                                                                                              · have hr : n - 2300 < 50 := by omega
                                                                                                have heq : n = (n - 2300) + 2300 := by omega
                                                                                                rw [heq]
                                                                                                exact pos_w46 ⟨n - 2300, hr⟩
                                                                                              · by_cases h47 : n < 2400
                                                                                                · have hr : n - 2350 < 50 := by omega
                                                                                                  have heq : n = (n - 2350) + 2350 := by omega
                                                                                                  rw [heq]
                                                                                                  exact pos_w47 ⟨n - 2350, hr⟩
                                                                                                · by_cases h48 : n < 2450
                                                                                                  · have hr : n - 2400 < 50 := by omega
                                                                                                    have heq : n = (n - 2400) + 2400 := by omega
                                                                                                    rw [heq]
                                                                                                    exact pos_w48 ⟨n - 2400, hr⟩
                                                                                                  · by_cases h49 : n < 2500
                                                                                                    · have hr : n - 2450 < 50 := by omega
                                                                                                      have heq : n = (n - 2450) + 2450 := by omega
                                                                                                      rw [heq]
                                                                                                      exact pos_w49 ⟨n - 2450, hr⟩
                                                                                                    · by_cases h50 : n < 2550
                                                                                                      · have hr : n - 2500 < 50 := by omega
                                                                                                        have heq : n = (n - 2500) + 2500 := by omega
                                                                                                        rw [heq]
                                                                                                        exact pos_w50 ⟨n - 2500, hr⟩
                                                                                                      · by_cases h51 : n < 2600
                                                                                                        · have hr : n - 2550 < 50 := by omega
                                                                                                          have heq : n = (n - 2550) + 2550 := by omega
                                                                                                          rw [heq]
                                                                                                          exact pos_w51 ⟨n - 2550, hr⟩
                                                                                                        · by_cases h52 : n < 2650
                                                                                                          · have hr : n - 2600 < 50 := by omega
                                                                                                            have heq : n = (n - 2600) + 2600 := by omega
                                                                                                            rw [heq]
                                                                                                            exact pos_w52 ⟨n - 2600, hr⟩
                                                                                                          · by_cases h53 : n < 2700
                                                                                                            · have hr : n - 2650 < 50 := by omega
                                                                                                              have heq : n = (n - 2650) + 2650 := by omega
                                                                                                              rw [heq]
                                                                                                              exact pos_w53 ⟨n - 2650, hr⟩
                                                                                                            · by_cases h54 : n < 2750
                                                                                                              · have hr : n - 2700 < 50 := by omega
                                                                                                                have heq : n = (n - 2700) + 2700 := by omega
                                                                                                                rw [heq]
                                                                                                                exact pos_w54 ⟨n - 2700, hr⟩
                                                                                                              · by_cases h55 : n < 2800
                                                                                                                · have hr : n - 2750 < 50 := by omega
                                                                                                                  have heq : n = (n - 2750) + 2750 := by omega
                                                                                                                  rw [heq]
                                                                                                                  exact pos_w55 ⟨n - 2750, hr⟩
                                                                                                                · by_cases h56 : n < 2850
                                                                                                                  · have hr : n - 2800 < 50 := by omega
                                                                                                                    have heq : n = (n - 2800) + 2800 := by omega
                                                                                                                    rw [heq]
                                                                                                                    exact pos_w56 ⟨n - 2800, hr⟩
                                                                                                                  · by_cases h57 : n < 2900
                                                                                                                    · have hr : n - 2850 < 50 := by omega
                                                                                                                      have heq : n = (n - 2850) + 2850 := by omega
                                                                                                                      rw [heq]
                                                                                                                      exact pos_w57 ⟨n - 2850, hr⟩
                                                                                                                    · by_cases h58 : n < 2950
                                                                                                                      · have hr : n - 2900 < 50 := by omega
                                                                                                                        have heq : n = (n - 2900) + 2900 := by omega
                                                                                                                        rw [heq]
                                                                                                                        exact pos_w58 ⟨n - 2900, hr⟩
                                                                                                                      · by_cases h59 : n < 3000
                                                                                                                        · have hr : n - 2950 < 50 := by omega
                                                                                                                          have heq : n = (n - 2950) + 2950 := by omega
                                                                                                                          rw [heq]
                                                                                                                          exact pos_w59 ⟨n - 2950, hr⟩
                                                                                                                        · by_cases h60 : n < 3050
                                                                                                                          · have hr : n - 3000 < 50 := by omega
                                                                                                                            have heq : n = (n - 3000) + 3000 := by omega
                                                                                                                            rw [heq]
                                                                                                                            exact pos_w60 ⟨n - 3000, hr⟩
                                                                                                                          · by_cases h61 : n < 3100
                                                                                                                            · have hr : n - 3050 < 50 := by omega
                                                                                                                              have heq : n = (n - 3050) + 3050 := by omega
                                                                                                                              rw [heq]
                                                                                                                              exact pos_w61 ⟨n - 3050, hr⟩
                                                                                                                            · by_cases h62 : n < 3150
                                                                                                                              · have hr : n - 3100 < 50 := by omega
                                                                                                                                have heq : n = (n - 3100) + 3100 := by omega
                                                                                                                                rw [heq]
                                                                                                                                exact pos_w62 ⟨n - 3100, hr⟩
                                                                                                                              · by_cases h63 : n < 3200
                                                                                                                                · have hr : n - 3150 < 50 := by omega
                                                                                                                                  have heq : n = (n - 3150) + 3150 := by omega
                                                                                                                                  rw [heq]
                                                                                                                                  exact pos_w63 ⟨n - 3150, hr⟩
                                                                                                                                · by_cases h64 : n < 3250
                                                                                                                                  · have hr : n - 3200 < 50 := by omega
                                                                                                                                    have heq : n = (n - 3200) + 3200 := by omega
                                                                                                                                    rw [heq]
                                                                                                                                    exact pos_w64 ⟨n - 3200, hr⟩
                                                                                                                                  · by_cases h65 : n < 3300
                                                                                                                                    · have hr : n - 3250 < 50 := by omega
                                                                                                                                      have heq : n = (n - 3250) + 3250 := by omega
                                                                                                                                      rw [heq]
                                                                                                                                      exact pos_w65 ⟨n - 3250, hr⟩
                                                                                                                                    · by_cases h66 : n < 3350
                                                                                                                                      · have hr : n - 3300 < 50 := by omega
                                                                                                                                        have heq : n = (n - 3300) + 3300 := by omega
                                                                                                                                        rw [heq]
                                                                                                                                        exact pos_w66 ⟨n - 3300, hr⟩
                                                                                                                                      · by_cases h67 : n < 3400
                                                                                                                                        · have hr : n - 3350 < 50 := by omega
                                                                                                                                          have heq : n = (n - 3350) + 3350 := by omega
                                                                                                                                          rw [heq]
                                                                                                                                          exact pos_w67 ⟨n - 3350, hr⟩
                                                                                                                                        · by_cases h68 : n < 3450
                                                                                                                                          · have hr : n - 3400 < 50 := by omega
                                                                                                                                            have heq : n = (n - 3400) + 3400 := by omega
                                                                                                                                            rw [heq]
                                                                                                                                            exact pos_w68 ⟨n - 3400, hr⟩
                                                                                                                                          · by_cases h69 : n < 3500
                                                                                                                                            · have hr : n - 3450 < 50 := by omega
                                                                                                                                              have heq : n = (n - 3450) + 3450 := by omega
                                                                                                                                              rw [heq]
                                                                                                                                              exact pos_w69 ⟨n - 3450, hr⟩
                                                                                                                                            · by_cases h70 : n < 3550
                                                                                                                                              · have hr : n - 3500 < 50 := by omega
                                                                                                                                                have heq : n = (n - 3500) + 3500 := by omega
                                                                                                                                                rw [heq]
                                                                                                                                                exact pos_w70 ⟨n - 3500, hr⟩
                                                                                                                                              · by_cases h71 : n < 3600
                                                                                                                                                · have hr : n - 3550 < 50 := by omega
                                                                                                                                                  have heq : n = (n - 3550) + 3550 := by omega
                                                                                                                                                  rw [heq]
                                                                                                                                                  exact pos_w71 ⟨n - 3550, hr⟩
                                                                                                                                                · by_cases h72 : n < 3650
                                                                                                                                                  · have hr : n - 3600 < 50 := by omega
                                                                                                                                                    have heq : n = (n - 3600) + 3600 := by omega
                                                                                                                                                    rw [heq]
                                                                                                                                                    exact pos_w72 ⟨n - 3600, hr⟩
                                                                                                                                                  · by_cases h73 : n < 3700
                                                                                                                                                    · have hr : n - 3650 < 50 := by omega
                                                                                                                                                      have heq : n = (n - 3650) + 3650 := by omega
                                                                                                                                                      rw [heq]
                                                                                                                                                      exact pos_w73 ⟨n - 3650, hr⟩
                                                                                                                                                    · by_cases h74 : n < 3750
                                                                                                                                                      · have hr : n - 3700 < 50 := by omega
                                                                                                                                                        have heq : n = (n - 3700) + 3700 := by omega
                                                                                                                                                        rw [heq]
                                                                                                                                                        exact pos_w74 ⟨n - 3700, hr⟩
                                                                                                                                                      · by_cases h75 : n < 3800
                                                                                                                                                        · have hr : n - 3750 < 50 := by omega
                                                                                                                                                          have heq : n = (n - 3750) + 3750 := by omega
                                                                                                                                                          rw [heq]
                                                                                                                                                          exact pos_w75 ⟨n - 3750, hr⟩
                                                                                                                                                        · by_cases h76 : n < 3850
                                                                                                                                                          · have hr : n - 3800 < 50 := by omega
                                                                                                                                                            have heq : n = (n - 3800) + 3800 := by omega
                                                                                                                                                            rw [heq]
                                                                                                                                                            exact pos_w76 ⟨n - 3800, hr⟩
                                                                                                                                                          · by_cases h77 : n < 3900
                                                                                                                                                            · have hr : n - 3850 < 50 := by omega
                                                                                                                                                              have heq : n = (n - 3850) + 3850 := by omega
                                                                                                                                                              rw [heq]
                                                                                                                                                              exact pos_w77 ⟨n - 3850, hr⟩
                                                                                                                                                            · by_cases h78 : n < 3950
                                                                                                                                                              · have hr : n - 3900 < 50 := by omega
                                                                                                                                                                have heq : n = (n - 3900) + 3900 := by omega
                                                                                                                                                                rw [heq]
                                                                                                                                                                exact pos_w78 ⟨n - 3900, hr⟩
                                                                                                                                                              · by_cases h79 : n < 4000
                                                                                                                                                                · have hr : n - 3950 < 50 := by omega
                                                                                                                                                                  have heq : n = (n - 3950) + 3950 := by omega
                                                                                                                                                                  rw [heq]
                                                                                                                                                                  exact pos_w79 ⟨n - 3950, hr⟩
                                                                                                                                                                · by_cases h80 : n < 4050
                                                                                                                                                                  · have hr : n - 4000 < 50 := by omega
                                                                                                                                                                    have heq : n = (n - 4000) + 4000 := by omega
                                                                                                                                                                    rw [heq]
                                                                                                                                                                    exact pos_w80 ⟨n - 4000, hr⟩
                                                                                                                                                                  · by_cases h81 : n < 4100
                                                                                                                                                                    · have hr : n - 4050 < 50 := by omega
                                                                                                                                                                      have heq : n = (n - 4050) + 4050 := by omega
                                                                                                                                                                      rw [heq]
                                                                                                                                                                      exact pos_w81 ⟨n - 4050, hr⟩
                                                                                                                                                                    · by_cases h82 : n < 4150
                                                                                                                                                                      · have hr : n - 4100 < 50 := by omega
                                                                                                                                                                        have heq : n = (n - 4100) + 4100 := by omega
                                                                                                                                                                        rw [heq]
                                                                                                                                                                        exact pos_w82 ⟨n - 4100, hr⟩
                                                                                                                                                                      · by_cases h83 : n < 4200
                                                                                                                                                                        · have hr : n - 4150 < 50 := by omega
                                                                                                                                                                          have heq : n = (n - 4150) + 4150 := by omega
                                                                                                                                                                          rw [heq]
                                                                                                                                                                          exact pos_w83 ⟨n - 4150, hr⟩
                                                                                                                                                                        · by_cases h84 : n < 4250
                                                                                                                                                                          · have hr : n - 4200 < 50 := by omega
                                                                                                                                                                            have heq : n = (n - 4200) + 4200 := by omega
                                                                                                                                                                            rw [heq]
                                                                                                                                                                            exact pos_w84 ⟨n - 4200, hr⟩
                                                                                                                                                                          · by_cases h85 : n < 4300
                                                                                                                                                                            · have hr : n - 4250 < 50 := by omega
                                                                                                                                                                              have heq : n = (n - 4250) + 4250 := by omega
                                                                                                                                                                              rw [heq]
                                                                                                                                                                              exact pos_w85 ⟨n - 4250, hr⟩
                                                                                                                                                                            · by_cases h86 : n < 4350
                                                                                                                                                                              · have hr : n - 4300 < 50 := by omega
                                                                                                                                                                                have heq : n = (n - 4300) + 4300 := by omega
                                                                                                                                                                                rw [heq]
                                                                                                                                                                                exact pos_w86 ⟨n - 4300, hr⟩
                                                                                                                                                                              · by_cases h87 : n < 4400
                                                                                                                                                                                · have hr : n - 4350 < 50 := by omega
                                                                                                                                                                                  have heq : n = (n - 4350) + 4350 := by omega
                                                                                                                                                                                  rw [heq]
                                                                                                                                                                                  exact pos_w87 ⟨n - 4350, hr⟩
                                                                                                                                                                                · by_cases h88 : n < 4450
                                                                                                                                                                                  · have hr : n - 4400 < 50 := by omega
                                                                                                                                                                                    have heq : n = (n - 4400) + 4400 := by omega
                                                                                                                                                                                    rw [heq]
                                                                                                                                                                                    exact pos_w88 ⟨n - 4400, hr⟩
                                                                                                                                                                                  · by_cases h89 : n < 4500
                                                                                                                                                                                    · have hr : n - 4450 < 50 := by omega
                                                                                                                                                                                      have heq : n = (n - 4450) + 4450 := by omega
                                                                                                                                                                                      rw [heq]
                                                                                                                                                                                      exact pos_w89 ⟨n - 4450, hr⟩
                                                                                                                                                                                    · by_cases h90 : n < 4550
                                                                                                                                                                                      · have hr : n - 4500 < 50 := by omega
                                                                                                                                                                                        have heq : n = (n - 4500) + 4500 := by omega
                                                                                                                                                                                        rw [heq]
                                                                                                                                                                                        exact pos_w90 ⟨n - 4500, hr⟩
                                                                                                                                                                                      · by_cases h91 : n < 4600
                                                                                                                                                                                        · have hr : n - 4550 < 50 := by omega
                                                                                                                                                                                          have heq : n = (n - 4550) + 4550 := by omega
                                                                                                                                                                                          rw [heq]
                                                                                                                                                                                          exact pos_w91 ⟨n - 4550, hr⟩
                                                                                                                                                                                        · by_cases h92 : n < 4650
                                                                                                                                                                                          · have hr : n - 4600 < 50 := by omega
                                                                                                                                                                                            have heq : n = (n - 4600) + 4600 := by omega
                                                                                                                                                                                            rw [heq]
                                                                                                                                                                                            exact pos_w92 ⟨n - 4600, hr⟩
                                                                                                                                                                                          · by_cases h93 : n < 4700
                                                                                                                                                                                            · have hr : n - 4650 < 50 := by omega
                                                                                                                                                                                              have heq : n = (n - 4650) + 4650 := by omega
                                                                                                                                                                                              rw [heq]
                                                                                                                                                                                              exact pos_w93 ⟨n - 4650, hr⟩
                                                                                                                                                                                            · by_cases h94 : n < 4750
                                                                                                                                                                                              · have hr : n - 4700 < 50 := by omega
                                                                                                                                                                                                have heq : n = (n - 4700) + 4700 := by omega
                                                                                                                                                                                                rw [heq]
                                                                                                                                                                                                exact pos_w94 ⟨n - 4700, hr⟩
                                                                                                                                                                                              · by_cases h95 : n < 4800
                                                                                                                                                                                                · have hr : n - 4750 < 50 := by omega
                                                                                                                                                                                                  have heq : n = (n - 4750) + 4750 := by omega
                                                                                                                                                                                                  rw [heq]
                                                                                                                                                                                                  exact pos_w95 ⟨n - 4750, hr⟩
                                                                                                                                                                                                · by_cases h96 : n < 4850
                                                                                                                                                                                                  · have hr : n - 4800 < 50 := by omega
                                                                                                                                                                                                    have heq : n = (n - 4800) + 4800 := by omega
                                                                                                                                                                                                    rw [heq]
                                                                                                                                                                                                    exact pos_w96 ⟨n - 4800, hr⟩
                                                                                                                                                                                                  · by_cases h97 : n < 4900
                                                                                                                                                                                                    · have hr : n - 4850 < 50 := by omega
                                                                                                                                                                                                      have heq : n = (n - 4850) + 4850 := by omega
                                                                                                                                                                                                      rw [heq]
                                                                                                                                                                                                      exact pos_w97 ⟨n - 4850, hr⟩
                                                                                                                                                                                                    · by_cases h98 : n < 4950
                                                                                                                                                                                                      · have hr : n - 4900 < 50 := by omega
                                                                                                                                                                                                        have heq : n = (n - 4900) + 4900 := by omega
                                                                                                                                                                                                        rw [heq]
                                                                                                                                                                                                        exact pos_w98 ⟨n - 4900, hr⟩
                                                                                                                                                                                                      · by_cases h99 : n < 5000
                                                                                                                                                                                                        · have hr : n - 4950 < 50 := by omega
                                                                                                                                                                                                          have heq : n = (n - 4950) + 4950 := by omega
                                                                                                                                                                                                          rw [heq]
                                                                                                                                                                                                          exact pos_w99 ⟨n - 4950, hr⟩
                                                                                                                                                                                                        · omega

end IntMul.Kappa.R8.Bit.Oppbank.DimBound0


