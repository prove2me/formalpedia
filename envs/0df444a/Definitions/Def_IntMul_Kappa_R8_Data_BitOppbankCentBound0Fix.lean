-- Prove2me | Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankCentBound0Fix
-- name    : IntMul_Kappa_R8_Data_BitOppbankCentBound0Fix
-- status  : Definition
-- author  : @Ethan Cheung Wang
-- created : 2026-10-28T22:23:06.251177+00:00
-- url     : https://prove2.me/theorems/f244ec8b-3f70-480b-8a19-f326478e480a
-- title:
--   IntMul Kappa R8 Data BitOppbankCentBound0Fix
-- statement:
--   Densified HasCentre support certificates (IntMul_Kappa_R8_Data_BitOppbankCentBound0Fix) retargeted to PndFix/CentFix.

-- CentBound0Fix: PndFix retarget
-- CentBound pack 0: densified HasCentre certificates on n ∈ [0, 5000)
-- Generated for AllDensCentred (star-mask land + centF).

import Definitions.Def_IntMul_Kappa_R6_Defs4
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankPndFix
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankSupG
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankCentFix
import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 1000000
set_option exponentiation.threshold 2000

open IntMul.Kappa.R8.Bit.Oppbank.Pnd
open IntMul.Kappa.R8.Bit.Oppbank.SupG
open IntMul.Kappa.R8.Bit.Oppbank.Cent

namespace IntMul.Kappa.R8.Bit.Oppbank.CentBound0Fix

private theorem cs_w0 : ∀ n : Fin 50, centredStar (densSupG (n.val + 0)) (centF (n.val + 0)) = true := by decide
private theorem cl_w0 : ∀ n : Fin 50, centF (n.val + 0) < 23 := by decide
private theorem bd_w0 : ∀ n : Fin 50, densSupG (n.val + 0) < 2 ^ 1771 := by decide
private theorem cs_w1 : ∀ n : Fin 50, centredStar (densSupG (n.val + 50)) (centF (n.val + 50)) = true := by decide
private theorem cl_w1 : ∀ n : Fin 50, centF (n.val + 50) < 23 := by decide
private theorem bd_w1 : ∀ n : Fin 50, densSupG (n.val + 50) < 2 ^ 1771 := by decide
private theorem cs_w2 : ∀ n : Fin 50, centredStar (densSupG (n.val + 100)) (centF (n.val + 100)) = true := by decide
private theorem cl_w2 : ∀ n : Fin 50, centF (n.val + 100) < 23 := by decide
private theorem bd_w2 : ∀ n : Fin 50, densSupG (n.val + 100) < 2 ^ 1771 := by decide
private theorem cs_w3 : ∀ n : Fin 50, centredStar (densSupG (n.val + 150)) (centF (n.val + 150)) = true := by decide
private theorem cl_w3 : ∀ n : Fin 50, centF (n.val + 150) < 23 := by decide
private theorem bd_w3 : ∀ n : Fin 50, densSupG (n.val + 150) < 2 ^ 1771 := by decide
private theorem cs_w4 : ∀ n : Fin 50, centredStar (densSupG (n.val + 200)) (centF (n.val + 200)) = true := by decide
private theorem cl_w4 : ∀ n : Fin 50, centF (n.val + 200) < 23 := by decide
private theorem bd_w4 : ∀ n : Fin 50, densSupG (n.val + 200) < 2 ^ 1771 := by decide
private theorem cs_w5 : ∀ n : Fin 50, centredStar (densSupG (n.val + 250)) (centF (n.val + 250)) = true := by decide
private theorem cl_w5 : ∀ n : Fin 50, centF (n.val + 250) < 23 := by decide
private theorem bd_w5 : ∀ n : Fin 50, densSupG (n.val + 250) < 2 ^ 1771 := by decide
private theorem cs_w6 : ∀ n : Fin 50, centredStar (densSupG (n.val + 300)) (centF (n.val + 300)) = true := by decide
private theorem cl_w6 : ∀ n : Fin 50, centF (n.val + 300) < 23 := by decide
private theorem bd_w6 : ∀ n : Fin 50, densSupG (n.val + 300) < 2 ^ 1771 := by decide
private theorem cs_w7 : ∀ n : Fin 50, centredStar (densSupG (n.val + 350)) (centF (n.val + 350)) = true := by decide
private theorem cl_w7 : ∀ n : Fin 50, centF (n.val + 350) < 23 := by decide
private theorem bd_w7 : ∀ n : Fin 50, densSupG (n.val + 350) < 2 ^ 1771 := by decide
private theorem cs_w8 : ∀ n : Fin 50, centredStar (densSupG (n.val + 400)) (centF (n.val + 400)) = true := by decide
private theorem cl_w8 : ∀ n : Fin 50, centF (n.val + 400) < 23 := by decide
private theorem bd_w8 : ∀ n : Fin 50, densSupG (n.val + 400) < 2 ^ 1771 := by decide
private theorem cs_w9 : ∀ n : Fin 50, centredStar (densSupG (n.val + 450)) (centF (n.val + 450)) = true := by decide
private theorem cl_w9 : ∀ n : Fin 50, centF (n.val + 450) < 23 := by decide
private theorem bd_w9 : ∀ n : Fin 50, densSupG (n.val + 450) < 2 ^ 1771 := by decide
private theorem cs_w10 : ∀ n : Fin 50, centredStar (densSupG (n.val + 500)) (centF (n.val + 500)) = true := by decide
private theorem cl_w10 : ∀ n : Fin 50, centF (n.val + 500) < 23 := by decide
private theorem bd_w10 : ∀ n : Fin 50, densSupG (n.val + 500) < 2 ^ 1771 := by decide
private theorem cs_w11 : ∀ n : Fin 50, centredStar (densSupG (n.val + 550)) (centF (n.val + 550)) = true := by decide
private theorem cl_w11 : ∀ n : Fin 50, centF (n.val + 550) < 23 := by decide
private theorem bd_w11 : ∀ n : Fin 50, densSupG (n.val + 550) < 2 ^ 1771 := by decide
private theorem cs_w12 : ∀ n : Fin 50, centredStar (densSupG (n.val + 600)) (centF (n.val + 600)) = true := by decide
private theorem cl_w12 : ∀ n : Fin 50, centF (n.val + 600) < 23 := by decide
private theorem bd_w12 : ∀ n : Fin 50, densSupG (n.val + 600) < 2 ^ 1771 := by decide
private theorem cs_w13 : ∀ n : Fin 50, centredStar (densSupG (n.val + 650)) (centF (n.val + 650)) = true := by decide
private theorem cl_w13 : ∀ n : Fin 50, centF (n.val + 650) < 23 := by decide
private theorem bd_w13 : ∀ n : Fin 50, densSupG (n.val + 650) < 2 ^ 1771 := by decide
private theorem cs_w14 : ∀ n : Fin 50, centredStar (densSupG (n.val + 700)) (centF (n.val + 700)) = true := by decide
private theorem cl_w14 : ∀ n : Fin 50, centF (n.val + 700) < 23 := by decide
private theorem bd_w14 : ∀ n : Fin 50, densSupG (n.val + 700) < 2 ^ 1771 := by decide
private theorem cs_w15 : ∀ n : Fin 50, centredStar (densSupG (n.val + 750)) (centF (n.val + 750)) = true := by decide
private theorem cl_w15 : ∀ n : Fin 50, centF (n.val + 750) < 23 := by decide
private theorem bd_w15 : ∀ n : Fin 50, densSupG (n.val + 750) < 2 ^ 1771 := by decide
private theorem cs_w16 : ∀ n : Fin 50, centredStar (densSupG (n.val + 800)) (centF (n.val + 800)) = true := by decide
private theorem cl_w16 : ∀ n : Fin 50, centF (n.val + 800) < 23 := by decide
private theorem bd_w16 : ∀ n : Fin 50, densSupG (n.val + 800) < 2 ^ 1771 := by decide
private theorem cs_w17 : ∀ n : Fin 50, centredStar (densSupG (n.val + 850)) (centF (n.val + 850)) = true := by decide
private theorem cl_w17 : ∀ n : Fin 50, centF (n.val + 850) < 23 := by decide
private theorem bd_w17 : ∀ n : Fin 50, densSupG (n.val + 850) < 2 ^ 1771 := by decide
private theorem cs_w18 : ∀ n : Fin 50, centredStar (densSupG (n.val + 900)) (centF (n.val + 900)) = true := by decide
private theorem cl_w18 : ∀ n : Fin 50, centF (n.val + 900) < 23 := by decide
private theorem bd_w18 : ∀ n : Fin 50, densSupG (n.val + 900) < 2 ^ 1771 := by decide
private theorem cs_w19 : ∀ n : Fin 50, centredStar (densSupG (n.val + 950)) (centF (n.val + 950)) = true := by decide
private theorem cl_w19 : ∀ n : Fin 50, centF (n.val + 950) < 23 := by decide
private theorem bd_w19 : ∀ n : Fin 50, densSupG (n.val + 950) < 2 ^ 1771 := by decide
private theorem cs_w20 : ∀ n : Fin 50, centredStar (densSupG (n.val + 1000)) (centF (n.val + 1000)) = true := by decide
private theorem cl_w20 : ∀ n : Fin 50, centF (n.val + 1000) < 23 := by decide
private theorem bd_w20 : ∀ n : Fin 50, densSupG (n.val + 1000) < 2 ^ 1771 := by decide
private theorem cs_w21 : ∀ n : Fin 50, centredStar (densSupG (n.val + 1050)) (centF (n.val + 1050)) = true := by decide
private theorem cl_w21 : ∀ n : Fin 50, centF (n.val + 1050) < 23 := by decide
private theorem bd_w21 : ∀ n : Fin 50, densSupG (n.val + 1050) < 2 ^ 1771 := by decide
private theorem cs_w22 : ∀ n : Fin 50, centredStar (densSupG (n.val + 1100)) (centF (n.val + 1100)) = true := by decide
private theorem cl_w22 : ∀ n : Fin 50, centF (n.val + 1100) < 23 := by decide
private theorem bd_w22 : ∀ n : Fin 50, densSupG (n.val + 1100) < 2 ^ 1771 := by decide
private theorem cs_w23 : ∀ n : Fin 50, centredStar (densSupG (n.val + 1150)) (centF (n.val + 1150)) = true := by decide
private theorem cl_w23 : ∀ n : Fin 50, centF (n.val + 1150) < 23 := by decide
private theorem bd_w23 : ∀ n : Fin 50, densSupG (n.val + 1150) < 2 ^ 1771 := by decide
private theorem cs_w24 : ∀ n : Fin 50, centredStar (densSupG (n.val + 1200)) (centF (n.val + 1200)) = true := by decide
private theorem cl_w24 : ∀ n : Fin 50, centF (n.val + 1200) < 23 := by decide
private theorem bd_w24 : ∀ n : Fin 50, densSupG (n.val + 1200) < 2 ^ 1771 := by decide
private theorem cs_w25 : ∀ n : Fin 50, centredStar (densSupG (n.val + 1250)) (centF (n.val + 1250)) = true := by decide
private theorem cl_w25 : ∀ n : Fin 50, centF (n.val + 1250) < 23 := by decide
private theorem bd_w25 : ∀ n : Fin 50, densSupG (n.val + 1250) < 2 ^ 1771 := by decide
private theorem cs_w26 : ∀ n : Fin 50, centredStar (densSupG (n.val + 1300)) (centF (n.val + 1300)) = true := by decide
private theorem cl_w26 : ∀ n : Fin 50, centF (n.val + 1300) < 23 := by decide
private theorem bd_w26 : ∀ n : Fin 50, densSupG (n.val + 1300) < 2 ^ 1771 := by decide
private theorem cs_w27 : ∀ n : Fin 50, centredStar (densSupG (n.val + 1350)) (centF (n.val + 1350)) = true := by decide
private theorem cl_w27 : ∀ n : Fin 50, centF (n.val + 1350) < 23 := by decide
private theorem bd_w27 : ∀ n : Fin 50, densSupG (n.val + 1350) < 2 ^ 1771 := by decide
private theorem cs_w28 : ∀ n : Fin 50, centredStar (densSupG (n.val + 1400)) (centF (n.val + 1400)) = true := by decide
private theorem cl_w28 : ∀ n : Fin 50, centF (n.val + 1400) < 23 := by decide
private theorem bd_w28 : ∀ n : Fin 50, densSupG (n.val + 1400) < 2 ^ 1771 := by decide
private theorem cs_w29 : ∀ n : Fin 50, centredStar (densSupG (n.val + 1450)) (centF (n.val + 1450)) = true := by decide
private theorem cl_w29 : ∀ n : Fin 50, centF (n.val + 1450) < 23 := by decide
private theorem bd_w29 : ∀ n : Fin 50, densSupG (n.val + 1450) < 2 ^ 1771 := by decide
private theorem cs_w30 : ∀ n : Fin 50, centredStar (densSupG (n.val + 1500)) (centF (n.val + 1500)) = true := by decide
private theorem cl_w30 : ∀ n : Fin 50, centF (n.val + 1500) < 23 := by decide
private theorem bd_w30 : ∀ n : Fin 50, densSupG (n.val + 1500) < 2 ^ 1771 := by decide
private theorem cs_w31 : ∀ n : Fin 50, centredStar (densSupG (n.val + 1550)) (centF (n.val + 1550)) = true := by decide
private theorem cl_w31 : ∀ n : Fin 50, centF (n.val + 1550) < 23 := by decide
private theorem bd_w31 : ∀ n : Fin 50, densSupG (n.val + 1550) < 2 ^ 1771 := by decide
private theorem cs_w32 : ∀ n : Fin 50, centredStar (densSupG (n.val + 1600)) (centF (n.val + 1600)) = true := by decide
private theorem cl_w32 : ∀ n : Fin 50, centF (n.val + 1600) < 23 := by decide
private theorem bd_w32 : ∀ n : Fin 50, densSupG (n.val + 1600) < 2 ^ 1771 := by decide
private theorem cs_w33 : ∀ n : Fin 50, centredStar (densSupG (n.val + 1650)) (centF (n.val + 1650)) = true := by decide
private theorem cl_w33 : ∀ n : Fin 50, centF (n.val + 1650) < 23 := by decide
private theorem bd_w33 : ∀ n : Fin 50, densSupG (n.val + 1650) < 2 ^ 1771 := by decide
private theorem cs_w34 : ∀ n : Fin 50, centredStar (densSupG (n.val + 1700)) (centF (n.val + 1700)) = true := by decide
private theorem cl_w34 : ∀ n : Fin 50, centF (n.val + 1700) < 23 := by decide
private theorem bd_w34 : ∀ n : Fin 50, densSupG (n.val + 1700) < 2 ^ 1771 := by decide
private theorem cs_w35 : ∀ n : Fin 50, centredStar (densSupG (n.val + 1750)) (centF (n.val + 1750)) = true := by decide
private theorem cl_w35 : ∀ n : Fin 50, centF (n.val + 1750) < 23 := by decide
private theorem bd_w35 : ∀ n : Fin 50, densSupG (n.val + 1750) < 2 ^ 1771 := by decide
private theorem cs_w36 : ∀ n : Fin 50, centredStar (densSupG (n.val + 1800)) (centF (n.val + 1800)) = true := by decide
private theorem cl_w36 : ∀ n : Fin 50, centF (n.val + 1800) < 23 := by decide
private theorem bd_w36 : ∀ n : Fin 50, densSupG (n.val + 1800) < 2 ^ 1771 := by decide
private theorem cs_w37 : ∀ n : Fin 50, centredStar (densSupG (n.val + 1850)) (centF (n.val + 1850)) = true := by decide
private theorem cl_w37 : ∀ n : Fin 50, centF (n.val + 1850) < 23 := by decide
private theorem bd_w37 : ∀ n : Fin 50, densSupG (n.val + 1850) < 2 ^ 1771 := by decide
private theorem cs_w38 : ∀ n : Fin 50, centredStar (densSupG (n.val + 1900)) (centF (n.val + 1900)) = true := by decide
private theorem cl_w38 : ∀ n : Fin 50, centF (n.val + 1900) < 23 := by decide
private theorem bd_w38 : ∀ n : Fin 50, densSupG (n.val + 1900) < 2 ^ 1771 := by decide
private theorem cs_w39 : ∀ n : Fin 50, centredStar (densSupG (n.val + 1950)) (centF (n.val + 1950)) = true := by decide
private theorem cl_w39 : ∀ n : Fin 50, centF (n.val + 1950) < 23 := by decide
private theorem bd_w39 : ∀ n : Fin 50, densSupG (n.val + 1950) < 2 ^ 1771 := by decide
private theorem cs_w40 : ∀ n : Fin 50, centredStar (densSupG (n.val + 2000)) (centF (n.val + 2000)) = true := by decide
private theorem cl_w40 : ∀ n : Fin 50, centF (n.val + 2000) < 23 := by decide
private theorem bd_w40 : ∀ n : Fin 50, densSupG (n.val + 2000) < 2 ^ 1771 := by decide
private theorem cs_w41 : ∀ n : Fin 50, centredStar (densSupG (n.val + 2050)) (centF (n.val + 2050)) = true := by decide
private theorem cl_w41 : ∀ n : Fin 50, centF (n.val + 2050) < 23 := by decide
private theorem bd_w41 : ∀ n : Fin 50, densSupG (n.val + 2050) < 2 ^ 1771 := by decide
private theorem cs_w42 : ∀ n : Fin 50, centredStar (densSupG (n.val + 2100)) (centF (n.val + 2100)) = true := by decide
private theorem cl_w42 : ∀ n : Fin 50, centF (n.val + 2100) < 23 := by decide
private theorem bd_w42 : ∀ n : Fin 50, densSupG (n.val + 2100) < 2 ^ 1771 := by decide
private theorem cs_w43 : ∀ n : Fin 50, centredStar (densSupG (n.val + 2150)) (centF (n.val + 2150)) = true := by decide
private theorem cl_w43 : ∀ n : Fin 50, centF (n.val + 2150) < 23 := by decide
private theorem bd_w43 : ∀ n : Fin 50, densSupG (n.val + 2150) < 2 ^ 1771 := by decide
private theorem cs_w44 : ∀ n : Fin 50, centredStar (densSupG (n.val + 2200)) (centF (n.val + 2200)) = true := by decide
private theorem cl_w44 : ∀ n : Fin 50, centF (n.val + 2200) < 23 := by decide
private theorem bd_w44 : ∀ n : Fin 50, densSupG (n.val + 2200) < 2 ^ 1771 := by decide
private theorem cs_w45 : ∀ n : Fin 50, centredStar (densSupG (n.val + 2250)) (centF (n.val + 2250)) = true := by decide
private theorem cl_w45 : ∀ n : Fin 50, centF (n.val + 2250) < 23 := by decide
private theorem bd_w45 : ∀ n : Fin 50, densSupG (n.val + 2250) < 2 ^ 1771 := by decide
private theorem cs_w46 : ∀ n : Fin 50, centredStar (densSupG (n.val + 2300)) (centF (n.val + 2300)) = true := by decide
private theorem cl_w46 : ∀ n : Fin 50, centF (n.val + 2300) < 23 := by decide
private theorem bd_w46 : ∀ n : Fin 50, densSupG (n.val + 2300) < 2 ^ 1771 := by decide
private theorem cs_w47 : ∀ n : Fin 50, centredStar (densSupG (n.val + 2350)) (centF (n.val + 2350)) = true := by decide
private theorem cl_w47 : ∀ n : Fin 50, centF (n.val + 2350) < 23 := by decide
private theorem bd_w47 : ∀ n : Fin 50, densSupG (n.val + 2350) < 2 ^ 1771 := by decide
private theorem cs_w48 : ∀ n : Fin 50, centredStar (densSupG (n.val + 2400)) (centF (n.val + 2400)) = true := by decide
private theorem cl_w48 : ∀ n : Fin 50, centF (n.val + 2400) < 23 := by decide
private theorem bd_w48 : ∀ n : Fin 50, densSupG (n.val + 2400) < 2 ^ 1771 := by decide
private theorem cs_w49 : ∀ n : Fin 50, centredStar (densSupG (n.val + 2450)) (centF (n.val + 2450)) = true := by decide
private theorem cl_w49 : ∀ n : Fin 50, centF (n.val + 2450) < 23 := by decide
private theorem bd_w49 : ∀ n : Fin 50, densSupG (n.val + 2450) < 2 ^ 1771 := by decide
private theorem cs_w50 : ∀ n : Fin 50, centredStar (densSupG (n.val + 2500)) (centF (n.val + 2500)) = true := by decide
private theorem cl_w50 : ∀ n : Fin 50, centF (n.val + 2500) < 23 := by decide
private theorem bd_w50 : ∀ n : Fin 50, densSupG (n.val + 2500) < 2 ^ 1771 := by decide
private theorem cs_w51 : ∀ n : Fin 50, centredStar (densSupG (n.val + 2550)) (centF (n.val + 2550)) = true := by decide
private theorem cl_w51 : ∀ n : Fin 50, centF (n.val + 2550) < 23 := by decide
private theorem bd_w51 : ∀ n : Fin 50, densSupG (n.val + 2550) < 2 ^ 1771 := by decide
private theorem cs_w52 : ∀ n : Fin 50, centredStar (densSupG (n.val + 2600)) (centF (n.val + 2600)) = true := by decide
private theorem cl_w52 : ∀ n : Fin 50, centF (n.val + 2600) < 23 := by decide
private theorem bd_w52 : ∀ n : Fin 50, densSupG (n.val + 2600) < 2 ^ 1771 := by decide
private theorem cs_w53 : ∀ n : Fin 50, centredStar (densSupG (n.val + 2650)) (centF (n.val + 2650)) = true := by decide
private theorem cl_w53 : ∀ n : Fin 50, centF (n.val + 2650) < 23 := by decide
private theorem bd_w53 : ∀ n : Fin 50, densSupG (n.val + 2650) < 2 ^ 1771 := by decide
private theorem cs_w54 : ∀ n : Fin 50, centredStar (densSupG (n.val + 2700)) (centF (n.val + 2700)) = true := by decide
private theorem cl_w54 : ∀ n : Fin 50, centF (n.val + 2700) < 23 := by decide
private theorem bd_w54 : ∀ n : Fin 50, densSupG (n.val + 2700) < 2 ^ 1771 := by decide
private theorem cs_w55 : ∀ n : Fin 50, centredStar (densSupG (n.val + 2750)) (centF (n.val + 2750)) = true := by decide
private theorem cl_w55 : ∀ n : Fin 50, centF (n.val + 2750) < 23 := by decide
private theorem bd_w55 : ∀ n : Fin 50, densSupG (n.val + 2750) < 2 ^ 1771 := by decide
private theorem cs_w56 : ∀ n : Fin 50, centredStar (densSupG (n.val + 2800)) (centF (n.val + 2800)) = true := by decide
private theorem cl_w56 : ∀ n : Fin 50, centF (n.val + 2800) < 23 := by decide
private theorem bd_w56 : ∀ n : Fin 50, densSupG (n.val + 2800) < 2 ^ 1771 := by decide
private theorem cs_w57 : ∀ n : Fin 50, centredStar (densSupG (n.val + 2850)) (centF (n.val + 2850)) = true := by decide
private theorem cl_w57 : ∀ n : Fin 50, centF (n.val + 2850) < 23 := by decide
private theorem bd_w57 : ∀ n : Fin 50, densSupG (n.val + 2850) < 2 ^ 1771 := by decide
private theorem cs_w58 : ∀ n : Fin 50, centredStar (densSupG (n.val + 2900)) (centF (n.val + 2900)) = true := by decide
private theorem cl_w58 : ∀ n : Fin 50, centF (n.val + 2900) < 23 := by decide
private theorem bd_w58 : ∀ n : Fin 50, densSupG (n.val + 2900) < 2 ^ 1771 := by decide
private theorem cs_w59 : ∀ n : Fin 50, centredStar (densSupG (n.val + 2950)) (centF (n.val + 2950)) = true := by decide
private theorem cl_w59 : ∀ n : Fin 50, centF (n.val + 2950) < 23 := by decide
private theorem bd_w59 : ∀ n : Fin 50, densSupG (n.val + 2950) < 2 ^ 1771 := by decide
private theorem cs_w60 : ∀ n : Fin 50, centredStar (densSupG (n.val + 3000)) (centF (n.val + 3000)) = true := by decide
private theorem cl_w60 : ∀ n : Fin 50, centF (n.val + 3000) < 23 := by decide
private theorem bd_w60 : ∀ n : Fin 50, densSupG (n.val + 3000) < 2 ^ 1771 := by decide
private theorem cs_w61 : ∀ n : Fin 50, centredStar (densSupG (n.val + 3050)) (centF (n.val + 3050)) = true := by decide
private theorem cl_w61 : ∀ n : Fin 50, centF (n.val + 3050) < 23 := by decide
private theorem bd_w61 : ∀ n : Fin 50, densSupG (n.val + 3050) < 2 ^ 1771 := by decide
private theorem cs_w62 : ∀ n : Fin 50, centredStar (densSupG (n.val + 3100)) (centF (n.val + 3100)) = true := by decide
private theorem cl_w62 : ∀ n : Fin 50, centF (n.val + 3100) < 23 := by decide
private theorem bd_w62 : ∀ n : Fin 50, densSupG (n.val + 3100) < 2 ^ 1771 := by decide
private theorem cs_w63 : ∀ n : Fin 50, centredStar (densSupG (n.val + 3150)) (centF (n.val + 3150)) = true := by decide
private theorem cl_w63 : ∀ n : Fin 50, centF (n.val + 3150) < 23 := by decide
private theorem bd_w63 : ∀ n : Fin 50, densSupG (n.val + 3150) < 2 ^ 1771 := by decide
private theorem cs_w64 : ∀ n : Fin 50, centredStar (densSupG (n.val + 3200)) (centF (n.val + 3200)) = true := by decide
private theorem cl_w64 : ∀ n : Fin 50, centF (n.val + 3200) < 23 := by decide
private theorem bd_w64 : ∀ n : Fin 50, densSupG (n.val + 3200) < 2 ^ 1771 := by decide
private theorem cs_w65 : ∀ n : Fin 50, centredStar (densSupG (n.val + 3250)) (centF (n.val + 3250)) = true := by decide
private theorem cl_w65 : ∀ n : Fin 50, centF (n.val + 3250) < 23 := by decide
private theorem bd_w65 : ∀ n : Fin 50, densSupG (n.val + 3250) < 2 ^ 1771 := by decide
private theorem cs_w66 : ∀ n : Fin 50, centredStar (densSupG (n.val + 3300)) (centF (n.val + 3300)) = true := by decide
private theorem cl_w66 : ∀ n : Fin 50, centF (n.val + 3300) < 23 := by decide
private theorem bd_w66 : ∀ n : Fin 50, densSupG (n.val + 3300) < 2 ^ 1771 := by decide
private theorem cs_w67 : ∀ n : Fin 50, centredStar (densSupG (n.val + 3350)) (centF (n.val + 3350)) = true := by decide
private theorem cl_w67 : ∀ n : Fin 50, centF (n.val + 3350) < 23 := by decide
private theorem bd_w67 : ∀ n : Fin 50, densSupG (n.val + 3350) < 2 ^ 1771 := by decide
private theorem cs_w68 : ∀ n : Fin 50, centredStar (densSupG (n.val + 3400)) (centF (n.val + 3400)) = true := by decide
private theorem cl_w68 : ∀ n : Fin 50, centF (n.val + 3400) < 23 := by decide
private theorem bd_w68 : ∀ n : Fin 50, densSupG (n.val + 3400) < 2 ^ 1771 := by decide
private theorem cs_w69 : ∀ n : Fin 50, centredStar (densSupG (n.val + 3450)) (centF (n.val + 3450)) = true := by decide
private theorem cl_w69 : ∀ n : Fin 50, centF (n.val + 3450) < 23 := by decide
private theorem bd_w69 : ∀ n : Fin 50, densSupG (n.val + 3450) < 2 ^ 1771 := by decide
private theorem cs_w70 : ∀ n : Fin 50, centredStar (densSupG (n.val + 3500)) (centF (n.val + 3500)) = true := by decide
private theorem cl_w70 : ∀ n : Fin 50, centF (n.val + 3500) < 23 := by decide
private theorem bd_w70 : ∀ n : Fin 50, densSupG (n.val + 3500) < 2 ^ 1771 := by decide
private theorem cs_w71 : ∀ n : Fin 50, centredStar (densSupG (n.val + 3550)) (centF (n.val + 3550)) = true := by decide
private theorem cl_w71 : ∀ n : Fin 50, centF (n.val + 3550) < 23 := by decide
private theorem bd_w71 : ∀ n : Fin 50, densSupG (n.val + 3550) < 2 ^ 1771 := by decide
private theorem cs_w72 : ∀ n : Fin 50, centredStar (densSupG (n.val + 3600)) (centF (n.val + 3600)) = true := by decide
private theorem cl_w72 : ∀ n : Fin 50, centF (n.val + 3600) < 23 := by decide
private theorem bd_w72 : ∀ n : Fin 50, densSupG (n.val + 3600) < 2 ^ 1771 := by decide
private theorem cs_w73 : ∀ n : Fin 50, centredStar (densSupG (n.val + 3650)) (centF (n.val + 3650)) = true := by decide
private theorem cl_w73 : ∀ n : Fin 50, centF (n.val + 3650) < 23 := by decide
private theorem bd_w73 : ∀ n : Fin 50, densSupG (n.val + 3650) < 2 ^ 1771 := by decide
private theorem cs_w74 : ∀ n : Fin 50, centredStar (densSupG (n.val + 3700)) (centF (n.val + 3700)) = true := by decide
private theorem cl_w74 : ∀ n : Fin 50, centF (n.val + 3700) < 23 := by decide
private theorem bd_w74 : ∀ n : Fin 50, densSupG (n.val + 3700) < 2 ^ 1771 := by decide
private theorem cs_w75 : ∀ n : Fin 50, centredStar (densSupG (n.val + 3750)) (centF (n.val + 3750)) = true := by decide
private theorem cl_w75 : ∀ n : Fin 50, centF (n.val + 3750) < 23 := by decide
private theorem bd_w75 : ∀ n : Fin 50, densSupG (n.val + 3750) < 2 ^ 1771 := by decide
private theorem cs_w76 : ∀ n : Fin 50, centredStar (densSupG (n.val + 3800)) (centF (n.val + 3800)) = true := by decide
private theorem cl_w76 : ∀ n : Fin 50, centF (n.val + 3800) < 23 := by decide
private theorem bd_w76 : ∀ n : Fin 50, densSupG (n.val + 3800) < 2 ^ 1771 := by decide
private theorem cs_w77 : ∀ n : Fin 50, centredStar (densSupG (n.val + 3850)) (centF (n.val + 3850)) = true := by decide
private theorem cl_w77 : ∀ n : Fin 50, centF (n.val + 3850) < 23 := by decide
private theorem bd_w77 : ∀ n : Fin 50, densSupG (n.val + 3850) < 2 ^ 1771 := by decide
private theorem cs_w78 : ∀ n : Fin 50, centredStar (densSupG (n.val + 3900)) (centF (n.val + 3900)) = true := by decide
private theorem cl_w78 : ∀ n : Fin 50, centF (n.val + 3900) < 23 := by decide
private theorem bd_w78 : ∀ n : Fin 50, densSupG (n.val + 3900) < 2 ^ 1771 := by decide
private theorem cs_w79 : ∀ n : Fin 50, centredStar (densSupG (n.val + 3950)) (centF (n.val + 3950)) = true := by decide
private theorem cl_w79 : ∀ n : Fin 50, centF (n.val + 3950) < 23 := by decide
private theorem bd_w79 : ∀ n : Fin 50, densSupG (n.val + 3950) < 2 ^ 1771 := by decide
private theorem cs_w80 : ∀ n : Fin 50, centredStar (densSupG (n.val + 4000)) (centF (n.val + 4000)) = true := by decide
private theorem cl_w80 : ∀ n : Fin 50, centF (n.val + 4000) < 23 := by decide
private theorem bd_w80 : ∀ n : Fin 50, densSupG (n.val + 4000) < 2 ^ 1771 := by decide
private theorem cs_w81 : ∀ n : Fin 50, centredStar (densSupG (n.val + 4050)) (centF (n.val + 4050)) = true := by decide
private theorem cl_w81 : ∀ n : Fin 50, centF (n.val + 4050) < 23 := by decide
private theorem bd_w81 : ∀ n : Fin 50, densSupG (n.val + 4050) < 2 ^ 1771 := by decide
private theorem cs_w82 : ∀ n : Fin 50, centredStar (densSupG (n.val + 4100)) (centF (n.val + 4100)) = true := by decide
private theorem cl_w82 : ∀ n : Fin 50, centF (n.val + 4100) < 23 := by decide
private theorem bd_w82 : ∀ n : Fin 50, densSupG (n.val + 4100) < 2 ^ 1771 := by decide
private theorem cs_w83 : ∀ n : Fin 50, centredStar (densSupG (n.val + 4150)) (centF (n.val + 4150)) = true := by decide
private theorem cl_w83 : ∀ n : Fin 50, centF (n.val + 4150) < 23 := by decide
private theorem bd_w83 : ∀ n : Fin 50, densSupG (n.val + 4150) < 2 ^ 1771 := by decide
private theorem cs_w84 : ∀ n : Fin 50, centredStar (densSupG (n.val + 4200)) (centF (n.val + 4200)) = true := by decide
private theorem cl_w84 : ∀ n : Fin 50, centF (n.val + 4200) < 23 := by decide
private theorem bd_w84 : ∀ n : Fin 50, densSupG (n.val + 4200) < 2 ^ 1771 := by decide
private theorem cs_w85 : ∀ n : Fin 50, centredStar (densSupG (n.val + 4250)) (centF (n.val + 4250)) = true := by decide
private theorem cl_w85 : ∀ n : Fin 50, centF (n.val + 4250) < 23 := by decide
private theorem bd_w85 : ∀ n : Fin 50, densSupG (n.val + 4250) < 2 ^ 1771 := by decide
private theorem cs_w86 : ∀ n : Fin 50, centredStar (densSupG (n.val + 4300)) (centF (n.val + 4300)) = true := by decide
private theorem cl_w86 : ∀ n : Fin 50, centF (n.val + 4300) < 23 := by decide
private theorem bd_w86 : ∀ n : Fin 50, densSupG (n.val + 4300) < 2 ^ 1771 := by decide
private theorem cs_w87 : ∀ n : Fin 50, centredStar (densSupG (n.val + 4350)) (centF (n.val + 4350)) = true := by decide
private theorem cl_w87 : ∀ n : Fin 50, centF (n.val + 4350) < 23 := by decide
private theorem bd_w87 : ∀ n : Fin 50, densSupG (n.val + 4350) < 2 ^ 1771 := by decide
private theorem cs_w88 : ∀ n : Fin 50, centredStar (densSupG (n.val + 4400)) (centF (n.val + 4400)) = true := by decide
private theorem cl_w88 : ∀ n : Fin 50, centF (n.val + 4400) < 23 := by decide
private theorem bd_w88 : ∀ n : Fin 50, densSupG (n.val + 4400) < 2 ^ 1771 := by decide
private theorem cs_w89 : ∀ n : Fin 50, centredStar (densSupG (n.val + 4450)) (centF (n.val + 4450)) = true := by decide
private theorem cl_w89 : ∀ n : Fin 50, centF (n.val + 4450) < 23 := by decide
private theorem bd_w89 : ∀ n : Fin 50, densSupG (n.val + 4450) < 2 ^ 1771 := by decide
private theorem cs_w90 : ∀ n : Fin 50, centredStar (densSupG (n.val + 4500)) (centF (n.val + 4500)) = true := by decide
private theorem cl_w90 : ∀ n : Fin 50, centF (n.val + 4500) < 23 := by decide
private theorem bd_w90 : ∀ n : Fin 50, densSupG (n.val + 4500) < 2 ^ 1771 := by decide
private theorem cs_w91 : ∀ n : Fin 50, centredStar (densSupG (n.val + 4550)) (centF (n.val + 4550)) = true := by decide
private theorem cl_w91 : ∀ n : Fin 50, centF (n.val + 4550) < 23 := by decide
private theorem bd_w91 : ∀ n : Fin 50, densSupG (n.val + 4550) < 2 ^ 1771 := by decide
private theorem cs_w92 : ∀ n : Fin 50, centredStar (densSupG (n.val + 4600)) (centF (n.val + 4600)) = true := by decide
private theorem cl_w92 : ∀ n : Fin 50, centF (n.val + 4600) < 23 := by decide
private theorem bd_w92 : ∀ n : Fin 50, densSupG (n.val + 4600) < 2 ^ 1771 := by decide
private theorem cs_w93 : ∀ n : Fin 50, centredStar (densSupG (n.val + 4650)) (centF (n.val + 4650)) = true := by decide
private theorem cl_w93 : ∀ n : Fin 50, centF (n.val + 4650) < 23 := by decide
private theorem bd_w93 : ∀ n : Fin 50, densSupG (n.val + 4650) < 2 ^ 1771 := by decide
private theorem cs_w94 : ∀ n : Fin 50, centredStar (densSupG (n.val + 4700)) (centF (n.val + 4700)) = true := by decide
private theorem cl_w94 : ∀ n : Fin 50, centF (n.val + 4700) < 23 := by decide
private theorem bd_w94 : ∀ n : Fin 50, densSupG (n.val + 4700) < 2 ^ 1771 := by decide
private theorem cs_w95 : ∀ n : Fin 50, centredStar (densSupG (n.val + 4750)) (centF (n.val + 4750)) = true := by decide
private theorem cl_w95 : ∀ n : Fin 50, centF (n.val + 4750) < 23 := by decide
private theorem bd_w95 : ∀ n : Fin 50, densSupG (n.val + 4750) < 2 ^ 1771 := by decide
private theorem cs_w96 : ∀ n : Fin 50, centredStar (densSupG (n.val + 4800)) (centF (n.val + 4800)) = true := by decide
private theorem cl_w96 : ∀ n : Fin 50, centF (n.val + 4800) < 23 := by decide
private theorem bd_w96 : ∀ n : Fin 50, densSupG (n.val + 4800) < 2 ^ 1771 := by decide
private theorem cs_w97 : ∀ n : Fin 50, centredStar (densSupG (n.val + 4850)) (centF (n.val + 4850)) = true := by decide
private theorem cl_w97 : ∀ n : Fin 50, centF (n.val + 4850) < 23 := by decide
private theorem bd_w97 : ∀ n : Fin 50, densSupG (n.val + 4850) < 2 ^ 1771 := by decide
private theorem cs_w98 : ∀ n : Fin 50, centredStar (densSupG (n.val + 4900)) (centF (n.val + 4900)) = true := by decide
private theorem cl_w98 : ∀ n : Fin 50, centF (n.val + 4900) < 23 := by decide
private theorem bd_w98 : ∀ n : Fin 50, densSupG (n.val + 4900) < 2 ^ 1771 := by decide
private theorem cs_w99 : ∀ n : Fin 50, centredStar (densSupG (n.val + 4950)) (centF (n.val + 4950)) = true := by decide
private theorem cl_w99 : ∀ n : Fin 50, centF (n.val + 4950) < 23 := by decide
private theorem bd_w99 : ∀ n : Fin 50, densSupG (n.val + 4950) < 2 ^ 1771 := by decide

theorem centredStar_range : ∀ n, 0 ≤ n → n < 5000 → centredStar (densSupG n) (centF n) = true := by
  intro n hlo hhi
  by_cases h0 : n < 50
  · have hr : n - 0 < 50 := by omega
    have heq : n = (n - 0) + 0 := by omega
    rw [heq]
    exact cs_w0 ⟨n - 0, hr⟩
  ·
    by_cases h1 : n < 100
    · have hr : n - 50 < 50 := by omega
      have heq : n = (n - 50) + 50 := by omega
      rw [heq]
      exact cs_w1 ⟨n - 50, hr⟩
    ·
      by_cases h2 : n < 150
      · have hr : n - 100 < 50 := by omega
        have heq : n = (n - 100) + 100 := by omega
        rw [heq]
        exact cs_w2 ⟨n - 100, hr⟩
      ·
        by_cases h3 : n < 200
        · have hr : n - 150 < 50 := by omega
          have heq : n = (n - 150) + 150 := by omega
          rw [heq]
          exact cs_w3 ⟨n - 150, hr⟩
        ·
          by_cases h4 : n < 250
          · have hr : n - 200 < 50 := by omega
            have heq : n = (n - 200) + 200 := by omega
            rw [heq]
            exact cs_w4 ⟨n - 200, hr⟩
          ·
            by_cases h5 : n < 300
            · have hr : n - 250 < 50 := by omega
              have heq : n = (n - 250) + 250 := by omega
              rw [heq]
              exact cs_w5 ⟨n - 250, hr⟩
            ·
              by_cases h6 : n < 350
              · have hr : n - 300 < 50 := by omega
                have heq : n = (n - 300) + 300 := by omega
                rw [heq]
                exact cs_w6 ⟨n - 300, hr⟩
              ·
                by_cases h7 : n < 400
                · have hr : n - 350 < 50 := by omega
                  have heq : n = (n - 350) + 350 := by omega
                  rw [heq]
                  exact cs_w7 ⟨n - 350, hr⟩
                ·
                  by_cases h8 : n < 450
                  · have hr : n - 400 < 50 := by omega
                    have heq : n = (n - 400) + 400 := by omega
                    rw [heq]
                    exact cs_w8 ⟨n - 400, hr⟩
                  ·
                    by_cases h9 : n < 500
                    · have hr : n - 450 < 50 := by omega
                      have heq : n = (n - 450) + 450 := by omega
                      rw [heq]
                      exact cs_w9 ⟨n - 450, hr⟩
                    ·
                      by_cases h10 : n < 550
                      · have hr : n - 500 < 50 := by omega
                        have heq : n = (n - 500) + 500 := by omega
                        rw [heq]
                        exact cs_w10 ⟨n - 500, hr⟩
                      ·
                        by_cases h11 : n < 600
                        · have hr : n - 550 < 50 := by omega
                          have heq : n = (n - 550) + 550 := by omega
                          rw [heq]
                          exact cs_w11 ⟨n - 550, hr⟩
                        ·
                          by_cases h12 : n < 650
                          · have hr : n - 600 < 50 := by omega
                            have heq : n = (n - 600) + 600 := by omega
                            rw [heq]
                            exact cs_w12 ⟨n - 600, hr⟩
                          ·
                            by_cases h13 : n < 700
                            · have hr : n - 650 < 50 := by omega
                              have heq : n = (n - 650) + 650 := by omega
                              rw [heq]
                              exact cs_w13 ⟨n - 650, hr⟩
                            ·
                              by_cases h14 : n < 750
                              · have hr : n - 700 < 50 := by omega
                                have heq : n = (n - 700) + 700 := by omega
                                rw [heq]
                                exact cs_w14 ⟨n - 700, hr⟩
                              ·
                                by_cases h15 : n < 800
                                · have hr : n - 750 < 50 := by omega
                                  have heq : n = (n - 750) + 750 := by omega
                                  rw [heq]
                                  exact cs_w15 ⟨n - 750, hr⟩
                                ·
                                  by_cases h16 : n < 850
                                  · have hr : n - 800 < 50 := by omega
                                    have heq : n = (n - 800) + 800 := by omega
                                    rw [heq]
                                    exact cs_w16 ⟨n - 800, hr⟩
                                  ·
                                    by_cases h17 : n < 900
                                    · have hr : n - 850 < 50 := by omega
                                      have heq : n = (n - 850) + 850 := by omega
                                      rw [heq]
                                      exact cs_w17 ⟨n - 850, hr⟩
                                    ·
                                      by_cases h18 : n < 950
                                      · have hr : n - 900 < 50 := by omega
                                        have heq : n = (n - 900) + 900 := by omega
                                        rw [heq]
                                        exact cs_w18 ⟨n - 900, hr⟩
                                      ·
                                        by_cases h19 : n < 1000
                                        · have hr : n - 950 < 50 := by omega
                                          have heq : n = (n - 950) + 950 := by omega
                                          rw [heq]
                                          exact cs_w19 ⟨n - 950, hr⟩
                                        ·
                                          by_cases h20 : n < 1050
                                          · have hr : n - 1000 < 50 := by omega
                                            have heq : n = (n - 1000) + 1000 := by omega
                                            rw [heq]
                                            exact cs_w20 ⟨n - 1000, hr⟩
                                          ·
                                            by_cases h21 : n < 1100
                                            · have hr : n - 1050 < 50 := by omega
                                              have heq : n = (n - 1050) + 1050 := by omega
                                              rw [heq]
                                              exact cs_w21 ⟨n - 1050, hr⟩
                                            ·
                                              by_cases h22 : n < 1150
                                              · have hr : n - 1100 < 50 := by omega
                                                have heq : n = (n - 1100) + 1100 := by omega
                                                rw [heq]
                                                exact cs_w22 ⟨n - 1100, hr⟩
                                              ·
                                                by_cases h23 : n < 1200
                                                · have hr : n - 1150 < 50 := by omega
                                                  have heq : n = (n - 1150) + 1150 := by omega
                                                  rw [heq]
                                                  exact cs_w23 ⟨n - 1150, hr⟩
                                                ·
                                                  by_cases h24 : n < 1250
                                                  · have hr : n - 1200 < 50 := by omega
                                                    have heq : n = (n - 1200) + 1200 := by omega
                                                    rw [heq]
                                                    exact cs_w24 ⟨n - 1200, hr⟩
                                                  ·
                                                    by_cases h25 : n < 1300
                                                    · have hr : n - 1250 < 50 := by omega
                                                      have heq : n = (n - 1250) + 1250 := by omega
                                                      rw [heq]
                                                      exact cs_w25 ⟨n - 1250, hr⟩
                                                    ·
                                                      by_cases h26 : n < 1350
                                                      · have hr : n - 1300 < 50 := by omega
                                                        have heq : n = (n - 1300) + 1300 := by omega
                                                        rw [heq]
                                                        exact cs_w26 ⟨n - 1300, hr⟩
                                                      ·
                                                        by_cases h27 : n < 1400
                                                        · have hr : n - 1350 < 50 := by omega
                                                          have heq : n = (n - 1350) + 1350 := by omega
                                                          rw [heq]
                                                          exact cs_w27 ⟨n - 1350, hr⟩
                                                        ·
                                                          by_cases h28 : n < 1450
                                                          · have hr : n - 1400 < 50 := by omega
                                                            have heq : n = (n - 1400) + 1400 := by omega
                                                            rw [heq]
                                                            exact cs_w28 ⟨n - 1400, hr⟩
                                                          ·
                                                            by_cases h29 : n < 1500
                                                            · have hr : n - 1450 < 50 := by omega
                                                              have heq : n = (n - 1450) + 1450 := by omega
                                                              rw [heq]
                                                              exact cs_w29 ⟨n - 1450, hr⟩
                                                            ·
                                                              by_cases h30 : n < 1550
                                                              · have hr : n - 1500 < 50 := by omega
                                                                have heq : n = (n - 1500) + 1500 := by omega
                                                                rw [heq]
                                                                exact cs_w30 ⟨n - 1500, hr⟩
                                                              ·
                                                                by_cases h31 : n < 1600
                                                                · have hr : n - 1550 < 50 := by omega
                                                                  have heq : n = (n - 1550) + 1550 := by omega
                                                                  rw [heq]
                                                                  exact cs_w31 ⟨n - 1550, hr⟩
                                                                ·
                                                                  by_cases h32 : n < 1650
                                                                  · have hr : n - 1600 < 50 := by omega
                                                                    have heq : n = (n - 1600) + 1600 := by omega
                                                                    rw [heq]
                                                                    exact cs_w32 ⟨n - 1600, hr⟩
                                                                  ·
                                                                    by_cases h33 : n < 1700
                                                                    · have hr : n - 1650 < 50 := by omega
                                                                      have heq : n = (n - 1650) + 1650 := by omega
                                                                      rw [heq]
                                                                      exact cs_w33 ⟨n - 1650, hr⟩
                                                                    ·
                                                                      by_cases h34 : n < 1750
                                                                      · have hr : n - 1700 < 50 := by omega
                                                                        have heq : n = (n - 1700) + 1700 := by omega
                                                                        rw [heq]
                                                                        exact cs_w34 ⟨n - 1700, hr⟩
                                                                      ·
                                                                        by_cases h35 : n < 1800
                                                                        · have hr : n - 1750 < 50 := by omega
                                                                          have heq : n = (n - 1750) + 1750 := by omega
                                                                          rw [heq]
                                                                          exact cs_w35 ⟨n - 1750, hr⟩
                                                                        ·
                                                                          by_cases h36 : n < 1850
                                                                          · have hr : n - 1800 < 50 := by omega
                                                                            have heq : n = (n - 1800) + 1800 := by omega
                                                                            rw [heq]
                                                                            exact cs_w36 ⟨n - 1800, hr⟩
                                                                          ·
                                                                            by_cases h37 : n < 1900
                                                                            · have hr : n - 1850 < 50 := by omega
                                                                              have heq : n = (n - 1850) + 1850 := by omega
                                                                              rw [heq]
                                                                              exact cs_w37 ⟨n - 1850, hr⟩
                                                                            ·
                                                                              by_cases h38 : n < 1950
                                                                              · have hr : n - 1900 < 50 := by omega
                                                                                have heq : n = (n - 1900) + 1900 := by omega
                                                                                rw [heq]
                                                                                exact cs_w38 ⟨n - 1900, hr⟩
                                                                              ·
                                                                                by_cases h39 : n < 2000
                                                                                · have hr : n - 1950 < 50 := by omega
                                                                                  have heq : n = (n - 1950) + 1950 := by omega
                                                                                  rw [heq]
                                                                                  exact cs_w39 ⟨n - 1950, hr⟩
                                                                                ·
                                                                                  by_cases h40 : n < 2050
                                                                                  · have hr : n - 2000 < 50 := by omega
                                                                                    have heq : n = (n - 2000) + 2000 := by omega
                                                                                    rw [heq]
                                                                                    exact cs_w40 ⟨n - 2000, hr⟩
                                                                                  ·
                                                                                    by_cases h41 : n < 2100
                                                                                    · have hr : n - 2050 < 50 := by omega
                                                                                      have heq : n = (n - 2050) + 2050 := by omega
                                                                                      rw [heq]
                                                                                      exact cs_w41 ⟨n - 2050, hr⟩
                                                                                    ·
                                                                                      by_cases h42 : n < 2150
                                                                                      · have hr : n - 2100 < 50 := by omega
                                                                                        have heq : n = (n - 2100) + 2100 := by omega
                                                                                        rw [heq]
                                                                                        exact cs_w42 ⟨n - 2100, hr⟩
                                                                                      ·
                                                                                        by_cases h43 : n < 2200
                                                                                        · have hr : n - 2150 < 50 := by omega
                                                                                          have heq : n = (n - 2150) + 2150 := by omega
                                                                                          rw [heq]
                                                                                          exact cs_w43 ⟨n - 2150, hr⟩
                                                                                        ·
                                                                                          by_cases h44 : n < 2250
                                                                                          · have hr : n - 2200 < 50 := by omega
                                                                                            have heq : n = (n - 2200) + 2200 := by omega
                                                                                            rw [heq]
                                                                                            exact cs_w44 ⟨n - 2200, hr⟩
                                                                                          ·
                                                                                            by_cases h45 : n < 2300
                                                                                            · have hr : n - 2250 < 50 := by omega
                                                                                              have heq : n = (n - 2250) + 2250 := by omega
                                                                                              rw [heq]
                                                                                              exact cs_w45 ⟨n - 2250, hr⟩
                                                                                            ·
                                                                                              by_cases h46 : n < 2350
                                                                                              · have hr : n - 2300 < 50 := by omega
                                                                                                have heq : n = (n - 2300) + 2300 := by omega
                                                                                                rw [heq]
                                                                                                exact cs_w46 ⟨n - 2300, hr⟩
                                                                                              ·
                                                                                                by_cases h47 : n < 2400
                                                                                                · have hr : n - 2350 < 50 := by omega
                                                                                                  have heq : n = (n - 2350) + 2350 := by omega
                                                                                                  rw [heq]
                                                                                                  exact cs_w47 ⟨n - 2350, hr⟩
                                                                                                ·
                                                                                                  by_cases h48 : n < 2450
                                                                                                  · have hr : n - 2400 < 50 := by omega
                                                                                                    have heq : n = (n - 2400) + 2400 := by omega
                                                                                                    rw [heq]
                                                                                                    exact cs_w48 ⟨n - 2400, hr⟩
                                                                                                  ·
                                                                                                    by_cases h49 : n < 2500
                                                                                                    · have hr : n - 2450 < 50 := by omega
                                                                                                      have heq : n = (n - 2450) + 2450 := by omega
                                                                                                      rw [heq]
                                                                                                      exact cs_w49 ⟨n - 2450, hr⟩
                                                                                                    ·
                                                                                                      by_cases h50 : n < 2550
                                                                                                      · have hr : n - 2500 < 50 := by omega
                                                                                                        have heq : n = (n - 2500) + 2500 := by omega
                                                                                                        rw [heq]
                                                                                                        exact cs_w50 ⟨n - 2500, hr⟩
                                                                                                      ·
                                                                                                        by_cases h51 : n < 2600
                                                                                                        · have hr : n - 2550 < 50 := by omega
                                                                                                          have heq : n = (n - 2550) + 2550 := by omega
                                                                                                          rw [heq]
                                                                                                          exact cs_w51 ⟨n - 2550, hr⟩
                                                                                                        ·
                                                                                                          by_cases h52 : n < 2650
                                                                                                          · have hr : n - 2600 < 50 := by omega
                                                                                                            have heq : n = (n - 2600) + 2600 := by omega
                                                                                                            rw [heq]
                                                                                                            exact cs_w52 ⟨n - 2600, hr⟩
                                                                                                          ·
                                                                                                            by_cases h53 : n < 2700
                                                                                                            · have hr : n - 2650 < 50 := by omega
                                                                                                              have heq : n = (n - 2650) + 2650 := by omega
                                                                                                              rw [heq]
                                                                                                              exact cs_w53 ⟨n - 2650, hr⟩
                                                                                                            ·
                                                                                                              by_cases h54 : n < 2750
                                                                                                              · have hr : n - 2700 < 50 := by omega
                                                                                                                have heq : n = (n - 2700) + 2700 := by omega
                                                                                                                rw [heq]
                                                                                                                exact cs_w54 ⟨n - 2700, hr⟩
                                                                                                              ·
                                                                                                                by_cases h55 : n < 2800
                                                                                                                · have hr : n - 2750 < 50 := by omega
                                                                                                                  have heq : n = (n - 2750) + 2750 := by omega
                                                                                                                  rw [heq]
                                                                                                                  exact cs_w55 ⟨n - 2750, hr⟩
                                                                                                                ·
                                                                                                                  by_cases h56 : n < 2850
                                                                                                                  · have hr : n - 2800 < 50 := by omega
                                                                                                                    have heq : n = (n - 2800) + 2800 := by omega
                                                                                                                    rw [heq]
                                                                                                                    exact cs_w56 ⟨n - 2800, hr⟩
                                                                                                                  ·
                                                                                                                    by_cases h57 : n < 2900
                                                                                                                    · have hr : n - 2850 < 50 := by omega
                                                                                                                      have heq : n = (n - 2850) + 2850 := by omega
                                                                                                                      rw [heq]
                                                                                                                      exact cs_w57 ⟨n - 2850, hr⟩
                                                                                                                    ·
                                                                                                                      by_cases h58 : n < 2950
                                                                                                                      · have hr : n - 2900 < 50 := by omega
                                                                                                                        have heq : n = (n - 2900) + 2900 := by omega
                                                                                                                        rw [heq]
                                                                                                                        exact cs_w58 ⟨n - 2900, hr⟩
                                                                                                                      ·
                                                                                                                        by_cases h59 : n < 3000
                                                                                                                        · have hr : n - 2950 < 50 := by omega
                                                                                                                          have heq : n = (n - 2950) + 2950 := by omega
                                                                                                                          rw [heq]
                                                                                                                          exact cs_w59 ⟨n - 2950, hr⟩
                                                                                                                        ·
                                                                                                                          by_cases h60 : n < 3050
                                                                                                                          · have hr : n - 3000 < 50 := by omega
                                                                                                                            have heq : n = (n - 3000) + 3000 := by omega
                                                                                                                            rw [heq]
                                                                                                                            exact cs_w60 ⟨n - 3000, hr⟩
                                                                                                                          ·
                                                                                                                            by_cases h61 : n < 3100
                                                                                                                            · have hr : n - 3050 < 50 := by omega
                                                                                                                              have heq : n = (n - 3050) + 3050 := by omega
                                                                                                                              rw [heq]
                                                                                                                              exact cs_w61 ⟨n - 3050, hr⟩
                                                                                                                            ·
                                                                                                                              by_cases h62 : n < 3150
                                                                                                                              · have hr : n - 3100 < 50 := by omega
                                                                                                                                have heq : n = (n - 3100) + 3100 := by omega
                                                                                                                                rw [heq]
                                                                                                                                exact cs_w62 ⟨n - 3100, hr⟩
                                                                                                                              ·
                                                                                                                                by_cases h63 : n < 3200
                                                                                                                                · have hr : n - 3150 < 50 := by omega
                                                                                                                                  have heq : n = (n - 3150) + 3150 := by omega
                                                                                                                                  rw [heq]
                                                                                                                                  exact cs_w63 ⟨n - 3150, hr⟩
                                                                                                                                ·
                                                                                                                                  by_cases h64 : n < 3250
                                                                                                                                  · have hr : n - 3200 < 50 := by omega
                                                                                                                                    have heq : n = (n - 3200) + 3200 := by omega
                                                                                                                                    rw [heq]
                                                                                                                                    exact cs_w64 ⟨n - 3200, hr⟩
                                                                                                                                  ·
                                                                                                                                    by_cases h65 : n < 3300
                                                                                                                                    · have hr : n - 3250 < 50 := by omega
                                                                                                                                      have heq : n = (n - 3250) + 3250 := by omega
                                                                                                                                      rw [heq]
                                                                                                                                      exact cs_w65 ⟨n - 3250, hr⟩
                                                                                                                                    ·
                                                                                                                                      by_cases h66 : n < 3350
                                                                                                                                      · have hr : n - 3300 < 50 := by omega
                                                                                                                                        have heq : n = (n - 3300) + 3300 := by omega
                                                                                                                                        rw [heq]
                                                                                                                                        exact cs_w66 ⟨n - 3300, hr⟩
                                                                                                                                      ·
                                                                                                                                        by_cases h67 : n < 3400
                                                                                                                                        · have hr : n - 3350 < 50 := by omega
                                                                                                                                          have heq : n = (n - 3350) + 3350 := by omega
                                                                                                                                          rw [heq]
                                                                                                                                          exact cs_w67 ⟨n - 3350, hr⟩
                                                                                                                                        ·
                                                                                                                                          by_cases h68 : n < 3450
                                                                                                                                          · have hr : n - 3400 < 50 := by omega
                                                                                                                                            have heq : n = (n - 3400) + 3400 := by omega
                                                                                                                                            rw [heq]
                                                                                                                                            exact cs_w68 ⟨n - 3400, hr⟩
                                                                                                                                          ·
                                                                                                                                            by_cases h69 : n < 3500
                                                                                                                                            · have hr : n - 3450 < 50 := by omega
                                                                                                                                              have heq : n = (n - 3450) + 3450 := by omega
                                                                                                                                              rw [heq]
                                                                                                                                              exact cs_w69 ⟨n - 3450, hr⟩
                                                                                                                                            ·
                                                                                                                                              by_cases h70 : n < 3550
                                                                                                                                              · have hr : n - 3500 < 50 := by omega
                                                                                                                                                have heq : n = (n - 3500) + 3500 := by omega
                                                                                                                                                rw [heq]
                                                                                                                                                exact cs_w70 ⟨n - 3500, hr⟩
                                                                                                                                              ·
                                                                                                                                                by_cases h71 : n < 3600
                                                                                                                                                · have hr : n - 3550 < 50 := by omega
                                                                                                                                                  have heq : n = (n - 3550) + 3550 := by omega
                                                                                                                                                  rw [heq]
                                                                                                                                                  exact cs_w71 ⟨n - 3550, hr⟩
                                                                                                                                                ·
                                                                                                                                                  by_cases h72 : n < 3650
                                                                                                                                                  · have hr : n - 3600 < 50 := by omega
                                                                                                                                                    have heq : n = (n - 3600) + 3600 := by omega
                                                                                                                                                    rw [heq]
                                                                                                                                                    exact cs_w72 ⟨n - 3600, hr⟩
                                                                                                                                                  ·
                                                                                                                                                    by_cases h73 : n < 3700
                                                                                                                                                    · have hr : n - 3650 < 50 := by omega
                                                                                                                                                      have heq : n = (n - 3650) + 3650 := by omega
                                                                                                                                                      rw [heq]
                                                                                                                                                      exact cs_w73 ⟨n - 3650, hr⟩
                                                                                                                                                    ·
                                                                                                                                                      by_cases h74 : n < 3750
                                                                                                                                                      · have hr : n - 3700 < 50 := by omega
                                                                                                                                                        have heq : n = (n - 3700) + 3700 := by omega
                                                                                                                                                        rw [heq]
                                                                                                                                                        exact cs_w74 ⟨n - 3700, hr⟩
                                                                                                                                                      ·
                                                                                                                                                        by_cases h75 : n < 3800
                                                                                                                                                        · have hr : n - 3750 < 50 := by omega
                                                                                                                                                          have heq : n = (n - 3750) + 3750 := by omega
                                                                                                                                                          rw [heq]
                                                                                                                                                          exact cs_w75 ⟨n - 3750, hr⟩
                                                                                                                                                        ·
                                                                                                                                                          by_cases h76 : n < 3850
                                                                                                                                                          · have hr : n - 3800 < 50 := by omega
                                                                                                                                                            have heq : n = (n - 3800) + 3800 := by omega
                                                                                                                                                            rw [heq]
                                                                                                                                                            exact cs_w76 ⟨n - 3800, hr⟩
                                                                                                                                                          ·
                                                                                                                                                            by_cases h77 : n < 3900
                                                                                                                                                            · have hr : n - 3850 < 50 := by omega
                                                                                                                                                              have heq : n = (n - 3850) + 3850 := by omega
                                                                                                                                                              rw [heq]
                                                                                                                                                              exact cs_w77 ⟨n - 3850, hr⟩
                                                                                                                                                            ·
                                                                                                                                                              by_cases h78 : n < 3950
                                                                                                                                                              · have hr : n - 3900 < 50 := by omega
                                                                                                                                                                have heq : n = (n - 3900) + 3900 := by omega
                                                                                                                                                                rw [heq]
                                                                                                                                                                exact cs_w78 ⟨n - 3900, hr⟩
                                                                                                                                                              ·
                                                                                                                                                                by_cases h79 : n < 4000
                                                                                                                                                                · have hr : n - 3950 < 50 := by omega
                                                                                                                                                                  have heq : n = (n - 3950) + 3950 := by omega
                                                                                                                                                                  rw [heq]
                                                                                                                                                                  exact cs_w79 ⟨n - 3950, hr⟩
                                                                                                                                                                ·
                                                                                                                                                                  by_cases h80 : n < 4050
                                                                                                                                                                  · have hr : n - 4000 < 50 := by omega
                                                                                                                                                                    have heq : n = (n - 4000) + 4000 := by omega
                                                                                                                                                                    rw [heq]
                                                                                                                                                                    exact cs_w80 ⟨n - 4000, hr⟩
                                                                                                                                                                  ·
                                                                                                                                                                    by_cases h81 : n < 4100
                                                                                                                                                                    · have hr : n - 4050 < 50 := by omega
                                                                                                                                                                      have heq : n = (n - 4050) + 4050 := by omega
                                                                                                                                                                      rw [heq]
                                                                                                                                                                      exact cs_w81 ⟨n - 4050, hr⟩
                                                                                                                                                                    ·
                                                                                                                                                                      by_cases h82 : n < 4150
                                                                                                                                                                      · have hr : n - 4100 < 50 := by omega
                                                                                                                                                                        have heq : n = (n - 4100) + 4100 := by omega
                                                                                                                                                                        rw [heq]
                                                                                                                                                                        exact cs_w82 ⟨n - 4100, hr⟩
                                                                                                                                                                      ·
                                                                                                                                                                        by_cases h83 : n < 4200
                                                                                                                                                                        · have hr : n - 4150 < 50 := by omega
                                                                                                                                                                          have heq : n = (n - 4150) + 4150 := by omega
                                                                                                                                                                          rw [heq]
                                                                                                                                                                          exact cs_w83 ⟨n - 4150, hr⟩
                                                                                                                                                                        ·
                                                                                                                                                                          by_cases h84 : n < 4250
                                                                                                                                                                          · have hr : n - 4200 < 50 := by omega
                                                                                                                                                                            have heq : n = (n - 4200) + 4200 := by omega
                                                                                                                                                                            rw [heq]
                                                                                                                                                                            exact cs_w84 ⟨n - 4200, hr⟩
                                                                                                                                                                          ·
                                                                                                                                                                            by_cases h85 : n < 4300
                                                                                                                                                                            · have hr : n - 4250 < 50 := by omega
                                                                                                                                                                              have heq : n = (n - 4250) + 4250 := by omega
                                                                                                                                                                              rw [heq]
                                                                                                                                                                              exact cs_w85 ⟨n - 4250, hr⟩
                                                                                                                                                                            ·
                                                                                                                                                                              by_cases h86 : n < 4350
                                                                                                                                                                              · have hr : n - 4300 < 50 := by omega
                                                                                                                                                                                have heq : n = (n - 4300) + 4300 := by omega
                                                                                                                                                                                rw [heq]
                                                                                                                                                                                exact cs_w86 ⟨n - 4300, hr⟩
                                                                                                                                                                              ·
                                                                                                                                                                                by_cases h87 : n < 4400
                                                                                                                                                                                · have hr : n - 4350 < 50 := by omega
                                                                                                                                                                                  have heq : n = (n - 4350) + 4350 := by omega
                                                                                                                                                                                  rw [heq]
                                                                                                                                                                                  exact cs_w87 ⟨n - 4350, hr⟩
                                                                                                                                                                                ·
                                                                                                                                                                                  by_cases h88 : n < 4450
                                                                                                                                                                                  · have hr : n - 4400 < 50 := by omega
                                                                                                                                                                                    have heq : n = (n - 4400) + 4400 := by omega
                                                                                                                                                                                    rw [heq]
                                                                                                                                                                                    exact cs_w88 ⟨n - 4400, hr⟩
                                                                                                                                                                                  ·
                                                                                                                                                                                    by_cases h89 : n < 4500
                                                                                                                                                                                    · have hr : n - 4450 < 50 := by omega
                                                                                                                                                                                      have heq : n = (n - 4450) + 4450 := by omega
                                                                                                                                                                                      rw [heq]
                                                                                                                                                                                      exact cs_w89 ⟨n - 4450, hr⟩
                                                                                                                                                                                    ·
                                                                                                                                                                                      by_cases h90 : n < 4550
                                                                                                                                                                                      · have hr : n - 4500 < 50 := by omega
                                                                                                                                                                                        have heq : n = (n - 4500) + 4500 := by omega
                                                                                                                                                                                        rw [heq]
                                                                                                                                                                                        exact cs_w90 ⟨n - 4500, hr⟩
                                                                                                                                                                                      ·
                                                                                                                                                                                        by_cases h91 : n < 4600
                                                                                                                                                                                        · have hr : n - 4550 < 50 := by omega
                                                                                                                                                                                          have heq : n = (n - 4550) + 4550 := by omega
                                                                                                                                                                                          rw [heq]
                                                                                                                                                                                          exact cs_w91 ⟨n - 4550, hr⟩
                                                                                                                                                                                        ·
                                                                                                                                                                                          by_cases h92 : n < 4650
                                                                                                                                                                                          · have hr : n - 4600 < 50 := by omega
                                                                                                                                                                                            have heq : n = (n - 4600) + 4600 := by omega
                                                                                                                                                                                            rw [heq]
                                                                                                                                                                                            exact cs_w92 ⟨n - 4600, hr⟩
                                                                                                                                                                                          ·
                                                                                                                                                                                            by_cases h93 : n < 4700
                                                                                                                                                                                            · have hr : n - 4650 < 50 := by omega
                                                                                                                                                                                              have heq : n = (n - 4650) + 4650 := by omega
                                                                                                                                                                                              rw [heq]
                                                                                                                                                                                              exact cs_w93 ⟨n - 4650, hr⟩
                                                                                                                                                                                            ·
                                                                                                                                                                                              by_cases h94 : n < 4750
                                                                                                                                                                                              · have hr : n - 4700 < 50 := by omega
                                                                                                                                                                                                have heq : n = (n - 4700) + 4700 := by omega
                                                                                                                                                                                                rw [heq]
                                                                                                                                                                                                exact cs_w94 ⟨n - 4700, hr⟩
                                                                                                                                                                                              ·
                                                                                                                                                                                                by_cases h95 : n < 4800
                                                                                                                                                                                                · have hr : n - 4750 < 50 := by omega
                                                                                                                                                                                                  have heq : n = (n - 4750) + 4750 := by omega
                                                                                                                                                                                                  rw [heq]
                                                                                                                                                                                                  exact cs_w95 ⟨n - 4750, hr⟩
                                                                                                                                                                                                ·
                                                                                                                                                                                                  by_cases h96 : n < 4850
                                                                                                                                                                                                  · have hr : n - 4800 < 50 := by omega
                                                                                                                                                                                                    have heq : n = (n - 4800) + 4800 := by omega
                                                                                                                                                                                                    rw [heq]
                                                                                                                                                                                                    exact cs_w96 ⟨n - 4800, hr⟩
                                                                                                                                                                                                  ·
                                                                                                                                                                                                    by_cases h97 : n < 4900
                                                                                                                                                                                                    · have hr : n - 4850 < 50 := by omega
                                                                                                                                                                                                      have heq : n = (n - 4850) + 4850 := by omega
                                                                                                                                                                                                      rw [heq]
                                                                                                                                                                                                      exact cs_w97 ⟨n - 4850, hr⟩
                                                                                                                                                                                                    ·
                                                                                                                                                                                                      by_cases h98 : n < 4950
                                                                                                                                                                                                      · have hr : n - 4900 < 50 := by omega
                                                                                                                                                                                                        have heq : n = (n - 4900) + 4900 := by omega
                                                                                                                                                                                                        rw [heq]
                                                                                                                                                                                                        exact cs_w98 ⟨n - 4900, hr⟩
                                                                                                                                                                                                      ·
                                                                                                                                                                                                        have hr : n - 4950 < 50 := by omega
                                                                                                                                                                                                        have heq : n = (n - 4950) + 4950 := by omega
                                                                                                                                                                                                        rw [heq]
                                                                                                                                                                                                        exact cs_w99 ⟨n - 4950, hr⟩

theorem centF_lt_range : ∀ n, 0 ≤ n → n < 5000 → centF n < 23 := by
  intro n hlo hhi
  by_cases h0 : n < 50
  · have hr : n - 0 < 50 := by omega
    have heq : n = (n - 0) + 0 := by omega
    rw [heq]
    exact cl_w0 ⟨n - 0, hr⟩
  ·
    by_cases h1 : n < 100
    · have hr : n - 50 < 50 := by omega
      have heq : n = (n - 50) + 50 := by omega
      rw [heq]
      exact cl_w1 ⟨n - 50, hr⟩
    ·
      by_cases h2 : n < 150
      · have hr : n - 100 < 50 := by omega
        have heq : n = (n - 100) + 100 := by omega
        rw [heq]
        exact cl_w2 ⟨n - 100, hr⟩
      ·
        by_cases h3 : n < 200
        · have hr : n - 150 < 50 := by omega
          have heq : n = (n - 150) + 150 := by omega
          rw [heq]
          exact cl_w3 ⟨n - 150, hr⟩
        ·
          by_cases h4 : n < 250
          · have hr : n - 200 < 50 := by omega
            have heq : n = (n - 200) + 200 := by omega
            rw [heq]
            exact cl_w4 ⟨n - 200, hr⟩
          ·
            by_cases h5 : n < 300
            · have hr : n - 250 < 50 := by omega
              have heq : n = (n - 250) + 250 := by omega
              rw [heq]
              exact cl_w5 ⟨n - 250, hr⟩
            ·
              by_cases h6 : n < 350
              · have hr : n - 300 < 50 := by omega
                have heq : n = (n - 300) + 300 := by omega
                rw [heq]
                exact cl_w6 ⟨n - 300, hr⟩
              ·
                by_cases h7 : n < 400
                · have hr : n - 350 < 50 := by omega
                  have heq : n = (n - 350) + 350 := by omega
                  rw [heq]
                  exact cl_w7 ⟨n - 350, hr⟩
                ·
                  by_cases h8 : n < 450
                  · have hr : n - 400 < 50 := by omega
                    have heq : n = (n - 400) + 400 := by omega
                    rw [heq]
                    exact cl_w8 ⟨n - 400, hr⟩
                  ·
                    by_cases h9 : n < 500
                    · have hr : n - 450 < 50 := by omega
                      have heq : n = (n - 450) + 450 := by omega
                      rw [heq]
                      exact cl_w9 ⟨n - 450, hr⟩
                    ·
                      by_cases h10 : n < 550
                      · have hr : n - 500 < 50 := by omega
                        have heq : n = (n - 500) + 500 := by omega
                        rw [heq]
                        exact cl_w10 ⟨n - 500, hr⟩
                      ·
                        by_cases h11 : n < 600
                        · have hr : n - 550 < 50 := by omega
                          have heq : n = (n - 550) + 550 := by omega
                          rw [heq]
                          exact cl_w11 ⟨n - 550, hr⟩
                        ·
                          by_cases h12 : n < 650
                          · have hr : n - 600 < 50 := by omega
                            have heq : n = (n - 600) + 600 := by omega
                            rw [heq]
                            exact cl_w12 ⟨n - 600, hr⟩
                          ·
                            by_cases h13 : n < 700
                            · have hr : n - 650 < 50 := by omega
                              have heq : n = (n - 650) + 650 := by omega
                              rw [heq]
                              exact cl_w13 ⟨n - 650, hr⟩
                            ·
                              by_cases h14 : n < 750
                              · have hr : n - 700 < 50 := by omega
                                have heq : n = (n - 700) + 700 := by omega
                                rw [heq]
                                exact cl_w14 ⟨n - 700, hr⟩
                              ·
                                by_cases h15 : n < 800
                                · have hr : n - 750 < 50 := by omega
                                  have heq : n = (n - 750) + 750 := by omega
                                  rw [heq]
                                  exact cl_w15 ⟨n - 750, hr⟩
                                ·
                                  by_cases h16 : n < 850
                                  · have hr : n - 800 < 50 := by omega
                                    have heq : n = (n - 800) + 800 := by omega
                                    rw [heq]
                                    exact cl_w16 ⟨n - 800, hr⟩
                                  ·
                                    by_cases h17 : n < 900
                                    · have hr : n - 850 < 50 := by omega
                                      have heq : n = (n - 850) + 850 := by omega
                                      rw [heq]
                                      exact cl_w17 ⟨n - 850, hr⟩
                                    ·
                                      by_cases h18 : n < 950
                                      · have hr : n - 900 < 50 := by omega
                                        have heq : n = (n - 900) + 900 := by omega
                                        rw [heq]
                                        exact cl_w18 ⟨n - 900, hr⟩
                                      ·
                                        by_cases h19 : n < 1000
                                        · have hr : n - 950 < 50 := by omega
                                          have heq : n = (n - 950) + 950 := by omega
                                          rw [heq]
                                          exact cl_w19 ⟨n - 950, hr⟩
                                        ·
                                          by_cases h20 : n < 1050
                                          · have hr : n - 1000 < 50 := by omega
                                            have heq : n = (n - 1000) + 1000 := by omega
                                            rw [heq]
                                            exact cl_w20 ⟨n - 1000, hr⟩
                                          ·
                                            by_cases h21 : n < 1100
                                            · have hr : n - 1050 < 50 := by omega
                                              have heq : n = (n - 1050) + 1050 := by omega
                                              rw [heq]
                                              exact cl_w21 ⟨n - 1050, hr⟩
                                            ·
                                              by_cases h22 : n < 1150
                                              · have hr : n - 1100 < 50 := by omega
                                                have heq : n = (n - 1100) + 1100 := by omega
                                                rw [heq]
                                                exact cl_w22 ⟨n - 1100, hr⟩
                                              ·
                                                by_cases h23 : n < 1200
                                                · have hr : n - 1150 < 50 := by omega
                                                  have heq : n = (n - 1150) + 1150 := by omega
                                                  rw [heq]
                                                  exact cl_w23 ⟨n - 1150, hr⟩
                                                ·
                                                  by_cases h24 : n < 1250
                                                  · have hr : n - 1200 < 50 := by omega
                                                    have heq : n = (n - 1200) + 1200 := by omega
                                                    rw [heq]
                                                    exact cl_w24 ⟨n - 1200, hr⟩
                                                  ·
                                                    by_cases h25 : n < 1300
                                                    · have hr : n - 1250 < 50 := by omega
                                                      have heq : n = (n - 1250) + 1250 := by omega
                                                      rw [heq]
                                                      exact cl_w25 ⟨n - 1250, hr⟩
                                                    ·
                                                      by_cases h26 : n < 1350
                                                      · have hr : n - 1300 < 50 := by omega
                                                        have heq : n = (n - 1300) + 1300 := by omega
                                                        rw [heq]
                                                        exact cl_w26 ⟨n - 1300, hr⟩
                                                      ·
                                                        by_cases h27 : n < 1400
                                                        · have hr : n - 1350 < 50 := by omega
                                                          have heq : n = (n - 1350) + 1350 := by omega
                                                          rw [heq]
                                                          exact cl_w27 ⟨n - 1350, hr⟩
                                                        ·
                                                          by_cases h28 : n < 1450
                                                          · have hr : n - 1400 < 50 := by omega
                                                            have heq : n = (n - 1400) + 1400 := by omega
                                                            rw [heq]
                                                            exact cl_w28 ⟨n - 1400, hr⟩
                                                          ·
                                                            by_cases h29 : n < 1500
                                                            · have hr : n - 1450 < 50 := by omega
                                                              have heq : n = (n - 1450) + 1450 := by omega
                                                              rw [heq]
                                                              exact cl_w29 ⟨n - 1450, hr⟩
                                                            ·
                                                              by_cases h30 : n < 1550
                                                              · have hr : n - 1500 < 50 := by omega
                                                                have heq : n = (n - 1500) + 1500 := by omega
                                                                rw [heq]
                                                                exact cl_w30 ⟨n - 1500, hr⟩
                                                              ·
                                                                by_cases h31 : n < 1600
                                                                · have hr : n - 1550 < 50 := by omega
                                                                  have heq : n = (n - 1550) + 1550 := by omega
                                                                  rw [heq]
                                                                  exact cl_w31 ⟨n - 1550, hr⟩
                                                                ·
                                                                  by_cases h32 : n < 1650
                                                                  · have hr : n - 1600 < 50 := by omega
                                                                    have heq : n = (n - 1600) + 1600 := by omega
                                                                    rw [heq]
                                                                    exact cl_w32 ⟨n - 1600, hr⟩
                                                                  ·
                                                                    by_cases h33 : n < 1700
                                                                    · have hr : n - 1650 < 50 := by omega
                                                                      have heq : n = (n - 1650) + 1650 := by omega
                                                                      rw [heq]
                                                                      exact cl_w33 ⟨n - 1650, hr⟩
                                                                    ·
                                                                      by_cases h34 : n < 1750
                                                                      · have hr : n - 1700 < 50 := by omega
                                                                        have heq : n = (n - 1700) + 1700 := by omega
                                                                        rw [heq]
                                                                        exact cl_w34 ⟨n - 1700, hr⟩
                                                                      ·
                                                                        by_cases h35 : n < 1800
                                                                        · have hr : n - 1750 < 50 := by omega
                                                                          have heq : n = (n - 1750) + 1750 := by omega
                                                                          rw [heq]
                                                                          exact cl_w35 ⟨n - 1750, hr⟩
                                                                        ·
                                                                          by_cases h36 : n < 1850
                                                                          · have hr : n - 1800 < 50 := by omega
                                                                            have heq : n = (n - 1800) + 1800 := by omega
                                                                            rw [heq]
                                                                            exact cl_w36 ⟨n - 1800, hr⟩
                                                                          ·
                                                                            by_cases h37 : n < 1900
                                                                            · have hr : n - 1850 < 50 := by omega
                                                                              have heq : n = (n - 1850) + 1850 := by omega
                                                                              rw [heq]
                                                                              exact cl_w37 ⟨n - 1850, hr⟩
                                                                            ·
                                                                              by_cases h38 : n < 1950
                                                                              · have hr : n - 1900 < 50 := by omega
                                                                                have heq : n = (n - 1900) + 1900 := by omega
                                                                                rw [heq]
                                                                                exact cl_w38 ⟨n - 1900, hr⟩
                                                                              ·
                                                                                by_cases h39 : n < 2000
                                                                                · have hr : n - 1950 < 50 := by omega
                                                                                  have heq : n = (n - 1950) + 1950 := by omega
                                                                                  rw [heq]
                                                                                  exact cl_w39 ⟨n - 1950, hr⟩
                                                                                ·
                                                                                  by_cases h40 : n < 2050
                                                                                  · have hr : n - 2000 < 50 := by omega
                                                                                    have heq : n = (n - 2000) + 2000 := by omega
                                                                                    rw [heq]
                                                                                    exact cl_w40 ⟨n - 2000, hr⟩
                                                                                  ·
                                                                                    by_cases h41 : n < 2100
                                                                                    · have hr : n - 2050 < 50 := by omega
                                                                                      have heq : n = (n - 2050) + 2050 := by omega
                                                                                      rw [heq]
                                                                                      exact cl_w41 ⟨n - 2050, hr⟩
                                                                                    ·
                                                                                      by_cases h42 : n < 2150
                                                                                      · have hr : n - 2100 < 50 := by omega
                                                                                        have heq : n = (n - 2100) + 2100 := by omega
                                                                                        rw [heq]
                                                                                        exact cl_w42 ⟨n - 2100, hr⟩
                                                                                      ·
                                                                                        by_cases h43 : n < 2200
                                                                                        · have hr : n - 2150 < 50 := by omega
                                                                                          have heq : n = (n - 2150) + 2150 := by omega
                                                                                          rw [heq]
                                                                                          exact cl_w43 ⟨n - 2150, hr⟩
                                                                                        ·
                                                                                          by_cases h44 : n < 2250
                                                                                          · have hr : n - 2200 < 50 := by omega
                                                                                            have heq : n = (n - 2200) + 2200 := by omega
                                                                                            rw [heq]
                                                                                            exact cl_w44 ⟨n - 2200, hr⟩
                                                                                          ·
                                                                                            by_cases h45 : n < 2300
                                                                                            · have hr : n - 2250 < 50 := by omega
                                                                                              have heq : n = (n - 2250) + 2250 := by omega
                                                                                              rw [heq]
                                                                                              exact cl_w45 ⟨n - 2250, hr⟩
                                                                                            ·
                                                                                              by_cases h46 : n < 2350
                                                                                              · have hr : n - 2300 < 50 := by omega
                                                                                                have heq : n = (n - 2300) + 2300 := by omega
                                                                                                rw [heq]
                                                                                                exact cl_w46 ⟨n - 2300, hr⟩
                                                                                              ·
                                                                                                by_cases h47 : n < 2400
                                                                                                · have hr : n - 2350 < 50 := by omega
                                                                                                  have heq : n = (n - 2350) + 2350 := by omega
                                                                                                  rw [heq]
                                                                                                  exact cl_w47 ⟨n - 2350, hr⟩
                                                                                                ·
                                                                                                  by_cases h48 : n < 2450
                                                                                                  · have hr : n - 2400 < 50 := by omega
                                                                                                    have heq : n = (n - 2400) + 2400 := by omega
                                                                                                    rw [heq]
                                                                                                    exact cl_w48 ⟨n - 2400, hr⟩
                                                                                                  ·
                                                                                                    by_cases h49 : n < 2500
                                                                                                    · have hr : n - 2450 < 50 := by omega
                                                                                                      have heq : n = (n - 2450) + 2450 := by omega
                                                                                                      rw [heq]
                                                                                                      exact cl_w49 ⟨n - 2450, hr⟩
                                                                                                    ·
                                                                                                      by_cases h50 : n < 2550
                                                                                                      · have hr : n - 2500 < 50 := by omega
                                                                                                        have heq : n = (n - 2500) + 2500 := by omega
                                                                                                        rw [heq]
                                                                                                        exact cl_w50 ⟨n - 2500, hr⟩
                                                                                                      ·
                                                                                                        by_cases h51 : n < 2600
                                                                                                        · have hr : n - 2550 < 50 := by omega
                                                                                                          have heq : n = (n - 2550) + 2550 := by omega
                                                                                                          rw [heq]
                                                                                                          exact cl_w51 ⟨n - 2550, hr⟩
                                                                                                        ·
                                                                                                          by_cases h52 : n < 2650
                                                                                                          · have hr : n - 2600 < 50 := by omega
                                                                                                            have heq : n = (n - 2600) + 2600 := by omega
                                                                                                            rw [heq]
                                                                                                            exact cl_w52 ⟨n - 2600, hr⟩
                                                                                                          ·
                                                                                                            by_cases h53 : n < 2700
                                                                                                            · have hr : n - 2650 < 50 := by omega
                                                                                                              have heq : n = (n - 2650) + 2650 := by omega
                                                                                                              rw [heq]
                                                                                                              exact cl_w53 ⟨n - 2650, hr⟩
                                                                                                            ·
                                                                                                              by_cases h54 : n < 2750
                                                                                                              · have hr : n - 2700 < 50 := by omega
                                                                                                                have heq : n = (n - 2700) + 2700 := by omega
                                                                                                                rw [heq]
                                                                                                                exact cl_w54 ⟨n - 2700, hr⟩
                                                                                                              ·
                                                                                                                by_cases h55 : n < 2800
                                                                                                                · have hr : n - 2750 < 50 := by omega
                                                                                                                  have heq : n = (n - 2750) + 2750 := by omega
                                                                                                                  rw [heq]
                                                                                                                  exact cl_w55 ⟨n - 2750, hr⟩
                                                                                                                ·
                                                                                                                  by_cases h56 : n < 2850
                                                                                                                  · have hr : n - 2800 < 50 := by omega
                                                                                                                    have heq : n = (n - 2800) + 2800 := by omega
                                                                                                                    rw [heq]
                                                                                                                    exact cl_w56 ⟨n - 2800, hr⟩
                                                                                                                  ·
                                                                                                                    by_cases h57 : n < 2900
                                                                                                                    · have hr : n - 2850 < 50 := by omega
                                                                                                                      have heq : n = (n - 2850) + 2850 := by omega
                                                                                                                      rw [heq]
                                                                                                                      exact cl_w57 ⟨n - 2850, hr⟩
                                                                                                                    ·
                                                                                                                      by_cases h58 : n < 2950
                                                                                                                      · have hr : n - 2900 < 50 := by omega
                                                                                                                        have heq : n = (n - 2900) + 2900 := by omega
                                                                                                                        rw [heq]
                                                                                                                        exact cl_w58 ⟨n - 2900, hr⟩
                                                                                                                      ·
                                                                                                                        by_cases h59 : n < 3000
                                                                                                                        · have hr : n - 2950 < 50 := by omega
                                                                                                                          have heq : n = (n - 2950) + 2950 := by omega
                                                                                                                          rw [heq]
                                                                                                                          exact cl_w59 ⟨n - 2950, hr⟩
                                                                                                                        ·
                                                                                                                          by_cases h60 : n < 3050
                                                                                                                          · have hr : n - 3000 < 50 := by omega
                                                                                                                            have heq : n = (n - 3000) + 3000 := by omega
                                                                                                                            rw [heq]
                                                                                                                            exact cl_w60 ⟨n - 3000, hr⟩
                                                                                                                          ·
                                                                                                                            by_cases h61 : n < 3100
                                                                                                                            · have hr : n - 3050 < 50 := by omega
                                                                                                                              have heq : n = (n - 3050) + 3050 := by omega
                                                                                                                              rw [heq]
                                                                                                                              exact cl_w61 ⟨n - 3050, hr⟩
                                                                                                                            ·
                                                                                                                              by_cases h62 : n < 3150
                                                                                                                              · have hr : n - 3100 < 50 := by omega
                                                                                                                                have heq : n = (n - 3100) + 3100 := by omega
                                                                                                                                rw [heq]
                                                                                                                                exact cl_w62 ⟨n - 3100, hr⟩
                                                                                                                              ·
                                                                                                                                by_cases h63 : n < 3200
                                                                                                                                · have hr : n - 3150 < 50 := by omega
                                                                                                                                  have heq : n = (n - 3150) + 3150 := by omega
                                                                                                                                  rw [heq]
                                                                                                                                  exact cl_w63 ⟨n - 3150, hr⟩
                                                                                                                                ·
                                                                                                                                  by_cases h64 : n < 3250
                                                                                                                                  · have hr : n - 3200 < 50 := by omega
                                                                                                                                    have heq : n = (n - 3200) + 3200 := by omega
                                                                                                                                    rw [heq]
                                                                                                                                    exact cl_w64 ⟨n - 3200, hr⟩
                                                                                                                                  ·
                                                                                                                                    by_cases h65 : n < 3300
                                                                                                                                    · have hr : n - 3250 < 50 := by omega
                                                                                                                                      have heq : n = (n - 3250) + 3250 := by omega
                                                                                                                                      rw [heq]
                                                                                                                                      exact cl_w65 ⟨n - 3250, hr⟩
                                                                                                                                    ·
                                                                                                                                      by_cases h66 : n < 3350
                                                                                                                                      · have hr : n - 3300 < 50 := by omega
                                                                                                                                        have heq : n = (n - 3300) + 3300 := by omega
                                                                                                                                        rw [heq]
                                                                                                                                        exact cl_w66 ⟨n - 3300, hr⟩
                                                                                                                                      ·
                                                                                                                                        by_cases h67 : n < 3400
                                                                                                                                        · have hr : n - 3350 < 50 := by omega
                                                                                                                                          have heq : n = (n - 3350) + 3350 := by omega
                                                                                                                                          rw [heq]
                                                                                                                                          exact cl_w67 ⟨n - 3350, hr⟩
                                                                                                                                        ·
                                                                                                                                          by_cases h68 : n < 3450
                                                                                                                                          · have hr : n - 3400 < 50 := by omega
                                                                                                                                            have heq : n = (n - 3400) + 3400 := by omega
                                                                                                                                            rw [heq]
                                                                                                                                            exact cl_w68 ⟨n - 3400, hr⟩
                                                                                                                                          ·
                                                                                                                                            by_cases h69 : n < 3500
                                                                                                                                            · have hr : n - 3450 < 50 := by omega
                                                                                                                                              have heq : n = (n - 3450) + 3450 := by omega
                                                                                                                                              rw [heq]
                                                                                                                                              exact cl_w69 ⟨n - 3450, hr⟩
                                                                                                                                            ·
                                                                                                                                              by_cases h70 : n < 3550
                                                                                                                                              · have hr : n - 3500 < 50 := by omega
                                                                                                                                                have heq : n = (n - 3500) + 3500 := by omega
                                                                                                                                                rw [heq]
                                                                                                                                                exact cl_w70 ⟨n - 3500, hr⟩
                                                                                                                                              ·
                                                                                                                                                by_cases h71 : n < 3600
                                                                                                                                                · have hr : n - 3550 < 50 := by omega
                                                                                                                                                  have heq : n = (n - 3550) + 3550 := by omega
                                                                                                                                                  rw [heq]
                                                                                                                                                  exact cl_w71 ⟨n - 3550, hr⟩
                                                                                                                                                ·
                                                                                                                                                  by_cases h72 : n < 3650
                                                                                                                                                  · have hr : n - 3600 < 50 := by omega
                                                                                                                                                    have heq : n = (n - 3600) + 3600 := by omega
                                                                                                                                                    rw [heq]
                                                                                                                                                    exact cl_w72 ⟨n - 3600, hr⟩
                                                                                                                                                  ·
                                                                                                                                                    by_cases h73 : n < 3700
                                                                                                                                                    · have hr : n - 3650 < 50 := by omega
                                                                                                                                                      have heq : n = (n - 3650) + 3650 := by omega
                                                                                                                                                      rw [heq]
                                                                                                                                                      exact cl_w73 ⟨n - 3650, hr⟩
                                                                                                                                                    ·
                                                                                                                                                      by_cases h74 : n < 3750
                                                                                                                                                      · have hr : n - 3700 < 50 := by omega
                                                                                                                                                        have heq : n = (n - 3700) + 3700 := by omega
                                                                                                                                                        rw [heq]
                                                                                                                                                        exact cl_w74 ⟨n - 3700, hr⟩
                                                                                                                                                      ·
                                                                                                                                                        by_cases h75 : n < 3800
                                                                                                                                                        · have hr : n - 3750 < 50 := by omega
                                                                                                                                                          have heq : n = (n - 3750) + 3750 := by omega
                                                                                                                                                          rw [heq]
                                                                                                                                                          exact cl_w75 ⟨n - 3750, hr⟩
                                                                                                                                                        ·
                                                                                                                                                          by_cases h76 : n < 3850
                                                                                                                                                          · have hr : n - 3800 < 50 := by omega
                                                                                                                                                            have heq : n = (n - 3800) + 3800 := by omega
                                                                                                                                                            rw [heq]
                                                                                                                                                            exact cl_w76 ⟨n - 3800, hr⟩
                                                                                                                                                          ·
                                                                                                                                                            by_cases h77 : n < 3900
                                                                                                                                                            · have hr : n - 3850 < 50 := by omega
                                                                                                                                                              have heq : n = (n - 3850) + 3850 := by omega
                                                                                                                                                              rw [heq]
                                                                                                                                                              exact cl_w77 ⟨n - 3850, hr⟩
                                                                                                                                                            ·
                                                                                                                                                              by_cases h78 : n < 3950
                                                                                                                                                              · have hr : n - 3900 < 50 := by omega
                                                                                                                                                                have heq : n = (n - 3900) + 3900 := by omega
                                                                                                                                                                rw [heq]
                                                                                                                                                                exact cl_w78 ⟨n - 3900, hr⟩
                                                                                                                                                              ·
                                                                                                                                                                by_cases h79 : n < 4000
                                                                                                                                                                · have hr : n - 3950 < 50 := by omega
                                                                                                                                                                  have heq : n = (n - 3950) + 3950 := by omega
                                                                                                                                                                  rw [heq]
                                                                                                                                                                  exact cl_w79 ⟨n - 3950, hr⟩
                                                                                                                                                                ·
                                                                                                                                                                  by_cases h80 : n < 4050
                                                                                                                                                                  · have hr : n - 4000 < 50 := by omega
                                                                                                                                                                    have heq : n = (n - 4000) + 4000 := by omega
                                                                                                                                                                    rw [heq]
                                                                                                                                                                    exact cl_w80 ⟨n - 4000, hr⟩
                                                                                                                                                                  ·
                                                                                                                                                                    by_cases h81 : n < 4100
                                                                                                                                                                    · have hr : n - 4050 < 50 := by omega
                                                                                                                                                                      have heq : n = (n - 4050) + 4050 := by omega
                                                                                                                                                                      rw [heq]
                                                                                                                                                                      exact cl_w81 ⟨n - 4050, hr⟩
                                                                                                                                                                    ·
                                                                                                                                                                      by_cases h82 : n < 4150
                                                                                                                                                                      · have hr : n - 4100 < 50 := by omega
                                                                                                                                                                        have heq : n = (n - 4100) + 4100 := by omega
                                                                                                                                                                        rw [heq]
                                                                                                                                                                        exact cl_w82 ⟨n - 4100, hr⟩
                                                                                                                                                                      ·
                                                                                                                                                                        by_cases h83 : n < 4200
                                                                                                                                                                        · have hr : n - 4150 < 50 := by omega
                                                                                                                                                                          have heq : n = (n - 4150) + 4150 := by omega
                                                                                                                                                                          rw [heq]
                                                                                                                                                                          exact cl_w83 ⟨n - 4150, hr⟩
                                                                                                                                                                        ·
                                                                                                                                                                          by_cases h84 : n < 4250
                                                                                                                                                                          · have hr : n - 4200 < 50 := by omega
                                                                                                                                                                            have heq : n = (n - 4200) + 4200 := by omega
                                                                                                                                                                            rw [heq]
                                                                                                                                                                            exact cl_w84 ⟨n - 4200, hr⟩
                                                                                                                                                                          ·
                                                                                                                                                                            by_cases h85 : n < 4300
                                                                                                                                                                            · have hr : n - 4250 < 50 := by omega
                                                                                                                                                                              have heq : n = (n - 4250) + 4250 := by omega
                                                                                                                                                                              rw [heq]
                                                                                                                                                                              exact cl_w85 ⟨n - 4250, hr⟩
                                                                                                                                                                            ·
                                                                                                                                                                              by_cases h86 : n < 4350
                                                                                                                                                                              · have hr : n - 4300 < 50 := by omega
                                                                                                                                                                                have heq : n = (n - 4300) + 4300 := by omega
                                                                                                                                                                                rw [heq]
                                                                                                                                                                                exact cl_w86 ⟨n - 4300, hr⟩
                                                                                                                                                                              ·
                                                                                                                                                                                by_cases h87 : n < 4400
                                                                                                                                                                                · have hr : n - 4350 < 50 := by omega
                                                                                                                                                                                  have heq : n = (n - 4350) + 4350 := by omega
                                                                                                                                                                                  rw [heq]
                                                                                                                                                                                  exact cl_w87 ⟨n - 4350, hr⟩
                                                                                                                                                                                ·
                                                                                                                                                                                  by_cases h88 : n < 4450
                                                                                                                                                                                  · have hr : n - 4400 < 50 := by omega
                                                                                                                                                                                    have heq : n = (n - 4400) + 4400 := by omega
                                                                                                                                                                                    rw [heq]
                                                                                                                                                                                    exact cl_w88 ⟨n - 4400, hr⟩
                                                                                                                                                                                  ·
                                                                                                                                                                                    by_cases h89 : n < 4500
                                                                                                                                                                                    · have hr : n - 4450 < 50 := by omega
                                                                                                                                                                                      have heq : n = (n - 4450) + 4450 := by omega
                                                                                                                                                                                      rw [heq]
                                                                                                                                                                                      exact cl_w89 ⟨n - 4450, hr⟩
                                                                                                                                                                                    ·
                                                                                                                                                                                      by_cases h90 : n < 4550
                                                                                                                                                                                      · have hr : n - 4500 < 50 := by omega
                                                                                                                                                                                        have heq : n = (n - 4500) + 4500 := by omega
                                                                                                                                                                                        rw [heq]
                                                                                                                                                                                        exact cl_w90 ⟨n - 4500, hr⟩
                                                                                                                                                                                      ·
                                                                                                                                                                                        by_cases h91 : n < 4600
                                                                                                                                                                                        · have hr : n - 4550 < 50 := by omega
                                                                                                                                                                                          have heq : n = (n - 4550) + 4550 := by omega
                                                                                                                                                                                          rw [heq]
                                                                                                                                                                                          exact cl_w91 ⟨n - 4550, hr⟩
                                                                                                                                                                                        ·
                                                                                                                                                                                          by_cases h92 : n < 4650
                                                                                                                                                                                          · have hr : n - 4600 < 50 := by omega
                                                                                                                                                                                            have heq : n = (n - 4600) + 4600 := by omega
                                                                                                                                                                                            rw [heq]
                                                                                                                                                                                            exact cl_w92 ⟨n - 4600, hr⟩
                                                                                                                                                                                          ·
                                                                                                                                                                                            by_cases h93 : n < 4700
                                                                                                                                                                                            · have hr : n - 4650 < 50 := by omega
                                                                                                                                                                                              have heq : n = (n - 4650) + 4650 := by omega
                                                                                                                                                                                              rw [heq]
                                                                                                                                                                                              exact cl_w93 ⟨n - 4650, hr⟩
                                                                                                                                                                                            ·
                                                                                                                                                                                              by_cases h94 : n < 4750
                                                                                                                                                                                              · have hr : n - 4700 < 50 := by omega
                                                                                                                                                                                                have heq : n = (n - 4700) + 4700 := by omega
                                                                                                                                                                                                rw [heq]
                                                                                                                                                                                                exact cl_w94 ⟨n - 4700, hr⟩
                                                                                                                                                                                              ·
                                                                                                                                                                                                by_cases h95 : n < 4800
                                                                                                                                                                                                · have hr : n - 4750 < 50 := by omega
                                                                                                                                                                                                  have heq : n = (n - 4750) + 4750 := by omega
                                                                                                                                                                                                  rw [heq]
                                                                                                                                                                                                  exact cl_w95 ⟨n - 4750, hr⟩
                                                                                                                                                                                                ·
                                                                                                                                                                                                  by_cases h96 : n < 4850
                                                                                                                                                                                                  · have hr : n - 4800 < 50 := by omega
                                                                                                                                                                                                    have heq : n = (n - 4800) + 4800 := by omega
                                                                                                                                                                                                    rw [heq]
                                                                                                                                                                                                    exact cl_w96 ⟨n - 4800, hr⟩
                                                                                                                                                                                                  ·
                                                                                                                                                                                                    by_cases h97 : n < 4900
                                                                                                                                                                                                    · have hr : n - 4850 < 50 := by omega
                                                                                                                                                                                                      have heq : n = (n - 4850) + 4850 := by omega
                                                                                                                                                                                                      rw [heq]
                                                                                                                                                                                                      exact cl_w97 ⟨n - 4850, hr⟩
                                                                                                                                                                                                    ·
                                                                                                                                                                                                      by_cases h98 : n < 4950
                                                                                                                                                                                                      · have hr : n - 4900 < 50 := by omega
                                                                                                                                                                                                        have heq : n = (n - 4900) + 4900 := by omega
                                                                                                                                                                                                        rw [heq]
                                                                                                                                                                                                        exact cl_w98 ⟨n - 4900, hr⟩
                                                                                                                                                                                                      ·
                                                                                                                                                                                                        have hr : n - 4950 < 50 := by omega
                                                                                                                                                                                                        have heq : n = (n - 4950) + 4950 := by omega
                                                                                                                                                                                                        rw [heq]
                                                                                                                                                                                                        exact cl_w99 ⟨n - 4950, hr⟩

theorem densSupG_lt_range : ∀ n, 0 ≤ n → n < 5000 → densSupG n < 2 ^ 1771 := by
  intro n hlo hhi
  by_cases h0 : n < 50
  · have hr : n - 0 < 50 := by omega
    have heq : n = (n - 0) + 0 := by omega
    rw [heq]
    exact bd_w0 ⟨n - 0, hr⟩
  ·
    by_cases h1 : n < 100
    · have hr : n - 50 < 50 := by omega
      have heq : n = (n - 50) + 50 := by omega
      rw [heq]
      exact bd_w1 ⟨n - 50, hr⟩
    ·
      by_cases h2 : n < 150
      · have hr : n - 100 < 50 := by omega
        have heq : n = (n - 100) + 100 := by omega
        rw [heq]
        exact bd_w2 ⟨n - 100, hr⟩
      ·
        by_cases h3 : n < 200
        · have hr : n - 150 < 50 := by omega
          have heq : n = (n - 150) + 150 := by omega
          rw [heq]
          exact bd_w3 ⟨n - 150, hr⟩
        ·
          by_cases h4 : n < 250
          · have hr : n - 200 < 50 := by omega
            have heq : n = (n - 200) + 200 := by omega
            rw [heq]
            exact bd_w4 ⟨n - 200, hr⟩
          ·
            by_cases h5 : n < 300
            · have hr : n - 250 < 50 := by omega
              have heq : n = (n - 250) + 250 := by omega
              rw [heq]
              exact bd_w5 ⟨n - 250, hr⟩
            ·
              by_cases h6 : n < 350
              · have hr : n - 300 < 50 := by omega
                have heq : n = (n - 300) + 300 := by omega
                rw [heq]
                exact bd_w6 ⟨n - 300, hr⟩
              ·
                by_cases h7 : n < 400
                · have hr : n - 350 < 50 := by omega
                  have heq : n = (n - 350) + 350 := by omega
                  rw [heq]
                  exact bd_w7 ⟨n - 350, hr⟩
                ·
                  by_cases h8 : n < 450
                  · have hr : n - 400 < 50 := by omega
                    have heq : n = (n - 400) + 400 := by omega
                    rw [heq]
                    exact bd_w8 ⟨n - 400, hr⟩
                  ·
                    by_cases h9 : n < 500
                    · have hr : n - 450 < 50 := by omega
                      have heq : n = (n - 450) + 450 := by omega
                      rw [heq]
                      exact bd_w9 ⟨n - 450, hr⟩
                    ·
                      by_cases h10 : n < 550
                      · have hr : n - 500 < 50 := by omega
                        have heq : n = (n - 500) + 500 := by omega
                        rw [heq]
                        exact bd_w10 ⟨n - 500, hr⟩
                      ·
                        by_cases h11 : n < 600
                        · have hr : n - 550 < 50 := by omega
                          have heq : n = (n - 550) + 550 := by omega
                          rw [heq]
                          exact bd_w11 ⟨n - 550, hr⟩
                        ·
                          by_cases h12 : n < 650
                          · have hr : n - 600 < 50 := by omega
                            have heq : n = (n - 600) + 600 := by omega
                            rw [heq]
                            exact bd_w12 ⟨n - 600, hr⟩
                          ·
                            by_cases h13 : n < 700
                            · have hr : n - 650 < 50 := by omega
                              have heq : n = (n - 650) + 650 := by omega
                              rw [heq]
                              exact bd_w13 ⟨n - 650, hr⟩
                            ·
                              by_cases h14 : n < 750
                              · have hr : n - 700 < 50 := by omega
                                have heq : n = (n - 700) + 700 := by omega
                                rw [heq]
                                exact bd_w14 ⟨n - 700, hr⟩
                              ·
                                by_cases h15 : n < 800
                                · have hr : n - 750 < 50 := by omega
                                  have heq : n = (n - 750) + 750 := by omega
                                  rw [heq]
                                  exact bd_w15 ⟨n - 750, hr⟩
                                ·
                                  by_cases h16 : n < 850
                                  · have hr : n - 800 < 50 := by omega
                                    have heq : n = (n - 800) + 800 := by omega
                                    rw [heq]
                                    exact bd_w16 ⟨n - 800, hr⟩
                                  ·
                                    by_cases h17 : n < 900
                                    · have hr : n - 850 < 50 := by omega
                                      have heq : n = (n - 850) + 850 := by omega
                                      rw [heq]
                                      exact bd_w17 ⟨n - 850, hr⟩
                                    ·
                                      by_cases h18 : n < 950
                                      · have hr : n - 900 < 50 := by omega
                                        have heq : n = (n - 900) + 900 := by omega
                                        rw [heq]
                                        exact bd_w18 ⟨n - 900, hr⟩
                                      ·
                                        by_cases h19 : n < 1000
                                        · have hr : n - 950 < 50 := by omega
                                          have heq : n = (n - 950) + 950 := by omega
                                          rw [heq]
                                          exact bd_w19 ⟨n - 950, hr⟩
                                        ·
                                          by_cases h20 : n < 1050
                                          · have hr : n - 1000 < 50 := by omega
                                            have heq : n = (n - 1000) + 1000 := by omega
                                            rw [heq]
                                            exact bd_w20 ⟨n - 1000, hr⟩
                                          ·
                                            by_cases h21 : n < 1100
                                            · have hr : n - 1050 < 50 := by omega
                                              have heq : n = (n - 1050) + 1050 := by omega
                                              rw [heq]
                                              exact bd_w21 ⟨n - 1050, hr⟩
                                            ·
                                              by_cases h22 : n < 1150
                                              · have hr : n - 1100 < 50 := by omega
                                                have heq : n = (n - 1100) + 1100 := by omega
                                                rw [heq]
                                                exact bd_w22 ⟨n - 1100, hr⟩
                                              ·
                                                by_cases h23 : n < 1200
                                                · have hr : n - 1150 < 50 := by omega
                                                  have heq : n = (n - 1150) + 1150 := by omega
                                                  rw [heq]
                                                  exact bd_w23 ⟨n - 1150, hr⟩
                                                ·
                                                  by_cases h24 : n < 1250
                                                  · have hr : n - 1200 < 50 := by omega
                                                    have heq : n = (n - 1200) + 1200 := by omega
                                                    rw [heq]
                                                    exact bd_w24 ⟨n - 1200, hr⟩
                                                  ·
                                                    by_cases h25 : n < 1300
                                                    · have hr : n - 1250 < 50 := by omega
                                                      have heq : n = (n - 1250) + 1250 := by omega
                                                      rw [heq]
                                                      exact bd_w25 ⟨n - 1250, hr⟩
                                                    ·
                                                      by_cases h26 : n < 1350
                                                      · have hr : n - 1300 < 50 := by omega
                                                        have heq : n = (n - 1300) + 1300 := by omega
                                                        rw [heq]
                                                        exact bd_w26 ⟨n - 1300, hr⟩
                                                      ·
                                                        by_cases h27 : n < 1400
                                                        · have hr : n - 1350 < 50 := by omega
                                                          have heq : n = (n - 1350) + 1350 := by omega
                                                          rw [heq]
                                                          exact bd_w27 ⟨n - 1350, hr⟩
                                                        ·
                                                          by_cases h28 : n < 1450
                                                          · have hr : n - 1400 < 50 := by omega
                                                            have heq : n = (n - 1400) + 1400 := by omega
                                                            rw [heq]
                                                            exact bd_w28 ⟨n - 1400, hr⟩
                                                          ·
                                                            by_cases h29 : n < 1500
                                                            · have hr : n - 1450 < 50 := by omega
                                                              have heq : n = (n - 1450) + 1450 := by omega
                                                              rw [heq]
                                                              exact bd_w29 ⟨n - 1450, hr⟩
                                                            ·
                                                              by_cases h30 : n < 1550
                                                              · have hr : n - 1500 < 50 := by omega
                                                                have heq : n = (n - 1500) + 1500 := by omega
                                                                rw [heq]
                                                                exact bd_w30 ⟨n - 1500, hr⟩
                                                              ·
                                                                by_cases h31 : n < 1600
                                                                · have hr : n - 1550 < 50 := by omega
                                                                  have heq : n = (n - 1550) + 1550 := by omega
                                                                  rw [heq]
                                                                  exact bd_w31 ⟨n - 1550, hr⟩
                                                                ·
                                                                  by_cases h32 : n < 1650
                                                                  · have hr : n - 1600 < 50 := by omega
                                                                    have heq : n = (n - 1600) + 1600 := by omega
                                                                    rw [heq]
                                                                    exact bd_w32 ⟨n - 1600, hr⟩
                                                                  ·
                                                                    by_cases h33 : n < 1700
                                                                    · have hr : n - 1650 < 50 := by omega
                                                                      have heq : n = (n - 1650) + 1650 := by omega
                                                                      rw [heq]
                                                                      exact bd_w33 ⟨n - 1650, hr⟩
                                                                    ·
                                                                      by_cases h34 : n < 1750
                                                                      · have hr : n - 1700 < 50 := by omega
                                                                        have heq : n = (n - 1700) + 1700 := by omega
                                                                        rw [heq]
                                                                        exact bd_w34 ⟨n - 1700, hr⟩
                                                                      ·
                                                                        by_cases h35 : n < 1800
                                                                        · have hr : n - 1750 < 50 := by omega
                                                                          have heq : n = (n - 1750) + 1750 := by omega
                                                                          rw [heq]
                                                                          exact bd_w35 ⟨n - 1750, hr⟩
                                                                        ·
                                                                          by_cases h36 : n < 1850
                                                                          · have hr : n - 1800 < 50 := by omega
                                                                            have heq : n = (n - 1800) + 1800 := by omega
                                                                            rw [heq]
                                                                            exact bd_w36 ⟨n - 1800, hr⟩
                                                                          ·
                                                                            by_cases h37 : n < 1900
                                                                            · have hr : n - 1850 < 50 := by omega
                                                                              have heq : n = (n - 1850) + 1850 := by omega
                                                                              rw [heq]
                                                                              exact bd_w37 ⟨n - 1850, hr⟩
                                                                            ·
                                                                              by_cases h38 : n < 1950
                                                                              · have hr : n - 1900 < 50 := by omega
                                                                                have heq : n = (n - 1900) + 1900 := by omega
                                                                                rw [heq]
                                                                                exact bd_w38 ⟨n - 1900, hr⟩
                                                                              ·
                                                                                by_cases h39 : n < 2000
                                                                                · have hr : n - 1950 < 50 := by omega
                                                                                  have heq : n = (n - 1950) + 1950 := by omega
                                                                                  rw [heq]
                                                                                  exact bd_w39 ⟨n - 1950, hr⟩
                                                                                ·
                                                                                  by_cases h40 : n < 2050
                                                                                  · have hr : n - 2000 < 50 := by omega
                                                                                    have heq : n = (n - 2000) + 2000 := by omega
                                                                                    rw [heq]
                                                                                    exact bd_w40 ⟨n - 2000, hr⟩
                                                                                  ·
                                                                                    by_cases h41 : n < 2100
                                                                                    · have hr : n - 2050 < 50 := by omega
                                                                                      have heq : n = (n - 2050) + 2050 := by omega
                                                                                      rw [heq]
                                                                                      exact bd_w41 ⟨n - 2050, hr⟩
                                                                                    ·
                                                                                      by_cases h42 : n < 2150
                                                                                      · have hr : n - 2100 < 50 := by omega
                                                                                        have heq : n = (n - 2100) + 2100 := by omega
                                                                                        rw [heq]
                                                                                        exact bd_w42 ⟨n - 2100, hr⟩
                                                                                      ·
                                                                                        by_cases h43 : n < 2200
                                                                                        · have hr : n - 2150 < 50 := by omega
                                                                                          have heq : n = (n - 2150) + 2150 := by omega
                                                                                          rw [heq]
                                                                                          exact bd_w43 ⟨n - 2150, hr⟩
                                                                                        ·
                                                                                          by_cases h44 : n < 2250
                                                                                          · have hr : n - 2200 < 50 := by omega
                                                                                            have heq : n = (n - 2200) + 2200 := by omega
                                                                                            rw [heq]
                                                                                            exact bd_w44 ⟨n - 2200, hr⟩
                                                                                          ·
                                                                                            by_cases h45 : n < 2300
                                                                                            · have hr : n - 2250 < 50 := by omega
                                                                                              have heq : n = (n - 2250) + 2250 := by omega
                                                                                              rw [heq]
                                                                                              exact bd_w45 ⟨n - 2250, hr⟩
                                                                                            ·
                                                                                              by_cases h46 : n < 2350
                                                                                              · have hr : n - 2300 < 50 := by omega
                                                                                                have heq : n = (n - 2300) + 2300 := by omega
                                                                                                rw [heq]
                                                                                                exact bd_w46 ⟨n - 2300, hr⟩
                                                                                              ·
                                                                                                by_cases h47 : n < 2400
                                                                                                · have hr : n - 2350 < 50 := by omega
                                                                                                  have heq : n = (n - 2350) + 2350 := by omega
                                                                                                  rw [heq]
                                                                                                  exact bd_w47 ⟨n - 2350, hr⟩
                                                                                                ·
                                                                                                  by_cases h48 : n < 2450
                                                                                                  · have hr : n - 2400 < 50 := by omega
                                                                                                    have heq : n = (n - 2400) + 2400 := by omega
                                                                                                    rw [heq]
                                                                                                    exact bd_w48 ⟨n - 2400, hr⟩
                                                                                                  ·
                                                                                                    by_cases h49 : n < 2500
                                                                                                    · have hr : n - 2450 < 50 := by omega
                                                                                                      have heq : n = (n - 2450) + 2450 := by omega
                                                                                                      rw [heq]
                                                                                                      exact bd_w49 ⟨n - 2450, hr⟩
                                                                                                    ·
                                                                                                      by_cases h50 : n < 2550
                                                                                                      · have hr : n - 2500 < 50 := by omega
                                                                                                        have heq : n = (n - 2500) + 2500 := by omega
                                                                                                        rw [heq]
                                                                                                        exact bd_w50 ⟨n - 2500, hr⟩
                                                                                                      ·
                                                                                                        by_cases h51 : n < 2600
                                                                                                        · have hr : n - 2550 < 50 := by omega
                                                                                                          have heq : n = (n - 2550) + 2550 := by omega
                                                                                                          rw [heq]
                                                                                                          exact bd_w51 ⟨n - 2550, hr⟩
                                                                                                        ·
                                                                                                          by_cases h52 : n < 2650
                                                                                                          · have hr : n - 2600 < 50 := by omega
                                                                                                            have heq : n = (n - 2600) + 2600 := by omega
                                                                                                            rw [heq]
                                                                                                            exact bd_w52 ⟨n - 2600, hr⟩
                                                                                                          ·
                                                                                                            by_cases h53 : n < 2700
                                                                                                            · have hr : n - 2650 < 50 := by omega
                                                                                                              have heq : n = (n - 2650) + 2650 := by omega
                                                                                                              rw [heq]
                                                                                                              exact bd_w53 ⟨n - 2650, hr⟩
                                                                                                            ·
                                                                                                              by_cases h54 : n < 2750
                                                                                                              · have hr : n - 2700 < 50 := by omega
                                                                                                                have heq : n = (n - 2700) + 2700 := by omega
                                                                                                                rw [heq]
                                                                                                                exact bd_w54 ⟨n - 2700, hr⟩
                                                                                                              ·
                                                                                                                by_cases h55 : n < 2800
                                                                                                                · have hr : n - 2750 < 50 := by omega
                                                                                                                  have heq : n = (n - 2750) + 2750 := by omega
                                                                                                                  rw [heq]
                                                                                                                  exact bd_w55 ⟨n - 2750, hr⟩
                                                                                                                ·
                                                                                                                  by_cases h56 : n < 2850
                                                                                                                  · have hr : n - 2800 < 50 := by omega
                                                                                                                    have heq : n = (n - 2800) + 2800 := by omega
                                                                                                                    rw [heq]
                                                                                                                    exact bd_w56 ⟨n - 2800, hr⟩
                                                                                                                  ·
                                                                                                                    by_cases h57 : n < 2900
                                                                                                                    · have hr : n - 2850 < 50 := by omega
                                                                                                                      have heq : n = (n - 2850) + 2850 := by omega
                                                                                                                      rw [heq]
                                                                                                                      exact bd_w57 ⟨n - 2850, hr⟩
                                                                                                                    ·
                                                                                                                      by_cases h58 : n < 2950
                                                                                                                      · have hr : n - 2900 < 50 := by omega
                                                                                                                        have heq : n = (n - 2900) + 2900 := by omega
                                                                                                                        rw [heq]
                                                                                                                        exact bd_w58 ⟨n - 2900, hr⟩
                                                                                                                      ·
                                                                                                                        by_cases h59 : n < 3000
                                                                                                                        · have hr : n - 2950 < 50 := by omega
                                                                                                                          have heq : n = (n - 2950) + 2950 := by omega
                                                                                                                          rw [heq]
                                                                                                                          exact bd_w59 ⟨n - 2950, hr⟩
                                                                                                                        ·
                                                                                                                          by_cases h60 : n < 3050
                                                                                                                          · have hr : n - 3000 < 50 := by omega
                                                                                                                            have heq : n = (n - 3000) + 3000 := by omega
                                                                                                                            rw [heq]
                                                                                                                            exact bd_w60 ⟨n - 3000, hr⟩
                                                                                                                          ·
                                                                                                                            by_cases h61 : n < 3100
                                                                                                                            · have hr : n - 3050 < 50 := by omega
                                                                                                                              have heq : n = (n - 3050) + 3050 := by omega
                                                                                                                              rw [heq]
                                                                                                                              exact bd_w61 ⟨n - 3050, hr⟩
                                                                                                                            ·
                                                                                                                              by_cases h62 : n < 3150
                                                                                                                              · have hr : n - 3100 < 50 := by omega
                                                                                                                                have heq : n = (n - 3100) + 3100 := by omega
                                                                                                                                rw [heq]
                                                                                                                                exact bd_w62 ⟨n - 3100, hr⟩
                                                                                                                              ·
                                                                                                                                by_cases h63 : n < 3200
                                                                                                                                · have hr : n - 3150 < 50 := by omega
                                                                                                                                  have heq : n = (n - 3150) + 3150 := by omega
                                                                                                                                  rw [heq]
                                                                                                                                  exact bd_w63 ⟨n - 3150, hr⟩
                                                                                                                                ·
                                                                                                                                  by_cases h64 : n < 3250
                                                                                                                                  · have hr : n - 3200 < 50 := by omega
                                                                                                                                    have heq : n = (n - 3200) + 3200 := by omega
                                                                                                                                    rw [heq]
                                                                                                                                    exact bd_w64 ⟨n - 3200, hr⟩
                                                                                                                                  ·
                                                                                                                                    by_cases h65 : n < 3300
                                                                                                                                    · have hr : n - 3250 < 50 := by omega
                                                                                                                                      have heq : n = (n - 3250) + 3250 := by omega
                                                                                                                                      rw [heq]
                                                                                                                                      exact bd_w65 ⟨n - 3250, hr⟩
                                                                                                                                    ·
                                                                                                                                      by_cases h66 : n < 3350
                                                                                                                                      · have hr : n - 3300 < 50 := by omega
                                                                                                                                        have heq : n = (n - 3300) + 3300 := by omega
                                                                                                                                        rw [heq]
                                                                                                                                        exact bd_w66 ⟨n - 3300, hr⟩
                                                                                                                                      ·
                                                                                                                                        by_cases h67 : n < 3400
                                                                                                                                        · have hr : n - 3350 < 50 := by omega
                                                                                                                                          have heq : n = (n - 3350) + 3350 := by omega
                                                                                                                                          rw [heq]
                                                                                                                                          exact bd_w67 ⟨n - 3350, hr⟩
                                                                                                                                        ·
                                                                                                                                          by_cases h68 : n < 3450
                                                                                                                                          · have hr : n - 3400 < 50 := by omega
                                                                                                                                            have heq : n = (n - 3400) + 3400 := by omega
                                                                                                                                            rw [heq]
                                                                                                                                            exact bd_w68 ⟨n - 3400, hr⟩
                                                                                                                                          ·
                                                                                                                                            by_cases h69 : n < 3500
                                                                                                                                            · have hr : n - 3450 < 50 := by omega
                                                                                                                                              have heq : n = (n - 3450) + 3450 := by omega
                                                                                                                                              rw [heq]
                                                                                                                                              exact bd_w69 ⟨n - 3450, hr⟩
                                                                                                                                            ·
                                                                                                                                              by_cases h70 : n < 3550
                                                                                                                                              · have hr : n - 3500 < 50 := by omega
                                                                                                                                                have heq : n = (n - 3500) + 3500 := by omega
                                                                                                                                                rw [heq]
                                                                                                                                                exact bd_w70 ⟨n - 3500, hr⟩
                                                                                                                                              ·
                                                                                                                                                by_cases h71 : n < 3600
                                                                                                                                                · have hr : n - 3550 < 50 := by omega
                                                                                                                                                  have heq : n = (n - 3550) + 3550 := by omega
                                                                                                                                                  rw [heq]
                                                                                                                                                  exact bd_w71 ⟨n - 3550, hr⟩
                                                                                                                                                ·
                                                                                                                                                  by_cases h72 : n < 3650
                                                                                                                                                  · have hr : n - 3600 < 50 := by omega
                                                                                                                                                    have heq : n = (n - 3600) + 3600 := by omega
                                                                                                                                                    rw [heq]
                                                                                                                                                    exact bd_w72 ⟨n - 3600, hr⟩
                                                                                                                                                  ·
                                                                                                                                                    by_cases h73 : n < 3700
                                                                                                                                                    · have hr : n - 3650 < 50 := by omega
                                                                                                                                                      have heq : n = (n - 3650) + 3650 := by omega
                                                                                                                                                      rw [heq]
                                                                                                                                                      exact bd_w73 ⟨n - 3650, hr⟩
                                                                                                                                                    ·
                                                                                                                                                      by_cases h74 : n < 3750
                                                                                                                                                      · have hr : n - 3700 < 50 := by omega
                                                                                                                                                        have heq : n = (n - 3700) + 3700 := by omega
                                                                                                                                                        rw [heq]
                                                                                                                                                        exact bd_w74 ⟨n - 3700, hr⟩
                                                                                                                                                      ·
                                                                                                                                                        by_cases h75 : n < 3800
                                                                                                                                                        · have hr : n - 3750 < 50 := by omega
                                                                                                                                                          have heq : n = (n - 3750) + 3750 := by omega
                                                                                                                                                          rw [heq]
                                                                                                                                                          exact bd_w75 ⟨n - 3750, hr⟩
                                                                                                                                                        ·
                                                                                                                                                          by_cases h76 : n < 3850
                                                                                                                                                          · have hr : n - 3800 < 50 := by omega
                                                                                                                                                            have heq : n = (n - 3800) + 3800 := by omega
                                                                                                                                                            rw [heq]
                                                                                                                                                            exact bd_w76 ⟨n - 3800, hr⟩
                                                                                                                                                          ·
                                                                                                                                                            by_cases h77 : n < 3900
                                                                                                                                                            · have hr : n - 3850 < 50 := by omega
                                                                                                                                                              have heq : n = (n - 3850) + 3850 := by omega
                                                                                                                                                              rw [heq]
                                                                                                                                                              exact bd_w77 ⟨n - 3850, hr⟩
                                                                                                                                                            ·
                                                                                                                                                              by_cases h78 : n < 3950
                                                                                                                                                              · have hr : n - 3900 < 50 := by omega
                                                                                                                                                                have heq : n = (n - 3900) + 3900 := by omega
                                                                                                                                                                rw [heq]
                                                                                                                                                                exact bd_w78 ⟨n - 3900, hr⟩
                                                                                                                                                              ·
                                                                                                                                                                by_cases h79 : n < 4000
                                                                                                                                                                · have hr : n - 3950 < 50 := by omega
                                                                                                                                                                  have heq : n = (n - 3950) + 3950 := by omega
                                                                                                                                                                  rw [heq]
                                                                                                                                                                  exact bd_w79 ⟨n - 3950, hr⟩
                                                                                                                                                                ·
                                                                                                                                                                  by_cases h80 : n < 4050
                                                                                                                                                                  · have hr : n - 4000 < 50 := by omega
                                                                                                                                                                    have heq : n = (n - 4000) + 4000 := by omega
                                                                                                                                                                    rw [heq]
                                                                                                                                                                    exact bd_w80 ⟨n - 4000, hr⟩
                                                                                                                                                                  ·
                                                                                                                                                                    by_cases h81 : n < 4100
                                                                                                                                                                    · have hr : n - 4050 < 50 := by omega
                                                                                                                                                                      have heq : n = (n - 4050) + 4050 := by omega
                                                                                                                                                                      rw [heq]
                                                                                                                                                                      exact bd_w81 ⟨n - 4050, hr⟩
                                                                                                                                                                    ·
                                                                                                                                                                      by_cases h82 : n < 4150
                                                                                                                                                                      · have hr : n - 4100 < 50 := by omega
                                                                                                                                                                        have heq : n = (n - 4100) + 4100 := by omega
                                                                                                                                                                        rw [heq]
                                                                                                                                                                        exact bd_w82 ⟨n - 4100, hr⟩
                                                                                                                                                                      ·
                                                                                                                                                                        by_cases h83 : n < 4200
                                                                                                                                                                        · have hr : n - 4150 < 50 := by omega
                                                                                                                                                                          have heq : n = (n - 4150) + 4150 := by omega
                                                                                                                                                                          rw [heq]
                                                                                                                                                                          exact bd_w83 ⟨n - 4150, hr⟩
                                                                                                                                                                        ·
                                                                                                                                                                          by_cases h84 : n < 4250
                                                                                                                                                                          · have hr : n - 4200 < 50 := by omega
                                                                                                                                                                            have heq : n = (n - 4200) + 4200 := by omega
                                                                                                                                                                            rw [heq]
                                                                                                                                                                            exact bd_w84 ⟨n - 4200, hr⟩
                                                                                                                                                                          ·
                                                                                                                                                                            by_cases h85 : n < 4300
                                                                                                                                                                            · have hr : n - 4250 < 50 := by omega
                                                                                                                                                                              have heq : n = (n - 4250) + 4250 := by omega
                                                                                                                                                                              rw [heq]
                                                                                                                                                                              exact bd_w85 ⟨n - 4250, hr⟩
                                                                                                                                                                            ·
                                                                                                                                                                              by_cases h86 : n < 4350
                                                                                                                                                                              · have hr : n - 4300 < 50 := by omega
                                                                                                                                                                                have heq : n = (n - 4300) + 4300 := by omega
                                                                                                                                                                                rw [heq]
                                                                                                                                                                                exact bd_w86 ⟨n - 4300, hr⟩
                                                                                                                                                                              ·
                                                                                                                                                                                by_cases h87 : n < 4400
                                                                                                                                                                                · have hr : n - 4350 < 50 := by omega
                                                                                                                                                                                  have heq : n = (n - 4350) + 4350 := by omega
                                                                                                                                                                                  rw [heq]
                                                                                                                                                                                  exact bd_w87 ⟨n - 4350, hr⟩
                                                                                                                                                                                ·
                                                                                                                                                                                  by_cases h88 : n < 4450
                                                                                                                                                                                  · have hr : n - 4400 < 50 := by omega
                                                                                                                                                                                    have heq : n = (n - 4400) + 4400 := by omega
                                                                                                                                                                                    rw [heq]
                                                                                                                                                                                    exact bd_w88 ⟨n - 4400, hr⟩
                                                                                                                                                                                  ·
                                                                                                                                                                                    by_cases h89 : n < 4500
                                                                                                                                                                                    · have hr : n - 4450 < 50 := by omega
                                                                                                                                                                                      have heq : n = (n - 4450) + 4450 := by omega
                                                                                                                                                                                      rw [heq]
                                                                                                                                                                                      exact bd_w89 ⟨n - 4450, hr⟩
                                                                                                                                                                                    ·
                                                                                                                                                                                      by_cases h90 : n < 4550
                                                                                                                                                                                      · have hr : n - 4500 < 50 := by omega
                                                                                                                                                                                        have heq : n = (n - 4500) + 4500 := by omega
                                                                                                                                                                                        rw [heq]
                                                                                                                                                                                        exact bd_w90 ⟨n - 4500, hr⟩
                                                                                                                                                                                      ·
                                                                                                                                                                                        by_cases h91 : n < 4600
                                                                                                                                                                                        · have hr : n - 4550 < 50 := by omega
                                                                                                                                                                                          have heq : n = (n - 4550) + 4550 := by omega
                                                                                                                                                                                          rw [heq]
                                                                                                                                                                                          exact bd_w91 ⟨n - 4550, hr⟩
                                                                                                                                                                                        ·
                                                                                                                                                                                          by_cases h92 : n < 4650
                                                                                                                                                                                          · have hr : n - 4600 < 50 := by omega
                                                                                                                                                                                            have heq : n = (n - 4600) + 4600 := by omega
                                                                                                                                                                                            rw [heq]
                                                                                                                                                                                            exact bd_w92 ⟨n - 4600, hr⟩
                                                                                                                                                                                          ·
                                                                                                                                                                                            by_cases h93 : n < 4700
                                                                                                                                                                                            · have hr : n - 4650 < 50 := by omega
                                                                                                                                                                                              have heq : n = (n - 4650) + 4650 := by omega
                                                                                                                                                                                              rw [heq]
                                                                                                                                                                                              exact bd_w93 ⟨n - 4650, hr⟩
                                                                                                                                                                                            ·
                                                                                                                                                                                              by_cases h94 : n < 4750
                                                                                                                                                                                              · have hr : n - 4700 < 50 := by omega
                                                                                                                                                                                                have heq : n = (n - 4700) + 4700 := by omega
                                                                                                                                                                                                rw [heq]
                                                                                                                                                                                                exact bd_w94 ⟨n - 4700, hr⟩
                                                                                                                                                                                              ·
                                                                                                                                                                                                by_cases h95 : n < 4800
                                                                                                                                                                                                · have hr : n - 4750 < 50 := by omega
                                                                                                                                                                                                  have heq : n = (n - 4750) + 4750 := by omega
                                                                                                                                                                                                  rw [heq]
                                                                                                                                                                                                  exact bd_w95 ⟨n - 4750, hr⟩
                                                                                                                                                                                                ·
                                                                                                                                                                                                  by_cases h96 : n < 4850
                                                                                                                                                                                                  · have hr : n - 4800 < 50 := by omega
                                                                                                                                                                                                    have heq : n = (n - 4800) + 4800 := by omega
                                                                                                                                                                                                    rw [heq]
                                                                                                                                                                                                    exact bd_w96 ⟨n - 4800, hr⟩
                                                                                                                                                                                                  ·
                                                                                                                                                                                                    by_cases h97 : n < 4900
                                                                                                                                                                                                    · have hr : n - 4850 < 50 := by omega
                                                                                                                                                                                                      have heq : n = (n - 4850) + 4850 := by omega
                                                                                                                                                                                                      rw [heq]
                                                                                                                                                                                                      exact bd_w97 ⟨n - 4850, hr⟩
                                                                                                                                                                                                    ·
                                                                                                                                                                                                      by_cases h98 : n < 4950
                                                                                                                                                                                                      · have hr : n - 4900 < 50 := by omega
                                                                                                                                                                                                        have heq : n = (n - 4900) + 4900 := by omega
                                                                                                                                                                                                        rw [heq]
                                                                                                                                                                                                        exact bd_w98 ⟨n - 4900, hr⟩
                                                                                                                                                                                                      ·
                                                                                                                                                                                                        have hr : n - 4950 < 50 := by omega
                                                                                                                                                                                                        have heq : n = (n - 4950) + 4950 := by omega
                                                                                                                                                                                                        rw [heq]
                                                                                                                                                                                                        exact bd_w99 ⟨n - 4950, hr⟩

end IntMul.Kappa.R8.Bit.Oppbank.CentBound0Fix


