-- Prove2me | Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankCentBound6Fix
-- name    : IntMul_Kappa_R8_Data_BitOppbankCentBound6Fix
-- status  : Definition
-- author  : @Ethan Cheung Wang
-- created : 2026-10-28T22:22:47.389395+00:00
-- url     : https://prove2.me/theorems/122f7fb9-23f3-43fb-ae16-1648996dd1db
-- title:
--   IntMul Kappa R8 Data BitOppbankCentBound6Fix
-- statement:
--   Densified HasCentre support certificates (IntMul_Kappa_R8_Data_BitOppbankCentBound6Fix) retargeted to PndFix/CentFix.

-- CentBound6Fix: PndFix retarget
-- CentBound pack 6: densified HasCentre certificates on n ∈ [30000, 35000)
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

namespace IntMul.Kappa.R8.Bit.Oppbank.CentBound6Fix

private theorem cs_w0 : ∀ n : Fin 50, centredStar (densSupG (n.val + 30000)) (centF (n.val + 30000)) = true := by decide
private theorem cl_w0 : ∀ n : Fin 50, centF (n.val + 30000) < 23 := by decide
private theorem bd_w0 : ∀ n : Fin 50, densSupG (n.val + 30000) < 2 ^ 1771 := by decide
private theorem cs_w1 : ∀ n : Fin 50, centredStar (densSupG (n.val + 30050)) (centF (n.val + 30050)) = true := by decide
private theorem cl_w1 : ∀ n : Fin 50, centF (n.val + 30050) < 23 := by decide
private theorem bd_w1 : ∀ n : Fin 50, densSupG (n.val + 30050) < 2 ^ 1771 := by decide
private theorem cs_w2 : ∀ n : Fin 50, centredStar (densSupG (n.val + 30100)) (centF (n.val + 30100)) = true := by decide
private theorem cl_w2 : ∀ n : Fin 50, centF (n.val + 30100) < 23 := by decide
private theorem bd_w2 : ∀ n : Fin 50, densSupG (n.val + 30100) < 2 ^ 1771 := by decide
private theorem cs_w3 : ∀ n : Fin 50, centredStar (densSupG (n.val + 30150)) (centF (n.val + 30150)) = true := by decide
private theorem cl_w3 : ∀ n : Fin 50, centF (n.val + 30150) < 23 := by decide
private theorem bd_w3 : ∀ n : Fin 50, densSupG (n.val + 30150) < 2 ^ 1771 := by decide
private theorem cs_w4 : ∀ n : Fin 50, centredStar (densSupG (n.val + 30200)) (centF (n.val + 30200)) = true := by decide
private theorem cl_w4 : ∀ n : Fin 50, centF (n.val + 30200) < 23 := by decide
private theorem bd_w4 : ∀ n : Fin 50, densSupG (n.val + 30200) < 2 ^ 1771 := by decide
private theorem cs_w5 : ∀ n : Fin 50, centredStar (densSupG (n.val + 30250)) (centF (n.val + 30250)) = true := by decide
private theorem cl_w5 : ∀ n : Fin 50, centF (n.val + 30250) < 23 := by decide
private theorem bd_w5 : ∀ n : Fin 50, densSupG (n.val + 30250) < 2 ^ 1771 := by decide
private theorem cs_w6 : ∀ n : Fin 50, centredStar (densSupG (n.val + 30300)) (centF (n.val + 30300)) = true := by decide
private theorem cl_w6 : ∀ n : Fin 50, centF (n.val + 30300) < 23 := by decide
private theorem bd_w6 : ∀ n : Fin 50, densSupG (n.val + 30300) < 2 ^ 1771 := by decide
private theorem cs_w7 : ∀ n : Fin 50, centredStar (densSupG (n.val + 30350)) (centF (n.val + 30350)) = true := by decide
private theorem cl_w7 : ∀ n : Fin 50, centF (n.val + 30350) < 23 := by decide
private theorem bd_w7 : ∀ n : Fin 50, densSupG (n.val + 30350) < 2 ^ 1771 := by decide
private theorem cs_w8 : ∀ n : Fin 50, centredStar (densSupG (n.val + 30400)) (centF (n.val + 30400)) = true := by decide
private theorem cl_w8 : ∀ n : Fin 50, centF (n.val + 30400) < 23 := by decide
private theorem bd_w8 : ∀ n : Fin 50, densSupG (n.val + 30400) < 2 ^ 1771 := by decide
private theorem cs_w9 : ∀ n : Fin 50, centredStar (densSupG (n.val + 30450)) (centF (n.val + 30450)) = true := by decide
private theorem cl_w9 : ∀ n : Fin 50, centF (n.val + 30450) < 23 := by decide
private theorem bd_w9 : ∀ n : Fin 50, densSupG (n.val + 30450) < 2 ^ 1771 := by decide
private theorem cs_w10 : ∀ n : Fin 50, centredStar (densSupG (n.val + 30500)) (centF (n.val + 30500)) = true := by decide
private theorem cl_w10 : ∀ n : Fin 50, centF (n.val + 30500) < 23 := by decide
private theorem bd_w10 : ∀ n : Fin 50, densSupG (n.val + 30500) < 2 ^ 1771 := by decide
private theorem cs_w11 : ∀ n : Fin 50, centredStar (densSupG (n.val + 30550)) (centF (n.val + 30550)) = true := by decide
private theorem cl_w11 : ∀ n : Fin 50, centF (n.val + 30550) < 23 := by decide
private theorem bd_w11 : ∀ n : Fin 50, densSupG (n.val + 30550) < 2 ^ 1771 := by decide
private theorem cs_w12 : ∀ n : Fin 50, centredStar (densSupG (n.val + 30600)) (centF (n.val + 30600)) = true := by decide
private theorem cl_w12 : ∀ n : Fin 50, centF (n.val + 30600) < 23 := by decide
private theorem bd_w12 : ∀ n : Fin 50, densSupG (n.val + 30600) < 2 ^ 1771 := by decide
private theorem cs_w13 : ∀ n : Fin 50, centredStar (densSupG (n.val + 30650)) (centF (n.val + 30650)) = true := by decide
private theorem cl_w13 : ∀ n : Fin 50, centF (n.val + 30650) < 23 := by decide
private theorem bd_w13 : ∀ n : Fin 50, densSupG (n.val + 30650) < 2 ^ 1771 := by decide
private theorem cs_w14 : ∀ n : Fin 50, centredStar (densSupG (n.val + 30700)) (centF (n.val + 30700)) = true := by decide
private theorem cl_w14 : ∀ n : Fin 50, centF (n.val + 30700) < 23 := by decide
private theorem bd_w14 : ∀ n : Fin 50, densSupG (n.val + 30700) < 2 ^ 1771 := by decide
private theorem cs_w15 : ∀ n : Fin 50, centredStar (densSupG (n.val + 30750)) (centF (n.val + 30750)) = true := by decide
private theorem cl_w15 : ∀ n : Fin 50, centF (n.val + 30750) < 23 := by decide
private theorem bd_w15 : ∀ n : Fin 50, densSupG (n.val + 30750) < 2 ^ 1771 := by decide
private theorem cs_w16 : ∀ n : Fin 50, centredStar (densSupG (n.val + 30800)) (centF (n.val + 30800)) = true := by decide
private theorem cl_w16 : ∀ n : Fin 50, centF (n.val + 30800) < 23 := by decide
private theorem bd_w16 : ∀ n : Fin 50, densSupG (n.val + 30800) < 2 ^ 1771 := by decide
private theorem cs_w17 : ∀ n : Fin 50, centredStar (densSupG (n.val + 30850)) (centF (n.val + 30850)) = true := by decide
private theorem cl_w17 : ∀ n : Fin 50, centF (n.val + 30850) < 23 := by decide
private theorem bd_w17 : ∀ n : Fin 50, densSupG (n.val + 30850) < 2 ^ 1771 := by decide
private theorem cs_w18 : ∀ n : Fin 50, centredStar (densSupG (n.val + 30900)) (centF (n.val + 30900)) = true := by decide
private theorem cl_w18 : ∀ n : Fin 50, centF (n.val + 30900) < 23 := by decide
private theorem bd_w18 : ∀ n : Fin 50, densSupG (n.val + 30900) < 2 ^ 1771 := by decide
private theorem cs_w19 : ∀ n : Fin 50, centredStar (densSupG (n.val + 30950)) (centF (n.val + 30950)) = true := by decide
private theorem cl_w19 : ∀ n : Fin 50, centF (n.val + 30950) < 23 := by decide
private theorem bd_w19 : ∀ n : Fin 50, densSupG (n.val + 30950) < 2 ^ 1771 := by decide
private theorem cs_w20 : ∀ n : Fin 50, centredStar (densSupG (n.val + 31000)) (centF (n.val + 31000)) = true := by decide
private theorem cl_w20 : ∀ n : Fin 50, centF (n.val + 31000) < 23 := by decide
private theorem bd_w20 : ∀ n : Fin 50, densSupG (n.val + 31000) < 2 ^ 1771 := by decide
private theorem cs_w21 : ∀ n : Fin 50, centredStar (densSupG (n.val + 31050)) (centF (n.val + 31050)) = true := by decide
private theorem cl_w21 : ∀ n : Fin 50, centF (n.val + 31050) < 23 := by decide
private theorem bd_w21 : ∀ n : Fin 50, densSupG (n.val + 31050) < 2 ^ 1771 := by decide
private theorem cs_w22 : ∀ n : Fin 50, centredStar (densSupG (n.val + 31100)) (centF (n.val + 31100)) = true := by decide
private theorem cl_w22 : ∀ n : Fin 50, centF (n.val + 31100) < 23 := by decide
private theorem bd_w22 : ∀ n : Fin 50, densSupG (n.val + 31100) < 2 ^ 1771 := by decide
private theorem cs_w23 : ∀ n : Fin 50, centredStar (densSupG (n.val + 31150)) (centF (n.val + 31150)) = true := by decide
private theorem cl_w23 : ∀ n : Fin 50, centF (n.val + 31150) < 23 := by decide
private theorem bd_w23 : ∀ n : Fin 50, densSupG (n.val + 31150) < 2 ^ 1771 := by decide
private theorem cs_w24 : ∀ n : Fin 50, centredStar (densSupG (n.val + 31200)) (centF (n.val + 31200)) = true := by decide
private theorem cl_w24 : ∀ n : Fin 50, centF (n.val + 31200) < 23 := by decide
private theorem bd_w24 : ∀ n : Fin 50, densSupG (n.val + 31200) < 2 ^ 1771 := by decide
private theorem cs_w25 : ∀ n : Fin 50, centredStar (densSupG (n.val + 31250)) (centF (n.val + 31250)) = true := by decide
private theorem cl_w25 : ∀ n : Fin 50, centF (n.val + 31250) < 23 := by decide
private theorem bd_w25 : ∀ n : Fin 50, densSupG (n.val + 31250) < 2 ^ 1771 := by decide
private theorem cs_w26 : ∀ n : Fin 50, centredStar (densSupG (n.val + 31300)) (centF (n.val + 31300)) = true := by decide
private theorem cl_w26 : ∀ n : Fin 50, centF (n.val + 31300) < 23 := by decide
private theorem bd_w26 : ∀ n : Fin 50, densSupG (n.val + 31300) < 2 ^ 1771 := by decide
private theorem cs_w27 : ∀ n : Fin 50, centredStar (densSupG (n.val + 31350)) (centF (n.val + 31350)) = true := by decide
private theorem cl_w27 : ∀ n : Fin 50, centF (n.val + 31350) < 23 := by decide
private theorem bd_w27 : ∀ n : Fin 50, densSupG (n.val + 31350) < 2 ^ 1771 := by decide
private theorem cs_w28 : ∀ n : Fin 50, centredStar (densSupG (n.val + 31400)) (centF (n.val + 31400)) = true := by decide
private theorem cl_w28 : ∀ n : Fin 50, centF (n.val + 31400) < 23 := by decide
private theorem bd_w28 : ∀ n : Fin 50, densSupG (n.val + 31400) < 2 ^ 1771 := by decide
private theorem cs_w29 : ∀ n : Fin 50, centredStar (densSupG (n.val + 31450)) (centF (n.val + 31450)) = true := by decide
private theorem cl_w29 : ∀ n : Fin 50, centF (n.val + 31450) < 23 := by decide
private theorem bd_w29 : ∀ n : Fin 50, densSupG (n.val + 31450) < 2 ^ 1771 := by decide
private theorem cs_w30 : ∀ n : Fin 50, centredStar (densSupG (n.val + 31500)) (centF (n.val + 31500)) = true := by decide
private theorem cl_w30 : ∀ n : Fin 50, centF (n.val + 31500) < 23 := by decide
private theorem bd_w30 : ∀ n : Fin 50, densSupG (n.val + 31500) < 2 ^ 1771 := by decide
private theorem cs_w31 : ∀ n : Fin 50, centredStar (densSupG (n.val + 31550)) (centF (n.val + 31550)) = true := by decide
private theorem cl_w31 : ∀ n : Fin 50, centF (n.val + 31550) < 23 := by decide
private theorem bd_w31 : ∀ n : Fin 50, densSupG (n.val + 31550) < 2 ^ 1771 := by decide
private theorem cs_w32 : ∀ n : Fin 50, centredStar (densSupG (n.val + 31600)) (centF (n.val + 31600)) = true := by decide
private theorem cl_w32 : ∀ n : Fin 50, centF (n.val + 31600) < 23 := by decide
private theorem bd_w32 : ∀ n : Fin 50, densSupG (n.val + 31600) < 2 ^ 1771 := by decide
private theorem cs_w33 : ∀ n : Fin 50, centredStar (densSupG (n.val + 31650)) (centF (n.val + 31650)) = true := by decide
private theorem cl_w33 : ∀ n : Fin 50, centF (n.val + 31650) < 23 := by decide
private theorem bd_w33 : ∀ n : Fin 50, densSupG (n.val + 31650) < 2 ^ 1771 := by decide
private theorem cs_w34 : ∀ n : Fin 50, centredStar (densSupG (n.val + 31700)) (centF (n.val + 31700)) = true := by decide
private theorem cl_w34 : ∀ n : Fin 50, centF (n.val + 31700) < 23 := by decide
private theorem bd_w34 : ∀ n : Fin 50, densSupG (n.val + 31700) < 2 ^ 1771 := by decide
private theorem cs_w35 : ∀ n : Fin 50, centredStar (densSupG (n.val + 31750)) (centF (n.val + 31750)) = true := by decide
private theorem cl_w35 : ∀ n : Fin 50, centF (n.val + 31750) < 23 := by decide
private theorem bd_w35 : ∀ n : Fin 50, densSupG (n.val + 31750) < 2 ^ 1771 := by decide
private theorem cs_w36 : ∀ n : Fin 50, centredStar (densSupG (n.val + 31800)) (centF (n.val + 31800)) = true := by decide
private theorem cl_w36 : ∀ n : Fin 50, centF (n.val + 31800) < 23 := by decide
private theorem bd_w36 : ∀ n : Fin 50, densSupG (n.val + 31800) < 2 ^ 1771 := by decide
private theorem cs_w37 : ∀ n : Fin 50, centredStar (densSupG (n.val + 31850)) (centF (n.val + 31850)) = true := by decide
private theorem cl_w37 : ∀ n : Fin 50, centF (n.val + 31850) < 23 := by decide
private theorem bd_w37 : ∀ n : Fin 50, densSupG (n.val + 31850) < 2 ^ 1771 := by decide
private theorem cs_w38 : ∀ n : Fin 50, centredStar (densSupG (n.val + 31900)) (centF (n.val + 31900)) = true := by decide
private theorem cl_w38 : ∀ n : Fin 50, centF (n.val + 31900) < 23 := by decide
private theorem bd_w38 : ∀ n : Fin 50, densSupG (n.val + 31900) < 2 ^ 1771 := by decide
private theorem cs_w39 : ∀ n : Fin 50, centredStar (densSupG (n.val + 31950)) (centF (n.val + 31950)) = true := by decide
private theorem cl_w39 : ∀ n : Fin 50, centF (n.val + 31950) < 23 := by decide
private theorem bd_w39 : ∀ n : Fin 50, densSupG (n.val + 31950) < 2 ^ 1771 := by decide
private theorem cs_w40 : ∀ n : Fin 50, centredStar (densSupG (n.val + 32000)) (centF (n.val + 32000)) = true := by decide
private theorem cl_w40 : ∀ n : Fin 50, centF (n.val + 32000) < 23 := by decide
private theorem bd_w40 : ∀ n : Fin 50, densSupG (n.val + 32000) < 2 ^ 1771 := by decide
private theorem cs_w41 : ∀ n : Fin 50, centredStar (densSupG (n.val + 32050)) (centF (n.val + 32050)) = true := by decide
private theorem cl_w41 : ∀ n : Fin 50, centF (n.val + 32050) < 23 := by decide
private theorem bd_w41 : ∀ n : Fin 50, densSupG (n.val + 32050) < 2 ^ 1771 := by decide
private theorem cs_w42 : ∀ n : Fin 50, centredStar (densSupG (n.val + 32100)) (centF (n.val + 32100)) = true := by decide
private theorem cl_w42 : ∀ n : Fin 50, centF (n.val + 32100) < 23 := by decide
private theorem bd_w42 : ∀ n : Fin 50, densSupG (n.val + 32100) < 2 ^ 1771 := by decide
private theorem cs_w43 : ∀ n : Fin 50, centredStar (densSupG (n.val + 32150)) (centF (n.val + 32150)) = true := by decide
private theorem cl_w43 : ∀ n : Fin 50, centF (n.val + 32150) < 23 := by decide
private theorem bd_w43 : ∀ n : Fin 50, densSupG (n.val + 32150) < 2 ^ 1771 := by decide
private theorem cs_w44 : ∀ n : Fin 50, centredStar (densSupG (n.val + 32200)) (centF (n.val + 32200)) = true := by decide
private theorem cl_w44 : ∀ n : Fin 50, centF (n.val + 32200) < 23 := by decide
private theorem bd_w44 : ∀ n : Fin 50, densSupG (n.val + 32200) < 2 ^ 1771 := by decide
private theorem cs_w45 : ∀ n : Fin 50, centredStar (densSupG (n.val + 32250)) (centF (n.val + 32250)) = true := by decide
private theorem cl_w45 : ∀ n : Fin 50, centF (n.val + 32250) < 23 := by decide
private theorem bd_w45 : ∀ n : Fin 50, densSupG (n.val + 32250) < 2 ^ 1771 := by decide
private theorem cs_w46 : ∀ n : Fin 50, centredStar (densSupG (n.val + 32300)) (centF (n.val + 32300)) = true := by decide
private theorem cl_w46 : ∀ n : Fin 50, centF (n.val + 32300) < 23 := by decide
private theorem bd_w46 : ∀ n : Fin 50, densSupG (n.val + 32300) < 2 ^ 1771 := by decide
private theorem cs_w47 : ∀ n : Fin 50, centredStar (densSupG (n.val + 32350)) (centF (n.val + 32350)) = true := by decide
private theorem cl_w47 : ∀ n : Fin 50, centF (n.val + 32350) < 23 := by decide
private theorem bd_w47 : ∀ n : Fin 50, densSupG (n.val + 32350) < 2 ^ 1771 := by decide
private theorem cs_w48 : ∀ n : Fin 50, centredStar (densSupG (n.val + 32400)) (centF (n.val + 32400)) = true := by decide
private theorem cl_w48 : ∀ n : Fin 50, centF (n.val + 32400) < 23 := by decide
private theorem bd_w48 : ∀ n : Fin 50, densSupG (n.val + 32400) < 2 ^ 1771 := by decide
private theorem cs_w49 : ∀ n : Fin 50, centredStar (densSupG (n.val + 32450)) (centF (n.val + 32450)) = true := by decide
private theorem cl_w49 : ∀ n : Fin 50, centF (n.val + 32450) < 23 := by decide
private theorem bd_w49 : ∀ n : Fin 50, densSupG (n.val + 32450) < 2 ^ 1771 := by decide
private theorem cs_w50 : ∀ n : Fin 50, centredStar (densSupG (n.val + 32500)) (centF (n.val + 32500)) = true := by decide
private theorem cl_w50 : ∀ n : Fin 50, centF (n.val + 32500) < 23 := by decide
private theorem bd_w50 : ∀ n : Fin 50, densSupG (n.val + 32500) < 2 ^ 1771 := by decide
private theorem cs_w51 : ∀ n : Fin 50, centredStar (densSupG (n.val + 32550)) (centF (n.val + 32550)) = true := by decide
private theorem cl_w51 : ∀ n : Fin 50, centF (n.val + 32550) < 23 := by decide
private theorem bd_w51 : ∀ n : Fin 50, densSupG (n.val + 32550) < 2 ^ 1771 := by decide
private theorem cs_w52 : ∀ n : Fin 50, centredStar (densSupG (n.val + 32600)) (centF (n.val + 32600)) = true := by decide
private theorem cl_w52 : ∀ n : Fin 50, centF (n.val + 32600) < 23 := by decide
private theorem bd_w52 : ∀ n : Fin 50, densSupG (n.val + 32600) < 2 ^ 1771 := by decide
private theorem cs_w53 : ∀ n : Fin 50, centredStar (densSupG (n.val + 32650)) (centF (n.val + 32650)) = true := by decide
private theorem cl_w53 : ∀ n : Fin 50, centF (n.val + 32650) < 23 := by decide
private theorem bd_w53 : ∀ n : Fin 50, densSupG (n.val + 32650) < 2 ^ 1771 := by decide
private theorem cs_w54 : ∀ n : Fin 50, centredStar (densSupG (n.val + 32700)) (centF (n.val + 32700)) = true := by decide
private theorem cl_w54 : ∀ n : Fin 50, centF (n.val + 32700) < 23 := by decide
private theorem bd_w54 : ∀ n : Fin 50, densSupG (n.val + 32700) < 2 ^ 1771 := by decide
private theorem cs_w55 : ∀ n : Fin 50, centredStar (densSupG (n.val + 32750)) (centF (n.val + 32750)) = true := by decide
private theorem cl_w55 : ∀ n : Fin 50, centF (n.val + 32750) < 23 := by decide
private theorem bd_w55 : ∀ n : Fin 50, densSupG (n.val + 32750) < 2 ^ 1771 := by decide
private theorem cs_w56 : ∀ n : Fin 50, centredStar (densSupG (n.val + 32800)) (centF (n.val + 32800)) = true := by decide
private theorem cl_w56 : ∀ n : Fin 50, centF (n.val + 32800) < 23 := by decide
private theorem bd_w56 : ∀ n : Fin 50, densSupG (n.val + 32800) < 2 ^ 1771 := by decide
private theorem cs_w57 : ∀ n : Fin 50, centredStar (densSupG (n.val + 32850)) (centF (n.val + 32850)) = true := by decide
private theorem cl_w57 : ∀ n : Fin 50, centF (n.val + 32850) < 23 := by decide
private theorem bd_w57 : ∀ n : Fin 50, densSupG (n.val + 32850) < 2 ^ 1771 := by decide
private theorem cs_w58 : ∀ n : Fin 50, centredStar (densSupG (n.val + 32900)) (centF (n.val + 32900)) = true := by decide
private theorem cl_w58 : ∀ n : Fin 50, centF (n.val + 32900) < 23 := by decide
private theorem bd_w58 : ∀ n : Fin 50, densSupG (n.val + 32900) < 2 ^ 1771 := by decide
private theorem cs_w59 : ∀ n : Fin 50, centredStar (densSupG (n.val + 32950)) (centF (n.val + 32950)) = true := by decide
private theorem cl_w59 : ∀ n : Fin 50, centF (n.val + 32950) < 23 := by decide
private theorem bd_w59 : ∀ n : Fin 50, densSupG (n.val + 32950) < 2 ^ 1771 := by decide
private theorem cs_w60 : ∀ n : Fin 50, centredStar (densSupG (n.val + 33000)) (centF (n.val + 33000)) = true := by decide
private theorem cl_w60 : ∀ n : Fin 50, centF (n.val + 33000) < 23 := by decide
private theorem bd_w60 : ∀ n : Fin 50, densSupG (n.val + 33000) < 2 ^ 1771 := by decide
private theorem cs_w61 : ∀ n : Fin 50, centredStar (densSupG (n.val + 33050)) (centF (n.val + 33050)) = true := by decide
private theorem cl_w61 : ∀ n : Fin 50, centF (n.val + 33050) < 23 := by decide
private theorem bd_w61 : ∀ n : Fin 50, densSupG (n.val + 33050) < 2 ^ 1771 := by decide
private theorem cs_w62 : ∀ n : Fin 50, centredStar (densSupG (n.val + 33100)) (centF (n.val + 33100)) = true := by decide
private theorem cl_w62 : ∀ n : Fin 50, centF (n.val + 33100) < 23 := by decide
private theorem bd_w62 : ∀ n : Fin 50, densSupG (n.val + 33100) < 2 ^ 1771 := by decide
private theorem cs_w63 : ∀ n : Fin 50, centredStar (densSupG (n.val + 33150)) (centF (n.val + 33150)) = true := by decide
private theorem cl_w63 : ∀ n : Fin 50, centF (n.val + 33150) < 23 := by decide
private theorem bd_w63 : ∀ n : Fin 50, densSupG (n.val + 33150) < 2 ^ 1771 := by decide
private theorem cs_w64 : ∀ n : Fin 50, centredStar (densSupG (n.val + 33200)) (centF (n.val + 33200)) = true := by decide
private theorem cl_w64 : ∀ n : Fin 50, centF (n.val + 33200) < 23 := by decide
private theorem bd_w64 : ∀ n : Fin 50, densSupG (n.val + 33200) < 2 ^ 1771 := by decide
private theorem cs_w65 : ∀ n : Fin 50, centredStar (densSupG (n.val + 33250)) (centF (n.val + 33250)) = true := by decide
private theorem cl_w65 : ∀ n : Fin 50, centF (n.val + 33250) < 23 := by decide
private theorem bd_w65 : ∀ n : Fin 50, densSupG (n.val + 33250) < 2 ^ 1771 := by decide
private theorem cs_w66 : ∀ n : Fin 50, centredStar (densSupG (n.val + 33300)) (centF (n.val + 33300)) = true := by decide
private theorem cl_w66 : ∀ n : Fin 50, centF (n.val + 33300) < 23 := by decide
private theorem bd_w66 : ∀ n : Fin 50, densSupG (n.val + 33300) < 2 ^ 1771 := by decide
private theorem cs_w67 : ∀ n : Fin 50, centredStar (densSupG (n.val + 33350)) (centF (n.val + 33350)) = true := by decide
private theorem cl_w67 : ∀ n : Fin 50, centF (n.val + 33350) < 23 := by decide
private theorem bd_w67 : ∀ n : Fin 50, densSupG (n.val + 33350) < 2 ^ 1771 := by decide
private theorem cs_w68 : ∀ n : Fin 50, centredStar (densSupG (n.val + 33400)) (centF (n.val + 33400)) = true := by decide
private theorem cl_w68 : ∀ n : Fin 50, centF (n.val + 33400) < 23 := by decide
private theorem bd_w68 : ∀ n : Fin 50, densSupG (n.val + 33400) < 2 ^ 1771 := by decide
private theorem cs_w69 : ∀ n : Fin 50, centredStar (densSupG (n.val + 33450)) (centF (n.val + 33450)) = true := by decide
private theorem cl_w69 : ∀ n : Fin 50, centF (n.val + 33450) < 23 := by decide
private theorem bd_w69 : ∀ n : Fin 50, densSupG (n.val + 33450) < 2 ^ 1771 := by decide
private theorem cs_w70 : ∀ n : Fin 50, centredStar (densSupG (n.val + 33500)) (centF (n.val + 33500)) = true := by decide
private theorem cl_w70 : ∀ n : Fin 50, centF (n.val + 33500) < 23 := by decide
private theorem bd_w70 : ∀ n : Fin 50, densSupG (n.val + 33500) < 2 ^ 1771 := by decide
private theorem cs_w71 : ∀ n : Fin 50, centredStar (densSupG (n.val + 33550)) (centF (n.val + 33550)) = true := by decide
private theorem cl_w71 : ∀ n : Fin 50, centF (n.val + 33550) < 23 := by decide
private theorem bd_w71 : ∀ n : Fin 50, densSupG (n.val + 33550) < 2 ^ 1771 := by decide
private theorem cs_w72 : ∀ n : Fin 50, centredStar (densSupG (n.val + 33600)) (centF (n.val + 33600)) = true := by decide
private theorem cl_w72 : ∀ n : Fin 50, centF (n.val + 33600) < 23 := by decide
private theorem bd_w72 : ∀ n : Fin 50, densSupG (n.val + 33600) < 2 ^ 1771 := by decide
private theorem cs_w73 : ∀ n : Fin 50, centredStar (densSupG (n.val + 33650)) (centF (n.val + 33650)) = true := by decide
private theorem cl_w73 : ∀ n : Fin 50, centF (n.val + 33650) < 23 := by decide
private theorem bd_w73 : ∀ n : Fin 50, densSupG (n.val + 33650) < 2 ^ 1771 := by decide
private theorem cs_w74 : ∀ n : Fin 50, centredStar (densSupG (n.val + 33700)) (centF (n.val + 33700)) = true := by decide
private theorem cl_w74 : ∀ n : Fin 50, centF (n.val + 33700) < 23 := by decide
private theorem bd_w74 : ∀ n : Fin 50, densSupG (n.val + 33700) < 2 ^ 1771 := by decide
private theorem cs_w75 : ∀ n : Fin 50, centredStar (densSupG (n.val + 33750)) (centF (n.val + 33750)) = true := by decide
private theorem cl_w75 : ∀ n : Fin 50, centF (n.val + 33750) < 23 := by decide
private theorem bd_w75 : ∀ n : Fin 50, densSupG (n.val + 33750) < 2 ^ 1771 := by decide
private theorem cs_w76 : ∀ n : Fin 50, centredStar (densSupG (n.val + 33800)) (centF (n.val + 33800)) = true := by decide
private theorem cl_w76 : ∀ n : Fin 50, centF (n.val + 33800) < 23 := by decide
private theorem bd_w76 : ∀ n : Fin 50, densSupG (n.val + 33800) < 2 ^ 1771 := by decide
private theorem cs_w77 : ∀ n : Fin 50, centredStar (densSupG (n.val + 33850)) (centF (n.val + 33850)) = true := by decide
private theorem cl_w77 : ∀ n : Fin 50, centF (n.val + 33850) < 23 := by decide
private theorem bd_w77 : ∀ n : Fin 50, densSupG (n.val + 33850) < 2 ^ 1771 := by decide
private theorem cs_w78 : ∀ n : Fin 50, centredStar (densSupG (n.val + 33900)) (centF (n.val + 33900)) = true := by decide
private theorem cl_w78 : ∀ n : Fin 50, centF (n.val + 33900) < 23 := by decide
private theorem bd_w78 : ∀ n : Fin 50, densSupG (n.val + 33900) < 2 ^ 1771 := by decide
private theorem cs_w79 : ∀ n : Fin 50, centredStar (densSupG (n.val + 33950)) (centF (n.val + 33950)) = true := by decide
private theorem cl_w79 : ∀ n : Fin 50, centF (n.val + 33950) < 23 := by decide
private theorem bd_w79 : ∀ n : Fin 50, densSupG (n.val + 33950) < 2 ^ 1771 := by decide
private theorem cs_w80 : ∀ n : Fin 50, centredStar (densSupG (n.val + 34000)) (centF (n.val + 34000)) = true := by decide
private theorem cl_w80 : ∀ n : Fin 50, centF (n.val + 34000) < 23 := by decide
private theorem bd_w80 : ∀ n : Fin 50, densSupG (n.val + 34000) < 2 ^ 1771 := by decide
private theorem cs_w81 : ∀ n : Fin 50, centredStar (densSupG (n.val + 34050)) (centF (n.val + 34050)) = true := by decide
private theorem cl_w81 : ∀ n : Fin 50, centF (n.val + 34050) < 23 := by decide
private theorem bd_w81 : ∀ n : Fin 50, densSupG (n.val + 34050) < 2 ^ 1771 := by decide
private theorem cs_w82 : ∀ n : Fin 50, centredStar (densSupG (n.val + 34100)) (centF (n.val + 34100)) = true := by decide
private theorem cl_w82 : ∀ n : Fin 50, centF (n.val + 34100) < 23 := by decide
private theorem bd_w82 : ∀ n : Fin 50, densSupG (n.val + 34100) < 2 ^ 1771 := by decide
private theorem cs_w83 : ∀ n : Fin 50, centredStar (densSupG (n.val + 34150)) (centF (n.val + 34150)) = true := by decide
private theorem cl_w83 : ∀ n : Fin 50, centF (n.val + 34150) < 23 := by decide
private theorem bd_w83 : ∀ n : Fin 50, densSupG (n.val + 34150) < 2 ^ 1771 := by decide
private theorem cs_w84 : ∀ n : Fin 50, centredStar (densSupG (n.val + 34200)) (centF (n.val + 34200)) = true := by decide
private theorem cl_w84 : ∀ n : Fin 50, centF (n.val + 34200) < 23 := by decide
private theorem bd_w84 : ∀ n : Fin 50, densSupG (n.val + 34200) < 2 ^ 1771 := by decide
private theorem cs_w85 : ∀ n : Fin 50, centredStar (densSupG (n.val + 34250)) (centF (n.val + 34250)) = true := by decide
private theorem cl_w85 : ∀ n : Fin 50, centF (n.val + 34250) < 23 := by decide
private theorem bd_w85 : ∀ n : Fin 50, densSupG (n.val + 34250) < 2 ^ 1771 := by decide
private theorem cs_w86 : ∀ n : Fin 50, centredStar (densSupG (n.val + 34300)) (centF (n.val + 34300)) = true := by decide
private theorem cl_w86 : ∀ n : Fin 50, centF (n.val + 34300) < 23 := by decide
private theorem bd_w86 : ∀ n : Fin 50, densSupG (n.val + 34300) < 2 ^ 1771 := by decide
private theorem cs_w87 : ∀ n : Fin 50, centredStar (densSupG (n.val + 34350)) (centF (n.val + 34350)) = true := by decide
private theorem cl_w87 : ∀ n : Fin 50, centF (n.val + 34350) < 23 := by decide
private theorem bd_w87 : ∀ n : Fin 50, densSupG (n.val + 34350) < 2 ^ 1771 := by decide
private theorem cs_w88 : ∀ n : Fin 50, centredStar (densSupG (n.val + 34400)) (centF (n.val + 34400)) = true := by decide
private theorem cl_w88 : ∀ n : Fin 50, centF (n.val + 34400) < 23 := by decide
private theorem bd_w88 : ∀ n : Fin 50, densSupG (n.val + 34400) < 2 ^ 1771 := by decide
private theorem cs_w89 : ∀ n : Fin 50, centredStar (densSupG (n.val + 34450)) (centF (n.val + 34450)) = true := by decide
private theorem cl_w89 : ∀ n : Fin 50, centF (n.val + 34450) < 23 := by decide
private theorem bd_w89 : ∀ n : Fin 50, densSupG (n.val + 34450) < 2 ^ 1771 := by decide
private theorem cs_w90 : ∀ n : Fin 50, centredStar (densSupG (n.val + 34500)) (centF (n.val + 34500)) = true := by decide
private theorem cl_w90 : ∀ n : Fin 50, centF (n.val + 34500) < 23 := by decide
private theorem bd_w90 : ∀ n : Fin 50, densSupG (n.val + 34500) < 2 ^ 1771 := by decide
private theorem cs_w91 : ∀ n : Fin 50, centredStar (densSupG (n.val + 34550)) (centF (n.val + 34550)) = true := by decide
private theorem cl_w91 : ∀ n : Fin 50, centF (n.val + 34550) < 23 := by decide
private theorem bd_w91 : ∀ n : Fin 50, densSupG (n.val + 34550) < 2 ^ 1771 := by decide
private theorem cs_w92 : ∀ n : Fin 50, centredStar (densSupG (n.val + 34600)) (centF (n.val + 34600)) = true := by decide
private theorem cl_w92 : ∀ n : Fin 50, centF (n.val + 34600) < 23 := by decide
private theorem bd_w92 : ∀ n : Fin 50, densSupG (n.val + 34600) < 2 ^ 1771 := by decide
private theorem cs_w93 : ∀ n : Fin 50, centredStar (densSupG (n.val + 34650)) (centF (n.val + 34650)) = true := by decide
private theorem cl_w93 : ∀ n : Fin 50, centF (n.val + 34650) < 23 := by decide
private theorem bd_w93 : ∀ n : Fin 50, densSupG (n.val + 34650) < 2 ^ 1771 := by decide
private theorem cs_w94 : ∀ n : Fin 50, centredStar (densSupG (n.val + 34700)) (centF (n.val + 34700)) = true := by decide
private theorem cl_w94 : ∀ n : Fin 50, centF (n.val + 34700) < 23 := by decide
private theorem bd_w94 : ∀ n : Fin 50, densSupG (n.val + 34700) < 2 ^ 1771 := by decide
private theorem cs_w95 : ∀ n : Fin 50, centredStar (densSupG (n.val + 34750)) (centF (n.val + 34750)) = true := by decide
private theorem cl_w95 : ∀ n : Fin 50, centF (n.val + 34750) < 23 := by decide
private theorem bd_w95 : ∀ n : Fin 50, densSupG (n.val + 34750) < 2 ^ 1771 := by decide
private theorem cs_w96 : ∀ n : Fin 50, centredStar (densSupG (n.val + 34800)) (centF (n.val + 34800)) = true := by decide
private theorem cl_w96 : ∀ n : Fin 50, centF (n.val + 34800) < 23 := by decide
private theorem bd_w96 : ∀ n : Fin 50, densSupG (n.val + 34800) < 2 ^ 1771 := by decide
private theorem cs_w97 : ∀ n : Fin 50, centredStar (densSupG (n.val + 34850)) (centF (n.val + 34850)) = true := by decide
private theorem cl_w97 : ∀ n : Fin 50, centF (n.val + 34850) < 23 := by decide
private theorem bd_w97 : ∀ n : Fin 50, densSupG (n.val + 34850) < 2 ^ 1771 := by decide
private theorem cs_w98 : ∀ n : Fin 50, centredStar (densSupG (n.val + 34900)) (centF (n.val + 34900)) = true := by decide
private theorem cl_w98 : ∀ n : Fin 50, centF (n.val + 34900) < 23 := by decide
private theorem bd_w98 : ∀ n : Fin 50, densSupG (n.val + 34900) < 2 ^ 1771 := by decide
private theorem cs_w99 : ∀ n : Fin 50, centredStar (densSupG (n.val + 34950)) (centF (n.val + 34950)) = true := by decide
private theorem cl_w99 : ∀ n : Fin 50, centF (n.val + 34950) < 23 := by decide
private theorem bd_w99 : ∀ n : Fin 50, densSupG (n.val + 34950) < 2 ^ 1771 := by decide

theorem centredStar_range : ∀ n, 30000 ≤ n → n < 35000 → centredStar (densSupG n) (centF n) = true := by
  intro n hlo hhi
  by_cases h0 : n < 30050
  · have hr : n - 30000 < 50 := by omega
    have heq : n = (n - 30000) + 30000 := by omega
    rw [heq]
    exact cs_w0 ⟨n - 30000, hr⟩
  ·
    by_cases h1 : n < 30100
    · have hr : n - 30050 < 50 := by omega
      have heq : n = (n - 30050) + 30050 := by omega
      rw [heq]
      exact cs_w1 ⟨n - 30050, hr⟩
    ·
      by_cases h2 : n < 30150
      · have hr : n - 30100 < 50 := by omega
        have heq : n = (n - 30100) + 30100 := by omega
        rw [heq]
        exact cs_w2 ⟨n - 30100, hr⟩
      ·
        by_cases h3 : n < 30200
        · have hr : n - 30150 < 50 := by omega
          have heq : n = (n - 30150) + 30150 := by omega
          rw [heq]
          exact cs_w3 ⟨n - 30150, hr⟩
        ·
          by_cases h4 : n < 30250
          · have hr : n - 30200 < 50 := by omega
            have heq : n = (n - 30200) + 30200 := by omega
            rw [heq]
            exact cs_w4 ⟨n - 30200, hr⟩
          ·
            by_cases h5 : n < 30300
            · have hr : n - 30250 < 50 := by omega
              have heq : n = (n - 30250) + 30250 := by omega
              rw [heq]
              exact cs_w5 ⟨n - 30250, hr⟩
            ·
              by_cases h6 : n < 30350
              · have hr : n - 30300 < 50 := by omega
                have heq : n = (n - 30300) + 30300 := by omega
                rw [heq]
                exact cs_w6 ⟨n - 30300, hr⟩
              ·
                by_cases h7 : n < 30400
                · have hr : n - 30350 < 50 := by omega
                  have heq : n = (n - 30350) + 30350 := by omega
                  rw [heq]
                  exact cs_w7 ⟨n - 30350, hr⟩
                ·
                  by_cases h8 : n < 30450
                  · have hr : n - 30400 < 50 := by omega
                    have heq : n = (n - 30400) + 30400 := by omega
                    rw [heq]
                    exact cs_w8 ⟨n - 30400, hr⟩
                  ·
                    by_cases h9 : n < 30500
                    · have hr : n - 30450 < 50 := by omega
                      have heq : n = (n - 30450) + 30450 := by omega
                      rw [heq]
                      exact cs_w9 ⟨n - 30450, hr⟩
                    ·
                      by_cases h10 : n < 30550
                      · have hr : n - 30500 < 50 := by omega
                        have heq : n = (n - 30500) + 30500 := by omega
                        rw [heq]
                        exact cs_w10 ⟨n - 30500, hr⟩
                      ·
                        by_cases h11 : n < 30600
                        · have hr : n - 30550 < 50 := by omega
                          have heq : n = (n - 30550) + 30550 := by omega
                          rw [heq]
                          exact cs_w11 ⟨n - 30550, hr⟩
                        ·
                          by_cases h12 : n < 30650
                          · have hr : n - 30600 < 50 := by omega
                            have heq : n = (n - 30600) + 30600 := by omega
                            rw [heq]
                            exact cs_w12 ⟨n - 30600, hr⟩
                          ·
                            by_cases h13 : n < 30700
                            · have hr : n - 30650 < 50 := by omega
                              have heq : n = (n - 30650) + 30650 := by omega
                              rw [heq]
                              exact cs_w13 ⟨n - 30650, hr⟩
                            ·
                              by_cases h14 : n < 30750
                              · have hr : n - 30700 < 50 := by omega
                                have heq : n = (n - 30700) + 30700 := by omega
                                rw [heq]
                                exact cs_w14 ⟨n - 30700, hr⟩
                              ·
                                by_cases h15 : n < 30800
                                · have hr : n - 30750 < 50 := by omega
                                  have heq : n = (n - 30750) + 30750 := by omega
                                  rw [heq]
                                  exact cs_w15 ⟨n - 30750, hr⟩
                                ·
                                  by_cases h16 : n < 30850
                                  · have hr : n - 30800 < 50 := by omega
                                    have heq : n = (n - 30800) + 30800 := by omega
                                    rw [heq]
                                    exact cs_w16 ⟨n - 30800, hr⟩
                                  ·
                                    by_cases h17 : n < 30900
                                    · have hr : n - 30850 < 50 := by omega
                                      have heq : n = (n - 30850) + 30850 := by omega
                                      rw [heq]
                                      exact cs_w17 ⟨n - 30850, hr⟩
                                    ·
                                      by_cases h18 : n < 30950
                                      · have hr : n - 30900 < 50 := by omega
                                        have heq : n = (n - 30900) + 30900 := by omega
                                        rw [heq]
                                        exact cs_w18 ⟨n - 30900, hr⟩
                                      ·
                                        by_cases h19 : n < 31000
                                        · have hr : n - 30950 < 50 := by omega
                                          have heq : n = (n - 30950) + 30950 := by omega
                                          rw [heq]
                                          exact cs_w19 ⟨n - 30950, hr⟩
                                        ·
                                          by_cases h20 : n < 31050
                                          · have hr : n - 31000 < 50 := by omega
                                            have heq : n = (n - 31000) + 31000 := by omega
                                            rw [heq]
                                            exact cs_w20 ⟨n - 31000, hr⟩
                                          ·
                                            by_cases h21 : n < 31100
                                            · have hr : n - 31050 < 50 := by omega
                                              have heq : n = (n - 31050) + 31050 := by omega
                                              rw [heq]
                                              exact cs_w21 ⟨n - 31050, hr⟩
                                            ·
                                              by_cases h22 : n < 31150
                                              · have hr : n - 31100 < 50 := by omega
                                                have heq : n = (n - 31100) + 31100 := by omega
                                                rw [heq]
                                                exact cs_w22 ⟨n - 31100, hr⟩
                                              ·
                                                by_cases h23 : n < 31200
                                                · have hr : n - 31150 < 50 := by omega
                                                  have heq : n = (n - 31150) + 31150 := by omega
                                                  rw [heq]
                                                  exact cs_w23 ⟨n - 31150, hr⟩
                                                ·
                                                  by_cases h24 : n < 31250
                                                  · have hr : n - 31200 < 50 := by omega
                                                    have heq : n = (n - 31200) + 31200 := by omega
                                                    rw [heq]
                                                    exact cs_w24 ⟨n - 31200, hr⟩
                                                  ·
                                                    by_cases h25 : n < 31300
                                                    · have hr : n - 31250 < 50 := by omega
                                                      have heq : n = (n - 31250) + 31250 := by omega
                                                      rw [heq]
                                                      exact cs_w25 ⟨n - 31250, hr⟩
                                                    ·
                                                      by_cases h26 : n < 31350
                                                      · have hr : n - 31300 < 50 := by omega
                                                        have heq : n = (n - 31300) + 31300 := by omega
                                                        rw [heq]
                                                        exact cs_w26 ⟨n - 31300, hr⟩
                                                      ·
                                                        by_cases h27 : n < 31400
                                                        · have hr : n - 31350 < 50 := by omega
                                                          have heq : n = (n - 31350) + 31350 := by omega
                                                          rw [heq]
                                                          exact cs_w27 ⟨n - 31350, hr⟩
                                                        ·
                                                          by_cases h28 : n < 31450
                                                          · have hr : n - 31400 < 50 := by omega
                                                            have heq : n = (n - 31400) + 31400 := by omega
                                                            rw [heq]
                                                            exact cs_w28 ⟨n - 31400, hr⟩
                                                          ·
                                                            by_cases h29 : n < 31500
                                                            · have hr : n - 31450 < 50 := by omega
                                                              have heq : n = (n - 31450) + 31450 := by omega
                                                              rw [heq]
                                                              exact cs_w29 ⟨n - 31450, hr⟩
                                                            ·
                                                              by_cases h30 : n < 31550
                                                              · have hr : n - 31500 < 50 := by omega
                                                                have heq : n = (n - 31500) + 31500 := by omega
                                                                rw [heq]
                                                                exact cs_w30 ⟨n - 31500, hr⟩
                                                              ·
                                                                by_cases h31 : n < 31600
                                                                · have hr : n - 31550 < 50 := by omega
                                                                  have heq : n = (n - 31550) + 31550 := by omega
                                                                  rw [heq]
                                                                  exact cs_w31 ⟨n - 31550, hr⟩
                                                                ·
                                                                  by_cases h32 : n < 31650
                                                                  · have hr : n - 31600 < 50 := by omega
                                                                    have heq : n = (n - 31600) + 31600 := by omega
                                                                    rw [heq]
                                                                    exact cs_w32 ⟨n - 31600, hr⟩
                                                                  ·
                                                                    by_cases h33 : n < 31700
                                                                    · have hr : n - 31650 < 50 := by omega
                                                                      have heq : n = (n - 31650) + 31650 := by omega
                                                                      rw [heq]
                                                                      exact cs_w33 ⟨n - 31650, hr⟩
                                                                    ·
                                                                      by_cases h34 : n < 31750
                                                                      · have hr : n - 31700 < 50 := by omega
                                                                        have heq : n = (n - 31700) + 31700 := by omega
                                                                        rw [heq]
                                                                        exact cs_w34 ⟨n - 31700, hr⟩
                                                                      ·
                                                                        by_cases h35 : n < 31800
                                                                        · have hr : n - 31750 < 50 := by omega
                                                                          have heq : n = (n - 31750) + 31750 := by omega
                                                                          rw [heq]
                                                                          exact cs_w35 ⟨n - 31750, hr⟩
                                                                        ·
                                                                          by_cases h36 : n < 31850
                                                                          · have hr : n - 31800 < 50 := by omega
                                                                            have heq : n = (n - 31800) + 31800 := by omega
                                                                            rw [heq]
                                                                            exact cs_w36 ⟨n - 31800, hr⟩
                                                                          ·
                                                                            by_cases h37 : n < 31900
                                                                            · have hr : n - 31850 < 50 := by omega
                                                                              have heq : n = (n - 31850) + 31850 := by omega
                                                                              rw [heq]
                                                                              exact cs_w37 ⟨n - 31850, hr⟩
                                                                            ·
                                                                              by_cases h38 : n < 31950
                                                                              · have hr : n - 31900 < 50 := by omega
                                                                                have heq : n = (n - 31900) + 31900 := by omega
                                                                                rw [heq]
                                                                                exact cs_w38 ⟨n - 31900, hr⟩
                                                                              ·
                                                                                by_cases h39 : n < 32000
                                                                                · have hr : n - 31950 < 50 := by omega
                                                                                  have heq : n = (n - 31950) + 31950 := by omega
                                                                                  rw [heq]
                                                                                  exact cs_w39 ⟨n - 31950, hr⟩
                                                                                ·
                                                                                  by_cases h40 : n < 32050
                                                                                  · have hr : n - 32000 < 50 := by omega
                                                                                    have heq : n = (n - 32000) + 32000 := by omega
                                                                                    rw [heq]
                                                                                    exact cs_w40 ⟨n - 32000, hr⟩
                                                                                  ·
                                                                                    by_cases h41 : n < 32100
                                                                                    · have hr : n - 32050 < 50 := by omega
                                                                                      have heq : n = (n - 32050) + 32050 := by omega
                                                                                      rw [heq]
                                                                                      exact cs_w41 ⟨n - 32050, hr⟩
                                                                                    ·
                                                                                      by_cases h42 : n < 32150
                                                                                      · have hr : n - 32100 < 50 := by omega
                                                                                        have heq : n = (n - 32100) + 32100 := by omega
                                                                                        rw [heq]
                                                                                        exact cs_w42 ⟨n - 32100, hr⟩
                                                                                      ·
                                                                                        by_cases h43 : n < 32200
                                                                                        · have hr : n - 32150 < 50 := by omega
                                                                                          have heq : n = (n - 32150) + 32150 := by omega
                                                                                          rw [heq]
                                                                                          exact cs_w43 ⟨n - 32150, hr⟩
                                                                                        ·
                                                                                          by_cases h44 : n < 32250
                                                                                          · have hr : n - 32200 < 50 := by omega
                                                                                            have heq : n = (n - 32200) + 32200 := by omega
                                                                                            rw [heq]
                                                                                            exact cs_w44 ⟨n - 32200, hr⟩
                                                                                          ·
                                                                                            by_cases h45 : n < 32300
                                                                                            · have hr : n - 32250 < 50 := by omega
                                                                                              have heq : n = (n - 32250) + 32250 := by omega
                                                                                              rw [heq]
                                                                                              exact cs_w45 ⟨n - 32250, hr⟩
                                                                                            ·
                                                                                              by_cases h46 : n < 32350
                                                                                              · have hr : n - 32300 < 50 := by omega
                                                                                                have heq : n = (n - 32300) + 32300 := by omega
                                                                                                rw [heq]
                                                                                                exact cs_w46 ⟨n - 32300, hr⟩
                                                                                              ·
                                                                                                by_cases h47 : n < 32400
                                                                                                · have hr : n - 32350 < 50 := by omega
                                                                                                  have heq : n = (n - 32350) + 32350 := by omega
                                                                                                  rw [heq]
                                                                                                  exact cs_w47 ⟨n - 32350, hr⟩
                                                                                                ·
                                                                                                  by_cases h48 : n < 32450
                                                                                                  · have hr : n - 32400 < 50 := by omega
                                                                                                    have heq : n = (n - 32400) + 32400 := by omega
                                                                                                    rw [heq]
                                                                                                    exact cs_w48 ⟨n - 32400, hr⟩
                                                                                                  ·
                                                                                                    by_cases h49 : n < 32500
                                                                                                    · have hr : n - 32450 < 50 := by omega
                                                                                                      have heq : n = (n - 32450) + 32450 := by omega
                                                                                                      rw [heq]
                                                                                                      exact cs_w49 ⟨n - 32450, hr⟩
                                                                                                    ·
                                                                                                      by_cases h50 : n < 32550
                                                                                                      · have hr : n - 32500 < 50 := by omega
                                                                                                        have heq : n = (n - 32500) + 32500 := by omega
                                                                                                        rw [heq]
                                                                                                        exact cs_w50 ⟨n - 32500, hr⟩
                                                                                                      ·
                                                                                                        by_cases h51 : n < 32600
                                                                                                        · have hr : n - 32550 < 50 := by omega
                                                                                                          have heq : n = (n - 32550) + 32550 := by omega
                                                                                                          rw [heq]
                                                                                                          exact cs_w51 ⟨n - 32550, hr⟩
                                                                                                        ·
                                                                                                          by_cases h52 : n < 32650
                                                                                                          · have hr : n - 32600 < 50 := by omega
                                                                                                            have heq : n = (n - 32600) + 32600 := by omega
                                                                                                            rw [heq]
                                                                                                            exact cs_w52 ⟨n - 32600, hr⟩
                                                                                                          ·
                                                                                                            by_cases h53 : n < 32700
                                                                                                            · have hr : n - 32650 < 50 := by omega
                                                                                                              have heq : n = (n - 32650) + 32650 := by omega
                                                                                                              rw [heq]
                                                                                                              exact cs_w53 ⟨n - 32650, hr⟩
                                                                                                            ·
                                                                                                              by_cases h54 : n < 32750
                                                                                                              · have hr : n - 32700 < 50 := by omega
                                                                                                                have heq : n = (n - 32700) + 32700 := by omega
                                                                                                                rw [heq]
                                                                                                                exact cs_w54 ⟨n - 32700, hr⟩
                                                                                                              ·
                                                                                                                by_cases h55 : n < 32800
                                                                                                                · have hr : n - 32750 < 50 := by omega
                                                                                                                  have heq : n = (n - 32750) + 32750 := by omega
                                                                                                                  rw [heq]
                                                                                                                  exact cs_w55 ⟨n - 32750, hr⟩
                                                                                                                ·
                                                                                                                  by_cases h56 : n < 32850
                                                                                                                  · have hr : n - 32800 < 50 := by omega
                                                                                                                    have heq : n = (n - 32800) + 32800 := by omega
                                                                                                                    rw [heq]
                                                                                                                    exact cs_w56 ⟨n - 32800, hr⟩
                                                                                                                  ·
                                                                                                                    by_cases h57 : n < 32900
                                                                                                                    · have hr : n - 32850 < 50 := by omega
                                                                                                                      have heq : n = (n - 32850) + 32850 := by omega
                                                                                                                      rw [heq]
                                                                                                                      exact cs_w57 ⟨n - 32850, hr⟩
                                                                                                                    ·
                                                                                                                      by_cases h58 : n < 32950
                                                                                                                      · have hr : n - 32900 < 50 := by omega
                                                                                                                        have heq : n = (n - 32900) + 32900 := by omega
                                                                                                                        rw [heq]
                                                                                                                        exact cs_w58 ⟨n - 32900, hr⟩
                                                                                                                      ·
                                                                                                                        by_cases h59 : n < 33000
                                                                                                                        · have hr : n - 32950 < 50 := by omega
                                                                                                                          have heq : n = (n - 32950) + 32950 := by omega
                                                                                                                          rw [heq]
                                                                                                                          exact cs_w59 ⟨n - 32950, hr⟩
                                                                                                                        ·
                                                                                                                          by_cases h60 : n < 33050
                                                                                                                          · have hr : n - 33000 < 50 := by omega
                                                                                                                            have heq : n = (n - 33000) + 33000 := by omega
                                                                                                                            rw [heq]
                                                                                                                            exact cs_w60 ⟨n - 33000, hr⟩
                                                                                                                          ·
                                                                                                                            by_cases h61 : n < 33100
                                                                                                                            · have hr : n - 33050 < 50 := by omega
                                                                                                                              have heq : n = (n - 33050) + 33050 := by omega
                                                                                                                              rw [heq]
                                                                                                                              exact cs_w61 ⟨n - 33050, hr⟩
                                                                                                                            ·
                                                                                                                              by_cases h62 : n < 33150
                                                                                                                              · have hr : n - 33100 < 50 := by omega
                                                                                                                                have heq : n = (n - 33100) + 33100 := by omega
                                                                                                                                rw [heq]
                                                                                                                                exact cs_w62 ⟨n - 33100, hr⟩
                                                                                                                              ·
                                                                                                                                by_cases h63 : n < 33200
                                                                                                                                · have hr : n - 33150 < 50 := by omega
                                                                                                                                  have heq : n = (n - 33150) + 33150 := by omega
                                                                                                                                  rw [heq]
                                                                                                                                  exact cs_w63 ⟨n - 33150, hr⟩
                                                                                                                                ·
                                                                                                                                  by_cases h64 : n < 33250
                                                                                                                                  · have hr : n - 33200 < 50 := by omega
                                                                                                                                    have heq : n = (n - 33200) + 33200 := by omega
                                                                                                                                    rw [heq]
                                                                                                                                    exact cs_w64 ⟨n - 33200, hr⟩
                                                                                                                                  ·
                                                                                                                                    by_cases h65 : n < 33300
                                                                                                                                    · have hr : n - 33250 < 50 := by omega
                                                                                                                                      have heq : n = (n - 33250) + 33250 := by omega
                                                                                                                                      rw [heq]
                                                                                                                                      exact cs_w65 ⟨n - 33250, hr⟩
                                                                                                                                    ·
                                                                                                                                      by_cases h66 : n < 33350
                                                                                                                                      · have hr : n - 33300 < 50 := by omega
                                                                                                                                        have heq : n = (n - 33300) + 33300 := by omega
                                                                                                                                        rw [heq]
                                                                                                                                        exact cs_w66 ⟨n - 33300, hr⟩
                                                                                                                                      ·
                                                                                                                                        by_cases h67 : n < 33400
                                                                                                                                        · have hr : n - 33350 < 50 := by omega
                                                                                                                                          have heq : n = (n - 33350) + 33350 := by omega
                                                                                                                                          rw [heq]
                                                                                                                                          exact cs_w67 ⟨n - 33350, hr⟩
                                                                                                                                        ·
                                                                                                                                          by_cases h68 : n < 33450
                                                                                                                                          · have hr : n - 33400 < 50 := by omega
                                                                                                                                            have heq : n = (n - 33400) + 33400 := by omega
                                                                                                                                            rw [heq]
                                                                                                                                            exact cs_w68 ⟨n - 33400, hr⟩
                                                                                                                                          ·
                                                                                                                                            by_cases h69 : n < 33500
                                                                                                                                            · have hr : n - 33450 < 50 := by omega
                                                                                                                                              have heq : n = (n - 33450) + 33450 := by omega
                                                                                                                                              rw [heq]
                                                                                                                                              exact cs_w69 ⟨n - 33450, hr⟩
                                                                                                                                            ·
                                                                                                                                              by_cases h70 : n < 33550
                                                                                                                                              · have hr : n - 33500 < 50 := by omega
                                                                                                                                                have heq : n = (n - 33500) + 33500 := by omega
                                                                                                                                                rw [heq]
                                                                                                                                                exact cs_w70 ⟨n - 33500, hr⟩
                                                                                                                                              ·
                                                                                                                                                by_cases h71 : n < 33600
                                                                                                                                                · have hr : n - 33550 < 50 := by omega
                                                                                                                                                  have heq : n = (n - 33550) + 33550 := by omega
                                                                                                                                                  rw [heq]
                                                                                                                                                  exact cs_w71 ⟨n - 33550, hr⟩
                                                                                                                                                ·
                                                                                                                                                  by_cases h72 : n < 33650
                                                                                                                                                  · have hr : n - 33600 < 50 := by omega
                                                                                                                                                    have heq : n = (n - 33600) + 33600 := by omega
                                                                                                                                                    rw [heq]
                                                                                                                                                    exact cs_w72 ⟨n - 33600, hr⟩
                                                                                                                                                  ·
                                                                                                                                                    by_cases h73 : n < 33700
                                                                                                                                                    · have hr : n - 33650 < 50 := by omega
                                                                                                                                                      have heq : n = (n - 33650) + 33650 := by omega
                                                                                                                                                      rw [heq]
                                                                                                                                                      exact cs_w73 ⟨n - 33650, hr⟩
                                                                                                                                                    ·
                                                                                                                                                      by_cases h74 : n < 33750
                                                                                                                                                      · have hr : n - 33700 < 50 := by omega
                                                                                                                                                        have heq : n = (n - 33700) + 33700 := by omega
                                                                                                                                                        rw [heq]
                                                                                                                                                        exact cs_w74 ⟨n - 33700, hr⟩
                                                                                                                                                      ·
                                                                                                                                                        by_cases h75 : n < 33800
                                                                                                                                                        · have hr : n - 33750 < 50 := by omega
                                                                                                                                                          have heq : n = (n - 33750) + 33750 := by omega
                                                                                                                                                          rw [heq]
                                                                                                                                                          exact cs_w75 ⟨n - 33750, hr⟩
                                                                                                                                                        ·
                                                                                                                                                          by_cases h76 : n < 33850
                                                                                                                                                          · have hr : n - 33800 < 50 := by omega
                                                                                                                                                            have heq : n = (n - 33800) + 33800 := by omega
                                                                                                                                                            rw [heq]
                                                                                                                                                            exact cs_w76 ⟨n - 33800, hr⟩
                                                                                                                                                          ·
                                                                                                                                                            by_cases h77 : n < 33900
                                                                                                                                                            · have hr : n - 33850 < 50 := by omega
                                                                                                                                                              have heq : n = (n - 33850) + 33850 := by omega
                                                                                                                                                              rw [heq]
                                                                                                                                                              exact cs_w77 ⟨n - 33850, hr⟩
                                                                                                                                                            ·
                                                                                                                                                              by_cases h78 : n < 33950
                                                                                                                                                              · have hr : n - 33900 < 50 := by omega
                                                                                                                                                                have heq : n = (n - 33900) + 33900 := by omega
                                                                                                                                                                rw [heq]
                                                                                                                                                                exact cs_w78 ⟨n - 33900, hr⟩
                                                                                                                                                              ·
                                                                                                                                                                by_cases h79 : n < 34000
                                                                                                                                                                · have hr : n - 33950 < 50 := by omega
                                                                                                                                                                  have heq : n = (n - 33950) + 33950 := by omega
                                                                                                                                                                  rw [heq]
                                                                                                                                                                  exact cs_w79 ⟨n - 33950, hr⟩
                                                                                                                                                                ·
                                                                                                                                                                  by_cases h80 : n < 34050
                                                                                                                                                                  · have hr : n - 34000 < 50 := by omega
                                                                                                                                                                    have heq : n = (n - 34000) + 34000 := by omega
                                                                                                                                                                    rw [heq]
                                                                                                                                                                    exact cs_w80 ⟨n - 34000, hr⟩
                                                                                                                                                                  ·
                                                                                                                                                                    by_cases h81 : n < 34100
                                                                                                                                                                    · have hr : n - 34050 < 50 := by omega
                                                                                                                                                                      have heq : n = (n - 34050) + 34050 := by omega
                                                                                                                                                                      rw [heq]
                                                                                                                                                                      exact cs_w81 ⟨n - 34050, hr⟩
                                                                                                                                                                    ·
                                                                                                                                                                      by_cases h82 : n < 34150
                                                                                                                                                                      · have hr : n - 34100 < 50 := by omega
                                                                                                                                                                        have heq : n = (n - 34100) + 34100 := by omega
                                                                                                                                                                        rw [heq]
                                                                                                                                                                        exact cs_w82 ⟨n - 34100, hr⟩
                                                                                                                                                                      ·
                                                                                                                                                                        by_cases h83 : n < 34200
                                                                                                                                                                        · have hr : n - 34150 < 50 := by omega
                                                                                                                                                                          have heq : n = (n - 34150) + 34150 := by omega
                                                                                                                                                                          rw [heq]
                                                                                                                                                                          exact cs_w83 ⟨n - 34150, hr⟩
                                                                                                                                                                        ·
                                                                                                                                                                          by_cases h84 : n < 34250
                                                                                                                                                                          · have hr : n - 34200 < 50 := by omega
                                                                                                                                                                            have heq : n = (n - 34200) + 34200 := by omega
                                                                                                                                                                            rw [heq]
                                                                                                                                                                            exact cs_w84 ⟨n - 34200, hr⟩
                                                                                                                                                                          ·
                                                                                                                                                                            by_cases h85 : n < 34300
                                                                                                                                                                            · have hr : n - 34250 < 50 := by omega
                                                                                                                                                                              have heq : n = (n - 34250) + 34250 := by omega
                                                                                                                                                                              rw [heq]
                                                                                                                                                                              exact cs_w85 ⟨n - 34250, hr⟩
                                                                                                                                                                            ·
                                                                                                                                                                              by_cases h86 : n < 34350
                                                                                                                                                                              · have hr : n - 34300 < 50 := by omega
                                                                                                                                                                                have heq : n = (n - 34300) + 34300 := by omega
                                                                                                                                                                                rw [heq]
                                                                                                                                                                                exact cs_w86 ⟨n - 34300, hr⟩
                                                                                                                                                                              ·
                                                                                                                                                                                by_cases h87 : n < 34400
                                                                                                                                                                                · have hr : n - 34350 < 50 := by omega
                                                                                                                                                                                  have heq : n = (n - 34350) + 34350 := by omega
                                                                                                                                                                                  rw [heq]
                                                                                                                                                                                  exact cs_w87 ⟨n - 34350, hr⟩
                                                                                                                                                                                ·
                                                                                                                                                                                  by_cases h88 : n < 34450
                                                                                                                                                                                  · have hr : n - 34400 < 50 := by omega
                                                                                                                                                                                    have heq : n = (n - 34400) + 34400 := by omega
                                                                                                                                                                                    rw [heq]
                                                                                                                                                                                    exact cs_w88 ⟨n - 34400, hr⟩
                                                                                                                                                                                  ·
                                                                                                                                                                                    by_cases h89 : n < 34500
                                                                                                                                                                                    · have hr : n - 34450 < 50 := by omega
                                                                                                                                                                                      have heq : n = (n - 34450) + 34450 := by omega
                                                                                                                                                                                      rw [heq]
                                                                                                                                                                                      exact cs_w89 ⟨n - 34450, hr⟩
                                                                                                                                                                                    ·
                                                                                                                                                                                      by_cases h90 : n < 34550
                                                                                                                                                                                      · have hr : n - 34500 < 50 := by omega
                                                                                                                                                                                        have heq : n = (n - 34500) + 34500 := by omega
                                                                                                                                                                                        rw [heq]
                                                                                                                                                                                        exact cs_w90 ⟨n - 34500, hr⟩
                                                                                                                                                                                      ·
                                                                                                                                                                                        by_cases h91 : n < 34600
                                                                                                                                                                                        · have hr : n - 34550 < 50 := by omega
                                                                                                                                                                                          have heq : n = (n - 34550) + 34550 := by omega
                                                                                                                                                                                          rw [heq]
                                                                                                                                                                                          exact cs_w91 ⟨n - 34550, hr⟩
                                                                                                                                                                                        ·
                                                                                                                                                                                          by_cases h92 : n < 34650
                                                                                                                                                                                          · have hr : n - 34600 < 50 := by omega
                                                                                                                                                                                            have heq : n = (n - 34600) + 34600 := by omega
                                                                                                                                                                                            rw [heq]
                                                                                                                                                                                            exact cs_w92 ⟨n - 34600, hr⟩
                                                                                                                                                                                          ·
                                                                                                                                                                                            by_cases h93 : n < 34700
                                                                                                                                                                                            · have hr : n - 34650 < 50 := by omega
                                                                                                                                                                                              have heq : n = (n - 34650) + 34650 := by omega
                                                                                                                                                                                              rw [heq]
                                                                                                                                                                                              exact cs_w93 ⟨n - 34650, hr⟩
                                                                                                                                                                                            ·
                                                                                                                                                                                              by_cases h94 : n < 34750
                                                                                                                                                                                              · have hr : n - 34700 < 50 := by omega
                                                                                                                                                                                                have heq : n = (n - 34700) + 34700 := by omega
                                                                                                                                                                                                rw [heq]
                                                                                                                                                                                                exact cs_w94 ⟨n - 34700, hr⟩
                                                                                                                                                                                              ·
                                                                                                                                                                                                by_cases h95 : n < 34800
                                                                                                                                                                                                · have hr : n - 34750 < 50 := by omega
                                                                                                                                                                                                  have heq : n = (n - 34750) + 34750 := by omega
                                                                                                                                                                                                  rw [heq]
                                                                                                                                                                                                  exact cs_w95 ⟨n - 34750, hr⟩
                                                                                                                                                                                                ·
                                                                                                                                                                                                  by_cases h96 : n < 34850
                                                                                                                                                                                                  · have hr : n - 34800 < 50 := by omega
                                                                                                                                                                                                    have heq : n = (n - 34800) + 34800 := by omega
                                                                                                                                                                                                    rw [heq]
                                                                                                                                                                                                    exact cs_w96 ⟨n - 34800, hr⟩
                                                                                                                                                                                                  ·
                                                                                                                                                                                                    by_cases h97 : n < 34900
                                                                                                                                                                                                    · have hr : n - 34850 < 50 := by omega
                                                                                                                                                                                                      have heq : n = (n - 34850) + 34850 := by omega
                                                                                                                                                                                                      rw [heq]
                                                                                                                                                                                                      exact cs_w97 ⟨n - 34850, hr⟩
                                                                                                                                                                                                    ·
                                                                                                                                                                                                      by_cases h98 : n < 34950
                                                                                                                                                                                                      · have hr : n - 34900 < 50 := by omega
                                                                                                                                                                                                        have heq : n = (n - 34900) + 34900 := by omega
                                                                                                                                                                                                        rw [heq]
                                                                                                                                                                                                        exact cs_w98 ⟨n - 34900, hr⟩
                                                                                                                                                                                                      ·
                                                                                                                                                                                                        have hr : n - 34950 < 50 := by omega
                                                                                                                                                                                                        have heq : n = (n - 34950) + 34950 := by omega
                                                                                                                                                                                                        rw [heq]
                                                                                                                                                                                                        exact cs_w99 ⟨n - 34950, hr⟩

theorem centF_lt_range : ∀ n, 30000 ≤ n → n < 35000 → centF n < 23 := by
  intro n hlo hhi
  by_cases h0 : n < 30050
  · have hr : n - 30000 < 50 := by omega
    have heq : n = (n - 30000) + 30000 := by omega
    rw [heq]
    exact cl_w0 ⟨n - 30000, hr⟩
  ·
    by_cases h1 : n < 30100
    · have hr : n - 30050 < 50 := by omega
      have heq : n = (n - 30050) + 30050 := by omega
      rw [heq]
      exact cl_w1 ⟨n - 30050, hr⟩
    ·
      by_cases h2 : n < 30150
      · have hr : n - 30100 < 50 := by omega
        have heq : n = (n - 30100) + 30100 := by omega
        rw [heq]
        exact cl_w2 ⟨n - 30100, hr⟩
      ·
        by_cases h3 : n < 30200
        · have hr : n - 30150 < 50 := by omega
          have heq : n = (n - 30150) + 30150 := by omega
          rw [heq]
          exact cl_w3 ⟨n - 30150, hr⟩
        ·
          by_cases h4 : n < 30250
          · have hr : n - 30200 < 50 := by omega
            have heq : n = (n - 30200) + 30200 := by omega
            rw [heq]
            exact cl_w4 ⟨n - 30200, hr⟩
          ·
            by_cases h5 : n < 30300
            · have hr : n - 30250 < 50 := by omega
              have heq : n = (n - 30250) + 30250 := by omega
              rw [heq]
              exact cl_w5 ⟨n - 30250, hr⟩
            ·
              by_cases h6 : n < 30350
              · have hr : n - 30300 < 50 := by omega
                have heq : n = (n - 30300) + 30300 := by omega
                rw [heq]
                exact cl_w6 ⟨n - 30300, hr⟩
              ·
                by_cases h7 : n < 30400
                · have hr : n - 30350 < 50 := by omega
                  have heq : n = (n - 30350) + 30350 := by omega
                  rw [heq]
                  exact cl_w7 ⟨n - 30350, hr⟩
                ·
                  by_cases h8 : n < 30450
                  · have hr : n - 30400 < 50 := by omega
                    have heq : n = (n - 30400) + 30400 := by omega
                    rw [heq]
                    exact cl_w8 ⟨n - 30400, hr⟩
                  ·
                    by_cases h9 : n < 30500
                    · have hr : n - 30450 < 50 := by omega
                      have heq : n = (n - 30450) + 30450 := by omega
                      rw [heq]
                      exact cl_w9 ⟨n - 30450, hr⟩
                    ·
                      by_cases h10 : n < 30550
                      · have hr : n - 30500 < 50 := by omega
                        have heq : n = (n - 30500) + 30500 := by omega
                        rw [heq]
                        exact cl_w10 ⟨n - 30500, hr⟩
                      ·
                        by_cases h11 : n < 30600
                        · have hr : n - 30550 < 50 := by omega
                          have heq : n = (n - 30550) + 30550 := by omega
                          rw [heq]
                          exact cl_w11 ⟨n - 30550, hr⟩
                        ·
                          by_cases h12 : n < 30650
                          · have hr : n - 30600 < 50 := by omega
                            have heq : n = (n - 30600) + 30600 := by omega
                            rw [heq]
                            exact cl_w12 ⟨n - 30600, hr⟩
                          ·
                            by_cases h13 : n < 30700
                            · have hr : n - 30650 < 50 := by omega
                              have heq : n = (n - 30650) + 30650 := by omega
                              rw [heq]
                              exact cl_w13 ⟨n - 30650, hr⟩
                            ·
                              by_cases h14 : n < 30750
                              · have hr : n - 30700 < 50 := by omega
                                have heq : n = (n - 30700) + 30700 := by omega
                                rw [heq]
                                exact cl_w14 ⟨n - 30700, hr⟩
                              ·
                                by_cases h15 : n < 30800
                                · have hr : n - 30750 < 50 := by omega
                                  have heq : n = (n - 30750) + 30750 := by omega
                                  rw [heq]
                                  exact cl_w15 ⟨n - 30750, hr⟩
                                ·
                                  by_cases h16 : n < 30850
                                  · have hr : n - 30800 < 50 := by omega
                                    have heq : n = (n - 30800) + 30800 := by omega
                                    rw [heq]
                                    exact cl_w16 ⟨n - 30800, hr⟩
                                  ·
                                    by_cases h17 : n < 30900
                                    · have hr : n - 30850 < 50 := by omega
                                      have heq : n = (n - 30850) + 30850 := by omega
                                      rw [heq]
                                      exact cl_w17 ⟨n - 30850, hr⟩
                                    ·
                                      by_cases h18 : n < 30950
                                      · have hr : n - 30900 < 50 := by omega
                                        have heq : n = (n - 30900) + 30900 := by omega
                                        rw [heq]
                                        exact cl_w18 ⟨n - 30900, hr⟩
                                      ·
                                        by_cases h19 : n < 31000
                                        · have hr : n - 30950 < 50 := by omega
                                          have heq : n = (n - 30950) + 30950 := by omega
                                          rw [heq]
                                          exact cl_w19 ⟨n - 30950, hr⟩
                                        ·
                                          by_cases h20 : n < 31050
                                          · have hr : n - 31000 < 50 := by omega
                                            have heq : n = (n - 31000) + 31000 := by omega
                                            rw [heq]
                                            exact cl_w20 ⟨n - 31000, hr⟩
                                          ·
                                            by_cases h21 : n < 31100
                                            · have hr : n - 31050 < 50 := by omega
                                              have heq : n = (n - 31050) + 31050 := by omega
                                              rw [heq]
                                              exact cl_w21 ⟨n - 31050, hr⟩
                                            ·
                                              by_cases h22 : n < 31150
                                              · have hr : n - 31100 < 50 := by omega
                                                have heq : n = (n - 31100) + 31100 := by omega
                                                rw [heq]
                                                exact cl_w22 ⟨n - 31100, hr⟩
                                              ·
                                                by_cases h23 : n < 31200
                                                · have hr : n - 31150 < 50 := by omega
                                                  have heq : n = (n - 31150) + 31150 := by omega
                                                  rw [heq]
                                                  exact cl_w23 ⟨n - 31150, hr⟩
                                                ·
                                                  by_cases h24 : n < 31250
                                                  · have hr : n - 31200 < 50 := by omega
                                                    have heq : n = (n - 31200) + 31200 := by omega
                                                    rw [heq]
                                                    exact cl_w24 ⟨n - 31200, hr⟩
                                                  ·
                                                    by_cases h25 : n < 31300
                                                    · have hr : n - 31250 < 50 := by omega
                                                      have heq : n = (n - 31250) + 31250 := by omega
                                                      rw [heq]
                                                      exact cl_w25 ⟨n - 31250, hr⟩
                                                    ·
                                                      by_cases h26 : n < 31350
                                                      · have hr : n - 31300 < 50 := by omega
                                                        have heq : n = (n - 31300) + 31300 := by omega
                                                        rw [heq]
                                                        exact cl_w26 ⟨n - 31300, hr⟩
                                                      ·
                                                        by_cases h27 : n < 31400
                                                        · have hr : n - 31350 < 50 := by omega
                                                          have heq : n = (n - 31350) + 31350 := by omega
                                                          rw [heq]
                                                          exact cl_w27 ⟨n - 31350, hr⟩
                                                        ·
                                                          by_cases h28 : n < 31450
                                                          · have hr : n - 31400 < 50 := by omega
                                                            have heq : n = (n - 31400) + 31400 := by omega
                                                            rw [heq]
                                                            exact cl_w28 ⟨n - 31400, hr⟩
                                                          ·
                                                            by_cases h29 : n < 31500
                                                            · have hr : n - 31450 < 50 := by omega
                                                              have heq : n = (n - 31450) + 31450 := by omega
                                                              rw [heq]
                                                              exact cl_w29 ⟨n - 31450, hr⟩
                                                            ·
                                                              by_cases h30 : n < 31550
                                                              · have hr : n - 31500 < 50 := by omega
                                                                have heq : n = (n - 31500) + 31500 := by omega
                                                                rw [heq]
                                                                exact cl_w30 ⟨n - 31500, hr⟩
                                                              ·
                                                                by_cases h31 : n < 31600
                                                                · have hr : n - 31550 < 50 := by omega
                                                                  have heq : n = (n - 31550) + 31550 := by omega
                                                                  rw [heq]
                                                                  exact cl_w31 ⟨n - 31550, hr⟩
                                                                ·
                                                                  by_cases h32 : n < 31650
                                                                  · have hr : n - 31600 < 50 := by omega
                                                                    have heq : n = (n - 31600) + 31600 := by omega
                                                                    rw [heq]
                                                                    exact cl_w32 ⟨n - 31600, hr⟩
                                                                  ·
                                                                    by_cases h33 : n < 31700
                                                                    · have hr : n - 31650 < 50 := by omega
                                                                      have heq : n = (n - 31650) + 31650 := by omega
                                                                      rw [heq]
                                                                      exact cl_w33 ⟨n - 31650, hr⟩
                                                                    ·
                                                                      by_cases h34 : n < 31750
                                                                      · have hr : n - 31700 < 50 := by omega
                                                                        have heq : n = (n - 31700) + 31700 := by omega
                                                                        rw [heq]
                                                                        exact cl_w34 ⟨n - 31700, hr⟩
                                                                      ·
                                                                        by_cases h35 : n < 31800
                                                                        · have hr : n - 31750 < 50 := by omega
                                                                          have heq : n = (n - 31750) + 31750 := by omega
                                                                          rw [heq]
                                                                          exact cl_w35 ⟨n - 31750, hr⟩
                                                                        ·
                                                                          by_cases h36 : n < 31850
                                                                          · have hr : n - 31800 < 50 := by omega
                                                                            have heq : n = (n - 31800) + 31800 := by omega
                                                                            rw [heq]
                                                                            exact cl_w36 ⟨n - 31800, hr⟩
                                                                          ·
                                                                            by_cases h37 : n < 31900
                                                                            · have hr : n - 31850 < 50 := by omega
                                                                              have heq : n = (n - 31850) + 31850 := by omega
                                                                              rw [heq]
                                                                              exact cl_w37 ⟨n - 31850, hr⟩
                                                                            ·
                                                                              by_cases h38 : n < 31950
                                                                              · have hr : n - 31900 < 50 := by omega
                                                                                have heq : n = (n - 31900) + 31900 := by omega
                                                                                rw [heq]
                                                                                exact cl_w38 ⟨n - 31900, hr⟩
                                                                              ·
                                                                                by_cases h39 : n < 32000
                                                                                · have hr : n - 31950 < 50 := by omega
                                                                                  have heq : n = (n - 31950) + 31950 := by omega
                                                                                  rw [heq]
                                                                                  exact cl_w39 ⟨n - 31950, hr⟩
                                                                                ·
                                                                                  by_cases h40 : n < 32050
                                                                                  · have hr : n - 32000 < 50 := by omega
                                                                                    have heq : n = (n - 32000) + 32000 := by omega
                                                                                    rw [heq]
                                                                                    exact cl_w40 ⟨n - 32000, hr⟩
                                                                                  ·
                                                                                    by_cases h41 : n < 32100
                                                                                    · have hr : n - 32050 < 50 := by omega
                                                                                      have heq : n = (n - 32050) + 32050 := by omega
                                                                                      rw [heq]
                                                                                      exact cl_w41 ⟨n - 32050, hr⟩
                                                                                    ·
                                                                                      by_cases h42 : n < 32150
                                                                                      · have hr : n - 32100 < 50 := by omega
                                                                                        have heq : n = (n - 32100) + 32100 := by omega
                                                                                        rw [heq]
                                                                                        exact cl_w42 ⟨n - 32100, hr⟩
                                                                                      ·
                                                                                        by_cases h43 : n < 32200
                                                                                        · have hr : n - 32150 < 50 := by omega
                                                                                          have heq : n = (n - 32150) + 32150 := by omega
                                                                                          rw [heq]
                                                                                          exact cl_w43 ⟨n - 32150, hr⟩
                                                                                        ·
                                                                                          by_cases h44 : n < 32250
                                                                                          · have hr : n - 32200 < 50 := by omega
                                                                                            have heq : n = (n - 32200) + 32200 := by omega
                                                                                            rw [heq]
                                                                                            exact cl_w44 ⟨n - 32200, hr⟩
                                                                                          ·
                                                                                            by_cases h45 : n < 32300
                                                                                            · have hr : n - 32250 < 50 := by omega
                                                                                              have heq : n = (n - 32250) + 32250 := by omega
                                                                                              rw [heq]
                                                                                              exact cl_w45 ⟨n - 32250, hr⟩
                                                                                            ·
                                                                                              by_cases h46 : n < 32350
                                                                                              · have hr : n - 32300 < 50 := by omega
                                                                                                have heq : n = (n - 32300) + 32300 := by omega
                                                                                                rw [heq]
                                                                                                exact cl_w46 ⟨n - 32300, hr⟩
                                                                                              ·
                                                                                                by_cases h47 : n < 32400
                                                                                                · have hr : n - 32350 < 50 := by omega
                                                                                                  have heq : n = (n - 32350) + 32350 := by omega
                                                                                                  rw [heq]
                                                                                                  exact cl_w47 ⟨n - 32350, hr⟩
                                                                                                ·
                                                                                                  by_cases h48 : n < 32450
                                                                                                  · have hr : n - 32400 < 50 := by omega
                                                                                                    have heq : n = (n - 32400) + 32400 := by omega
                                                                                                    rw [heq]
                                                                                                    exact cl_w48 ⟨n - 32400, hr⟩
                                                                                                  ·
                                                                                                    by_cases h49 : n < 32500
                                                                                                    · have hr : n - 32450 < 50 := by omega
                                                                                                      have heq : n = (n - 32450) + 32450 := by omega
                                                                                                      rw [heq]
                                                                                                      exact cl_w49 ⟨n - 32450, hr⟩
                                                                                                    ·
                                                                                                      by_cases h50 : n < 32550
                                                                                                      · have hr : n - 32500 < 50 := by omega
                                                                                                        have heq : n = (n - 32500) + 32500 := by omega
                                                                                                        rw [heq]
                                                                                                        exact cl_w50 ⟨n - 32500, hr⟩
                                                                                                      ·
                                                                                                        by_cases h51 : n < 32600
                                                                                                        · have hr : n - 32550 < 50 := by omega
                                                                                                          have heq : n = (n - 32550) + 32550 := by omega
                                                                                                          rw [heq]
                                                                                                          exact cl_w51 ⟨n - 32550, hr⟩
                                                                                                        ·
                                                                                                          by_cases h52 : n < 32650
                                                                                                          · have hr : n - 32600 < 50 := by omega
                                                                                                            have heq : n = (n - 32600) + 32600 := by omega
                                                                                                            rw [heq]
                                                                                                            exact cl_w52 ⟨n - 32600, hr⟩
                                                                                                          ·
                                                                                                            by_cases h53 : n < 32700
                                                                                                            · have hr : n - 32650 < 50 := by omega
                                                                                                              have heq : n = (n - 32650) + 32650 := by omega
                                                                                                              rw [heq]
                                                                                                              exact cl_w53 ⟨n - 32650, hr⟩
                                                                                                            ·
                                                                                                              by_cases h54 : n < 32750
                                                                                                              · have hr : n - 32700 < 50 := by omega
                                                                                                                have heq : n = (n - 32700) + 32700 := by omega
                                                                                                                rw [heq]
                                                                                                                exact cl_w54 ⟨n - 32700, hr⟩
                                                                                                              ·
                                                                                                                by_cases h55 : n < 32800
                                                                                                                · have hr : n - 32750 < 50 := by omega
                                                                                                                  have heq : n = (n - 32750) + 32750 := by omega
                                                                                                                  rw [heq]
                                                                                                                  exact cl_w55 ⟨n - 32750, hr⟩
                                                                                                                ·
                                                                                                                  by_cases h56 : n < 32850
                                                                                                                  · have hr : n - 32800 < 50 := by omega
                                                                                                                    have heq : n = (n - 32800) + 32800 := by omega
                                                                                                                    rw [heq]
                                                                                                                    exact cl_w56 ⟨n - 32800, hr⟩
                                                                                                                  ·
                                                                                                                    by_cases h57 : n < 32900
                                                                                                                    · have hr : n - 32850 < 50 := by omega
                                                                                                                      have heq : n = (n - 32850) + 32850 := by omega
                                                                                                                      rw [heq]
                                                                                                                      exact cl_w57 ⟨n - 32850, hr⟩
                                                                                                                    ·
                                                                                                                      by_cases h58 : n < 32950
                                                                                                                      · have hr : n - 32900 < 50 := by omega
                                                                                                                        have heq : n = (n - 32900) + 32900 := by omega
                                                                                                                        rw [heq]
                                                                                                                        exact cl_w58 ⟨n - 32900, hr⟩
                                                                                                                      ·
                                                                                                                        by_cases h59 : n < 33000
                                                                                                                        · have hr : n - 32950 < 50 := by omega
                                                                                                                          have heq : n = (n - 32950) + 32950 := by omega
                                                                                                                          rw [heq]
                                                                                                                          exact cl_w59 ⟨n - 32950, hr⟩
                                                                                                                        ·
                                                                                                                          by_cases h60 : n < 33050
                                                                                                                          · have hr : n - 33000 < 50 := by omega
                                                                                                                            have heq : n = (n - 33000) + 33000 := by omega
                                                                                                                            rw [heq]
                                                                                                                            exact cl_w60 ⟨n - 33000, hr⟩
                                                                                                                          ·
                                                                                                                            by_cases h61 : n < 33100
                                                                                                                            · have hr : n - 33050 < 50 := by omega
                                                                                                                              have heq : n = (n - 33050) + 33050 := by omega
                                                                                                                              rw [heq]
                                                                                                                              exact cl_w61 ⟨n - 33050, hr⟩
                                                                                                                            ·
                                                                                                                              by_cases h62 : n < 33150
                                                                                                                              · have hr : n - 33100 < 50 := by omega
                                                                                                                                have heq : n = (n - 33100) + 33100 := by omega
                                                                                                                                rw [heq]
                                                                                                                                exact cl_w62 ⟨n - 33100, hr⟩
                                                                                                                              ·
                                                                                                                                by_cases h63 : n < 33200
                                                                                                                                · have hr : n - 33150 < 50 := by omega
                                                                                                                                  have heq : n = (n - 33150) + 33150 := by omega
                                                                                                                                  rw [heq]
                                                                                                                                  exact cl_w63 ⟨n - 33150, hr⟩
                                                                                                                                ·
                                                                                                                                  by_cases h64 : n < 33250
                                                                                                                                  · have hr : n - 33200 < 50 := by omega
                                                                                                                                    have heq : n = (n - 33200) + 33200 := by omega
                                                                                                                                    rw [heq]
                                                                                                                                    exact cl_w64 ⟨n - 33200, hr⟩
                                                                                                                                  ·
                                                                                                                                    by_cases h65 : n < 33300
                                                                                                                                    · have hr : n - 33250 < 50 := by omega
                                                                                                                                      have heq : n = (n - 33250) + 33250 := by omega
                                                                                                                                      rw [heq]
                                                                                                                                      exact cl_w65 ⟨n - 33250, hr⟩
                                                                                                                                    ·
                                                                                                                                      by_cases h66 : n < 33350
                                                                                                                                      · have hr : n - 33300 < 50 := by omega
                                                                                                                                        have heq : n = (n - 33300) + 33300 := by omega
                                                                                                                                        rw [heq]
                                                                                                                                        exact cl_w66 ⟨n - 33300, hr⟩
                                                                                                                                      ·
                                                                                                                                        by_cases h67 : n < 33400
                                                                                                                                        · have hr : n - 33350 < 50 := by omega
                                                                                                                                          have heq : n = (n - 33350) + 33350 := by omega
                                                                                                                                          rw [heq]
                                                                                                                                          exact cl_w67 ⟨n - 33350, hr⟩
                                                                                                                                        ·
                                                                                                                                          by_cases h68 : n < 33450
                                                                                                                                          · have hr : n - 33400 < 50 := by omega
                                                                                                                                            have heq : n = (n - 33400) + 33400 := by omega
                                                                                                                                            rw [heq]
                                                                                                                                            exact cl_w68 ⟨n - 33400, hr⟩
                                                                                                                                          ·
                                                                                                                                            by_cases h69 : n < 33500
                                                                                                                                            · have hr : n - 33450 < 50 := by omega
                                                                                                                                              have heq : n = (n - 33450) + 33450 := by omega
                                                                                                                                              rw [heq]
                                                                                                                                              exact cl_w69 ⟨n - 33450, hr⟩
                                                                                                                                            ·
                                                                                                                                              by_cases h70 : n < 33550
                                                                                                                                              · have hr : n - 33500 < 50 := by omega
                                                                                                                                                have heq : n = (n - 33500) + 33500 := by omega
                                                                                                                                                rw [heq]
                                                                                                                                                exact cl_w70 ⟨n - 33500, hr⟩
                                                                                                                                              ·
                                                                                                                                                by_cases h71 : n < 33600
                                                                                                                                                · have hr : n - 33550 < 50 := by omega
                                                                                                                                                  have heq : n = (n - 33550) + 33550 := by omega
                                                                                                                                                  rw [heq]
                                                                                                                                                  exact cl_w71 ⟨n - 33550, hr⟩
                                                                                                                                                ·
                                                                                                                                                  by_cases h72 : n < 33650
                                                                                                                                                  · have hr : n - 33600 < 50 := by omega
                                                                                                                                                    have heq : n = (n - 33600) + 33600 := by omega
                                                                                                                                                    rw [heq]
                                                                                                                                                    exact cl_w72 ⟨n - 33600, hr⟩
                                                                                                                                                  ·
                                                                                                                                                    by_cases h73 : n < 33700
                                                                                                                                                    · have hr : n - 33650 < 50 := by omega
                                                                                                                                                      have heq : n = (n - 33650) + 33650 := by omega
                                                                                                                                                      rw [heq]
                                                                                                                                                      exact cl_w73 ⟨n - 33650, hr⟩
                                                                                                                                                    ·
                                                                                                                                                      by_cases h74 : n < 33750
                                                                                                                                                      · have hr : n - 33700 < 50 := by omega
                                                                                                                                                        have heq : n = (n - 33700) + 33700 := by omega
                                                                                                                                                        rw [heq]
                                                                                                                                                        exact cl_w74 ⟨n - 33700, hr⟩
                                                                                                                                                      ·
                                                                                                                                                        by_cases h75 : n < 33800
                                                                                                                                                        · have hr : n - 33750 < 50 := by omega
                                                                                                                                                          have heq : n = (n - 33750) + 33750 := by omega
                                                                                                                                                          rw [heq]
                                                                                                                                                          exact cl_w75 ⟨n - 33750, hr⟩
                                                                                                                                                        ·
                                                                                                                                                          by_cases h76 : n < 33850
                                                                                                                                                          · have hr : n - 33800 < 50 := by omega
                                                                                                                                                            have heq : n = (n - 33800) + 33800 := by omega
                                                                                                                                                            rw [heq]
                                                                                                                                                            exact cl_w76 ⟨n - 33800, hr⟩
                                                                                                                                                          ·
                                                                                                                                                            by_cases h77 : n < 33900
                                                                                                                                                            · have hr : n - 33850 < 50 := by omega
                                                                                                                                                              have heq : n = (n - 33850) + 33850 := by omega
                                                                                                                                                              rw [heq]
                                                                                                                                                              exact cl_w77 ⟨n - 33850, hr⟩
                                                                                                                                                            ·
                                                                                                                                                              by_cases h78 : n < 33950
                                                                                                                                                              · have hr : n - 33900 < 50 := by omega
                                                                                                                                                                have heq : n = (n - 33900) + 33900 := by omega
                                                                                                                                                                rw [heq]
                                                                                                                                                                exact cl_w78 ⟨n - 33900, hr⟩
                                                                                                                                                              ·
                                                                                                                                                                by_cases h79 : n < 34000
                                                                                                                                                                · have hr : n - 33950 < 50 := by omega
                                                                                                                                                                  have heq : n = (n - 33950) + 33950 := by omega
                                                                                                                                                                  rw [heq]
                                                                                                                                                                  exact cl_w79 ⟨n - 33950, hr⟩
                                                                                                                                                                ·
                                                                                                                                                                  by_cases h80 : n < 34050
                                                                                                                                                                  · have hr : n - 34000 < 50 := by omega
                                                                                                                                                                    have heq : n = (n - 34000) + 34000 := by omega
                                                                                                                                                                    rw [heq]
                                                                                                                                                                    exact cl_w80 ⟨n - 34000, hr⟩
                                                                                                                                                                  ·
                                                                                                                                                                    by_cases h81 : n < 34100
                                                                                                                                                                    · have hr : n - 34050 < 50 := by omega
                                                                                                                                                                      have heq : n = (n - 34050) + 34050 := by omega
                                                                                                                                                                      rw [heq]
                                                                                                                                                                      exact cl_w81 ⟨n - 34050, hr⟩
                                                                                                                                                                    ·
                                                                                                                                                                      by_cases h82 : n < 34150
                                                                                                                                                                      · have hr : n - 34100 < 50 := by omega
                                                                                                                                                                        have heq : n = (n - 34100) + 34100 := by omega
                                                                                                                                                                        rw [heq]
                                                                                                                                                                        exact cl_w82 ⟨n - 34100, hr⟩
                                                                                                                                                                      ·
                                                                                                                                                                        by_cases h83 : n < 34200
                                                                                                                                                                        · have hr : n - 34150 < 50 := by omega
                                                                                                                                                                          have heq : n = (n - 34150) + 34150 := by omega
                                                                                                                                                                          rw [heq]
                                                                                                                                                                          exact cl_w83 ⟨n - 34150, hr⟩
                                                                                                                                                                        ·
                                                                                                                                                                          by_cases h84 : n < 34250
                                                                                                                                                                          · have hr : n - 34200 < 50 := by omega
                                                                                                                                                                            have heq : n = (n - 34200) + 34200 := by omega
                                                                                                                                                                            rw [heq]
                                                                                                                                                                            exact cl_w84 ⟨n - 34200, hr⟩
                                                                                                                                                                          ·
                                                                                                                                                                            by_cases h85 : n < 34300
                                                                                                                                                                            · have hr : n - 34250 < 50 := by omega
                                                                                                                                                                              have heq : n = (n - 34250) + 34250 := by omega
                                                                                                                                                                              rw [heq]
                                                                                                                                                                              exact cl_w85 ⟨n - 34250, hr⟩
                                                                                                                                                                            ·
                                                                                                                                                                              by_cases h86 : n < 34350
                                                                                                                                                                              · have hr : n - 34300 < 50 := by omega
                                                                                                                                                                                have heq : n = (n - 34300) + 34300 := by omega
                                                                                                                                                                                rw [heq]
                                                                                                                                                                                exact cl_w86 ⟨n - 34300, hr⟩
                                                                                                                                                                              ·
                                                                                                                                                                                by_cases h87 : n < 34400
                                                                                                                                                                                · have hr : n - 34350 < 50 := by omega
                                                                                                                                                                                  have heq : n = (n - 34350) + 34350 := by omega
                                                                                                                                                                                  rw [heq]
                                                                                                                                                                                  exact cl_w87 ⟨n - 34350, hr⟩
                                                                                                                                                                                ·
                                                                                                                                                                                  by_cases h88 : n < 34450
                                                                                                                                                                                  · have hr : n - 34400 < 50 := by omega
                                                                                                                                                                                    have heq : n = (n - 34400) + 34400 := by omega
                                                                                                                                                                                    rw [heq]
                                                                                                                                                                                    exact cl_w88 ⟨n - 34400, hr⟩
                                                                                                                                                                                  ·
                                                                                                                                                                                    by_cases h89 : n < 34500
                                                                                                                                                                                    · have hr : n - 34450 < 50 := by omega
                                                                                                                                                                                      have heq : n = (n - 34450) + 34450 := by omega
                                                                                                                                                                                      rw [heq]
                                                                                                                                                                                      exact cl_w89 ⟨n - 34450, hr⟩
                                                                                                                                                                                    ·
                                                                                                                                                                                      by_cases h90 : n < 34550
                                                                                                                                                                                      · have hr : n - 34500 < 50 := by omega
                                                                                                                                                                                        have heq : n = (n - 34500) + 34500 := by omega
                                                                                                                                                                                        rw [heq]
                                                                                                                                                                                        exact cl_w90 ⟨n - 34500, hr⟩
                                                                                                                                                                                      ·
                                                                                                                                                                                        by_cases h91 : n < 34600
                                                                                                                                                                                        · have hr : n - 34550 < 50 := by omega
                                                                                                                                                                                          have heq : n = (n - 34550) + 34550 := by omega
                                                                                                                                                                                          rw [heq]
                                                                                                                                                                                          exact cl_w91 ⟨n - 34550, hr⟩
                                                                                                                                                                                        ·
                                                                                                                                                                                          by_cases h92 : n < 34650
                                                                                                                                                                                          · have hr : n - 34600 < 50 := by omega
                                                                                                                                                                                            have heq : n = (n - 34600) + 34600 := by omega
                                                                                                                                                                                            rw [heq]
                                                                                                                                                                                            exact cl_w92 ⟨n - 34600, hr⟩
                                                                                                                                                                                          ·
                                                                                                                                                                                            by_cases h93 : n < 34700
                                                                                                                                                                                            · have hr : n - 34650 < 50 := by omega
                                                                                                                                                                                              have heq : n = (n - 34650) + 34650 := by omega
                                                                                                                                                                                              rw [heq]
                                                                                                                                                                                              exact cl_w93 ⟨n - 34650, hr⟩
                                                                                                                                                                                            ·
                                                                                                                                                                                              by_cases h94 : n < 34750
                                                                                                                                                                                              · have hr : n - 34700 < 50 := by omega
                                                                                                                                                                                                have heq : n = (n - 34700) + 34700 := by omega
                                                                                                                                                                                                rw [heq]
                                                                                                                                                                                                exact cl_w94 ⟨n - 34700, hr⟩
                                                                                                                                                                                              ·
                                                                                                                                                                                                by_cases h95 : n < 34800
                                                                                                                                                                                                · have hr : n - 34750 < 50 := by omega
                                                                                                                                                                                                  have heq : n = (n - 34750) + 34750 := by omega
                                                                                                                                                                                                  rw [heq]
                                                                                                                                                                                                  exact cl_w95 ⟨n - 34750, hr⟩
                                                                                                                                                                                                ·
                                                                                                                                                                                                  by_cases h96 : n < 34850
                                                                                                                                                                                                  · have hr : n - 34800 < 50 := by omega
                                                                                                                                                                                                    have heq : n = (n - 34800) + 34800 := by omega
                                                                                                                                                                                                    rw [heq]
                                                                                                                                                                                                    exact cl_w96 ⟨n - 34800, hr⟩
                                                                                                                                                                                                  ·
                                                                                                                                                                                                    by_cases h97 : n < 34900
                                                                                                                                                                                                    · have hr : n - 34850 < 50 := by omega
                                                                                                                                                                                                      have heq : n = (n - 34850) + 34850 := by omega
                                                                                                                                                                                                      rw [heq]
                                                                                                                                                                                                      exact cl_w97 ⟨n - 34850, hr⟩
                                                                                                                                                                                                    ·
                                                                                                                                                                                                      by_cases h98 : n < 34950
                                                                                                                                                                                                      · have hr : n - 34900 < 50 := by omega
                                                                                                                                                                                                        have heq : n = (n - 34900) + 34900 := by omega
                                                                                                                                                                                                        rw [heq]
                                                                                                                                                                                                        exact cl_w98 ⟨n - 34900, hr⟩
                                                                                                                                                                                                      ·
                                                                                                                                                                                                        have hr : n - 34950 < 50 := by omega
                                                                                                                                                                                                        have heq : n = (n - 34950) + 34950 := by omega
                                                                                                                                                                                                        rw [heq]
                                                                                                                                                                                                        exact cl_w99 ⟨n - 34950, hr⟩

theorem densSupG_lt_range : ∀ n, 30000 ≤ n → n < 35000 → densSupG n < 2 ^ 1771 := by
  intro n hlo hhi
  by_cases h0 : n < 30050
  · have hr : n - 30000 < 50 := by omega
    have heq : n = (n - 30000) + 30000 := by omega
    rw [heq]
    exact bd_w0 ⟨n - 30000, hr⟩
  ·
    by_cases h1 : n < 30100
    · have hr : n - 30050 < 50 := by omega
      have heq : n = (n - 30050) + 30050 := by omega
      rw [heq]
      exact bd_w1 ⟨n - 30050, hr⟩
    ·
      by_cases h2 : n < 30150
      · have hr : n - 30100 < 50 := by omega
        have heq : n = (n - 30100) + 30100 := by omega
        rw [heq]
        exact bd_w2 ⟨n - 30100, hr⟩
      ·
        by_cases h3 : n < 30200
        · have hr : n - 30150 < 50 := by omega
          have heq : n = (n - 30150) + 30150 := by omega
          rw [heq]
          exact bd_w3 ⟨n - 30150, hr⟩
        ·
          by_cases h4 : n < 30250
          · have hr : n - 30200 < 50 := by omega
            have heq : n = (n - 30200) + 30200 := by omega
            rw [heq]
            exact bd_w4 ⟨n - 30200, hr⟩
          ·
            by_cases h5 : n < 30300
            · have hr : n - 30250 < 50 := by omega
              have heq : n = (n - 30250) + 30250 := by omega
              rw [heq]
              exact bd_w5 ⟨n - 30250, hr⟩
            ·
              by_cases h6 : n < 30350
              · have hr : n - 30300 < 50 := by omega
                have heq : n = (n - 30300) + 30300 := by omega
                rw [heq]
                exact bd_w6 ⟨n - 30300, hr⟩
              ·
                by_cases h7 : n < 30400
                · have hr : n - 30350 < 50 := by omega
                  have heq : n = (n - 30350) + 30350 := by omega
                  rw [heq]
                  exact bd_w7 ⟨n - 30350, hr⟩
                ·
                  by_cases h8 : n < 30450
                  · have hr : n - 30400 < 50 := by omega
                    have heq : n = (n - 30400) + 30400 := by omega
                    rw [heq]
                    exact bd_w8 ⟨n - 30400, hr⟩
                  ·
                    by_cases h9 : n < 30500
                    · have hr : n - 30450 < 50 := by omega
                      have heq : n = (n - 30450) + 30450 := by omega
                      rw [heq]
                      exact bd_w9 ⟨n - 30450, hr⟩
                    ·
                      by_cases h10 : n < 30550
                      · have hr : n - 30500 < 50 := by omega
                        have heq : n = (n - 30500) + 30500 := by omega
                        rw [heq]
                        exact bd_w10 ⟨n - 30500, hr⟩
                      ·
                        by_cases h11 : n < 30600
                        · have hr : n - 30550 < 50 := by omega
                          have heq : n = (n - 30550) + 30550 := by omega
                          rw [heq]
                          exact bd_w11 ⟨n - 30550, hr⟩
                        ·
                          by_cases h12 : n < 30650
                          · have hr : n - 30600 < 50 := by omega
                            have heq : n = (n - 30600) + 30600 := by omega
                            rw [heq]
                            exact bd_w12 ⟨n - 30600, hr⟩
                          ·
                            by_cases h13 : n < 30700
                            · have hr : n - 30650 < 50 := by omega
                              have heq : n = (n - 30650) + 30650 := by omega
                              rw [heq]
                              exact bd_w13 ⟨n - 30650, hr⟩
                            ·
                              by_cases h14 : n < 30750
                              · have hr : n - 30700 < 50 := by omega
                                have heq : n = (n - 30700) + 30700 := by omega
                                rw [heq]
                                exact bd_w14 ⟨n - 30700, hr⟩
                              ·
                                by_cases h15 : n < 30800
                                · have hr : n - 30750 < 50 := by omega
                                  have heq : n = (n - 30750) + 30750 := by omega
                                  rw [heq]
                                  exact bd_w15 ⟨n - 30750, hr⟩
                                ·
                                  by_cases h16 : n < 30850
                                  · have hr : n - 30800 < 50 := by omega
                                    have heq : n = (n - 30800) + 30800 := by omega
                                    rw [heq]
                                    exact bd_w16 ⟨n - 30800, hr⟩
                                  ·
                                    by_cases h17 : n < 30900
                                    · have hr : n - 30850 < 50 := by omega
                                      have heq : n = (n - 30850) + 30850 := by omega
                                      rw [heq]
                                      exact bd_w17 ⟨n - 30850, hr⟩
                                    ·
                                      by_cases h18 : n < 30950
                                      · have hr : n - 30900 < 50 := by omega
                                        have heq : n = (n - 30900) + 30900 := by omega
                                        rw [heq]
                                        exact bd_w18 ⟨n - 30900, hr⟩
                                      ·
                                        by_cases h19 : n < 31000
                                        · have hr : n - 30950 < 50 := by omega
                                          have heq : n = (n - 30950) + 30950 := by omega
                                          rw [heq]
                                          exact bd_w19 ⟨n - 30950, hr⟩
                                        ·
                                          by_cases h20 : n < 31050
                                          · have hr : n - 31000 < 50 := by omega
                                            have heq : n = (n - 31000) + 31000 := by omega
                                            rw [heq]
                                            exact bd_w20 ⟨n - 31000, hr⟩
                                          ·
                                            by_cases h21 : n < 31100
                                            · have hr : n - 31050 < 50 := by omega
                                              have heq : n = (n - 31050) + 31050 := by omega
                                              rw [heq]
                                              exact bd_w21 ⟨n - 31050, hr⟩
                                            ·
                                              by_cases h22 : n < 31150
                                              · have hr : n - 31100 < 50 := by omega
                                                have heq : n = (n - 31100) + 31100 := by omega
                                                rw [heq]
                                                exact bd_w22 ⟨n - 31100, hr⟩
                                              ·
                                                by_cases h23 : n < 31200
                                                · have hr : n - 31150 < 50 := by omega
                                                  have heq : n = (n - 31150) + 31150 := by omega
                                                  rw [heq]
                                                  exact bd_w23 ⟨n - 31150, hr⟩
                                                ·
                                                  by_cases h24 : n < 31250
                                                  · have hr : n - 31200 < 50 := by omega
                                                    have heq : n = (n - 31200) + 31200 := by omega
                                                    rw [heq]
                                                    exact bd_w24 ⟨n - 31200, hr⟩
                                                  ·
                                                    by_cases h25 : n < 31300
                                                    · have hr : n - 31250 < 50 := by omega
                                                      have heq : n = (n - 31250) + 31250 := by omega
                                                      rw [heq]
                                                      exact bd_w25 ⟨n - 31250, hr⟩
                                                    ·
                                                      by_cases h26 : n < 31350
                                                      · have hr : n - 31300 < 50 := by omega
                                                        have heq : n = (n - 31300) + 31300 := by omega
                                                        rw [heq]
                                                        exact bd_w26 ⟨n - 31300, hr⟩
                                                      ·
                                                        by_cases h27 : n < 31400
                                                        · have hr : n - 31350 < 50 := by omega
                                                          have heq : n = (n - 31350) + 31350 := by omega
                                                          rw [heq]
                                                          exact bd_w27 ⟨n - 31350, hr⟩
                                                        ·
                                                          by_cases h28 : n < 31450
                                                          · have hr : n - 31400 < 50 := by omega
                                                            have heq : n = (n - 31400) + 31400 := by omega
                                                            rw [heq]
                                                            exact bd_w28 ⟨n - 31400, hr⟩
                                                          ·
                                                            by_cases h29 : n < 31500
                                                            · have hr : n - 31450 < 50 := by omega
                                                              have heq : n = (n - 31450) + 31450 := by omega
                                                              rw [heq]
                                                              exact bd_w29 ⟨n - 31450, hr⟩
                                                            ·
                                                              by_cases h30 : n < 31550
                                                              · have hr : n - 31500 < 50 := by omega
                                                                have heq : n = (n - 31500) + 31500 := by omega
                                                                rw [heq]
                                                                exact bd_w30 ⟨n - 31500, hr⟩
                                                              ·
                                                                by_cases h31 : n < 31600
                                                                · have hr : n - 31550 < 50 := by omega
                                                                  have heq : n = (n - 31550) + 31550 := by omega
                                                                  rw [heq]
                                                                  exact bd_w31 ⟨n - 31550, hr⟩
                                                                ·
                                                                  by_cases h32 : n < 31650
                                                                  · have hr : n - 31600 < 50 := by omega
                                                                    have heq : n = (n - 31600) + 31600 := by omega
                                                                    rw [heq]
                                                                    exact bd_w32 ⟨n - 31600, hr⟩
                                                                  ·
                                                                    by_cases h33 : n < 31700
                                                                    · have hr : n - 31650 < 50 := by omega
                                                                      have heq : n = (n - 31650) + 31650 := by omega
                                                                      rw [heq]
                                                                      exact bd_w33 ⟨n - 31650, hr⟩
                                                                    ·
                                                                      by_cases h34 : n < 31750
                                                                      · have hr : n - 31700 < 50 := by omega
                                                                        have heq : n = (n - 31700) + 31700 := by omega
                                                                        rw [heq]
                                                                        exact bd_w34 ⟨n - 31700, hr⟩
                                                                      ·
                                                                        by_cases h35 : n < 31800
                                                                        · have hr : n - 31750 < 50 := by omega
                                                                          have heq : n = (n - 31750) + 31750 := by omega
                                                                          rw [heq]
                                                                          exact bd_w35 ⟨n - 31750, hr⟩
                                                                        ·
                                                                          by_cases h36 : n < 31850
                                                                          · have hr : n - 31800 < 50 := by omega
                                                                            have heq : n = (n - 31800) + 31800 := by omega
                                                                            rw [heq]
                                                                            exact bd_w36 ⟨n - 31800, hr⟩
                                                                          ·
                                                                            by_cases h37 : n < 31900
                                                                            · have hr : n - 31850 < 50 := by omega
                                                                              have heq : n = (n - 31850) + 31850 := by omega
                                                                              rw [heq]
                                                                              exact bd_w37 ⟨n - 31850, hr⟩
                                                                            ·
                                                                              by_cases h38 : n < 31950
                                                                              · have hr : n - 31900 < 50 := by omega
                                                                                have heq : n = (n - 31900) + 31900 := by omega
                                                                                rw [heq]
                                                                                exact bd_w38 ⟨n - 31900, hr⟩
                                                                              ·
                                                                                by_cases h39 : n < 32000
                                                                                · have hr : n - 31950 < 50 := by omega
                                                                                  have heq : n = (n - 31950) + 31950 := by omega
                                                                                  rw [heq]
                                                                                  exact bd_w39 ⟨n - 31950, hr⟩
                                                                                ·
                                                                                  by_cases h40 : n < 32050
                                                                                  · have hr : n - 32000 < 50 := by omega
                                                                                    have heq : n = (n - 32000) + 32000 := by omega
                                                                                    rw [heq]
                                                                                    exact bd_w40 ⟨n - 32000, hr⟩
                                                                                  ·
                                                                                    by_cases h41 : n < 32100
                                                                                    · have hr : n - 32050 < 50 := by omega
                                                                                      have heq : n = (n - 32050) + 32050 := by omega
                                                                                      rw [heq]
                                                                                      exact bd_w41 ⟨n - 32050, hr⟩
                                                                                    ·
                                                                                      by_cases h42 : n < 32150
                                                                                      · have hr : n - 32100 < 50 := by omega
                                                                                        have heq : n = (n - 32100) + 32100 := by omega
                                                                                        rw [heq]
                                                                                        exact bd_w42 ⟨n - 32100, hr⟩
                                                                                      ·
                                                                                        by_cases h43 : n < 32200
                                                                                        · have hr : n - 32150 < 50 := by omega
                                                                                          have heq : n = (n - 32150) + 32150 := by omega
                                                                                          rw [heq]
                                                                                          exact bd_w43 ⟨n - 32150, hr⟩
                                                                                        ·
                                                                                          by_cases h44 : n < 32250
                                                                                          · have hr : n - 32200 < 50 := by omega
                                                                                            have heq : n = (n - 32200) + 32200 := by omega
                                                                                            rw [heq]
                                                                                            exact bd_w44 ⟨n - 32200, hr⟩
                                                                                          ·
                                                                                            by_cases h45 : n < 32300
                                                                                            · have hr : n - 32250 < 50 := by omega
                                                                                              have heq : n = (n - 32250) + 32250 := by omega
                                                                                              rw [heq]
                                                                                              exact bd_w45 ⟨n - 32250, hr⟩
                                                                                            ·
                                                                                              by_cases h46 : n < 32350
                                                                                              · have hr : n - 32300 < 50 := by omega
                                                                                                have heq : n = (n - 32300) + 32300 := by omega
                                                                                                rw [heq]
                                                                                                exact bd_w46 ⟨n - 32300, hr⟩
                                                                                              ·
                                                                                                by_cases h47 : n < 32400
                                                                                                · have hr : n - 32350 < 50 := by omega
                                                                                                  have heq : n = (n - 32350) + 32350 := by omega
                                                                                                  rw [heq]
                                                                                                  exact bd_w47 ⟨n - 32350, hr⟩
                                                                                                ·
                                                                                                  by_cases h48 : n < 32450
                                                                                                  · have hr : n - 32400 < 50 := by omega
                                                                                                    have heq : n = (n - 32400) + 32400 := by omega
                                                                                                    rw [heq]
                                                                                                    exact bd_w48 ⟨n - 32400, hr⟩
                                                                                                  ·
                                                                                                    by_cases h49 : n < 32500
                                                                                                    · have hr : n - 32450 < 50 := by omega
                                                                                                      have heq : n = (n - 32450) + 32450 := by omega
                                                                                                      rw [heq]
                                                                                                      exact bd_w49 ⟨n - 32450, hr⟩
                                                                                                    ·
                                                                                                      by_cases h50 : n < 32550
                                                                                                      · have hr : n - 32500 < 50 := by omega
                                                                                                        have heq : n = (n - 32500) + 32500 := by omega
                                                                                                        rw [heq]
                                                                                                        exact bd_w50 ⟨n - 32500, hr⟩
                                                                                                      ·
                                                                                                        by_cases h51 : n < 32600
                                                                                                        · have hr : n - 32550 < 50 := by omega
                                                                                                          have heq : n = (n - 32550) + 32550 := by omega
                                                                                                          rw [heq]
                                                                                                          exact bd_w51 ⟨n - 32550, hr⟩
                                                                                                        ·
                                                                                                          by_cases h52 : n < 32650
                                                                                                          · have hr : n - 32600 < 50 := by omega
                                                                                                            have heq : n = (n - 32600) + 32600 := by omega
                                                                                                            rw [heq]
                                                                                                            exact bd_w52 ⟨n - 32600, hr⟩
                                                                                                          ·
                                                                                                            by_cases h53 : n < 32700
                                                                                                            · have hr : n - 32650 < 50 := by omega
                                                                                                              have heq : n = (n - 32650) + 32650 := by omega
                                                                                                              rw [heq]
                                                                                                              exact bd_w53 ⟨n - 32650, hr⟩
                                                                                                            ·
                                                                                                              by_cases h54 : n < 32750
                                                                                                              · have hr : n - 32700 < 50 := by omega
                                                                                                                have heq : n = (n - 32700) + 32700 := by omega
                                                                                                                rw [heq]
                                                                                                                exact bd_w54 ⟨n - 32700, hr⟩
                                                                                                              ·
                                                                                                                by_cases h55 : n < 32800
                                                                                                                · have hr : n - 32750 < 50 := by omega
                                                                                                                  have heq : n = (n - 32750) + 32750 := by omega
                                                                                                                  rw [heq]
                                                                                                                  exact bd_w55 ⟨n - 32750, hr⟩
                                                                                                                ·
                                                                                                                  by_cases h56 : n < 32850
                                                                                                                  · have hr : n - 32800 < 50 := by omega
                                                                                                                    have heq : n = (n - 32800) + 32800 := by omega
                                                                                                                    rw [heq]
                                                                                                                    exact bd_w56 ⟨n - 32800, hr⟩
                                                                                                                  ·
                                                                                                                    by_cases h57 : n < 32900
                                                                                                                    · have hr : n - 32850 < 50 := by omega
                                                                                                                      have heq : n = (n - 32850) + 32850 := by omega
                                                                                                                      rw [heq]
                                                                                                                      exact bd_w57 ⟨n - 32850, hr⟩
                                                                                                                    ·
                                                                                                                      by_cases h58 : n < 32950
                                                                                                                      · have hr : n - 32900 < 50 := by omega
                                                                                                                        have heq : n = (n - 32900) + 32900 := by omega
                                                                                                                        rw [heq]
                                                                                                                        exact bd_w58 ⟨n - 32900, hr⟩
                                                                                                                      ·
                                                                                                                        by_cases h59 : n < 33000
                                                                                                                        · have hr : n - 32950 < 50 := by omega
                                                                                                                          have heq : n = (n - 32950) + 32950 := by omega
                                                                                                                          rw [heq]
                                                                                                                          exact bd_w59 ⟨n - 32950, hr⟩
                                                                                                                        ·
                                                                                                                          by_cases h60 : n < 33050
                                                                                                                          · have hr : n - 33000 < 50 := by omega
                                                                                                                            have heq : n = (n - 33000) + 33000 := by omega
                                                                                                                            rw [heq]
                                                                                                                            exact bd_w60 ⟨n - 33000, hr⟩
                                                                                                                          ·
                                                                                                                            by_cases h61 : n < 33100
                                                                                                                            · have hr : n - 33050 < 50 := by omega
                                                                                                                              have heq : n = (n - 33050) + 33050 := by omega
                                                                                                                              rw [heq]
                                                                                                                              exact bd_w61 ⟨n - 33050, hr⟩
                                                                                                                            ·
                                                                                                                              by_cases h62 : n < 33150
                                                                                                                              · have hr : n - 33100 < 50 := by omega
                                                                                                                                have heq : n = (n - 33100) + 33100 := by omega
                                                                                                                                rw [heq]
                                                                                                                                exact bd_w62 ⟨n - 33100, hr⟩
                                                                                                                              ·
                                                                                                                                by_cases h63 : n < 33200
                                                                                                                                · have hr : n - 33150 < 50 := by omega
                                                                                                                                  have heq : n = (n - 33150) + 33150 := by omega
                                                                                                                                  rw [heq]
                                                                                                                                  exact bd_w63 ⟨n - 33150, hr⟩
                                                                                                                                ·
                                                                                                                                  by_cases h64 : n < 33250
                                                                                                                                  · have hr : n - 33200 < 50 := by omega
                                                                                                                                    have heq : n = (n - 33200) + 33200 := by omega
                                                                                                                                    rw [heq]
                                                                                                                                    exact bd_w64 ⟨n - 33200, hr⟩
                                                                                                                                  ·
                                                                                                                                    by_cases h65 : n < 33300
                                                                                                                                    · have hr : n - 33250 < 50 := by omega
                                                                                                                                      have heq : n = (n - 33250) + 33250 := by omega
                                                                                                                                      rw [heq]
                                                                                                                                      exact bd_w65 ⟨n - 33250, hr⟩
                                                                                                                                    ·
                                                                                                                                      by_cases h66 : n < 33350
                                                                                                                                      · have hr : n - 33300 < 50 := by omega
                                                                                                                                        have heq : n = (n - 33300) + 33300 := by omega
                                                                                                                                        rw [heq]
                                                                                                                                        exact bd_w66 ⟨n - 33300, hr⟩
                                                                                                                                      ·
                                                                                                                                        by_cases h67 : n < 33400
                                                                                                                                        · have hr : n - 33350 < 50 := by omega
                                                                                                                                          have heq : n = (n - 33350) + 33350 := by omega
                                                                                                                                          rw [heq]
                                                                                                                                          exact bd_w67 ⟨n - 33350, hr⟩
                                                                                                                                        ·
                                                                                                                                          by_cases h68 : n < 33450
                                                                                                                                          · have hr : n - 33400 < 50 := by omega
                                                                                                                                            have heq : n = (n - 33400) + 33400 := by omega
                                                                                                                                            rw [heq]
                                                                                                                                            exact bd_w68 ⟨n - 33400, hr⟩
                                                                                                                                          ·
                                                                                                                                            by_cases h69 : n < 33500
                                                                                                                                            · have hr : n - 33450 < 50 := by omega
                                                                                                                                              have heq : n = (n - 33450) + 33450 := by omega
                                                                                                                                              rw [heq]
                                                                                                                                              exact bd_w69 ⟨n - 33450, hr⟩
                                                                                                                                            ·
                                                                                                                                              by_cases h70 : n < 33550
                                                                                                                                              · have hr : n - 33500 < 50 := by omega
                                                                                                                                                have heq : n = (n - 33500) + 33500 := by omega
                                                                                                                                                rw [heq]
                                                                                                                                                exact bd_w70 ⟨n - 33500, hr⟩
                                                                                                                                              ·
                                                                                                                                                by_cases h71 : n < 33600
                                                                                                                                                · have hr : n - 33550 < 50 := by omega
                                                                                                                                                  have heq : n = (n - 33550) + 33550 := by omega
                                                                                                                                                  rw [heq]
                                                                                                                                                  exact bd_w71 ⟨n - 33550, hr⟩
                                                                                                                                                ·
                                                                                                                                                  by_cases h72 : n < 33650
                                                                                                                                                  · have hr : n - 33600 < 50 := by omega
                                                                                                                                                    have heq : n = (n - 33600) + 33600 := by omega
                                                                                                                                                    rw [heq]
                                                                                                                                                    exact bd_w72 ⟨n - 33600, hr⟩
                                                                                                                                                  ·
                                                                                                                                                    by_cases h73 : n < 33700
                                                                                                                                                    · have hr : n - 33650 < 50 := by omega
                                                                                                                                                      have heq : n = (n - 33650) + 33650 := by omega
                                                                                                                                                      rw [heq]
                                                                                                                                                      exact bd_w73 ⟨n - 33650, hr⟩
                                                                                                                                                    ·
                                                                                                                                                      by_cases h74 : n < 33750
                                                                                                                                                      · have hr : n - 33700 < 50 := by omega
                                                                                                                                                        have heq : n = (n - 33700) + 33700 := by omega
                                                                                                                                                        rw [heq]
                                                                                                                                                        exact bd_w74 ⟨n - 33700, hr⟩
                                                                                                                                                      ·
                                                                                                                                                        by_cases h75 : n < 33800
                                                                                                                                                        · have hr : n - 33750 < 50 := by omega
                                                                                                                                                          have heq : n = (n - 33750) + 33750 := by omega
                                                                                                                                                          rw [heq]
                                                                                                                                                          exact bd_w75 ⟨n - 33750, hr⟩
                                                                                                                                                        ·
                                                                                                                                                          by_cases h76 : n < 33850
                                                                                                                                                          · have hr : n - 33800 < 50 := by omega
                                                                                                                                                            have heq : n = (n - 33800) + 33800 := by omega
                                                                                                                                                            rw [heq]
                                                                                                                                                            exact bd_w76 ⟨n - 33800, hr⟩
                                                                                                                                                          ·
                                                                                                                                                            by_cases h77 : n < 33900
                                                                                                                                                            · have hr : n - 33850 < 50 := by omega
                                                                                                                                                              have heq : n = (n - 33850) + 33850 := by omega
                                                                                                                                                              rw [heq]
                                                                                                                                                              exact bd_w77 ⟨n - 33850, hr⟩
                                                                                                                                                            ·
                                                                                                                                                              by_cases h78 : n < 33950
                                                                                                                                                              · have hr : n - 33900 < 50 := by omega
                                                                                                                                                                have heq : n = (n - 33900) + 33900 := by omega
                                                                                                                                                                rw [heq]
                                                                                                                                                                exact bd_w78 ⟨n - 33900, hr⟩
                                                                                                                                                              ·
                                                                                                                                                                by_cases h79 : n < 34000
                                                                                                                                                                · have hr : n - 33950 < 50 := by omega
                                                                                                                                                                  have heq : n = (n - 33950) + 33950 := by omega
                                                                                                                                                                  rw [heq]
                                                                                                                                                                  exact bd_w79 ⟨n - 33950, hr⟩
                                                                                                                                                                ·
                                                                                                                                                                  by_cases h80 : n < 34050
                                                                                                                                                                  · have hr : n - 34000 < 50 := by omega
                                                                                                                                                                    have heq : n = (n - 34000) + 34000 := by omega
                                                                                                                                                                    rw [heq]
                                                                                                                                                                    exact bd_w80 ⟨n - 34000, hr⟩
                                                                                                                                                                  ·
                                                                                                                                                                    by_cases h81 : n < 34100
                                                                                                                                                                    · have hr : n - 34050 < 50 := by omega
                                                                                                                                                                      have heq : n = (n - 34050) + 34050 := by omega
                                                                                                                                                                      rw [heq]
                                                                                                                                                                      exact bd_w81 ⟨n - 34050, hr⟩
                                                                                                                                                                    ·
                                                                                                                                                                      by_cases h82 : n < 34150
                                                                                                                                                                      · have hr : n - 34100 < 50 := by omega
                                                                                                                                                                        have heq : n = (n - 34100) + 34100 := by omega
                                                                                                                                                                        rw [heq]
                                                                                                                                                                        exact bd_w82 ⟨n - 34100, hr⟩
                                                                                                                                                                      ·
                                                                                                                                                                        by_cases h83 : n < 34200
                                                                                                                                                                        · have hr : n - 34150 < 50 := by omega
                                                                                                                                                                          have heq : n = (n - 34150) + 34150 := by omega
                                                                                                                                                                          rw [heq]
                                                                                                                                                                          exact bd_w83 ⟨n - 34150, hr⟩
                                                                                                                                                                        ·
                                                                                                                                                                          by_cases h84 : n < 34250
                                                                                                                                                                          · have hr : n - 34200 < 50 := by omega
                                                                                                                                                                            have heq : n = (n - 34200) + 34200 := by omega
                                                                                                                                                                            rw [heq]
                                                                                                                                                                            exact bd_w84 ⟨n - 34200, hr⟩
                                                                                                                                                                          ·
                                                                                                                                                                            by_cases h85 : n < 34300
                                                                                                                                                                            · have hr : n - 34250 < 50 := by omega
                                                                                                                                                                              have heq : n = (n - 34250) + 34250 := by omega
                                                                                                                                                                              rw [heq]
                                                                                                                                                                              exact bd_w85 ⟨n - 34250, hr⟩
                                                                                                                                                                            ·
                                                                                                                                                                              by_cases h86 : n < 34350
                                                                                                                                                                              · have hr : n - 34300 < 50 := by omega
                                                                                                                                                                                have heq : n = (n - 34300) + 34300 := by omega
                                                                                                                                                                                rw [heq]
                                                                                                                                                                                exact bd_w86 ⟨n - 34300, hr⟩
                                                                                                                                                                              ·
                                                                                                                                                                                by_cases h87 : n < 34400
                                                                                                                                                                                · have hr : n - 34350 < 50 := by omega
                                                                                                                                                                                  have heq : n = (n - 34350) + 34350 := by omega
                                                                                                                                                                                  rw [heq]
                                                                                                                                                                                  exact bd_w87 ⟨n - 34350, hr⟩
                                                                                                                                                                                ·
                                                                                                                                                                                  by_cases h88 : n < 34450
                                                                                                                                                                                  · have hr : n - 34400 < 50 := by omega
                                                                                                                                                                                    have heq : n = (n - 34400) + 34400 := by omega
                                                                                                                                                                                    rw [heq]
                                                                                                                                                                                    exact bd_w88 ⟨n - 34400, hr⟩
                                                                                                                                                                                  ·
                                                                                                                                                                                    by_cases h89 : n < 34500
                                                                                                                                                                                    · have hr : n - 34450 < 50 := by omega
                                                                                                                                                                                      have heq : n = (n - 34450) + 34450 := by omega
                                                                                                                                                                                      rw [heq]
                                                                                                                                                                                      exact bd_w89 ⟨n - 34450, hr⟩
                                                                                                                                                                                    ·
                                                                                                                                                                                      by_cases h90 : n < 34550
                                                                                                                                                                                      · have hr : n - 34500 < 50 := by omega
                                                                                                                                                                                        have heq : n = (n - 34500) + 34500 := by omega
                                                                                                                                                                                        rw [heq]
                                                                                                                                                                                        exact bd_w90 ⟨n - 34500, hr⟩
                                                                                                                                                                                      ·
                                                                                                                                                                                        by_cases h91 : n < 34600
                                                                                                                                                                                        · have hr : n - 34550 < 50 := by omega
                                                                                                                                                                                          have heq : n = (n - 34550) + 34550 := by omega
                                                                                                                                                                                          rw [heq]
                                                                                                                                                                                          exact bd_w91 ⟨n - 34550, hr⟩
                                                                                                                                                                                        ·
                                                                                                                                                                                          by_cases h92 : n < 34650
                                                                                                                                                                                          · have hr : n - 34600 < 50 := by omega
                                                                                                                                                                                            have heq : n = (n - 34600) + 34600 := by omega
                                                                                                                                                                                            rw [heq]
                                                                                                                                                                                            exact bd_w92 ⟨n - 34600, hr⟩
                                                                                                                                                                                          ·
                                                                                                                                                                                            by_cases h93 : n < 34700
                                                                                                                                                                                            · have hr : n - 34650 < 50 := by omega
                                                                                                                                                                                              have heq : n = (n - 34650) + 34650 := by omega
                                                                                                                                                                                              rw [heq]
                                                                                                                                                                                              exact bd_w93 ⟨n - 34650, hr⟩
                                                                                                                                                                                            ·
                                                                                                                                                                                              by_cases h94 : n < 34750
                                                                                                                                                                                              · have hr : n - 34700 < 50 := by omega
                                                                                                                                                                                                have heq : n = (n - 34700) + 34700 := by omega
                                                                                                                                                                                                rw [heq]
                                                                                                                                                                                                exact bd_w94 ⟨n - 34700, hr⟩
                                                                                                                                                                                              ·
                                                                                                                                                                                                by_cases h95 : n < 34800
                                                                                                                                                                                                · have hr : n - 34750 < 50 := by omega
                                                                                                                                                                                                  have heq : n = (n - 34750) + 34750 := by omega
                                                                                                                                                                                                  rw [heq]
                                                                                                                                                                                                  exact bd_w95 ⟨n - 34750, hr⟩
                                                                                                                                                                                                ·
                                                                                                                                                                                                  by_cases h96 : n < 34850
                                                                                                                                                                                                  · have hr : n - 34800 < 50 := by omega
                                                                                                                                                                                                    have heq : n = (n - 34800) + 34800 := by omega
                                                                                                                                                                                                    rw [heq]
                                                                                                                                                                                                    exact bd_w96 ⟨n - 34800, hr⟩
                                                                                                                                                                                                  ·
                                                                                                                                                                                                    by_cases h97 : n < 34900
                                                                                                                                                                                                    · have hr : n - 34850 < 50 := by omega
                                                                                                                                                                                                      have heq : n = (n - 34850) + 34850 := by omega
                                                                                                                                                                                                      rw [heq]
                                                                                                                                                                                                      exact bd_w97 ⟨n - 34850, hr⟩
                                                                                                                                                                                                    ·
                                                                                                                                                                                                      by_cases h98 : n < 34950
                                                                                                                                                                                                      · have hr : n - 34900 < 50 := by omega
                                                                                                                                                                                                        have heq : n = (n - 34900) + 34900 := by omega
                                                                                                                                                                                                        rw [heq]
                                                                                                                                                                                                        exact bd_w98 ⟨n - 34900, hr⟩
                                                                                                                                                                                                      ·
                                                                                                                                                                                                        have hr : n - 34950 < 50 := by omega
                                                                                                                                                                                                        have heq : n = (n - 34950) + 34950 := by omega
                                                                                                                                                                                                        rw [heq]
                                                                                                                                                                                                        exact bd_w99 ⟨n - 34950, hr⟩

end IntMul.Kappa.R8.Bit.Oppbank.CentBound6Fix


