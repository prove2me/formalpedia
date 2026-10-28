-- Prove2me | Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankCentBound2
-- name    : IntMul_Kappa_R8_Data_BitOppbankCentBound2
-- status  : Definition
-- author  : @Ethan Cheung Wang
-- created : 2026-10-28T19:47:42.702163+00:00
-- url     : https://prove2.me/theorems/f32acb4d-3011-422f-a1a0-bb93fd61378f
-- title:
--   HasCentre certificates dens nodes [10000,15000)
-- statement:
--   # Densified centre certificates, pack 2
--
--   For every densified node index $ with \le n<15000$,
--   84126
--   \mathrm{centredStar}(\mathrm{densSupG}\,n,\mathrm{centF}\,n)=\mathsf{true},\quad
--   \mathrm{centF}\,n<23,\quad
--   \mathrm{densSupG}\,n < 2^{1771}.
--   84126
--   Proved by  on  windows (no ).
-- source:
--   R8 BitOppbank AllDensCentred; jfstack_23 densified supports

-- CentBound pack 2: densified HasCentre certificates on n ∈ [10000, 15000)
-- Generated for AllDensCentred (star-mask land + centF).

import Definitions.Def_IntMul_Kappa_R6_Defs4
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankPnd
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankSupG
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankCent
import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 1000000
set_option exponentiation.threshold 2000

open IntMul.Kappa.R8.Bit.Oppbank.Pnd
open IntMul.Kappa.R8.Bit.Oppbank.SupG
open IntMul.Kappa.R8.Bit.Oppbank.Cent

namespace IntMul.Kappa.R8.Bit.Oppbank.CentBound2

private theorem cs_w0 : ∀ n : Fin 50, centredStar (densSupG (n.val + 10000)) (centF (n.val + 10000)) = true := by decide
private theorem cl_w0 : ∀ n : Fin 50, centF (n.val + 10000) < 23 := by decide
private theorem bd_w0 : ∀ n : Fin 50, densSupG (n.val + 10000) < 2 ^ 1771 := by decide
private theorem cs_w1 : ∀ n : Fin 50, centredStar (densSupG (n.val + 10050)) (centF (n.val + 10050)) = true := by decide
private theorem cl_w1 : ∀ n : Fin 50, centF (n.val + 10050) < 23 := by decide
private theorem bd_w1 : ∀ n : Fin 50, densSupG (n.val + 10050) < 2 ^ 1771 := by decide
private theorem cs_w2 : ∀ n : Fin 50, centredStar (densSupG (n.val + 10100)) (centF (n.val + 10100)) = true := by decide
private theorem cl_w2 : ∀ n : Fin 50, centF (n.val + 10100) < 23 := by decide
private theorem bd_w2 : ∀ n : Fin 50, densSupG (n.val + 10100) < 2 ^ 1771 := by decide
private theorem cs_w3 : ∀ n : Fin 50, centredStar (densSupG (n.val + 10150)) (centF (n.val + 10150)) = true := by decide
private theorem cl_w3 : ∀ n : Fin 50, centF (n.val + 10150) < 23 := by decide
private theorem bd_w3 : ∀ n : Fin 50, densSupG (n.val + 10150) < 2 ^ 1771 := by decide
private theorem cs_w4 : ∀ n : Fin 50, centredStar (densSupG (n.val + 10200)) (centF (n.val + 10200)) = true := by decide
private theorem cl_w4 : ∀ n : Fin 50, centF (n.val + 10200) < 23 := by decide
private theorem bd_w4 : ∀ n : Fin 50, densSupG (n.val + 10200) < 2 ^ 1771 := by decide
private theorem cs_w5 : ∀ n : Fin 50, centredStar (densSupG (n.val + 10250)) (centF (n.val + 10250)) = true := by decide
private theorem cl_w5 : ∀ n : Fin 50, centF (n.val + 10250) < 23 := by decide
private theorem bd_w5 : ∀ n : Fin 50, densSupG (n.val + 10250) < 2 ^ 1771 := by decide
private theorem cs_w6 : ∀ n : Fin 50, centredStar (densSupG (n.val + 10300)) (centF (n.val + 10300)) = true := by decide
private theorem cl_w6 : ∀ n : Fin 50, centF (n.val + 10300) < 23 := by decide
private theorem bd_w6 : ∀ n : Fin 50, densSupG (n.val + 10300) < 2 ^ 1771 := by decide
private theorem cs_w7 : ∀ n : Fin 50, centredStar (densSupG (n.val + 10350)) (centF (n.val + 10350)) = true := by decide
private theorem cl_w7 : ∀ n : Fin 50, centF (n.val + 10350) < 23 := by decide
private theorem bd_w7 : ∀ n : Fin 50, densSupG (n.val + 10350) < 2 ^ 1771 := by decide
private theorem cs_w8 : ∀ n : Fin 50, centredStar (densSupG (n.val + 10400)) (centF (n.val + 10400)) = true := by decide
private theorem cl_w8 : ∀ n : Fin 50, centF (n.val + 10400) < 23 := by decide
private theorem bd_w8 : ∀ n : Fin 50, densSupG (n.val + 10400) < 2 ^ 1771 := by decide
private theorem cs_w9 : ∀ n : Fin 50, centredStar (densSupG (n.val + 10450)) (centF (n.val + 10450)) = true := by decide
private theorem cl_w9 : ∀ n : Fin 50, centF (n.val + 10450) < 23 := by decide
private theorem bd_w9 : ∀ n : Fin 50, densSupG (n.val + 10450) < 2 ^ 1771 := by decide
private theorem cs_w10 : ∀ n : Fin 50, centredStar (densSupG (n.val + 10500)) (centF (n.val + 10500)) = true := by decide
private theorem cl_w10 : ∀ n : Fin 50, centF (n.val + 10500) < 23 := by decide
private theorem bd_w10 : ∀ n : Fin 50, densSupG (n.val + 10500) < 2 ^ 1771 := by decide
private theorem cs_w11 : ∀ n : Fin 50, centredStar (densSupG (n.val + 10550)) (centF (n.val + 10550)) = true := by decide
private theorem cl_w11 : ∀ n : Fin 50, centF (n.val + 10550) < 23 := by decide
private theorem bd_w11 : ∀ n : Fin 50, densSupG (n.val + 10550) < 2 ^ 1771 := by decide
private theorem cs_w12 : ∀ n : Fin 50, centredStar (densSupG (n.val + 10600)) (centF (n.val + 10600)) = true := by decide
private theorem cl_w12 : ∀ n : Fin 50, centF (n.val + 10600) < 23 := by decide
private theorem bd_w12 : ∀ n : Fin 50, densSupG (n.val + 10600) < 2 ^ 1771 := by decide
private theorem cs_w13 : ∀ n : Fin 50, centredStar (densSupG (n.val + 10650)) (centF (n.val + 10650)) = true := by decide
private theorem cl_w13 : ∀ n : Fin 50, centF (n.val + 10650) < 23 := by decide
private theorem bd_w13 : ∀ n : Fin 50, densSupG (n.val + 10650) < 2 ^ 1771 := by decide
private theorem cs_w14 : ∀ n : Fin 50, centredStar (densSupG (n.val + 10700)) (centF (n.val + 10700)) = true := by decide
private theorem cl_w14 : ∀ n : Fin 50, centF (n.val + 10700) < 23 := by decide
private theorem bd_w14 : ∀ n : Fin 50, densSupG (n.val + 10700) < 2 ^ 1771 := by decide
private theorem cs_w15 : ∀ n : Fin 50, centredStar (densSupG (n.val + 10750)) (centF (n.val + 10750)) = true := by decide
private theorem cl_w15 : ∀ n : Fin 50, centF (n.val + 10750) < 23 := by decide
private theorem bd_w15 : ∀ n : Fin 50, densSupG (n.val + 10750) < 2 ^ 1771 := by decide
private theorem cs_w16 : ∀ n : Fin 50, centredStar (densSupG (n.val + 10800)) (centF (n.val + 10800)) = true := by decide
private theorem cl_w16 : ∀ n : Fin 50, centF (n.val + 10800) < 23 := by decide
private theorem bd_w16 : ∀ n : Fin 50, densSupG (n.val + 10800) < 2 ^ 1771 := by decide
private theorem cs_w17 : ∀ n : Fin 50, centredStar (densSupG (n.val + 10850)) (centF (n.val + 10850)) = true := by decide
private theorem cl_w17 : ∀ n : Fin 50, centF (n.val + 10850) < 23 := by decide
private theorem bd_w17 : ∀ n : Fin 50, densSupG (n.val + 10850) < 2 ^ 1771 := by decide
private theorem cs_w18 : ∀ n : Fin 50, centredStar (densSupG (n.val + 10900)) (centF (n.val + 10900)) = true := by decide
private theorem cl_w18 : ∀ n : Fin 50, centF (n.val + 10900) < 23 := by decide
private theorem bd_w18 : ∀ n : Fin 50, densSupG (n.val + 10900) < 2 ^ 1771 := by decide
private theorem cs_w19 : ∀ n : Fin 50, centredStar (densSupG (n.val + 10950)) (centF (n.val + 10950)) = true := by decide
private theorem cl_w19 : ∀ n : Fin 50, centF (n.val + 10950) < 23 := by decide
private theorem bd_w19 : ∀ n : Fin 50, densSupG (n.val + 10950) < 2 ^ 1771 := by decide
private theorem cs_w20 : ∀ n : Fin 50, centredStar (densSupG (n.val + 11000)) (centF (n.val + 11000)) = true := by decide
private theorem cl_w20 : ∀ n : Fin 50, centF (n.val + 11000) < 23 := by decide
private theorem bd_w20 : ∀ n : Fin 50, densSupG (n.val + 11000) < 2 ^ 1771 := by decide
private theorem cs_w21 : ∀ n : Fin 50, centredStar (densSupG (n.val + 11050)) (centF (n.val + 11050)) = true := by decide
private theorem cl_w21 : ∀ n : Fin 50, centF (n.val + 11050) < 23 := by decide
private theorem bd_w21 : ∀ n : Fin 50, densSupG (n.val + 11050) < 2 ^ 1771 := by decide
private theorem cs_w22 : ∀ n : Fin 50, centredStar (densSupG (n.val + 11100)) (centF (n.val + 11100)) = true := by decide
private theorem cl_w22 : ∀ n : Fin 50, centF (n.val + 11100) < 23 := by decide
private theorem bd_w22 : ∀ n : Fin 50, densSupG (n.val + 11100) < 2 ^ 1771 := by decide
private theorem cs_w23 : ∀ n : Fin 50, centredStar (densSupG (n.val + 11150)) (centF (n.val + 11150)) = true := by decide
private theorem cl_w23 : ∀ n : Fin 50, centF (n.val + 11150) < 23 := by decide
private theorem bd_w23 : ∀ n : Fin 50, densSupG (n.val + 11150) < 2 ^ 1771 := by decide
private theorem cs_w24 : ∀ n : Fin 50, centredStar (densSupG (n.val + 11200)) (centF (n.val + 11200)) = true := by decide
private theorem cl_w24 : ∀ n : Fin 50, centF (n.val + 11200) < 23 := by decide
private theorem bd_w24 : ∀ n : Fin 50, densSupG (n.val + 11200) < 2 ^ 1771 := by decide
private theorem cs_w25 : ∀ n : Fin 50, centredStar (densSupG (n.val + 11250)) (centF (n.val + 11250)) = true := by decide
private theorem cl_w25 : ∀ n : Fin 50, centF (n.val + 11250) < 23 := by decide
private theorem bd_w25 : ∀ n : Fin 50, densSupG (n.val + 11250) < 2 ^ 1771 := by decide
private theorem cs_w26 : ∀ n : Fin 50, centredStar (densSupG (n.val + 11300)) (centF (n.val + 11300)) = true := by decide
private theorem cl_w26 : ∀ n : Fin 50, centF (n.val + 11300) < 23 := by decide
private theorem bd_w26 : ∀ n : Fin 50, densSupG (n.val + 11300) < 2 ^ 1771 := by decide
private theorem cs_w27 : ∀ n : Fin 50, centredStar (densSupG (n.val + 11350)) (centF (n.val + 11350)) = true := by decide
private theorem cl_w27 : ∀ n : Fin 50, centF (n.val + 11350) < 23 := by decide
private theorem bd_w27 : ∀ n : Fin 50, densSupG (n.val + 11350) < 2 ^ 1771 := by decide
private theorem cs_w28 : ∀ n : Fin 50, centredStar (densSupG (n.val + 11400)) (centF (n.val + 11400)) = true := by decide
private theorem cl_w28 : ∀ n : Fin 50, centF (n.val + 11400) < 23 := by decide
private theorem bd_w28 : ∀ n : Fin 50, densSupG (n.val + 11400) < 2 ^ 1771 := by decide
private theorem cs_w29 : ∀ n : Fin 50, centredStar (densSupG (n.val + 11450)) (centF (n.val + 11450)) = true := by decide
private theorem cl_w29 : ∀ n : Fin 50, centF (n.val + 11450) < 23 := by decide
private theorem bd_w29 : ∀ n : Fin 50, densSupG (n.val + 11450) < 2 ^ 1771 := by decide
private theorem cs_w30 : ∀ n : Fin 50, centredStar (densSupG (n.val + 11500)) (centF (n.val + 11500)) = true := by decide
private theorem cl_w30 : ∀ n : Fin 50, centF (n.val + 11500) < 23 := by decide
private theorem bd_w30 : ∀ n : Fin 50, densSupG (n.val + 11500) < 2 ^ 1771 := by decide
private theorem cs_w31 : ∀ n : Fin 50, centredStar (densSupG (n.val + 11550)) (centF (n.val + 11550)) = true := by decide
private theorem cl_w31 : ∀ n : Fin 50, centF (n.val + 11550) < 23 := by decide
private theorem bd_w31 : ∀ n : Fin 50, densSupG (n.val + 11550) < 2 ^ 1771 := by decide
private theorem cs_w32 : ∀ n : Fin 50, centredStar (densSupG (n.val + 11600)) (centF (n.val + 11600)) = true := by decide
private theorem cl_w32 : ∀ n : Fin 50, centF (n.val + 11600) < 23 := by decide
private theorem bd_w32 : ∀ n : Fin 50, densSupG (n.val + 11600) < 2 ^ 1771 := by decide
private theorem cs_w33 : ∀ n : Fin 50, centredStar (densSupG (n.val + 11650)) (centF (n.val + 11650)) = true := by decide
private theorem cl_w33 : ∀ n : Fin 50, centF (n.val + 11650) < 23 := by decide
private theorem bd_w33 : ∀ n : Fin 50, densSupG (n.val + 11650) < 2 ^ 1771 := by decide
private theorem cs_w34 : ∀ n : Fin 50, centredStar (densSupG (n.val + 11700)) (centF (n.val + 11700)) = true := by decide
private theorem cl_w34 : ∀ n : Fin 50, centF (n.val + 11700) < 23 := by decide
private theorem bd_w34 : ∀ n : Fin 50, densSupG (n.val + 11700) < 2 ^ 1771 := by decide
private theorem cs_w35 : ∀ n : Fin 50, centredStar (densSupG (n.val + 11750)) (centF (n.val + 11750)) = true := by decide
private theorem cl_w35 : ∀ n : Fin 50, centF (n.val + 11750) < 23 := by decide
private theorem bd_w35 : ∀ n : Fin 50, densSupG (n.val + 11750) < 2 ^ 1771 := by decide
private theorem cs_w36 : ∀ n : Fin 50, centredStar (densSupG (n.val + 11800)) (centF (n.val + 11800)) = true := by decide
private theorem cl_w36 : ∀ n : Fin 50, centF (n.val + 11800) < 23 := by decide
private theorem bd_w36 : ∀ n : Fin 50, densSupG (n.val + 11800) < 2 ^ 1771 := by decide
private theorem cs_w37 : ∀ n : Fin 50, centredStar (densSupG (n.val + 11850)) (centF (n.val + 11850)) = true := by decide
private theorem cl_w37 : ∀ n : Fin 50, centF (n.val + 11850) < 23 := by decide
private theorem bd_w37 : ∀ n : Fin 50, densSupG (n.val + 11850) < 2 ^ 1771 := by decide
private theorem cs_w38 : ∀ n : Fin 50, centredStar (densSupG (n.val + 11900)) (centF (n.val + 11900)) = true := by decide
private theorem cl_w38 : ∀ n : Fin 50, centF (n.val + 11900) < 23 := by decide
private theorem bd_w38 : ∀ n : Fin 50, densSupG (n.val + 11900) < 2 ^ 1771 := by decide
private theorem cs_w39 : ∀ n : Fin 50, centredStar (densSupG (n.val + 11950)) (centF (n.val + 11950)) = true := by decide
private theorem cl_w39 : ∀ n : Fin 50, centF (n.val + 11950) < 23 := by decide
private theorem bd_w39 : ∀ n : Fin 50, densSupG (n.val + 11950) < 2 ^ 1771 := by decide
private theorem cs_w40 : ∀ n : Fin 50, centredStar (densSupG (n.val + 12000)) (centF (n.val + 12000)) = true := by decide
private theorem cl_w40 : ∀ n : Fin 50, centF (n.val + 12000) < 23 := by decide
private theorem bd_w40 : ∀ n : Fin 50, densSupG (n.val + 12000) < 2 ^ 1771 := by decide
private theorem cs_w41 : ∀ n : Fin 50, centredStar (densSupG (n.val + 12050)) (centF (n.val + 12050)) = true := by decide
private theorem cl_w41 : ∀ n : Fin 50, centF (n.val + 12050) < 23 := by decide
private theorem bd_w41 : ∀ n : Fin 50, densSupG (n.val + 12050) < 2 ^ 1771 := by decide
private theorem cs_w42 : ∀ n : Fin 50, centredStar (densSupG (n.val + 12100)) (centF (n.val + 12100)) = true := by decide
private theorem cl_w42 : ∀ n : Fin 50, centF (n.val + 12100) < 23 := by decide
private theorem bd_w42 : ∀ n : Fin 50, densSupG (n.val + 12100) < 2 ^ 1771 := by decide
private theorem cs_w43 : ∀ n : Fin 50, centredStar (densSupG (n.val + 12150)) (centF (n.val + 12150)) = true := by decide
private theorem cl_w43 : ∀ n : Fin 50, centF (n.val + 12150) < 23 := by decide
private theorem bd_w43 : ∀ n : Fin 50, densSupG (n.val + 12150) < 2 ^ 1771 := by decide
private theorem cs_w44 : ∀ n : Fin 50, centredStar (densSupG (n.val + 12200)) (centF (n.val + 12200)) = true := by decide
private theorem cl_w44 : ∀ n : Fin 50, centF (n.val + 12200) < 23 := by decide
private theorem bd_w44 : ∀ n : Fin 50, densSupG (n.val + 12200) < 2 ^ 1771 := by decide
private theorem cs_w45 : ∀ n : Fin 50, centredStar (densSupG (n.val + 12250)) (centF (n.val + 12250)) = true := by decide
private theorem cl_w45 : ∀ n : Fin 50, centF (n.val + 12250) < 23 := by decide
private theorem bd_w45 : ∀ n : Fin 50, densSupG (n.val + 12250) < 2 ^ 1771 := by decide
private theorem cs_w46 : ∀ n : Fin 50, centredStar (densSupG (n.val + 12300)) (centF (n.val + 12300)) = true := by decide
private theorem cl_w46 : ∀ n : Fin 50, centF (n.val + 12300) < 23 := by decide
private theorem bd_w46 : ∀ n : Fin 50, densSupG (n.val + 12300) < 2 ^ 1771 := by decide
private theorem cs_w47 : ∀ n : Fin 50, centredStar (densSupG (n.val + 12350)) (centF (n.val + 12350)) = true := by decide
private theorem cl_w47 : ∀ n : Fin 50, centF (n.val + 12350) < 23 := by decide
private theorem bd_w47 : ∀ n : Fin 50, densSupG (n.val + 12350) < 2 ^ 1771 := by decide
private theorem cs_w48 : ∀ n : Fin 50, centredStar (densSupG (n.val + 12400)) (centF (n.val + 12400)) = true := by decide
private theorem cl_w48 : ∀ n : Fin 50, centF (n.val + 12400) < 23 := by decide
private theorem bd_w48 : ∀ n : Fin 50, densSupG (n.val + 12400) < 2 ^ 1771 := by decide
private theorem cs_w49 : ∀ n : Fin 50, centredStar (densSupG (n.val + 12450)) (centF (n.val + 12450)) = true := by decide
private theorem cl_w49 : ∀ n : Fin 50, centF (n.val + 12450) < 23 := by decide
private theorem bd_w49 : ∀ n : Fin 50, densSupG (n.val + 12450) < 2 ^ 1771 := by decide
private theorem cs_w50 : ∀ n : Fin 50, centredStar (densSupG (n.val + 12500)) (centF (n.val + 12500)) = true := by decide
private theorem cl_w50 : ∀ n : Fin 50, centF (n.val + 12500) < 23 := by decide
private theorem bd_w50 : ∀ n : Fin 50, densSupG (n.val + 12500) < 2 ^ 1771 := by decide
private theorem cs_w51 : ∀ n : Fin 50, centredStar (densSupG (n.val + 12550)) (centF (n.val + 12550)) = true := by decide
private theorem cl_w51 : ∀ n : Fin 50, centF (n.val + 12550) < 23 := by decide
private theorem bd_w51 : ∀ n : Fin 50, densSupG (n.val + 12550) < 2 ^ 1771 := by decide
private theorem cs_w52 : ∀ n : Fin 50, centredStar (densSupG (n.val + 12600)) (centF (n.val + 12600)) = true := by decide
private theorem cl_w52 : ∀ n : Fin 50, centF (n.val + 12600) < 23 := by decide
private theorem bd_w52 : ∀ n : Fin 50, densSupG (n.val + 12600) < 2 ^ 1771 := by decide
private theorem cs_w53 : ∀ n : Fin 50, centredStar (densSupG (n.val + 12650)) (centF (n.val + 12650)) = true := by decide
private theorem cl_w53 : ∀ n : Fin 50, centF (n.val + 12650) < 23 := by decide
private theorem bd_w53 : ∀ n : Fin 50, densSupG (n.val + 12650) < 2 ^ 1771 := by decide
private theorem cs_w54 : ∀ n : Fin 50, centredStar (densSupG (n.val + 12700)) (centF (n.val + 12700)) = true := by decide
private theorem cl_w54 : ∀ n : Fin 50, centF (n.val + 12700) < 23 := by decide
private theorem bd_w54 : ∀ n : Fin 50, densSupG (n.val + 12700) < 2 ^ 1771 := by decide
private theorem cs_w55 : ∀ n : Fin 50, centredStar (densSupG (n.val + 12750)) (centF (n.val + 12750)) = true := by decide
private theorem cl_w55 : ∀ n : Fin 50, centF (n.val + 12750) < 23 := by decide
private theorem bd_w55 : ∀ n : Fin 50, densSupG (n.val + 12750) < 2 ^ 1771 := by decide
private theorem cs_w56 : ∀ n : Fin 50, centredStar (densSupG (n.val + 12800)) (centF (n.val + 12800)) = true := by decide
private theorem cl_w56 : ∀ n : Fin 50, centF (n.val + 12800) < 23 := by decide
private theorem bd_w56 : ∀ n : Fin 50, densSupG (n.val + 12800) < 2 ^ 1771 := by decide
private theorem cs_w57 : ∀ n : Fin 50, centredStar (densSupG (n.val + 12850)) (centF (n.val + 12850)) = true := by decide
private theorem cl_w57 : ∀ n : Fin 50, centF (n.val + 12850) < 23 := by decide
private theorem bd_w57 : ∀ n : Fin 50, densSupG (n.val + 12850) < 2 ^ 1771 := by decide
private theorem cs_w58 : ∀ n : Fin 50, centredStar (densSupG (n.val + 12900)) (centF (n.val + 12900)) = true := by decide
private theorem cl_w58 : ∀ n : Fin 50, centF (n.val + 12900) < 23 := by decide
private theorem bd_w58 : ∀ n : Fin 50, densSupG (n.val + 12900) < 2 ^ 1771 := by decide
private theorem cs_w59 : ∀ n : Fin 50, centredStar (densSupG (n.val + 12950)) (centF (n.val + 12950)) = true := by decide
private theorem cl_w59 : ∀ n : Fin 50, centF (n.val + 12950) < 23 := by decide
private theorem bd_w59 : ∀ n : Fin 50, densSupG (n.val + 12950) < 2 ^ 1771 := by decide
private theorem cs_w60 : ∀ n : Fin 50, centredStar (densSupG (n.val + 13000)) (centF (n.val + 13000)) = true := by decide
private theorem cl_w60 : ∀ n : Fin 50, centF (n.val + 13000) < 23 := by decide
private theorem bd_w60 : ∀ n : Fin 50, densSupG (n.val + 13000) < 2 ^ 1771 := by decide
private theorem cs_w61 : ∀ n : Fin 50, centredStar (densSupG (n.val + 13050)) (centF (n.val + 13050)) = true := by decide
private theorem cl_w61 : ∀ n : Fin 50, centF (n.val + 13050) < 23 := by decide
private theorem bd_w61 : ∀ n : Fin 50, densSupG (n.val + 13050) < 2 ^ 1771 := by decide
private theorem cs_w62 : ∀ n : Fin 50, centredStar (densSupG (n.val + 13100)) (centF (n.val + 13100)) = true := by decide
private theorem cl_w62 : ∀ n : Fin 50, centF (n.val + 13100) < 23 := by decide
private theorem bd_w62 : ∀ n : Fin 50, densSupG (n.val + 13100) < 2 ^ 1771 := by decide
private theorem cs_w63 : ∀ n : Fin 50, centredStar (densSupG (n.val + 13150)) (centF (n.val + 13150)) = true := by decide
private theorem cl_w63 : ∀ n : Fin 50, centF (n.val + 13150) < 23 := by decide
private theorem bd_w63 : ∀ n : Fin 50, densSupG (n.val + 13150) < 2 ^ 1771 := by decide
private theorem cs_w64 : ∀ n : Fin 50, centredStar (densSupG (n.val + 13200)) (centF (n.val + 13200)) = true := by decide
private theorem cl_w64 : ∀ n : Fin 50, centF (n.val + 13200) < 23 := by decide
private theorem bd_w64 : ∀ n : Fin 50, densSupG (n.val + 13200) < 2 ^ 1771 := by decide
private theorem cs_w65 : ∀ n : Fin 50, centredStar (densSupG (n.val + 13250)) (centF (n.val + 13250)) = true := by decide
private theorem cl_w65 : ∀ n : Fin 50, centF (n.val + 13250) < 23 := by decide
private theorem bd_w65 : ∀ n : Fin 50, densSupG (n.val + 13250) < 2 ^ 1771 := by decide
private theorem cs_w66 : ∀ n : Fin 50, centredStar (densSupG (n.val + 13300)) (centF (n.val + 13300)) = true := by decide
private theorem cl_w66 : ∀ n : Fin 50, centF (n.val + 13300) < 23 := by decide
private theorem bd_w66 : ∀ n : Fin 50, densSupG (n.val + 13300) < 2 ^ 1771 := by decide
private theorem cs_w67 : ∀ n : Fin 50, centredStar (densSupG (n.val + 13350)) (centF (n.val + 13350)) = true := by decide
private theorem cl_w67 : ∀ n : Fin 50, centF (n.val + 13350) < 23 := by decide
private theorem bd_w67 : ∀ n : Fin 50, densSupG (n.val + 13350) < 2 ^ 1771 := by decide
private theorem cs_w68 : ∀ n : Fin 50, centredStar (densSupG (n.val + 13400)) (centF (n.val + 13400)) = true := by decide
private theorem cl_w68 : ∀ n : Fin 50, centF (n.val + 13400) < 23 := by decide
private theorem bd_w68 : ∀ n : Fin 50, densSupG (n.val + 13400) < 2 ^ 1771 := by decide
private theorem cs_w69 : ∀ n : Fin 50, centredStar (densSupG (n.val + 13450)) (centF (n.val + 13450)) = true := by decide
private theorem cl_w69 : ∀ n : Fin 50, centF (n.val + 13450) < 23 := by decide
private theorem bd_w69 : ∀ n : Fin 50, densSupG (n.val + 13450) < 2 ^ 1771 := by decide
private theorem cs_w70 : ∀ n : Fin 50, centredStar (densSupG (n.val + 13500)) (centF (n.val + 13500)) = true := by decide
private theorem cl_w70 : ∀ n : Fin 50, centF (n.val + 13500) < 23 := by decide
private theorem bd_w70 : ∀ n : Fin 50, densSupG (n.val + 13500) < 2 ^ 1771 := by decide
private theorem cs_w71 : ∀ n : Fin 50, centredStar (densSupG (n.val + 13550)) (centF (n.val + 13550)) = true := by decide
private theorem cl_w71 : ∀ n : Fin 50, centF (n.val + 13550) < 23 := by decide
private theorem bd_w71 : ∀ n : Fin 50, densSupG (n.val + 13550) < 2 ^ 1771 := by decide
private theorem cs_w72 : ∀ n : Fin 50, centredStar (densSupG (n.val + 13600)) (centF (n.val + 13600)) = true := by decide
private theorem cl_w72 : ∀ n : Fin 50, centF (n.val + 13600) < 23 := by decide
private theorem bd_w72 : ∀ n : Fin 50, densSupG (n.val + 13600) < 2 ^ 1771 := by decide
private theorem cs_w73 : ∀ n : Fin 50, centredStar (densSupG (n.val + 13650)) (centF (n.val + 13650)) = true := by decide
private theorem cl_w73 : ∀ n : Fin 50, centF (n.val + 13650) < 23 := by decide
private theorem bd_w73 : ∀ n : Fin 50, densSupG (n.val + 13650) < 2 ^ 1771 := by decide
private theorem cs_w74 : ∀ n : Fin 50, centredStar (densSupG (n.val + 13700)) (centF (n.val + 13700)) = true := by decide
private theorem cl_w74 : ∀ n : Fin 50, centF (n.val + 13700) < 23 := by decide
private theorem bd_w74 : ∀ n : Fin 50, densSupG (n.val + 13700) < 2 ^ 1771 := by decide
private theorem cs_w75 : ∀ n : Fin 50, centredStar (densSupG (n.val + 13750)) (centF (n.val + 13750)) = true := by decide
private theorem cl_w75 : ∀ n : Fin 50, centF (n.val + 13750) < 23 := by decide
private theorem bd_w75 : ∀ n : Fin 50, densSupG (n.val + 13750) < 2 ^ 1771 := by decide
private theorem cs_w76 : ∀ n : Fin 50, centredStar (densSupG (n.val + 13800)) (centF (n.val + 13800)) = true := by decide
private theorem cl_w76 : ∀ n : Fin 50, centF (n.val + 13800) < 23 := by decide
private theorem bd_w76 : ∀ n : Fin 50, densSupG (n.val + 13800) < 2 ^ 1771 := by decide
private theorem cs_w77 : ∀ n : Fin 50, centredStar (densSupG (n.val + 13850)) (centF (n.val + 13850)) = true := by decide
private theorem cl_w77 : ∀ n : Fin 50, centF (n.val + 13850) < 23 := by decide
private theorem bd_w77 : ∀ n : Fin 50, densSupG (n.val + 13850) < 2 ^ 1771 := by decide
private theorem cs_w78 : ∀ n : Fin 50, centredStar (densSupG (n.val + 13900)) (centF (n.val + 13900)) = true := by decide
private theorem cl_w78 : ∀ n : Fin 50, centF (n.val + 13900) < 23 := by decide
private theorem bd_w78 : ∀ n : Fin 50, densSupG (n.val + 13900) < 2 ^ 1771 := by decide
private theorem cs_w79 : ∀ n : Fin 50, centredStar (densSupG (n.val + 13950)) (centF (n.val + 13950)) = true := by decide
private theorem cl_w79 : ∀ n : Fin 50, centF (n.val + 13950) < 23 := by decide
private theorem bd_w79 : ∀ n : Fin 50, densSupG (n.val + 13950) < 2 ^ 1771 := by decide
private theorem cs_w80 : ∀ n : Fin 50, centredStar (densSupG (n.val + 14000)) (centF (n.val + 14000)) = true := by decide
private theorem cl_w80 : ∀ n : Fin 50, centF (n.val + 14000) < 23 := by decide
private theorem bd_w80 : ∀ n : Fin 50, densSupG (n.val + 14000) < 2 ^ 1771 := by decide
private theorem cs_w81 : ∀ n : Fin 50, centredStar (densSupG (n.val + 14050)) (centF (n.val + 14050)) = true := by decide
private theorem cl_w81 : ∀ n : Fin 50, centF (n.val + 14050) < 23 := by decide
private theorem bd_w81 : ∀ n : Fin 50, densSupG (n.val + 14050) < 2 ^ 1771 := by decide
private theorem cs_w82 : ∀ n : Fin 50, centredStar (densSupG (n.val + 14100)) (centF (n.val + 14100)) = true := by decide
private theorem cl_w82 : ∀ n : Fin 50, centF (n.val + 14100) < 23 := by decide
private theorem bd_w82 : ∀ n : Fin 50, densSupG (n.val + 14100) < 2 ^ 1771 := by decide
private theorem cs_w83 : ∀ n : Fin 50, centredStar (densSupG (n.val + 14150)) (centF (n.val + 14150)) = true := by decide
private theorem cl_w83 : ∀ n : Fin 50, centF (n.val + 14150) < 23 := by decide
private theorem bd_w83 : ∀ n : Fin 50, densSupG (n.val + 14150) < 2 ^ 1771 := by decide
private theorem cs_w84 : ∀ n : Fin 50, centredStar (densSupG (n.val + 14200)) (centF (n.val + 14200)) = true := by decide
private theorem cl_w84 : ∀ n : Fin 50, centF (n.val + 14200) < 23 := by decide
private theorem bd_w84 : ∀ n : Fin 50, densSupG (n.val + 14200) < 2 ^ 1771 := by decide
private theorem cs_w85 : ∀ n : Fin 50, centredStar (densSupG (n.val + 14250)) (centF (n.val + 14250)) = true := by decide
private theorem cl_w85 : ∀ n : Fin 50, centF (n.val + 14250) < 23 := by decide
private theorem bd_w85 : ∀ n : Fin 50, densSupG (n.val + 14250) < 2 ^ 1771 := by decide
private theorem cs_w86 : ∀ n : Fin 50, centredStar (densSupG (n.val + 14300)) (centF (n.val + 14300)) = true := by decide
private theorem cl_w86 : ∀ n : Fin 50, centF (n.val + 14300) < 23 := by decide
private theorem bd_w86 : ∀ n : Fin 50, densSupG (n.val + 14300) < 2 ^ 1771 := by decide
private theorem cs_w87 : ∀ n : Fin 50, centredStar (densSupG (n.val + 14350)) (centF (n.val + 14350)) = true := by decide
private theorem cl_w87 : ∀ n : Fin 50, centF (n.val + 14350) < 23 := by decide
private theorem bd_w87 : ∀ n : Fin 50, densSupG (n.val + 14350) < 2 ^ 1771 := by decide
private theorem cs_w88 : ∀ n : Fin 50, centredStar (densSupG (n.val + 14400)) (centF (n.val + 14400)) = true := by decide
private theorem cl_w88 : ∀ n : Fin 50, centF (n.val + 14400) < 23 := by decide
private theorem bd_w88 : ∀ n : Fin 50, densSupG (n.val + 14400) < 2 ^ 1771 := by decide
private theorem cs_w89 : ∀ n : Fin 50, centredStar (densSupG (n.val + 14450)) (centF (n.val + 14450)) = true := by decide
private theorem cl_w89 : ∀ n : Fin 50, centF (n.val + 14450) < 23 := by decide
private theorem bd_w89 : ∀ n : Fin 50, densSupG (n.val + 14450) < 2 ^ 1771 := by decide
private theorem cs_w90 : ∀ n : Fin 50, centredStar (densSupG (n.val + 14500)) (centF (n.val + 14500)) = true := by decide
private theorem cl_w90 : ∀ n : Fin 50, centF (n.val + 14500) < 23 := by decide
private theorem bd_w90 : ∀ n : Fin 50, densSupG (n.val + 14500) < 2 ^ 1771 := by decide
private theorem cs_w91 : ∀ n : Fin 50, centredStar (densSupG (n.val + 14550)) (centF (n.val + 14550)) = true := by decide
private theorem cl_w91 : ∀ n : Fin 50, centF (n.val + 14550) < 23 := by decide
private theorem bd_w91 : ∀ n : Fin 50, densSupG (n.val + 14550) < 2 ^ 1771 := by decide
private theorem cs_w92 : ∀ n : Fin 50, centredStar (densSupG (n.val + 14600)) (centF (n.val + 14600)) = true := by decide
private theorem cl_w92 : ∀ n : Fin 50, centF (n.val + 14600) < 23 := by decide
private theorem bd_w92 : ∀ n : Fin 50, densSupG (n.val + 14600) < 2 ^ 1771 := by decide
private theorem cs_w93 : ∀ n : Fin 50, centredStar (densSupG (n.val + 14650)) (centF (n.val + 14650)) = true := by decide
private theorem cl_w93 : ∀ n : Fin 50, centF (n.val + 14650) < 23 := by decide
private theorem bd_w93 : ∀ n : Fin 50, densSupG (n.val + 14650) < 2 ^ 1771 := by decide
private theorem cs_w94 : ∀ n : Fin 50, centredStar (densSupG (n.val + 14700)) (centF (n.val + 14700)) = true := by decide
private theorem cl_w94 : ∀ n : Fin 50, centF (n.val + 14700) < 23 := by decide
private theorem bd_w94 : ∀ n : Fin 50, densSupG (n.val + 14700) < 2 ^ 1771 := by decide
private theorem cs_w95 : ∀ n : Fin 50, centredStar (densSupG (n.val + 14750)) (centF (n.val + 14750)) = true := by decide
private theorem cl_w95 : ∀ n : Fin 50, centF (n.val + 14750) < 23 := by decide
private theorem bd_w95 : ∀ n : Fin 50, densSupG (n.val + 14750) < 2 ^ 1771 := by decide
private theorem cs_w96 : ∀ n : Fin 50, centredStar (densSupG (n.val + 14800)) (centF (n.val + 14800)) = true := by decide
private theorem cl_w96 : ∀ n : Fin 50, centF (n.val + 14800) < 23 := by decide
private theorem bd_w96 : ∀ n : Fin 50, densSupG (n.val + 14800) < 2 ^ 1771 := by decide
private theorem cs_w97 : ∀ n : Fin 50, centredStar (densSupG (n.val + 14850)) (centF (n.val + 14850)) = true := by decide
private theorem cl_w97 : ∀ n : Fin 50, centF (n.val + 14850) < 23 := by decide
private theorem bd_w97 : ∀ n : Fin 50, densSupG (n.val + 14850) < 2 ^ 1771 := by decide
private theorem cs_w98 : ∀ n : Fin 50, centredStar (densSupG (n.val + 14900)) (centF (n.val + 14900)) = true := by decide
private theorem cl_w98 : ∀ n : Fin 50, centF (n.val + 14900) < 23 := by decide
private theorem bd_w98 : ∀ n : Fin 50, densSupG (n.val + 14900) < 2 ^ 1771 := by decide
private theorem cs_w99 : ∀ n : Fin 50, centredStar (densSupG (n.val + 14950)) (centF (n.val + 14950)) = true := by decide
private theorem cl_w99 : ∀ n : Fin 50, centF (n.val + 14950) < 23 := by decide
private theorem bd_w99 : ∀ n : Fin 50, densSupG (n.val + 14950) < 2 ^ 1771 := by decide

theorem centredStar_range : ∀ n, 10000 ≤ n → n < 15000 → centredStar (densSupG n) (centF n) = true := by
  intro n hlo hhi
  by_cases h0 : n < 10050
  · have hr : n - 10000 < 50 := by omega
    have heq : n = (n - 10000) + 10000 := by omega
    rw [heq]
    exact cs_w0 ⟨n - 10000, hr⟩
  ·
    by_cases h1 : n < 10100
    · have hr : n - 10050 < 50 := by omega
      have heq : n = (n - 10050) + 10050 := by omega
      rw [heq]
      exact cs_w1 ⟨n - 10050, hr⟩
    ·
      by_cases h2 : n < 10150
      · have hr : n - 10100 < 50 := by omega
        have heq : n = (n - 10100) + 10100 := by omega
        rw [heq]
        exact cs_w2 ⟨n - 10100, hr⟩
      ·
        by_cases h3 : n < 10200
        · have hr : n - 10150 < 50 := by omega
          have heq : n = (n - 10150) + 10150 := by omega
          rw [heq]
          exact cs_w3 ⟨n - 10150, hr⟩
        ·
          by_cases h4 : n < 10250
          · have hr : n - 10200 < 50 := by omega
            have heq : n = (n - 10200) + 10200 := by omega
            rw [heq]
            exact cs_w4 ⟨n - 10200, hr⟩
          ·
            by_cases h5 : n < 10300
            · have hr : n - 10250 < 50 := by omega
              have heq : n = (n - 10250) + 10250 := by omega
              rw [heq]
              exact cs_w5 ⟨n - 10250, hr⟩
            ·
              by_cases h6 : n < 10350
              · have hr : n - 10300 < 50 := by omega
                have heq : n = (n - 10300) + 10300 := by omega
                rw [heq]
                exact cs_w6 ⟨n - 10300, hr⟩
              ·
                by_cases h7 : n < 10400
                · have hr : n - 10350 < 50 := by omega
                  have heq : n = (n - 10350) + 10350 := by omega
                  rw [heq]
                  exact cs_w7 ⟨n - 10350, hr⟩
                ·
                  by_cases h8 : n < 10450
                  · have hr : n - 10400 < 50 := by omega
                    have heq : n = (n - 10400) + 10400 := by omega
                    rw [heq]
                    exact cs_w8 ⟨n - 10400, hr⟩
                  ·
                    by_cases h9 : n < 10500
                    · have hr : n - 10450 < 50 := by omega
                      have heq : n = (n - 10450) + 10450 := by omega
                      rw [heq]
                      exact cs_w9 ⟨n - 10450, hr⟩
                    ·
                      by_cases h10 : n < 10550
                      · have hr : n - 10500 < 50 := by omega
                        have heq : n = (n - 10500) + 10500 := by omega
                        rw [heq]
                        exact cs_w10 ⟨n - 10500, hr⟩
                      ·
                        by_cases h11 : n < 10600
                        · have hr : n - 10550 < 50 := by omega
                          have heq : n = (n - 10550) + 10550 := by omega
                          rw [heq]
                          exact cs_w11 ⟨n - 10550, hr⟩
                        ·
                          by_cases h12 : n < 10650
                          · have hr : n - 10600 < 50 := by omega
                            have heq : n = (n - 10600) + 10600 := by omega
                            rw [heq]
                            exact cs_w12 ⟨n - 10600, hr⟩
                          ·
                            by_cases h13 : n < 10700
                            · have hr : n - 10650 < 50 := by omega
                              have heq : n = (n - 10650) + 10650 := by omega
                              rw [heq]
                              exact cs_w13 ⟨n - 10650, hr⟩
                            ·
                              by_cases h14 : n < 10750
                              · have hr : n - 10700 < 50 := by omega
                                have heq : n = (n - 10700) + 10700 := by omega
                                rw [heq]
                                exact cs_w14 ⟨n - 10700, hr⟩
                              ·
                                by_cases h15 : n < 10800
                                · have hr : n - 10750 < 50 := by omega
                                  have heq : n = (n - 10750) + 10750 := by omega
                                  rw [heq]
                                  exact cs_w15 ⟨n - 10750, hr⟩
                                ·
                                  by_cases h16 : n < 10850
                                  · have hr : n - 10800 < 50 := by omega
                                    have heq : n = (n - 10800) + 10800 := by omega
                                    rw [heq]
                                    exact cs_w16 ⟨n - 10800, hr⟩
                                  ·
                                    by_cases h17 : n < 10900
                                    · have hr : n - 10850 < 50 := by omega
                                      have heq : n = (n - 10850) + 10850 := by omega
                                      rw [heq]
                                      exact cs_w17 ⟨n - 10850, hr⟩
                                    ·
                                      by_cases h18 : n < 10950
                                      · have hr : n - 10900 < 50 := by omega
                                        have heq : n = (n - 10900) + 10900 := by omega
                                        rw [heq]
                                        exact cs_w18 ⟨n - 10900, hr⟩
                                      ·
                                        by_cases h19 : n < 11000
                                        · have hr : n - 10950 < 50 := by omega
                                          have heq : n = (n - 10950) + 10950 := by omega
                                          rw [heq]
                                          exact cs_w19 ⟨n - 10950, hr⟩
                                        ·
                                          by_cases h20 : n < 11050
                                          · have hr : n - 11000 < 50 := by omega
                                            have heq : n = (n - 11000) + 11000 := by omega
                                            rw [heq]
                                            exact cs_w20 ⟨n - 11000, hr⟩
                                          ·
                                            by_cases h21 : n < 11100
                                            · have hr : n - 11050 < 50 := by omega
                                              have heq : n = (n - 11050) + 11050 := by omega
                                              rw [heq]
                                              exact cs_w21 ⟨n - 11050, hr⟩
                                            ·
                                              by_cases h22 : n < 11150
                                              · have hr : n - 11100 < 50 := by omega
                                                have heq : n = (n - 11100) + 11100 := by omega
                                                rw [heq]
                                                exact cs_w22 ⟨n - 11100, hr⟩
                                              ·
                                                by_cases h23 : n < 11200
                                                · have hr : n - 11150 < 50 := by omega
                                                  have heq : n = (n - 11150) + 11150 := by omega
                                                  rw [heq]
                                                  exact cs_w23 ⟨n - 11150, hr⟩
                                                ·
                                                  by_cases h24 : n < 11250
                                                  · have hr : n - 11200 < 50 := by omega
                                                    have heq : n = (n - 11200) + 11200 := by omega
                                                    rw [heq]
                                                    exact cs_w24 ⟨n - 11200, hr⟩
                                                  ·
                                                    by_cases h25 : n < 11300
                                                    · have hr : n - 11250 < 50 := by omega
                                                      have heq : n = (n - 11250) + 11250 := by omega
                                                      rw [heq]
                                                      exact cs_w25 ⟨n - 11250, hr⟩
                                                    ·
                                                      by_cases h26 : n < 11350
                                                      · have hr : n - 11300 < 50 := by omega
                                                        have heq : n = (n - 11300) + 11300 := by omega
                                                        rw [heq]
                                                        exact cs_w26 ⟨n - 11300, hr⟩
                                                      ·
                                                        by_cases h27 : n < 11400
                                                        · have hr : n - 11350 < 50 := by omega
                                                          have heq : n = (n - 11350) + 11350 := by omega
                                                          rw [heq]
                                                          exact cs_w27 ⟨n - 11350, hr⟩
                                                        ·
                                                          by_cases h28 : n < 11450
                                                          · have hr : n - 11400 < 50 := by omega
                                                            have heq : n = (n - 11400) + 11400 := by omega
                                                            rw [heq]
                                                            exact cs_w28 ⟨n - 11400, hr⟩
                                                          ·
                                                            by_cases h29 : n < 11500
                                                            · have hr : n - 11450 < 50 := by omega
                                                              have heq : n = (n - 11450) + 11450 := by omega
                                                              rw [heq]
                                                              exact cs_w29 ⟨n - 11450, hr⟩
                                                            ·
                                                              by_cases h30 : n < 11550
                                                              · have hr : n - 11500 < 50 := by omega
                                                                have heq : n = (n - 11500) + 11500 := by omega
                                                                rw [heq]
                                                                exact cs_w30 ⟨n - 11500, hr⟩
                                                              ·
                                                                by_cases h31 : n < 11600
                                                                · have hr : n - 11550 < 50 := by omega
                                                                  have heq : n = (n - 11550) + 11550 := by omega
                                                                  rw [heq]
                                                                  exact cs_w31 ⟨n - 11550, hr⟩
                                                                ·
                                                                  by_cases h32 : n < 11650
                                                                  · have hr : n - 11600 < 50 := by omega
                                                                    have heq : n = (n - 11600) + 11600 := by omega
                                                                    rw [heq]
                                                                    exact cs_w32 ⟨n - 11600, hr⟩
                                                                  ·
                                                                    by_cases h33 : n < 11700
                                                                    · have hr : n - 11650 < 50 := by omega
                                                                      have heq : n = (n - 11650) + 11650 := by omega
                                                                      rw [heq]
                                                                      exact cs_w33 ⟨n - 11650, hr⟩
                                                                    ·
                                                                      by_cases h34 : n < 11750
                                                                      · have hr : n - 11700 < 50 := by omega
                                                                        have heq : n = (n - 11700) + 11700 := by omega
                                                                        rw [heq]
                                                                        exact cs_w34 ⟨n - 11700, hr⟩
                                                                      ·
                                                                        by_cases h35 : n < 11800
                                                                        · have hr : n - 11750 < 50 := by omega
                                                                          have heq : n = (n - 11750) + 11750 := by omega
                                                                          rw [heq]
                                                                          exact cs_w35 ⟨n - 11750, hr⟩
                                                                        ·
                                                                          by_cases h36 : n < 11850
                                                                          · have hr : n - 11800 < 50 := by omega
                                                                            have heq : n = (n - 11800) + 11800 := by omega
                                                                            rw [heq]
                                                                            exact cs_w36 ⟨n - 11800, hr⟩
                                                                          ·
                                                                            by_cases h37 : n < 11900
                                                                            · have hr : n - 11850 < 50 := by omega
                                                                              have heq : n = (n - 11850) + 11850 := by omega
                                                                              rw [heq]
                                                                              exact cs_w37 ⟨n - 11850, hr⟩
                                                                            ·
                                                                              by_cases h38 : n < 11950
                                                                              · have hr : n - 11900 < 50 := by omega
                                                                                have heq : n = (n - 11900) + 11900 := by omega
                                                                                rw [heq]
                                                                                exact cs_w38 ⟨n - 11900, hr⟩
                                                                              ·
                                                                                by_cases h39 : n < 12000
                                                                                · have hr : n - 11950 < 50 := by omega
                                                                                  have heq : n = (n - 11950) + 11950 := by omega
                                                                                  rw [heq]
                                                                                  exact cs_w39 ⟨n - 11950, hr⟩
                                                                                ·
                                                                                  by_cases h40 : n < 12050
                                                                                  · have hr : n - 12000 < 50 := by omega
                                                                                    have heq : n = (n - 12000) + 12000 := by omega
                                                                                    rw [heq]
                                                                                    exact cs_w40 ⟨n - 12000, hr⟩
                                                                                  ·
                                                                                    by_cases h41 : n < 12100
                                                                                    · have hr : n - 12050 < 50 := by omega
                                                                                      have heq : n = (n - 12050) + 12050 := by omega
                                                                                      rw [heq]
                                                                                      exact cs_w41 ⟨n - 12050, hr⟩
                                                                                    ·
                                                                                      by_cases h42 : n < 12150
                                                                                      · have hr : n - 12100 < 50 := by omega
                                                                                        have heq : n = (n - 12100) + 12100 := by omega
                                                                                        rw [heq]
                                                                                        exact cs_w42 ⟨n - 12100, hr⟩
                                                                                      ·
                                                                                        by_cases h43 : n < 12200
                                                                                        · have hr : n - 12150 < 50 := by omega
                                                                                          have heq : n = (n - 12150) + 12150 := by omega
                                                                                          rw [heq]
                                                                                          exact cs_w43 ⟨n - 12150, hr⟩
                                                                                        ·
                                                                                          by_cases h44 : n < 12250
                                                                                          · have hr : n - 12200 < 50 := by omega
                                                                                            have heq : n = (n - 12200) + 12200 := by omega
                                                                                            rw [heq]
                                                                                            exact cs_w44 ⟨n - 12200, hr⟩
                                                                                          ·
                                                                                            by_cases h45 : n < 12300
                                                                                            · have hr : n - 12250 < 50 := by omega
                                                                                              have heq : n = (n - 12250) + 12250 := by omega
                                                                                              rw [heq]
                                                                                              exact cs_w45 ⟨n - 12250, hr⟩
                                                                                            ·
                                                                                              by_cases h46 : n < 12350
                                                                                              · have hr : n - 12300 < 50 := by omega
                                                                                                have heq : n = (n - 12300) + 12300 := by omega
                                                                                                rw [heq]
                                                                                                exact cs_w46 ⟨n - 12300, hr⟩
                                                                                              ·
                                                                                                by_cases h47 : n < 12400
                                                                                                · have hr : n - 12350 < 50 := by omega
                                                                                                  have heq : n = (n - 12350) + 12350 := by omega
                                                                                                  rw [heq]
                                                                                                  exact cs_w47 ⟨n - 12350, hr⟩
                                                                                                ·
                                                                                                  by_cases h48 : n < 12450
                                                                                                  · have hr : n - 12400 < 50 := by omega
                                                                                                    have heq : n = (n - 12400) + 12400 := by omega
                                                                                                    rw [heq]
                                                                                                    exact cs_w48 ⟨n - 12400, hr⟩
                                                                                                  ·
                                                                                                    by_cases h49 : n < 12500
                                                                                                    · have hr : n - 12450 < 50 := by omega
                                                                                                      have heq : n = (n - 12450) + 12450 := by omega
                                                                                                      rw [heq]
                                                                                                      exact cs_w49 ⟨n - 12450, hr⟩
                                                                                                    ·
                                                                                                      by_cases h50 : n < 12550
                                                                                                      · have hr : n - 12500 < 50 := by omega
                                                                                                        have heq : n = (n - 12500) + 12500 := by omega
                                                                                                        rw [heq]
                                                                                                        exact cs_w50 ⟨n - 12500, hr⟩
                                                                                                      ·
                                                                                                        by_cases h51 : n < 12600
                                                                                                        · have hr : n - 12550 < 50 := by omega
                                                                                                          have heq : n = (n - 12550) + 12550 := by omega
                                                                                                          rw [heq]
                                                                                                          exact cs_w51 ⟨n - 12550, hr⟩
                                                                                                        ·
                                                                                                          by_cases h52 : n < 12650
                                                                                                          · have hr : n - 12600 < 50 := by omega
                                                                                                            have heq : n = (n - 12600) + 12600 := by omega
                                                                                                            rw [heq]
                                                                                                            exact cs_w52 ⟨n - 12600, hr⟩
                                                                                                          ·
                                                                                                            by_cases h53 : n < 12700
                                                                                                            · have hr : n - 12650 < 50 := by omega
                                                                                                              have heq : n = (n - 12650) + 12650 := by omega
                                                                                                              rw [heq]
                                                                                                              exact cs_w53 ⟨n - 12650, hr⟩
                                                                                                            ·
                                                                                                              by_cases h54 : n < 12750
                                                                                                              · have hr : n - 12700 < 50 := by omega
                                                                                                                have heq : n = (n - 12700) + 12700 := by omega
                                                                                                                rw [heq]
                                                                                                                exact cs_w54 ⟨n - 12700, hr⟩
                                                                                                              ·
                                                                                                                by_cases h55 : n < 12800
                                                                                                                · have hr : n - 12750 < 50 := by omega
                                                                                                                  have heq : n = (n - 12750) + 12750 := by omega
                                                                                                                  rw [heq]
                                                                                                                  exact cs_w55 ⟨n - 12750, hr⟩
                                                                                                                ·
                                                                                                                  by_cases h56 : n < 12850
                                                                                                                  · have hr : n - 12800 < 50 := by omega
                                                                                                                    have heq : n = (n - 12800) + 12800 := by omega
                                                                                                                    rw [heq]
                                                                                                                    exact cs_w56 ⟨n - 12800, hr⟩
                                                                                                                  ·
                                                                                                                    by_cases h57 : n < 12900
                                                                                                                    · have hr : n - 12850 < 50 := by omega
                                                                                                                      have heq : n = (n - 12850) + 12850 := by omega
                                                                                                                      rw [heq]
                                                                                                                      exact cs_w57 ⟨n - 12850, hr⟩
                                                                                                                    ·
                                                                                                                      by_cases h58 : n < 12950
                                                                                                                      · have hr : n - 12900 < 50 := by omega
                                                                                                                        have heq : n = (n - 12900) + 12900 := by omega
                                                                                                                        rw [heq]
                                                                                                                        exact cs_w58 ⟨n - 12900, hr⟩
                                                                                                                      ·
                                                                                                                        by_cases h59 : n < 13000
                                                                                                                        · have hr : n - 12950 < 50 := by omega
                                                                                                                          have heq : n = (n - 12950) + 12950 := by omega
                                                                                                                          rw [heq]
                                                                                                                          exact cs_w59 ⟨n - 12950, hr⟩
                                                                                                                        ·
                                                                                                                          by_cases h60 : n < 13050
                                                                                                                          · have hr : n - 13000 < 50 := by omega
                                                                                                                            have heq : n = (n - 13000) + 13000 := by omega
                                                                                                                            rw [heq]
                                                                                                                            exact cs_w60 ⟨n - 13000, hr⟩
                                                                                                                          ·
                                                                                                                            by_cases h61 : n < 13100
                                                                                                                            · have hr : n - 13050 < 50 := by omega
                                                                                                                              have heq : n = (n - 13050) + 13050 := by omega
                                                                                                                              rw [heq]
                                                                                                                              exact cs_w61 ⟨n - 13050, hr⟩
                                                                                                                            ·
                                                                                                                              by_cases h62 : n < 13150
                                                                                                                              · have hr : n - 13100 < 50 := by omega
                                                                                                                                have heq : n = (n - 13100) + 13100 := by omega
                                                                                                                                rw [heq]
                                                                                                                                exact cs_w62 ⟨n - 13100, hr⟩
                                                                                                                              ·
                                                                                                                                by_cases h63 : n < 13200
                                                                                                                                · have hr : n - 13150 < 50 := by omega
                                                                                                                                  have heq : n = (n - 13150) + 13150 := by omega
                                                                                                                                  rw [heq]
                                                                                                                                  exact cs_w63 ⟨n - 13150, hr⟩
                                                                                                                                ·
                                                                                                                                  by_cases h64 : n < 13250
                                                                                                                                  · have hr : n - 13200 < 50 := by omega
                                                                                                                                    have heq : n = (n - 13200) + 13200 := by omega
                                                                                                                                    rw [heq]
                                                                                                                                    exact cs_w64 ⟨n - 13200, hr⟩
                                                                                                                                  ·
                                                                                                                                    by_cases h65 : n < 13300
                                                                                                                                    · have hr : n - 13250 < 50 := by omega
                                                                                                                                      have heq : n = (n - 13250) + 13250 := by omega
                                                                                                                                      rw [heq]
                                                                                                                                      exact cs_w65 ⟨n - 13250, hr⟩
                                                                                                                                    ·
                                                                                                                                      by_cases h66 : n < 13350
                                                                                                                                      · have hr : n - 13300 < 50 := by omega
                                                                                                                                        have heq : n = (n - 13300) + 13300 := by omega
                                                                                                                                        rw [heq]
                                                                                                                                        exact cs_w66 ⟨n - 13300, hr⟩
                                                                                                                                      ·
                                                                                                                                        by_cases h67 : n < 13400
                                                                                                                                        · have hr : n - 13350 < 50 := by omega
                                                                                                                                          have heq : n = (n - 13350) + 13350 := by omega
                                                                                                                                          rw [heq]
                                                                                                                                          exact cs_w67 ⟨n - 13350, hr⟩
                                                                                                                                        ·
                                                                                                                                          by_cases h68 : n < 13450
                                                                                                                                          · have hr : n - 13400 < 50 := by omega
                                                                                                                                            have heq : n = (n - 13400) + 13400 := by omega
                                                                                                                                            rw [heq]
                                                                                                                                            exact cs_w68 ⟨n - 13400, hr⟩
                                                                                                                                          ·
                                                                                                                                            by_cases h69 : n < 13500
                                                                                                                                            · have hr : n - 13450 < 50 := by omega
                                                                                                                                              have heq : n = (n - 13450) + 13450 := by omega
                                                                                                                                              rw [heq]
                                                                                                                                              exact cs_w69 ⟨n - 13450, hr⟩
                                                                                                                                            ·
                                                                                                                                              by_cases h70 : n < 13550
                                                                                                                                              · have hr : n - 13500 < 50 := by omega
                                                                                                                                                have heq : n = (n - 13500) + 13500 := by omega
                                                                                                                                                rw [heq]
                                                                                                                                                exact cs_w70 ⟨n - 13500, hr⟩
                                                                                                                                              ·
                                                                                                                                                by_cases h71 : n < 13600
                                                                                                                                                · have hr : n - 13550 < 50 := by omega
                                                                                                                                                  have heq : n = (n - 13550) + 13550 := by omega
                                                                                                                                                  rw [heq]
                                                                                                                                                  exact cs_w71 ⟨n - 13550, hr⟩
                                                                                                                                                ·
                                                                                                                                                  by_cases h72 : n < 13650
                                                                                                                                                  · have hr : n - 13600 < 50 := by omega
                                                                                                                                                    have heq : n = (n - 13600) + 13600 := by omega
                                                                                                                                                    rw [heq]
                                                                                                                                                    exact cs_w72 ⟨n - 13600, hr⟩
                                                                                                                                                  ·
                                                                                                                                                    by_cases h73 : n < 13700
                                                                                                                                                    · have hr : n - 13650 < 50 := by omega
                                                                                                                                                      have heq : n = (n - 13650) + 13650 := by omega
                                                                                                                                                      rw [heq]
                                                                                                                                                      exact cs_w73 ⟨n - 13650, hr⟩
                                                                                                                                                    ·
                                                                                                                                                      by_cases h74 : n < 13750
                                                                                                                                                      · have hr : n - 13700 < 50 := by omega
                                                                                                                                                        have heq : n = (n - 13700) + 13700 := by omega
                                                                                                                                                        rw [heq]
                                                                                                                                                        exact cs_w74 ⟨n - 13700, hr⟩
                                                                                                                                                      ·
                                                                                                                                                        by_cases h75 : n < 13800
                                                                                                                                                        · have hr : n - 13750 < 50 := by omega
                                                                                                                                                          have heq : n = (n - 13750) + 13750 := by omega
                                                                                                                                                          rw [heq]
                                                                                                                                                          exact cs_w75 ⟨n - 13750, hr⟩
                                                                                                                                                        ·
                                                                                                                                                          by_cases h76 : n < 13850
                                                                                                                                                          · have hr : n - 13800 < 50 := by omega
                                                                                                                                                            have heq : n = (n - 13800) + 13800 := by omega
                                                                                                                                                            rw [heq]
                                                                                                                                                            exact cs_w76 ⟨n - 13800, hr⟩
                                                                                                                                                          ·
                                                                                                                                                            by_cases h77 : n < 13900
                                                                                                                                                            · have hr : n - 13850 < 50 := by omega
                                                                                                                                                              have heq : n = (n - 13850) + 13850 := by omega
                                                                                                                                                              rw [heq]
                                                                                                                                                              exact cs_w77 ⟨n - 13850, hr⟩
                                                                                                                                                            ·
                                                                                                                                                              by_cases h78 : n < 13950
                                                                                                                                                              · have hr : n - 13900 < 50 := by omega
                                                                                                                                                                have heq : n = (n - 13900) + 13900 := by omega
                                                                                                                                                                rw [heq]
                                                                                                                                                                exact cs_w78 ⟨n - 13900, hr⟩
                                                                                                                                                              ·
                                                                                                                                                                by_cases h79 : n < 14000
                                                                                                                                                                · have hr : n - 13950 < 50 := by omega
                                                                                                                                                                  have heq : n = (n - 13950) + 13950 := by omega
                                                                                                                                                                  rw [heq]
                                                                                                                                                                  exact cs_w79 ⟨n - 13950, hr⟩
                                                                                                                                                                ·
                                                                                                                                                                  by_cases h80 : n < 14050
                                                                                                                                                                  · have hr : n - 14000 < 50 := by omega
                                                                                                                                                                    have heq : n = (n - 14000) + 14000 := by omega
                                                                                                                                                                    rw [heq]
                                                                                                                                                                    exact cs_w80 ⟨n - 14000, hr⟩
                                                                                                                                                                  ·
                                                                                                                                                                    by_cases h81 : n < 14100
                                                                                                                                                                    · have hr : n - 14050 < 50 := by omega
                                                                                                                                                                      have heq : n = (n - 14050) + 14050 := by omega
                                                                                                                                                                      rw [heq]
                                                                                                                                                                      exact cs_w81 ⟨n - 14050, hr⟩
                                                                                                                                                                    ·
                                                                                                                                                                      by_cases h82 : n < 14150
                                                                                                                                                                      · have hr : n - 14100 < 50 := by omega
                                                                                                                                                                        have heq : n = (n - 14100) + 14100 := by omega
                                                                                                                                                                        rw [heq]
                                                                                                                                                                        exact cs_w82 ⟨n - 14100, hr⟩
                                                                                                                                                                      ·
                                                                                                                                                                        by_cases h83 : n < 14200
                                                                                                                                                                        · have hr : n - 14150 < 50 := by omega
                                                                                                                                                                          have heq : n = (n - 14150) + 14150 := by omega
                                                                                                                                                                          rw [heq]
                                                                                                                                                                          exact cs_w83 ⟨n - 14150, hr⟩
                                                                                                                                                                        ·
                                                                                                                                                                          by_cases h84 : n < 14250
                                                                                                                                                                          · have hr : n - 14200 < 50 := by omega
                                                                                                                                                                            have heq : n = (n - 14200) + 14200 := by omega
                                                                                                                                                                            rw [heq]
                                                                                                                                                                            exact cs_w84 ⟨n - 14200, hr⟩
                                                                                                                                                                          ·
                                                                                                                                                                            by_cases h85 : n < 14300
                                                                                                                                                                            · have hr : n - 14250 < 50 := by omega
                                                                                                                                                                              have heq : n = (n - 14250) + 14250 := by omega
                                                                                                                                                                              rw [heq]
                                                                                                                                                                              exact cs_w85 ⟨n - 14250, hr⟩
                                                                                                                                                                            ·
                                                                                                                                                                              by_cases h86 : n < 14350
                                                                                                                                                                              · have hr : n - 14300 < 50 := by omega
                                                                                                                                                                                have heq : n = (n - 14300) + 14300 := by omega
                                                                                                                                                                                rw [heq]
                                                                                                                                                                                exact cs_w86 ⟨n - 14300, hr⟩
                                                                                                                                                                              ·
                                                                                                                                                                                by_cases h87 : n < 14400
                                                                                                                                                                                · have hr : n - 14350 < 50 := by omega
                                                                                                                                                                                  have heq : n = (n - 14350) + 14350 := by omega
                                                                                                                                                                                  rw [heq]
                                                                                                                                                                                  exact cs_w87 ⟨n - 14350, hr⟩
                                                                                                                                                                                ·
                                                                                                                                                                                  by_cases h88 : n < 14450
                                                                                                                                                                                  · have hr : n - 14400 < 50 := by omega
                                                                                                                                                                                    have heq : n = (n - 14400) + 14400 := by omega
                                                                                                                                                                                    rw [heq]
                                                                                                                                                                                    exact cs_w88 ⟨n - 14400, hr⟩
                                                                                                                                                                                  ·
                                                                                                                                                                                    by_cases h89 : n < 14500
                                                                                                                                                                                    · have hr : n - 14450 < 50 := by omega
                                                                                                                                                                                      have heq : n = (n - 14450) + 14450 := by omega
                                                                                                                                                                                      rw [heq]
                                                                                                                                                                                      exact cs_w89 ⟨n - 14450, hr⟩
                                                                                                                                                                                    ·
                                                                                                                                                                                      by_cases h90 : n < 14550
                                                                                                                                                                                      · have hr : n - 14500 < 50 := by omega
                                                                                                                                                                                        have heq : n = (n - 14500) + 14500 := by omega
                                                                                                                                                                                        rw [heq]
                                                                                                                                                                                        exact cs_w90 ⟨n - 14500, hr⟩
                                                                                                                                                                                      ·
                                                                                                                                                                                        by_cases h91 : n < 14600
                                                                                                                                                                                        · have hr : n - 14550 < 50 := by omega
                                                                                                                                                                                          have heq : n = (n - 14550) + 14550 := by omega
                                                                                                                                                                                          rw [heq]
                                                                                                                                                                                          exact cs_w91 ⟨n - 14550, hr⟩
                                                                                                                                                                                        ·
                                                                                                                                                                                          by_cases h92 : n < 14650
                                                                                                                                                                                          · have hr : n - 14600 < 50 := by omega
                                                                                                                                                                                            have heq : n = (n - 14600) + 14600 := by omega
                                                                                                                                                                                            rw [heq]
                                                                                                                                                                                            exact cs_w92 ⟨n - 14600, hr⟩
                                                                                                                                                                                          ·
                                                                                                                                                                                            by_cases h93 : n < 14700
                                                                                                                                                                                            · have hr : n - 14650 < 50 := by omega
                                                                                                                                                                                              have heq : n = (n - 14650) + 14650 := by omega
                                                                                                                                                                                              rw [heq]
                                                                                                                                                                                              exact cs_w93 ⟨n - 14650, hr⟩
                                                                                                                                                                                            ·
                                                                                                                                                                                              by_cases h94 : n < 14750
                                                                                                                                                                                              · have hr : n - 14700 < 50 := by omega
                                                                                                                                                                                                have heq : n = (n - 14700) + 14700 := by omega
                                                                                                                                                                                                rw [heq]
                                                                                                                                                                                                exact cs_w94 ⟨n - 14700, hr⟩
                                                                                                                                                                                              ·
                                                                                                                                                                                                by_cases h95 : n < 14800
                                                                                                                                                                                                · have hr : n - 14750 < 50 := by omega
                                                                                                                                                                                                  have heq : n = (n - 14750) + 14750 := by omega
                                                                                                                                                                                                  rw [heq]
                                                                                                                                                                                                  exact cs_w95 ⟨n - 14750, hr⟩
                                                                                                                                                                                                ·
                                                                                                                                                                                                  by_cases h96 : n < 14850
                                                                                                                                                                                                  · have hr : n - 14800 < 50 := by omega
                                                                                                                                                                                                    have heq : n = (n - 14800) + 14800 := by omega
                                                                                                                                                                                                    rw [heq]
                                                                                                                                                                                                    exact cs_w96 ⟨n - 14800, hr⟩
                                                                                                                                                                                                  ·
                                                                                                                                                                                                    by_cases h97 : n < 14900
                                                                                                                                                                                                    · have hr : n - 14850 < 50 := by omega
                                                                                                                                                                                                      have heq : n = (n - 14850) + 14850 := by omega
                                                                                                                                                                                                      rw [heq]
                                                                                                                                                                                                      exact cs_w97 ⟨n - 14850, hr⟩
                                                                                                                                                                                                    ·
                                                                                                                                                                                                      by_cases h98 : n < 14950
                                                                                                                                                                                                      · have hr : n - 14900 < 50 := by omega
                                                                                                                                                                                                        have heq : n = (n - 14900) + 14900 := by omega
                                                                                                                                                                                                        rw [heq]
                                                                                                                                                                                                        exact cs_w98 ⟨n - 14900, hr⟩
                                                                                                                                                                                                      ·
                                                                                                                                                                                                        have hr : n - 14950 < 50 := by omega
                                                                                                                                                                                                        have heq : n = (n - 14950) + 14950 := by omega
                                                                                                                                                                                                        rw [heq]
                                                                                                                                                                                                        exact cs_w99 ⟨n - 14950, hr⟩

theorem centF_lt_range : ∀ n, 10000 ≤ n → n < 15000 → centF n < 23 := by
  intro n hlo hhi
  by_cases h0 : n < 10050
  · have hr : n - 10000 < 50 := by omega
    have heq : n = (n - 10000) + 10000 := by omega
    rw [heq]
    exact cl_w0 ⟨n - 10000, hr⟩
  ·
    by_cases h1 : n < 10100
    · have hr : n - 10050 < 50 := by omega
      have heq : n = (n - 10050) + 10050 := by omega
      rw [heq]
      exact cl_w1 ⟨n - 10050, hr⟩
    ·
      by_cases h2 : n < 10150
      · have hr : n - 10100 < 50 := by omega
        have heq : n = (n - 10100) + 10100 := by omega
        rw [heq]
        exact cl_w2 ⟨n - 10100, hr⟩
      ·
        by_cases h3 : n < 10200
        · have hr : n - 10150 < 50 := by omega
          have heq : n = (n - 10150) + 10150 := by omega
          rw [heq]
          exact cl_w3 ⟨n - 10150, hr⟩
        ·
          by_cases h4 : n < 10250
          · have hr : n - 10200 < 50 := by omega
            have heq : n = (n - 10200) + 10200 := by omega
            rw [heq]
            exact cl_w4 ⟨n - 10200, hr⟩
          ·
            by_cases h5 : n < 10300
            · have hr : n - 10250 < 50 := by omega
              have heq : n = (n - 10250) + 10250 := by omega
              rw [heq]
              exact cl_w5 ⟨n - 10250, hr⟩
            ·
              by_cases h6 : n < 10350
              · have hr : n - 10300 < 50 := by omega
                have heq : n = (n - 10300) + 10300 := by omega
                rw [heq]
                exact cl_w6 ⟨n - 10300, hr⟩
              ·
                by_cases h7 : n < 10400
                · have hr : n - 10350 < 50 := by omega
                  have heq : n = (n - 10350) + 10350 := by omega
                  rw [heq]
                  exact cl_w7 ⟨n - 10350, hr⟩
                ·
                  by_cases h8 : n < 10450
                  · have hr : n - 10400 < 50 := by omega
                    have heq : n = (n - 10400) + 10400 := by omega
                    rw [heq]
                    exact cl_w8 ⟨n - 10400, hr⟩
                  ·
                    by_cases h9 : n < 10500
                    · have hr : n - 10450 < 50 := by omega
                      have heq : n = (n - 10450) + 10450 := by omega
                      rw [heq]
                      exact cl_w9 ⟨n - 10450, hr⟩
                    ·
                      by_cases h10 : n < 10550
                      · have hr : n - 10500 < 50 := by omega
                        have heq : n = (n - 10500) + 10500 := by omega
                        rw [heq]
                        exact cl_w10 ⟨n - 10500, hr⟩
                      ·
                        by_cases h11 : n < 10600
                        · have hr : n - 10550 < 50 := by omega
                          have heq : n = (n - 10550) + 10550 := by omega
                          rw [heq]
                          exact cl_w11 ⟨n - 10550, hr⟩
                        ·
                          by_cases h12 : n < 10650
                          · have hr : n - 10600 < 50 := by omega
                            have heq : n = (n - 10600) + 10600 := by omega
                            rw [heq]
                            exact cl_w12 ⟨n - 10600, hr⟩
                          ·
                            by_cases h13 : n < 10700
                            · have hr : n - 10650 < 50 := by omega
                              have heq : n = (n - 10650) + 10650 := by omega
                              rw [heq]
                              exact cl_w13 ⟨n - 10650, hr⟩
                            ·
                              by_cases h14 : n < 10750
                              · have hr : n - 10700 < 50 := by omega
                                have heq : n = (n - 10700) + 10700 := by omega
                                rw [heq]
                                exact cl_w14 ⟨n - 10700, hr⟩
                              ·
                                by_cases h15 : n < 10800
                                · have hr : n - 10750 < 50 := by omega
                                  have heq : n = (n - 10750) + 10750 := by omega
                                  rw [heq]
                                  exact cl_w15 ⟨n - 10750, hr⟩
                                ·
                                  by_cases h16 : n < 10850
                                  · have hr : n - 10800 < 50 := by omega
                                    have heq : n = (n - 10800) + 10800 := by omega
                                    rw [heq]
                                    exact cl_w16 ⟨n - 10800, hr⟩
                                  ·
                                    by_cases h17 : n < 10900
                                    · have hr : n - 10850 < 50 := by omega
                                      have heq : n = (n - 10850) + 10850 := by omega
                                      rw [heq]
                                      exact cl_w17 ⟨n - 10850, hr⟩
                                    ·
                                      by_cases h18 : n < 10950
                                      · have hr : n - 10900 < 50 := by omega
                                        have heq : n = (n - 10900) + 10900 := by omega
                                        rw [heq]
                                        exact cl_w18 ⟨n - 10900, hr⟩
                                      ·
                                        by_cases h19 : n < 11000
                                        · have hr : n - 10950 < 50 := by omega
                                          have heq : n = (n - 10950) + 10950 := by omega
                                          rw [heq]
                                          exact cl_w19 ⟨n - 10950, hr⟩
                                        ·
                                          by_cases h20 : n < 11050
                                          · have hr : n - 11000 < 50 := by omega
                                            have heq : n = (n - 11000) + 11000 := by omega
                                            rw [heq]
                                            exact cl_w20 ⟨n - 11000, hr⟩
                                          ·
                                            by_cases h21 : n < 11100
                                            · have hr : n - 11050 < 50 := by omega
                                              have heq : n = (n - 11050) + 11050 := by omega
                                              rw [heq]
                                              exact cl_w21 ⟨n - 11050, hr⟩
                                            ·
                                              by_cases h22 : n < 11150
                                              · have hr : n - 11100 < 50 := by omega
                                                have heq : n = (n - 11100) + 11100 := by omega
                                                rw [heq]
                                                exact cl_w22 ⟨n - 11100, hr⟩
                                              ·
                                                by_cases h23 : n < 11200
                                                · have hr : n - 11150 < 50 := by omega
                                                  have heq : n = (n - 11150) + 11150 := by omega
                                                  rw [heq]
                                                  exact cl_w23 ⟨n - 11150, hr⟩
                                                ·
                                                  by_cases h24 : n < 11250
                                                  · have hr : n - 11200 < 50 := by omega
                                                    have heq : n = (n - 11200) + 11200 := by omega
                                                    rw [heq]
                                                    exact cl_w24 ⟨n - 11200, hr⟩
                                                  ·
                                                    by_cases h25 : n < 11300
                                                    · have hr : n - 11250 < 50 := by omega
                                                      have heq : n = (n - 11250) + 11250 := by omega
                                                      rw [heq]
                                                      exact cl_w25 ⟨n - 11250, hr⟩
                                                    ·
                                                      by_cases h26 : n < 11350
                                                      · have hr : n - 11300 < 50 := by omega
                                                        have heq : n = (n - 11300) + 11300 := by omega
                                                        rw [heq]
                                                        exact cl_w26 ⟨n - 11300, hr⟩
                                                      ·
                                                        by_cases h27 : n < 11400
                                                        · have hr : n - 11350 < 50 := by omega
                                                          have heq : n = (n - 11350) + 11350 := by omega
                                                          rw [heq]
                                                          exact cl_w27 ⟨n - 11350, hr⟩
                                                        ·
                                                          by_cases h28 : n < 11450
                                                          · have hr : n - 11400 < 50 := by omega
                                                            have heq : n = (n - 11400) + 11400 := by omega
                                                            rw [heq]
                                                            exact cl_w28 ⟨n - 11400, hr⟩
                                                          ·
                                                            by_cases h29 : n < 11500
                                                            · have hr : n - 11450 < 50 := by omega
                                                              have heq : n = (n - 11450) + 11450 := by omega
                                                              rw [heq]
                                                              exact cl_w29 ⟨n - 11450, hr⟩
                                                            ·
                                                              by_cases h30 : n < 11550
                                                              · have hr : n - 11500 < 50 := by omega
                                                                have heq : n = (n - 11500) + 11500 := by omega
                                                                rw [heq]
                                                                exact cl_w30 ⟨n - 11500, hr⟩
                                                              ·
                                                                by_cases h31 : n < 11600
                                                                · have hr : n - 11550 < 50 := by omega
                                                                  have heq : n = (n - 11550) + 11550 := by omega
                                                                  rw [heq]
                                                                  exact cl_w31 ⟨n - 11550, hr⟩
                                                                ·
                                                                  by_cases h32 : n < 11650
                                                                  · have hr : n - 11600 < 50 := by omega
                                                                    have heq : n = (n - 11600) + 11600 := by omega
                                                                    rw [heq]
                                                                    exact cl_w32 ⟨n - 11600, hr⟩
                                                                  ·
                                                                    by_cases h33 : n < 11700
                                                                    · have hr : n - 11650 < 50 := by omega
                                                                      have heq : n = (n - 11650) + 11650 := by omega
                                                                      rw [heq]
                                                                      exact cl_w33 ⟨n - 11650, hr⟩
                                                                    ·
                                                                      by_cases h34 : n < 11750
                                                                      · have hr : n - 11700 < 50 := by omega
                                                                        have heq : n = (n - 11700) + 11700 := by omega
                                                                        rw [heq]
                                                                        exact cl_w34 ⟨n - 11700, hr⟩
                                                                      ·
                                                                        by_cases h35 : n < 11800
                                                                        · have hr : n - 11750 < 50 := by omega
                                                                          have heq : n = (n - 11750) + 11750 := by omega
                                                                          rw [heq]
                                                                          exact cl_w35 ⟨n - 11750, hr⟩
                                                                        ·
                                                                          by_cases h36 : n < 11850
                                                                          · have hr : n - 11800 < 50 := by omega
                                                                            have heq : n = (n - 11800) + 11800 := by omega
                                                                            rw [heq]
                                                                            exact cl_w36 ⟨n - 11800, hr⟩
                                                                          ·
                                                                            by_cases h37 : n < 11900
                                                                            · have hr : n - 11850 < 50 := by omega
                                                                              have heq : n = (n - 11850) + 11850 := by omega
                                                                              rw [heq]
                                                                              exact cl_w37 ⟨n - 11850, hr⟩
                                                                            ·
                                                                              by_cases h38 : n < 11950
                                                                              · have hr : n - 11900 < 50 := by omega
                                                                                have heq : n = (n - 11900) + 11900 := by omega
                                                                                rw [heq]
                                                                                exact cl_w38 ⟨n - 11900, hr⟩
                                                                              ·
                                                                                by_cases h39 : n < 12000
                                                                                · have hr : n - 11950 < 50 := by omega
                                                                                  have heq : n = (n - 11950) + 11950 := by omega
                                                                                  rw [heq]
                                                                                  exact cl_w39 ⟨n - 11950, hr⟩
                                                                                ·
                                                                                  by_cases h40 : n < 12050
                                                                                  · have hr : n - 12000 < 50 := by omega
                                                                                    have heq : n = (n - 12000) + 12000 := by omega
                                                                                    rw [heq]
                                                                                    exact cl_w40 ⟨n - 12000, hr⟩
                                                                                  ·
                                                                                    by_cases h41 : n < 12100
                                                                                    · have hr : n - 12050 < 50 := by omega
                                                                                      have heq : n = (n - 12050) + 12050 := by omega
                                                                                      rw [heq]
                                                                                      exact cl_w41 ⟨n - 12050, hr⟩
                                                                                    ·
                                                                                      by_cases h42 : n < 12150
                                                                                      · have hr : n - 12100 < 50 := by omega
                                                                                        have heq : n = (n - 12100) + 12100 := by omega
                                                                                        rw [heq]
                                                                                        exact cl_w42 ⟨n - 12100, hr⟩
                                                                                      ·
                                                                                        by_cases h43 : n < 12200
                                                                                        · have hr : n - 12150 < 50 := by omega
                                                                                          have heq : n = (n - 12150) + 12150 := by omega
                                                                                          rw [heq]
                                                                                          exact cl_w43 ⟨n - 12150, hr⟩
                                                                                        ·
                                                                                          by_cases h44 : n < 12250
                                                                                          · have hr : n - 12200 < 50 := by omega
                                                                                            have heq : n = (n - 12200) + 12200 := by omega
                                                                                            rw [heq]
                                                                                            exact cl_w44 ⟨n - 12200, hr⟩
                                                                                          ·
                                                                                            by_cases h45 : n < 12300
                                                                                            · have hr : n - 12250 < 50 := by omega
                                                                                              have heq : n = (n - 12250) + 12250 := by omega
                                                                                              rw [heq]
                                                                                              exact cl_w45 ⟨n - 12250, hr⟩
                                                                                            ·
                                                                                              by_cases h46 : n < 12350
                                                                                              · have hr : n - 12300 < 50 := by omega
                                                                                                have heq : n = (n - 12300) + 12300 := by omega
                                                                                                rw [heq]
                                                                                                exact cl_w46 ⟨n - 12300, hr⟩
                                                                                              ·
                                                                                                by_cases h47 : n < 12400
                                                                                                · have hr : n - 12350 < 50 := by omega
                                                                                                  have heq : n = (n - 12350) + 12350 := by omega
                                                                                                  rw [heq]
                                                                                                  exact cl_w47 ⟨n - 12350, hr⟩
                                                                                                ·
                                                                                                  by_cases h48 : n < 12450
                                                                                                  · have hr : n - 12400 < 50 := by omega
                                                                                                    have heq : n = (n - 12400) + 12400 := by omega
                                                                                                    rw [heq]
                                                                                                    exact cl_w48 ⟨n - 12400, hr⟩
                                                                                                  ·
                                                                                                    by_cases h49 : n < 12500
                                                                                                    · have hr : n - 12450 < 50 := by omega
                                                                                                      have heq : n = (n - 12450) + 12450 := by omega
                                                                                                      rw [heq]
                                                                                                      exact cl_w49 ⟨n - 12450, hr⟩
                                                                                                    ·
                                                                                                      by_cases h50 : n < 12550
                                                                                                      · have hr : n - 12500 < 50 := by omega
                                                                                                        have heq : n = (n - 12500) + 12500 := by omega
                                                                                                        rw [heq]
                                                                                                        exact cl_w50 ⟨n - 12500, hr⟩
                                                                                                      ·
                                                                                                        by_cases h51 : n < 12600
                                                                                                        · have hr : n - 12550 < 50 := by omega
                                                                                                          have heq : n = (n - 12550) + 12550 := by omega
                                                                                                          rw [heq]
                                                                                                          exact cl_w51 ⟨n - 12550, hr⟩
                                                                                                        ·
                                                                                                          by_cases h52 : n < 12650
                                                                                                          · have hr : n - 12600 < 50 := by omega
                                                                                                            have heq : n = (n - 12600) + 12600 := by omega
                                                                                                            rw [heq]
                                                                                                            exact cl_w52 ⟨n - 12600, hr⟩
                                                                                                          ·
                                                                                                            by_cases h53 : n < 12700
                                                                                                            · have hr : n - 12650 < 50 := by omega
                                                                                                              have heq : n = (n - 12650) + 12650 := by omega
                                                                                                              rw [heq]
                                                                                                              exact cl_w53 ⟨n - 12650, hr⟩
                                                                                                            ·
                                                                                                              by_cases h54 : n < 12750
                                                                                                              · have hr : n - 12700 < 50 := by omega
                                                                                                                have heq : n = (n - 12700) + 12700 := by omega
                                                                                                                rw [heq]
                                                                                                                exact cl_w54 ⟨n - 12700, hr⟩
                                                                                                              ·
                                                                                                                by_cases h55 : n < 12800
                                                                                                                · have hr : n - 12750 < 50 := by omega
                                                                                                                  have heq : n = (n - 12750) + 12750 := by omega
                                                                                                                  rw [heq]
                                                                                                                  exact cl_w55 ⟨n - 12750, hr⟩
                                                                                                                ·
                                                                                                                  by_cases h56 : n < 12850
                                                                                                                  · have hr : n - 12800 < 50 := by omega
                                                                                                                    have heq : n = (n - 12800) + 12800 := by omega
                                                                                                                    rw [heq]
                                                                                                                    exact cl_w56 ⟨n - 12800, hr⟩
                                                                                                                  ·
                                                                                                                    by_cases h57 : n < 12900
                                                                                                                    · have hr : n - 12850 < 50 := by omega
                                                                                                                      have heq : n = (n - 12850) + 12850 := by omega
                                                                                                                      rw [heq]
                                                                                                                      exact cl_w57 ⟨n - 12850, hr⟩
                                                                                                                    ·
                                                                                                                      by_cases h58 : n < 12950
                                                                                                                      · have hr : n - 12900 < 50 := by omega
                                                                                                                        have heq : n = (n - 12900) + 12900 := by omega
                                                                                                                        rw [heq]
                                                                                                                        exact cl_w58 ⟨n - 12900, hr⟩
                                                                                                                      ·
                                                                                                                        by_cases h59 : n < 13000
                                                                                                                        · have hr : n - 12950 < 50 := by omega
                                                                                                                          have heq : n = (n - 12950) + 12950 := by omega
                                                                                                                          rw [heq]
                                                                                                                          exact cl_w59 ⟨n - 12950, hr⟩
                                                                                                                        ·
                                                                                                                          by_cases h60 : n < 13050
                                                                                                                          · have hr : n - 13000 < 50 := by omega
                                                                                                                            have heq : n = (n - 13000) + 13000 := by omega
                                                                                                                            rw [heq]
                                                                                                                            exact cl_w60 ⟨n - 13000, hr⟩
                                                                                                                          ·
                                                                                                                            by_cases h61 : n < 13100
                                                                                                                            · have hr : n - 13050 < 50 := by omega
                                                                                                                              have heq : n = (n - 13050) + 13050 := by omega
                                                                                                                              rw [heq]
                                                                                                                              exact cl_w61 ⟨n - 13050, hr⟩
                                                                                                                            ·
                                                                                                                              by_cases h62 : n < 13150
                                                                                                                              · have hr : n - 13100 < 50 := by omega
                                                                                                                                have heq : n = (n - 13100) + 13100 := by omega
                                                                                                                                rw [heq]
                                                                                                                                exact cl_w62 ⟨n - 13100, hr⟩
                                                                                                                              ·
                                                                                                                                by_cases h63 : n < 13200
                                                                                                                                · have hr : n - 13150 < 50 := by omega
                                                                                                                                  have heq : n = (n - 13150) + 13150 := by omega
                                                                                                                                  rw [heq]
                                                                                                                                  exact cl_w63 ⟨n - 13150, hr⟩
                                                                                                                                ·
                                                                                                                                  by_cases h64 : n < 13250
                                                                                                                                  · have hr : n - 13200 < 50 := by omega
                                                                                                                                    have heq : n = (n - 13200) + 13200 := by omega
                                                                                                                                    rw [heq]
                                                                                                                                    exact cl_w64 ⟨n - 13200, hr⟩
                                                                                                                                  ·
                                                                                                                                    by_cases h65 : n < 13300
                                                                                                                                    · have hr : n - 13250 < 50 := by omega
                                                                                                                                      have heq : n = (n - 13250) + 13250 := by omega
                                                                                                                                      rw [heq]
                                                                                                                                      exact cl_w65 ⟨n - 13250, hr⟩
                                                                                                                                    ·
                                                                                                                                      by_cases h66 : n < 13350
                                                                                                                                      · have hr : n - 13300 < 50 := by omega
                                                                                                                                        have heq : n = (n - 13300) + 13300 := by omega
                                                                                                                                        rw [heq]
                                                                                                                                        exact cl_w66 ⟨n - 13300, hr⟩
                                                                                                                                      ·
                                                                                                                                        by_cases h67 : n < 13400
                                                                                                                                        · have hr : n - 13350 < 50 := by omega
                                                                                                                                          have heq : n = (n - 13350) + 13350 := by omega
                                                                                                                                          rw [heq]
                                                                                                                                          exact cl_w67 ⟨n - 13350, hr⟩
                                                                                                                                        ·
                                                                                                                                          by_cases h68 : n < 13450
                                                                                                                                          · have hr : n - 13400 < 50 := by omega
                                                                                                                                            have heq : n = (n - 13400) + 13400 := by omega
                                                                                                                                            rw [heq]
                                                                                                                                            exact cl_w68 ⟨n - 13400, hr⟩
                                                                                                                                          ·
                                                                                                                                            by_cases h69 : n < 13500
                                                                                                                                            · have hr : n - 13450 < 50 := by omega
                                                                                                                                              have heq : n = (n - 13450) + 13450 := by omega
                                                                                                                                              rw [heq]
                                                                                                                                              exact cl_w69 ⟨n - 13450, hr⟩
                                                                                                                                            ·
                                                                                                                                              by_cases h70 : n < 13550
                                                                                                                                              · have hr : n - 13500 < 50 := by omega
                                                                                                                                                have heq : n = (n - 13500) + 13500 := by omega
                                                                                                                                                rw [heq]
                                                                                                                                                exact cl_w70 ⟨n - 13500, hr⟩
                                                                                                                                              ·
                                                                                                                                                by_cases h71 : n < 13600
                                                                                                                                                · have hr : n - 13550 < 50 := by omega
                                                                                                                                                  have heq : n = (n - 13550) + 13550 := by omega
                                                                                                                                                  rw [heq]
                                                                                                                                                  exact cl_w71 ⟨n - 13550, hr⟩
                                                                                                                                                ·
                                                                                                                                                  by_cases h72 : n < 13650
                                                                                                                                                  · have hr : n - 13600 < 50 := by omega
                                                                                                                                                    have heq : n = (n - 13600) + 13600 := by omega
                                                                                                                                                    rw [heq]
                                                                                                                                                    exact cl_w72 ⟨n - 13600, hr⟩
                                                                                                                                                  ·
                                                                                                                                                    by_cases h73 : n < 13700
                                                                                                                                                    · have hr : n - 13650 < 50 := by omega
                                                                                                                                                      have heq : n = (n - 13650) + 13650 := by omega
                                                                                                                                                      rw [heq]
                                                                                                                                                      exact cl_w73 ⟨n - 13650, hr⟩
                                                                                                                                                    ·
                                                                                                                                                      by_cases h74 : n < 13750
                                                                                                                                                      · have hr : n - 13700 < 50 := by omega
                                                                                                                                                        have heq : n = (n - 13700) + 13700 := by omega
                                                                                                                                                        rw [heq]
                                                                                                                                                        exact cl_w74 ⟨n - 13700, hr⟩
                                                                                                                                                      ·
                                                                                                                                                        by_cases h75 : n < 13800
                                                                                                                                                        · have hr : n - 13750 < 50 := by omega
                                                                                                                                                          have heq : n = (n - 13750) + 13750 := by omega
                                                                                                                                                          rw [heq]
                                                                                                                                                          exact cl_w75 ⟨n - 13750, hr⟩
                                                                                                                                                        ·
                                                                                                                                                          by_cases h76 : n < 13850
                                                                                                                                                          · have hr : n - 13800 < 50 := by omega
                                                                                                                                                            have heq : n = (n - 13800) + 13800 := by omega
                                                                                                                                                            rw [heq]
                                                                                                                                                            exact cl_w76 ⟨n - 13800, hr⟩
                                                                                                                                                          ·
                                                                                                                                                            by_cases h77 : n < 13900
                                                                                                                                                            · have hr : n - 13850 < 50 := by omega
                                                                                                                                                              have heq : n = (n - 13850) + 13850 := by omega
                                                                                                                                                              rw [heq]
                                                                                                                                                              exact cl_w77 ⟨n - 13850, hr⟩
                                                                                                                                                            ·
                                                                                                                                                              by_cases h78 : n < 13950
                                                                                                                                                              · have hr : n - 13900 < 50 := by omega
                                                                                                                                                                have heq : n = (n - 13900) + 13900 := by omega
                                                                                                                                                                rw [heq]
                                                                                                                                                                exact cl_w78 ⟨n - 13900, hr⟩
                                                                                                                                                              ·
                                                                                                                                                                by_cases h79 : n < 14000
                                                                                                                                                                · have hr : n - 13950 < 50 := by omega
                                                                                                                                                                  have heq : n = (n - 13950) + 13950 := by omega
                                                                                                                                                                  rw [heq]
                                                                                                                                                                  exact cl_w79 ⟨n - 13950, hr⟩
                                                                                                                                                                ·
                                                                                                                                                                  by_cases h80 : n < 14050
                                                                                                                                                                  · have hr : n - 14000 < 50 := by omega
                                                                                                                                                                    have heq : n = (n - 14000) + 14000 := by omega
                                                                                                                                                                    rw [heq]
                                                                                                                                                                    exact cl_w80 ⟨n - 14000, hr⟩
                                                                                                                                                                  ·
                                                                                                                                                                    by_cases h81 : n < 14100
                                                                                                                                                                    · have hr : n - 14050 < 50 := by omega
                                                                                                                                                                      have heq : n = (n - 14050) + 14050 := by omega
                                                                                                                                                                      rw [heq]
                                                                                                                                                                      exact cl_w81 ⟨n - 14050, hr⟩
                                                                                                                                                                    ·
                                                                                                                                                                      by_cases h82 : n < 14150
                                                                                                                                                                      · have hr : n - 14100 < 50 := by omega
                                                                                                                                                                        have heq : n = (n - 14100) + 14100 := by omega
                                                                                                                                                                        rw [heq]
                                                                                                                                                                        exact cl_w82 ⟨n - 14100, hr⟩
                                                                                                                                                                      ·
                                                                                                                                                                        by_cases h83 : n < 14200
                                                                                                                                                                        · have hr : n - 14150 < 50 := by omega
                                                                                                                                                                          have heq : n = (n - 14150) + 14150 := by omega
                                                                                                                                                                          rw [heq]
                                                                                                                                                                          exact cl_w83 ⟨n - 14150, hr⟩
                                                                                                                                                                        ·
                                                                                                                                                                          by_cases h84 : n < 14250
                                                                                                                                                                          · have hr : n - 14200 < 50 := by omega
                                                                                                                                                                            have heq : n = (n - 14200) + 14200 := by omega
                                                                                                                                                                            rw [heq]
                                                                                                                                                                            exact cl_w84 ⟨n - 14200, hr⟩
                                                                                                                                                                          ·
                                                                                                                                                                            by_cases h85 : n < 14300
                                                                                                                                                                            · have hr : n - 14250 < 50 := by omega
                                                                                                                                                                              have heq : n = (n - 14250) + 14250 := by omega
                                                                                                                                                                              rw [heq]
                                                                                                                                                                              exact cl_w85 ⟨n - 14250, hr⟩
                                                                                                                                                                            ·
                                                                                                                                                                              by_cases h86 : n < 14350
                                                                                                                                                                              · have hr : n - 14300 < 50 := by omega
                                                                                                                                                                                have heq : n = (n - 14300) + 14300 := by omega
                                                                                                                                                                                rw [heq]
                                                                                                                                                                                exact cl_w86 ⟨n - 14300, hr⟩
                                                                                                                                                                              ·
                                                                                                                                                                                by_cases h87 : n < 14400
                                                                                                                                                                                · have hr : n - 14350 < 50 := by omega
                                                                                                                                                                                  have heq : n = (n - 14350) + 14350 := by omega
                                                                                                                                                                                  rw [heq]
                                                                                                                                                                                  exact cl_w87 ⟨n - 14350, hr⟩
                                                                                                                                                                                ·
                                                                                                                                                                                  by_cases h88 : n < 14450
                                                                                                                                                                                  · have hr : n - 14400 < 50 := by omega
                                                                                                                                                                                    have heq : n = (n - 14400) + 14400 := by omega
                                                                                                                                                                                    rw [heq]
                                                                                                                                                                                    exact cl_w88 ⟨n - 14400, hr⟩
                                                                                                                                                                                  ·
                                                                                                                                                                                    by_cases h89 : n < 14500
                                                                                                                                                                                    · have hr : n - 14450 < 50 := by omega
                                                                                                                                                                                      have heq : n = (n - 14450) + 14450 := by omega
                                                                                                                                                                                      rw [heq]
                                                                                                                                                                                      exact cl_w89 ⟨n - 14450, hr⟩
                                                                                                                                                                                    ·
                                                                                                                                                                                      by_cases h90 : n < 14550
                                                                                                                                                                                      · have hr : n - 14500 < 50 := by omega
                                                                                                                                                                                        have heq : n = (n - 14500) + 14500 := by omega
                                                                                                                                                                                        rw [heq]
                                                                                                                                                                                        exact cl_w90 ⟨n - 14500, hr⟩
                                                                                                                                                                                      ·
                                                                                                                                                                                        by_cases h91 : n < 14600
                                                                                                                                                                                        · have hr : n - 14550 < 50 := by omega
                                                                                                                                                                                          have heq : n = (n - 14550) + 14550 := by omega
                                                                                                                                                                                          rw [heq]
                                                                                                                                                                                          exact cl_w91 ⟨n - 14550, hr⟩
                                                                                                                                                                                        ·
                                                                                                                                                                                          by_cases h92 : n < 14650
                                                                                                                                                                                          · have hr : n - 14600 < 50 := by omega
                                                                                                                                                                                            have heq : n = (n - 14600) + 14600 := by omega
                                                                                                                                                                                            rw [heq]
                                                                                                                                                                                            exact cl_w92 ⟨n - 14600, hr⟩
                                                                                                                                                                                          ·
                                                                                                                                                                                            by_cases h93 : n < 14700
                                                                                                                                                                                            · have hr : n - 14650 < 50 := by omega
                                                                                                                                                                                              have heq : n = (n - 14650) + 14650 := by omega
                                                                                                                                                                                              rw [heq]
                                                                                                                                                                                              exact cl_w93 ⟨n - 14650, hr⟩
                                                                                                                                                                                            ·
                                                                                                                                                                                              by_cases h94 : n < 14750
                                                                                                                                                                                              · have hr : n - 14700 < 50 := by omega
                                                                                                                                                                                                have heq : n = (n - 14700) + 14700 := by omega
                                                                                                                                                                                                rw [heq]
                                                                                                                                                                                                exact cl_w94 ⟨n - 14700, hr⟩
                                                                                                                                                                                              ·
                                                                                                                                                                                                by_cases h95 : n < 14800
                                                                                                                                                                                                · have hr : n - 14750 < 50 := by omega
                                                                                                                                                                                                  have heq : n = (n - 14750) + 14750 := by omega
                                                                                                                                                                                                  rw [heq]
                                                                                                                                                                                                  exact cl_w95 ⟨n - 14750, hr⟩
                                                                                                                                                                                                ·
                                                                                                                                                                                                  by_cases h96 : n < 14850
                                                                                                                                                                                                  · have hr : n - 14800 < 50 := by omega
                                                                                                                                                                                                    have heq : n = (n - 14800) + 14800 := by omega
                                                                                                                                                                                                    rw [heq]
                                                                                                                                                                                                    exact cl_w96 ⟨n - 14800, hr⟩
                                                                                                                                                                                                  ·
                                                                                                                                                                                                    by_cases h97 : n < 14900
                                                                                                                                                                                                    · have hr : n - 14850 < 50 := by omega
                                                                                                                                                                                                      have heq : n = (n - 14850) + 14850 := by omega
                                                                                                                                                                                                      rw [heq]
                                                                                                                                                                                                      exact cl_w97 ⟨n - 14850, hr⟩
                                                                                                                                                                                                    ·
                                                                                                                                                                                                      by_cases h98 : n < 14950
                                                                                                                                                                                                      · have hr : n - 14900 < 50 := by omega
                                                                                                                                                                                                        have heq : n = (n - 14900) + 14900 := by omega
                                                                                                                                                                                                        rw [heq]
                                                                                                                                                                                                        exact cl_w98 ⟨n - 14900, hr⟩
                                                                                                                                                                                                      ·
                                                                                                                                                                                                        have hr : n - 14950 < 50 := by omega
                                                                                                                                                                                                        have heq : n = (n - 14950) + 14950 := by omega
                                                                                                                                                                                                        rw [heq]
                                                                                                                                                                                                        exact cl_w99 ⟨n - 14950, hr⟩

theorem densSupG_lt_range : ∀ n, 10000 ≤ n → n < 15000 → densSupG n < 2 ^ 1771 := by
  intro n hlo hhi
  by_cases h0 : n < 10050
  · have hr : n - 10000 < 50 := by omega
    have heq : n = (n - 10000) + 10000 := by omega
    rw [heq]
    exact bd_w0 ⟨n - 10000, hr⟩
  ·
    by_cases h1 : n < 10100
    · have hr : n - 10050 < 50 := by omega
      have heq : n = (n - 10050) + 10050 := by omega
      rw [heq]
      exact bd_w1 ⟨n - 10050, hr⟩
    ·
      by_cases h2 : n < 10150
      · have hr : n - 10100 < 50 := by omega
        have heq : n = (n - 10100) + 10100 := by omega
        rw [heq]
        exact bd_w2 ⟨n - 10100, hr⟩
      ·
        by_cases h3 : n < 10200
        · have hr : n - 10150 < 50 := by omega
          have heq : n = (n - 10150) + 10150 := by omega
          rw [heq]
          exact bd_w3 ⟨n - 10150, hr⟩
        ·
          by_cases h4 : n < 10250
          · have hr : n - 10200 < 50 := by omega
            have heq : n = (n - 10200) + 10200 := by omega
            rw [heq]
            exact bd_w4 ⟨n - 10200, hr⟩
          ·
            by_cases h5 : n < 10300
            · have hr : n - 10250 < 50 := by omega
              have heq : n = (n - 10250) + 10250 := by omega
              rw [heq]
              exact bd_w5 ⟨n - 10250, hr⟩
            ·
              by_cases h6 : n < 10350
              · have hr : n - 10300 < 50 := by omega
                have heq : n = (n - 10300) + 10300 := by omega
                rw [heq]
                exact bd_w6 ⟨n - 10300, hr⟩
              ·
                by_cases h7 : n < 10400
                · have hr : n - 10350 < 50 := by omega
                  have heq : n = (n - 10350) + 10350 := by omega
                  rw [heq]
                  exact bd_w7 ⟨n - 10350, hr⟩
                ·
                  by_cases h8 : n < 10450
                  · have hr : n - 10400 < 50 := by omega
                    have heq : n = (n - 10400) + 10400 := by omega
                    rw [heq]
                    exact bd_w8 ⟨n - 10400, hr⟩
                  ·
                    by_cases h9 : n < 10500
                    · have hr : n - 10450 < 50 := by omega
                      have heq : n = (n - 10450) + 10450 := by omega
                      rw [heq]
                      exact bd_w9 ⟨n - 10450, hr⟩
                    ·
                      by_cases h10 : n < 10550
                      · have hr : n - 10500 < 50 := by omega
                        have heq : n = (n - 10500) + 10500 := by omega
                        rw [heq]
                        exact bd_w10 ⟨n - 10500, hr⟩
                      ·
                        by_cases h11 : n < 10600
                        · have hr : n - 10550 < 50 := by omega
                          have heq : n = (n - 10550) + 10550 := by omega
                          rw [heq]
                          exact bd_w11 ⟨n - 10550, hr⟩
                        ·
                          by_cases h12 : n < 10650
                          · have hr : n - 10600 < 50 := by omega
                            have heq : n = (n - 10600) + 10600 := by omega
                            rw [heq]
                            exact bd_w12 ⟨n - 10600, hr⟩
                          ·
                            by_cases h13 : n < 10700
                            · have hr : n - 10650 < 50 := by omega
                              have heq : n = (n - 10650) + 10650 := by omega
                              rw [heq]
                              exact bd_w13 ⟨n - 10650, hr⟩
                            ·
                              by_cases h14 : n < 10750
                              · have hr : n - 10700 < 50 := by omega
                                have heq : n = (n - 10700) + 10700 := by omega
                                rw [heq]
                                exact bd_w14 ⟨n - 10700, hr⟩
                              ·
                                by_cases h15 : n < 10800
                                · have hr : n - 10750 < 50 := by omega
                                  have heq : n = (n - 10750) + 10750 := by omega
                                  rw [heq]
                                  exact bd_w15 ⟨n - 10750, hr⟩
                                ·
                                  by_cases h16 : n < 10850
                                  · have hr : n - 10800 < 50 := by omega
                                    have heq : n = (n - 10800) + 10800 := by omega
                                    rw [heq]
                                    exact bd_w16 ⟨n - 10800, hr⟩
                                  ·
                                    by_cases h17 : n < 10900
                                    · have hr : n - 10850 < 50 := by omega
                                      have heq : n = (n - 10850) + 10850 := by omega
                                      rw [heq]
                                      exact bd_w17 ⟨n - 10850, hr⟩
                                    ·
                                      by_cases h18 : n < 10950
                                      · have hr : n - 10900 < 50 := by omega
                                        have heq : n = (n - 10900) + 10900 := by omega
                                        rw [heq]
                                        exact bd_w18 ⟨n - 10900, hr⟩
                                      ·
                                        by_cases h19 : n < 11000
                                        · have hr : n - 10950 < 50 := by omega
                                          have heq : n = (n - 10950) + 10950 := by omega
                                          rw [heq]
                                          exact bd_w19 ⟨n - 10950, hr⟩
                                        ·
                                          by_cases h20 : n < 11050
                                          · have hr : n - 11000 < 50 := by omega
                                            have heq : n = (n - 11000) + 11000 := by omega
                                            rw [heq]
                                            exact bd_w20 ⟨n - 11000, hr⟩
                                          ·
                                            by_cases h21 : n < 11100
                                            · have hr : n - 11050 < 50 := by omega
                                              have heq : n = (n - 11050) + 11050 := by omega
                                              rw [heq]
                                              exact bd_w21 ⟨n - 11050, hr⟩
                                            ·
                                              by_cases h22 : n < 11150
                                              · have hr : n - 11100 < 50 := by omega
                                                have heq : n = (n - 11100) + 11100 := by omega
                                                rw [heq]
                                                exact bd_w22 ⟨n - 11100, hr⟩
                                              ·
                                                by_cases h23 : n < 11200
                                                · have hr : n - 11150 < 50 := by omega
                                                  have heq : n = (n - 11150) + 11150 := by omega
                                                  rw [heq]
                                                  exact bd_w23 ⟨n - 11150, hr⟩
                                                ·
                                                  by_cases h24 : n < 11250
                                                  · have hr : n - 11200 < 50 := by omega
                                                    have heq : n = (n - 11200) + 11200 := by omega
                                                    rw [heq]
                                                    exact bd_w24 ⟨n - 11200, hr⟩
                                                  ·
                                                    by_cases h25 : n < 11300
                                                    · have hr : n - 11250 < 50 := by omega
                                                      have heq : n = (n - 11250) + 11250 := by omega
                                                      rw [heq]
                                                      exact bd_w25 ⟨n - 11250, hr⟩
                                                    ·
                                                      by_cases h26 : n < 11350
                                                      · have hr : n - 11300 < 50 := by omega
                                                        have heq : n = (n - 11300) + 11300 := by omega
                                                        rw [heq]
                                                        exact bd_w26 ⟨n - 11300, hr⟩
                                                      ·
                                                        by_cases h27 : n < 11400
                                                        · have hr : n - 11350 < 50 := by omega
                                                          have heq : n = (n - 11350) + 11350 := by omega
                                                          rw [heq]
                                                          exact bd_w27 ⟨n - 11350, hr⟩
                                                        ·
                                                          by_cases h28 : n < 11450
                                                          · have hr : n - 11400 < 50 := by omega
                                                            have heq : n = (n - 11400) + 11400 := by omega
                                                            rw [heq]
                                                            exact bd_w28 ⟨n - 11400, hr⟩
                                                          ·
                                                            by_cases h29 : n < 11500
                                                            · have hr : n - 11450 < 50 := by omega
                                                              have heq : n = (n - 11450) + 11450 := by omega
                                                              rw [heq]
                                                              exact bd_w29 ⟨n - 11450, hr⟩
                                                            ·
                                                              by_cases h30 : n < 11550
                                                              · have hr : n - 11500 < 50 := by omega
                                                                have heq : n = (n - 11500) + 11500 := by omega
                                                                rw [heq]
                                                                exact bd_w30 ⟨n - 11500, hr⟩
                                                              ·
                                                                by_cases h31 : n < 11600
                                                                · have hr : n - 11550 < 50 := by omega
                                                                  have heq : n = (n - 11550) + 11550 := by omega
                                                                  rw [heq]
                                                                  exact bd_w31 ⟨n - 11550, hr⟩
                                                                ·
                                                                  by_cases h32 : n < 11650
                                                                  · have hr : n - 11600 < 50 := by omega
                                                                    have heq : n = (n - 11600) + 11600 := by omega
                                                                    rw [heq]
                                                                    exact bd_w32 ⟨n - 11600, hr⟩
                                                                  ·
                                                                    by_cases h33 : n < 11700
                                                                    · have hr : n - 11650 < 50 := by omega
                                                                      have heq : n = (n - 11650) + 11650 := by omega
                                                                      rw [heq]
                                                                      exact bd_w33 ⟨n - 11650, hr⟩
                                                                    ·
                                                                      by_cases h34 : n < 11750
                                                                      · have hr : n - 11700 < 50 := by omega
                                                                        have heq : n = (n - 11700) + 11700 := by omega
                                                                        rw [heq]
                                                                        exact bd_w34 ⟨n - 11700, hr⟩
                                                                      ·
                                                                        by_cases h35 : n < 11800
                                                                        · have hr : n - 11750 < 50 := by omega
                                                                          have heq : n = (n - 11750) + 11750 := by omega
                                                                          rw [heq]
                                                                          exact bd_w35 ⟨n - 11750, hr⟩
                                                                        ·
                                                                          by_cases h36 : n < 11850
                                                                          · have hr : n - 11800 < 50 := by omega
                                                                            have heq : n = (n - 11800) + 11800 := by omega
                                                                            rw [heq]
                                                                            exact bd_w36 ⟨n - 11800, hr⟩
                                                                          ·
                                                                            by_cases h37 : n < 11900
                                                                            · have hr : n - 11850 < 50 := by omega
                                                                              have heq : n = (n - 11850) + 11850 := by omega
                                                                              rw [heq]
                                                                              exact bd_w37 ⟨n - 11850, hr⟩
                                                                            ·
                                                                              by_cases h38 : n < 11950
                                                                              · have hr : n - 11900 < 50 := by omega
                                                                                have heq : n = (n - 11900) + 11900 := by omega
                                                                                rw [heq]
                                                                                exact bd_w38 ⟨n - 11900, hr⟩
                                                                              ·
                                                                                by_cases h39 : n < 12000
                                                                                · have hr : n - 11950 < 50 := by omega
                                                                                  have heq : n = (n - 11950) + 11950 := by omega
                                                                                  rw [heq]
                                                                                  exact bd_w39 ⟨n - 11950, hr⟩
                                                                                ·
                                                                                  by_cases h40 : n < 12050
                                                                                  · have hr : n - 12000 < 50 := by omega
                                                                                    have heq : n = (n - 12000) + 12000 := by omega
                                                                                    rw [heq]
                                                                                    exact bd_w40 ⟨n - 12000, hr⟩
                                                                                  ·
                                                                                    by_cases h41 : n < 12100
                                                                                    · have hr : n - 12050 < 50 := by omega
                                                                                      have heq : n = (n - 12050) + 12050 := by omega
                                                                                      rw [heq]
                                                                                      exact bd_w41 ⟨n - 12050, hr⟩
                                                                                    ·
                                                                                      by_cases h42 : n < 12150
                                                                                      · have hr : n - 12100 < 50 := by omega
                                                                                        have heq : n = (n - 12100) + 12100 := by omega
                                                                                        rw [heq]
                                                                                        exact bd_w42 ⟨n - 12100, hr⟩
                                                                                      ·
                                                                                        by_cases h43 : n < 12200
                                                                                        · have hr : n - 12150 < 50 := by omega
                                                                                          have heq : n = (n - 12150) + 12150 := by omega
                                                                                          rw [heq]
                                                                                          exact bd_w43 ⟨n - 12150, hr⟩
                                                                                        ·
                                                                                          by_cases h44 : n < 12250
                                                                                          · have hr : n - 12200 < 50 := by omega
                                                                                            have heq : n = (n - 12200) + 12200 := by omega
                                                                                            rw [heq]
                                                                                            exact bd_w44 ⟨n - 12200, hr⟩
                                                                                          ·
                                                                                            by_cases h45 : n < 12300
                                                                                            · have hr : n - 12250 < 50 := by omega
                                                                                              have heq : n = (n - 12250) + 12250 := by omega
                                                                                              rw [heq]
                                                                                              exact bd_w45 ⟨n - 12250, hr⟩
                                                                                            ·
                                                                                              by_cases h46 : n < 12350
                                                                                              · have hr : n - 12300 < 50 := by omega
                                                                                                have heq : n = (n - 12300) + 12300 := by omega
                                                                                                rw [heq]
                                                                                                exact bd_w46 ⟨n - 12300, hr⟩
                                                                                              ·
                                                                                                by_cases h47 : n < 12400
                                                                                                · have hr : n - 12350 < 50 := by omega
                                                                                                  have heq : n = (n - 12350) + 12350 := by omega
                                                                                                  rw [heq]
                                                                                                  exact bd_w47 ⟨n - 12350, hr⟩
                                                                                                ·
                                                                                                  by_cases h48 : n < 12450
                                                                                                  · have hr : n - 12400 < 50 := by omega
                                                                                                    have heq : n = (n - 12400) + 12400 := by omega
                                                                                                    rw [heq]
                                                                                                    exact bd_w48 ⟨n - 12400, hr⟩
                                                                                                  ·
                                                                                                    by_cases h49 : n < 12500
                                                                                                    · have hr : n - 12450 < 50 := by omega
                                                                                                      have heq : n = (n - 12450) + 12450 := by omega
                                                                                                      rw [heq]
                                                                                                      exact bd_w49 ⟨n - 12450, hr⟩
                                                                                                    ·
                                                                                                      by_cases h50 : n < 12550
                                                                                                      · have hr : n - 12500 < 50 := by omega
                                                                                                        have heq : n = (n - 12500) + 12500 := by omega
                                                                                                        rw [heq]
                                                                                                        exact bd_w50 ⟨n - 12500, hr⟩
                                                                                                      ·
                                                                                                        by_cases h51 : n < 12600
                                                                                                        · have hr : n - 12550 < 50 := by omega
                                                                                                          have heq : n = (n - 12550) + 12550 := by omega
                                                                                                          rw [heq]
                                                                                                          exact bd_w51 ⟨n - 12550, hr⟩
                                                                                                        ·
                                                                                                          by_cases h52 : n < 12650
                                                                                                          · have hr : n - 12600 < 50 := by omega
                                                                                                            have heq : n = (n - 12600) + 12600 := by omega
                                                                                                            rw [heq]
                                                                                                            exact bd_w52 ⟨n - 12600, hr⟩
                                                                                                          ·
                                                                                                            by_cases h53 : n < 12700
                                                                                                            · have hr : n - 12650 < 50 := by omega
                                                                                                              have heq : n = (n - 12650) + 12650 := by omega
                                                                                                              rw [heq]
                                                                                                              exact bd_w53 ⟨n - 12650, hr⟩
                                                                                                            ·
                                                                                                              by_cases h54 : n < 12750
                                                                                                              · have hr : n - 12700 < 50 := by omega
                                                                                                                have heq : n = (n - 12700) + 12700 := by omega
                                                                                                                rw [heq]
                                                                                                                exact bd_w54 ⟨n - 12700, hr⟩
                                                                                                              ·
                                                                                                                by_cases h55 : n < 12800
                                                                                                                · have hr : n - 12750 < 50 := by omega
                                                                                                                  have heq : n = (n - 12750) + 12750 := by omega
                                                                                                                  rw [heq]
                                                                                                                  exact bd_w55 ⟨n - 12750, hr⟩
                                                                                                                ·
                                                                                                                  by_cases h56 : n < 12850
                                                                                                                  · have hr : n - 12800 < 50 := by omega
                                                                                                                    have heq : n = (n - 12800) + 12800 := by omega
                                                                                                                    rw [heq]
                                                                                                                    exact bd_w56 ⟨n - 12800, hr⟩
                                                                                                                  ·
                                                                                                                    by_cases h57 : n < 12900
                                                                                                                    · have hr : n - 12850 < 50 := by omega
                                                                                                                      have heq : n = (n - 12850) + 12850 := by omega
                                                                                                                      rw [heq]
                                                                                                                      exact bd_w57 ⟨n - 12850, hr⟩
                                                                                                                    ·
                                                                                                                      by_cases h58 : n < 12950
                                                                                                                      · have hr : n - 12900 < 50 := by omega
                                                                                                                        have heq : n = (n - 12900) + 12900 := by omega
                                                                                                                        rw [heq]
                                                                                                                        exact bd_w58 ⟨n - 12900, hr⟩
                                                                                                                      ·
                                                                                                                        by_cases h59 : n < 13000
                                                                                                                        · have hr : n - 12950 < 50 := by omega
                                                                                                                          have heq : n = (n - 12950) + 12950 := by omega
                                                                                                                          rw [heq]
                                                                                                                          exact bd_w59 ⟨n - 12950, hr⟩
                                                                                                                        ·
                                                                                                                          by_cases h60 : n < 13050
                                                                                                                          · have hr : n - 13000 < 50 := by omega
                                                                                                                            have heq : n = (n - 13000) + 13000 := by omega
                                                                                                                            rw [heq]
                                                                                                                            exact bd_w60 ⟨n - 13000, hr⟩
                                                                                                                          ·
                                                                                                                            by_cases h61 : n < 13100
                                                                                                                            · have hr : n - 13050 < 50 := by omega
                                                                                                                              have heq : n = (n - 13050) + 13050 := by omega
                                                                                                                              rw [heq]
                                                                                                                              exact bd_w61 ⟨n - 13050, hr⟩
                                                                                                                            ·
                                                                                                                              by_cases h62 : n < 13150
                                                                                                                              · have hr : n - 13100 < 50 := by omega
                                                                                                                                have heq : n = (n - 13100) + 13100 := by omega
                                                                                                                                rw [heq]
                                                                                                                                exact bd_w62 ⟨n - 13100, hr⟩
                                                                                                                              ·
                                                                                                                                by_cases h63 : n < 13200
                                                                                                                                · have hr : n - 13150 < 50 := by omega
                                                                                                                                  have heq : n = (n - 13150) + 13150 := by omega
                                                                                                                                  rw [heq]
                                                                                                                                  exact bd_w63 ⟨n - 13150, hr⟩
                                                                                                                                ·
                                                                                                                                  by_cases h64 : n < 13250
                                                                                                                                  · have hr : n - 13200 < 50 := by omega
                                                                                                                                    have heq : n = (n - 13200) + 13200 := by omega
                                                                                                                                    rw [heq]
                                                                                                                                    exact bd_w64 ⟨n - 13200, hr⟩
                                                                                                                                  ·
                                                                                                                                    by_cases h65 : n < 13300
                                                                                                                                    · have hr : n - 13250 < 50 := by omega
                                                                                                                                      have heq : n = (n - 13250) + 13250 := by omega
                                                                                                                                      rw [heq]
                                                                                                                                      exact bd_w65 ⟨n - 13250, hr⟩
                                                                                                                                    ·
                                                                                                                                      by_cases h66 : n < 13350
                                                                                                                                      · have hr : n - 13300 < 50 := by omega
                                                                                                                                        have heq : n = (n - 13300) + 13300 := by omega
                                                                                                                                        rw [heq]
                                                                                                                                        exact bd_w66 ⟨n - 13300, hr⟩
                                                                                                                                      ·
                                                                                                                                        by_cases h67 : n < 13400
                                                                                                                                        · have hr : n - 13350 < 50 := by omega
                                                                                                                                          have heq : n = (n - 13350) + 13350 := by omega
                                                                                                                                          rw [heq]
                                                                                                                                          exact bd_w67 ⟨n - 13350, hr⟩
                                                                                                                                        ·
                                                                                                                                          by_cases h68 : n < 13450
                                                                                                                                          · have hr : n - 13400 < 50 := by omega
                                                                                                                                            have heq : n = (n - 13400) + 13400 := by omega
                                                                                                                                            rw [heq]
                                                                                                                                            exact bd_w68 ⟨n - 13400, hr⟩
                                                                                                                                          ·
                                                                                                                                            by_cases h69 : n < 13500
                                                                                                                                            · have hr : n - 13450 < 50 := by omega
                                                                                                                                              have heq : n = (n - 13450) + 13450 := by omega
                                                                                                                                              rw [heq]
                                                                                                                                              exact bd_w69 ⟨n - 13450, hr⟩
                                                                                                                                            ·
                                                                                                                                              by_cases h70 : n < 13550
                                                                                                                                              · have hr : n - 13500 < 50 := by omega
                                                                                                                                                have heq : n = (n - 13500) + 13500 := by omega
                                                                                                                                                rw [heq]
                                                                                                                                                exact bd_w70 ⟨n - 13500, hr⟩
                                                                                                                                              ·
                                                                                                                                                by_cases h71 : n < 13600
                                                                                                                                                · have hr : n - 13550 < 50 := by omega
                                                                                                                                                  have heq : n = (n - 13550) + 13550 := by omega
                                                                                                                                                  rw [heq]
                                                                                                                                                  exact bd_w71 ⟨n - 13550, hr⟩
                                                                                                                                                ·
                                                                                                                                                  by_cases h72 : n < 13650
                                                                                                                                                  · have hr : n - 13600 < 50 := by omega
                                                                                                                                                    have heq : n = (n - 13600) + 13600 := by omega
                                                                                                                                                    rw [heq]
                                                                                                                                                    exact bd_w72 ⟨n - 13600, hr⟩
                                                                                                                                                  ·
                                                                                                                                                    by_cases h73 : n < 13700
                                                                                                                                                    · have hr : n - 13650 < 50 := by omega
                                                                                                                                                      have heq : n = (n - 13650) + 13650 := by omega
                                                                                                                                                      rw [heq]
                                                                                                                                                      exact bd_w73 ⟨n - 13650, hr⟩
                                                                                                                                                    ·
                                                                                                                                                      by_cases h74 : n < 13750
                                                                                                                                                      · have hr : n - 13700 < 50 := by omega
                                                                                                                                                        have heq : n = (n - 13700) + 13700 := by omega
                                                                                                                                                        rw [heq]
                                                                                                                                                        exact bd_w74 ⟨n - 13700, hr⟩
                                                                                                                                                      ·
                                                                                                                                                        by_cases h75 : n < 13800
                                                                                                                                                        · have hr : n - 13750 < 50 := by omega
                                                                                                                                                          have heq : n = (n - 13750) + 13750 := by omega
                                                                                                                                                          rw [heq]
                                                                                                                                                          exact bd_w75 ⟨n - 13750, hr⟩
                                                                                                                                                        ·
                                                                                                                                                          by_cases h76 : n < 13850
                                                                                                                                                          · have hr : n - 13800 < 50 := by omega
                                                                                                                                                            have heq : n = (n - 13800) + 13800 := by omega
                                                                                                                                                            rw [heq]
                                                                                                                                                            exact bd_w76 ⟨n - 13800, hr⟩
                                                                                                                                                          ·
                                                                                                                                                            by_cases h77 : n < 13900
                                                                                                                                                            · have hr : n - 13850 < 50 := by omega
                                                                                                                                                              have heq : n = (n - 13850) + 13850 := by omega
                                                                                                                                                              rw [heq]
                                                                                                                                                              exact bd_w77 ⟨n - 13850, hr⟩
                                                                                                                                                            ·
                                                                                                                                                              by_cases h78 : n < 13950
                                                                                                                                                              · have hr : n - 13900 < 50 := by omega
                                                                                                                                                                have heq : n = (n - 13900) + 13900 := by omega
                                                                                                                                                                rw [heq]
                                                                                                                                                                exact bd_w78 ⟨n - 13900, hr⟩
                                                                                                                                                              ·
                                                                                                                                                                by_cases h79 : n < 14000
                                                                                                                                                                · have hr : n - 13950 < 50 := by omega
                                                                                                                                                                  have heq : n = (n - 13950) + 13950 := by omega
                                                                                                                                                                  rw [heq]
                                                                                                                                                                  exact bd_w79 ⟨n - 13950, hr⟩
                                                                                                                                                                ·
                                                                                                                                                                  by_cases h80 : n < 14050
                                                                                                                                                                  · have hr : n - 14000 < 50 := by omega
                                                                                                                                                                    have heq : n = (n - 14000) + 14000 := by omega
                                                                                                                                                                    rw [heq]
                                                                                                                                                                    exact bd_w80 ⟨n - 14000, hr⟩
                                                                                                                                                                  ·
                                                                                                                                                                    by_cases h81 : n < 14100
                                                                                                                                                                    · have hr : n - 14050 < 50 := by omega
                                                                                                                                                                      have heq : n = (n - 14050) + 14050 := by omega
                                                                                                                                                                      rw [heq]
                                                                                                                                                                      exact bd_w81 ⟨n - 14050, hr⟩
                                                                                                                                                                    ·
                                                                                                                                                                      by_cases h82 : n < 14150
                                                                                                                                                                      · have hr : n - 14100 < 50 := by omega
                                                                                                                                                                        have heq : n = (n - 14100) + 14100 := by omega
                                                                                                                                                                        rw [heq]
                                                                                                                                                                        exact bd_w82 ⟨n - 14100, hr⟩
                                                                                                                                                                      ·
                                                                                                                                                                        by_cases h83 : n < 14200
                                                                                                                                                                        · have hr : n - 14150 < 50 := by omega
                                                                                                                                                                          have heq : n = (n - 14150) + 14150 := by omega
                                                                                                                                                                          rw [heq]
                                                                                                                                                                          exact bd_w83 ⟨n - 14150, hr⟩
                                                                                                                                                                        ·
                                                                                                                                                                          by_cases h84 : n < 14250
                                                                                                                                                                          · have hr : n - 14200 < 50 := by omega
                                                                                                                                                                            have heq : n = (n - 14200) + 14200 := by omega
                                                                                                                                                                            rw [heq]
                                                                                                                                                                            exact bd_w84 ⟨n - 14200, hr⟩
                                                                                                                                                                          ·
                                                                                                                                                                            by_cases h85 : n < 14300
                                                                                                                                                                            · have hr : n - 14250 < 50 := by omega
                                                                                                                                                                              have heq : n = (n - 14250) + 14250 := by omega
                                                                                                                                                                              rw [heq]
                                                                                                                                                                              exact bd_w85 ⟨n - 14250, hr⟩
                                                                                                                                                                            ·
                                                                                                                                                                              by_cases h86 : n < 14350
                                                                                                                                                                              · have hr : n - 14300 < 50 := by omega
                                                                                                                                                                                have heq : n = (n - 14300) + 14300 := by omega
                                                                                                                                                                                rw [heq]
                                                                                                                                                                                exact bd_w86 ⟨n - 14300, hr⟩
                                                                                                                                                                              ·
                                                                                                                                                                                by_cases h87 : n < 14400
                                                                                                                                                                                · have hr : n - 14350 < 50 := by omega
                                                                                                                                                                                  have heq : n = (n - 14350) + 14350 := by omega
                                                                                                                                                                                  rw [heq]
                                                                                                                                                                                  exact bd_w87 ⟨n - 14350, hr⟩
                                                                                                                                                                                ·
                                                                                                                                                                                  by_cases h88 : n < 14450
                                                                                                                                                                                  · have hr : n - 14400 < 50 := by omega
                                                                                                                                                                                    have heq : n = (n - 14400) + 14400 := by omega
                                                                                                                                                                                    rw [heq]
                                                                                                                                                                                    exact bd_w88 ⟨n - 14400, hr⟩
                                                                                                                                                                                  ·
                                                                                                                                                                                    by_cases h89 : n < 14500
                                                                                                                                                                                    · have hr : n - 14450 < 50 := by omega
                                                                                                                                                                                      have heq : n = (n - 14450) + 14450 := by omega
                                                                                                                                                                                      rw [heq]
                                                                                                                                                                                      exact bd_w89 ⟨n - 14450, hr⟩
                                                                                                                                                                                    ·
                                                                                                                                                                                      by_cases h90 : n < 14550
                                                                                                                                                                                      · have hr : n - 14500 < 50 := by omega
                                                                                                                                                                                        have heq : n = (n - 14500) + 14500 := by omega
                                                                                                                                                                                        rw [heq]
                                                                                                                                                                                        exact bd_w90 ⟨n - 14500, hr⟩
                                                                                                                                                                                      ·
                                                                                                                                                                                        by_cases h91 : n < 14600
                                                                                                                                                                                        · have hr : n - 14550 < 50 := by omega
                                                                                                                                                                                          have heq : n = (n - 14550) + 14550 := by omega
                                                                                                                                                                                          rw [heq]
                                                                                                                                                                                          exact bd_w91 ⟨n - 14550, hr⟩
                                                                                                                                                                                        ·
                                                                                                                                                                                          by_cases h92 : n < 14650
                                                                                                                                                                                          · have hr : n - 14600 < 50 := by omega
                                                                                                                                                                                            have heq : n = (n - 14600) + 14600 := by omega
                                                                                                                                                                                            rw [heq]
                                                                                                                                                                                            exact bd_w92 ⟨n - 14600, hr⟩
                                                                                                                                                                                          ·
                                                                                                                                                                                            by_cases h93 : n < 14700
                                                                                                                                                                                            · have hr : n - 14650 < 50 := by omega
                                                                                                                                                                                              have heq : n = (n - 14650) + 14650 := by omega
                                                                                                                                                                                              rw [heq]
                                                                                                                                                                                              exact bd_w93 ⟨n - 14650, hr⟩
                                                                                                                                                                                            ·
                                                                                                                                                                                              by_cases h94 : n < 14750
                                                                                                                                                                                              · have hr : n - 14700 < 50 := by omega
                                                                                                                                                                                                have heq : n = (n - 14700) + 14700 := by omega
                                                                                                                                                                                                rw [heq]
                                                                                                                                                                                                exact bd_w94 ⟨n - 14700, hr⟩
                                                                                                                                                                                              ·
                                                                                                                                                                                                by_cases h95 : n < 14800
                                                                                                                                                                                                · have hr : n - 14750 < 50 := by omega
                                                                                                                                                                                                  have heq : n = (n - 14750) + 14750 := by omega
                                                                                                                                                                                                  rw [heq]
                                                                                                                                                                                                  exact bd_w95 ⟨n - 14750, hr⟩
                                                                                                                                                                                                ·
                                                                                                                                                                                                  by_cases h96 : n < 14850
                                                                                                                                                                                                  · have hr : n - 14800 < 50 := by omega
                                                                                                                                                                                                    have heq : n = (n - 14800) + 14800 := by omega
                                                                                                                                                                                                    rw [heq]
                                                                                                                                                                                                    exact bd_w96 ⟨n - 14800, hr⟩
                                                                                                                                                                                                  ·
                                                                                                                                                                                                    by_cases h97 : n < 14900
                                                                                                                                                                                                    · have hr : n - 14850 < 50 := by omega
                                                                                                                                                                                                      have heq : n = (n - 14850) + 14850 := by omega
                                                                                                                                                                                                      rw [heq]
                                                                                                                                                                                                      exact bd_w97 ⟨n - 14850, hr⟩
                                                                                                                                                                                                    ·
                                                                                                                                                                                                      by_cases h98 : n < 14950
                                                                                                                                                                                                      · have hr : n - 14900 < 50 := by omega
                                                                                                                                                                                                        have heq : n = (n - 14900) + 14900 := by omega
                                                                                                                                                                                                        rw [heq]
                                                                                                                                                                                                        exact bd_w98 ⟨n - 14900, hr⟩
                                                                                                                                                                                                      ·
                                                                                                                                                                                                        have hr : n - 14950 < 50 := by omega
                                                                                                                                                                                                        have heq : n = (n - 14950) + 14950 := by omega
                                                                                                                                                                                                        rw [heq]
                                                                                                                                                                                                        exact bd_w99 ⟨n - 14950, hr⟩

end IntMul.Kappa.R8.Bit.Oppbank.CentBound2


