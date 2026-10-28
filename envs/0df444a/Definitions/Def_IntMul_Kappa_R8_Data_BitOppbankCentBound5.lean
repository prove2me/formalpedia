-- Prove2me | Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankCentBound5
-- name    : IntMul_Kappa_R8_Data_BitOppbankCentBound5
-- status  : Definition
-- author  : @Ethan Cheung Wang
-- created : 2026-10-28T19:51:17.532761+00:00
-- url     : https://prove2.me/theorems/715b4268-4616-4b91-81a1-c694753908c6
-- title:
--   HasCentre certificates dens nodes [25000,30000)
-- statement:
--   # Densified centre certificates, pack 5
--
--   For every densified node index $n$ with $25000\le n<30000$,
--   $$
--   \mathrm{centredStar}(\mathrm{densSupG}\,n,\mathrm{centF}\,n)=\mathsf{true},\quad
--   \mathrm{centF}\,n<23,\quad
--   \mathrm{densSupG}\,n < 2^{1771}.
--   $$
--   Proved by decide on Fin 50 windows (no native_decide).
-- source:
--   R8 BitOppbank AllDensCentred; jfstack_23 densified supports

-- CentBound pack 5: densified HasCentre certificates on n ∈ [25000, 30000)
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

namespace IntMul.Kappa.R8.Bit.Oppbank.CentBound5

private theorem cs_w0 : ∀ n : Fin 50, centredStar (densSupG (n.val + 25000)) (centF (n.val + 25000)) = true := by decide
private theorem cl_w0 : ∀ n : Fin 50, centF (n.val + 25000) < 23 := by decide
private theorem bd_w0 : ∀ n : Fin 50, densSupG (n.val + 25000) < 2 ^ 1771 := by decide
private theorem cs_w1 : ∀ n : Fin 50, centredStar (densSupG (n.val + 25050)) (centF (n.val + 25050)) = true := by decide
private theorem cl_w1 : ∀ n : Fin 50, centF (n.val + 25050) < 23 := by decide
private theorem bd_w1 : ∀ n : Fin 50, densSupG (n.val + 25050) < 2 ^ 1771 := by decide
private theorem cs_w2 : ∀ n : Fin 50, centredStar (densSupG (n.val + 25100)) (centF (n.val + 25100)) = true := by decide
private theorem cl_w2 : ∀ n : Fin 50, centF (n.val + 25100) < 23 := by decide
private theorem bd_w2 : ∀ n : Fin 50, densSupG (n.val + 25100) < 2 ^ 1771 := by decide
private theorem cs_w3 : ∀ n : Fin 50, centredStar (densSupG (n.val + 25150)) (centF (n.val + 25150)) = true := by decide
private theorem cl_w3 : ∀ n : Fin 50, centF (n.val + 25150) < 23 := by decide
private theorem bd_w3 : ∀ n : Fin 50, densSupG (n.val + 25150) < 2 ^ 1771 := by decide
private theorem cs_w4 : ∀ n : Fin 50, centredStar (densSupG (n.val + 25200)) (centF (n.val + 25200)) = true := by decide
private theorem cl_w4 : ∀ n : Fin 50, centF (n.val + 25200) < 23 := by decide
private theorem bd_w4 : ∀ n : Fin 50, densSupG (n.val + 25200) < 2 ^ 1771 := by decide
private theorem cs_w5 : ∀ n : Fin 50, centredStar (densSupG (n.val + 25250)) (centF (n.val + 25250)) = true := by decide
private theorem cl_w5 : ∀ n : Fin 50, centF (n.val + 25250) < 23 := by decide
private theorem bd_w5 : ∀ n : Fin 50, densSupG (n.val + 25250) < 2 ^ 1771 := by decide
private theorem cs_w6 : ∀ n : Fin 50, centredStar (densSupG (n.val + 25300)) (centF (n.val + 25300)) = true := by decide
private theorem cl_w6 : ∀ n : Fin 50, centF (n.val + 25300) < 23 := by decide
private theorem bd_w6 : ∀ n : Fin 50, densSupG (n.val + 25300) < 2 ^ 1771 := by decide
private theorem cs_w7 : ∀ n : Fin 50, centredStar (densSupG (n.val + 25350)) (centF (n.val + 25350)) = true := by decide
private theorem cl_w7 : ∀ n : Fin 50, centF (n.val + 25350) < 23 := by decide
private theorem bd_w7 : ∀ n : Fin 50, densSupG (n.val + 25350) < 2 ^ 1771 := by decide
private theorem cs_w8 : ∀ n : Fin 50, centredStar (densSupG (n.val + 25400)) (centF (n.val + 25400)) = true := by decide
private theorem cl_w8 : ∀ n : Fin 50, centF (n.val + 25400) < 23 := by decide
private theorem bd_w8 : ∀ n : Fin 50, densSupG (n.val + 25400) < 2 ^ 1771 := by decide
private theorem cs_w9 : ∀ n : Fin 50, centredStar (densSupG (n.val + 25450)) (centF (n.val + 25450)) = true := by decide
private theorem cl_w9 : ∀ n : Fin 50, centF (n.val + 25450) < 23 := by decide
private theorem bd_w9 : ∀ n : Fin 50, densSupG (n.val + 25450) < 2 ^ 1771 := by decide
private theorem cs_w10 : ∀ n : Fin 50, centredStar (densSupG (n.val + 25500)) (centF (n.val + 25500)) = true := by decide
private theorem cl_w10 : ∀ n : Fin 50, centF (n.val + 25500) < 23 := by decide
private theorem bd_w10 : ∀ n : Fin 50, densSupG (n.val + 25500) < 2 ^ 1771 := by decide
private theorem cs_w11 : ∀ n : Fin 50, centredStar (densSupG (n.val + 25550)) (centF (n.val + 25550)) = true := by decide
private theorem cl_w11 : ∀ n : Fin 50, centF (n.val + 25550) < 23 := by decide
private theorem bd_w11 : ∀ n : Fin 50, densSupG (n.val + 25550) < 2 ^ 1771 := by decide
private theorem cs_w12 : ∀ n : Fin 50, centredStar (densSupG (n.val + 25600)) (centF (n.val + 25600)) = true := by decide
private theorem cl_w12 : ∀ n : Fin 50, centF (n.val + 25600) < 23 := by decide
private theorem bd_w12 : ∀ n : Fin 50, densSupG (n.val + 25600) < 2 ^ 1771 := by decide
private theorem cs_w13 : ∀ n : Fin 50, centredStar (densSupG (n.val + 25650)) (centF (n.val + 25650)) = true := by decide
private theorem cl_w13 : ∀ n : Fin 50, centF (n.val + 25650) < 23 := by decide
private theorem bd_w13 : ∀ n : Fin 50, densSupG (n.val + 25650) < 2 ^ 1771 := by decide
private theorem cs_w14 : ∀ n : Fin 50, centredStar (densSupG (n.val + 25700)) (centF (n.val + 25700)) = true := by decide
private theorem cl_w14 : ∀ n : Fin 50, centF (n.val + 25700) < 23 := by decide
private theorem bd_w14 : ∀ n : Fin 50, densSupG (n.val + 25700) < 2 ^ 1771 := by decide
private theorem cs_w15 : ∀ n : Fin 50, centredStar (densSupG (n.val + 25750)) (centF (n.val + 25750)) = true := by decide
private theorem cl_w15 : ∀ n : Fin 50, centF (n.val + 25750) < 23 := by decide
private theorem bd_w15 : ∀ n : Fin 50, densSupG (n.val + 25750) < 2 ^ 1771 := by decide
private theorem cs_w16 : ∀ n : Fin 50, centredStar (densSupG (n.val + 25800)) (centF (n.val + 25800)) = true := by decide
private theorem cl_w16 : ∀ n : Fin 50, centF (n.val + 25800) < 23 := by decide
private theorem bd_w16 : ∀ n : Fin 50, densSupG (n.val + 25800) < 2 ^ 1771 := by decide
private theorem cs_w17 : ∀ n : Fin 50, centredStar (densSupG (n.val + 25850)) (centF (n.val + 25850)) = true := by decide
private theorem cl_w17 : ∀ n : Fin 50, centF (n.val + 25850) < 23 := by decide
private theorem bd_w17 : ∀ n : Fin 50, densSupG (n.val + 25850) < 2 ^ 1771 := by decide
private theorem cs_w18 : ∀ n : Fin 50, centredStar (densSupG (n.val + 25900)) (centF (n.val + 25900)) = true := by decide
private theorem cl_w18 : ∀ n : Fin 50, centF (n.val + 25900) < 23 := by decide
private theorem bd_w18 : ∀ n : Fin 50, densSupG (n.val + 25900) < 2 ^ 1771 := by decide
private theorem cs_w19 : ∀ n : Fin 50, centredStar (densSupG (n.val + 25950)) (centF (n.val + 25950)) = true := by decide
private theorem cl_w19 : ∀ n : Fin 50, centF (n.val + 25950) < 23 := by decide
private theorem bd_w19 : ∀ n : Fin 50, densSupG (n.val + 25950) < 2 ^ 1771 := by decide
private theorem cs_w20 : ∀ n : Fin 50, centredStar (densSupG (n.val + 26000)) (centF (n.val + 26000)) = true := by decide
private theorem cl_w20 : ∀ n : Fin 50, centF (n.val + 26000) < 23 := by decide
private theorem bd_w20 : ∀ n : Fin 50, densSupG (n.val + 26000) < 2 ^ 1771 := by decide
private theorem cs_w21 : ∀ n : Fin 50, centredStar (densSupG (n.val + 26050)) (centF (n.val + 26050)) = true := by decide
private theorem cl_w21 : ∀ n : Fin 50, centF (n.val + 26050) < 23 := by decide
private theorem bd_w21 : ∀ n : Fin 50, densSupG (n.val + 26050) < 2 ^ 1771 := by decide
private theorem cs_w22 : ∀ n : Fin 50, centredStar (densSupG (n.val + 26100)) (centF (n.val + 26100)) = true := by decide
private theorem cl_w22 : ∀ n : Fin 50, centF (n.val + 26100) < 23 := by decide
private theorem bd_w22 : ∀ n : Fin 50, densSupG (n.val + 26100) < 2 ^ 1771 := by decide
private theorem cs_w23 : ∀ n : Fin 50, centredStar (densSupG (n.val + 26150)) (centF (n.val + 26150)) = true := by decide
private theorem cl_w23 : ∀ n : Fin 50, centF (n.val + 26150) < 23 := by decide
private theorem bd_w23 : ∀ n : Fin 50, densSupG (n.val + 26150) < 2 ^ 1771 := by decide
private theorem cs_w24 : ∀ n : Fin 50, centredStar (densSupG (n.val + 26200)) (centF (n.val + 26200)) = true := by decide
private theorem cl_w24 : ∀ n : Fin 50, centF (n.val + 26200) < 23 := by decide
private theorem bd_w24 : ∀ n : Fin 50, densSupG (n.val + 26200) < 2 ^ 1771 := by decide
private theorem cs_w25 : ∀ n : Fin 50, centredStar (densSupG (n.val + 26250)) (centF (n.val + 26250)) = true := by decide
private theorem cl_w25 : ∀ n : Fin 50, centF (n.val + 26250) < 23 := by decide
private theorem bd_w25 : ∀ n : Fin 50, densSupG (n.val + 26250) < 2 ^ 1771 := by decide
private theorem cs_w26 : ∀ n : Fin 50, centredStar (densSupG (n.val + 26300)) (centF (n.val + 26300)) = true := by decide
private theorem cl_w26 : ∀ n : Fin 50, centF (n.val + 26300) < 23 := by decide
private theorem bd_w26 : ∀ n : Fin 50, densSupG (n.val + 26300) < 2 ^ 1771 := by decide
private theorem cs_w27 : ∀ n : Fin 50, centredStar (densSupG (n.val + 26350)) (centF (n.val + 26350)) = true := by decide
private theorem cl_w27 : ∀ n : Fin 50, centF (n.val + 26350) < 23 := by decide
private theorem bd_w27 : ∀ n : Fin 50, densSupG (n.val + 26350) < 2 ^ 1771 := by decide
private theorem cs_w28 : ∀ n : Fin 50, centredStar (densSupG (n.val + 26400)) (centF (n.val + 26400)) = true := by decide
private theorem cl_w28 : ∀ n : Fin 50, centF (n.val + 26400) < 23 := by decide
private theorem bd_w28 : ∀ n : Fin 50, densSupG (n.val + 26400) < 2 ^ 1771 := by decide
private theorem cs_w29 : ∀ n : Fin 50, centredStar (densSupG (n.val + 26450)) (centF (n.val + 26450)) = true := by decide
private theorem cl_w29 : ∀ n : Fin 50, centF (n.val + 26450) < 23 := by decide
private theorem bd_w29 : ∀ n : Fin 50, densSupG (n.val + 26450) < 2 ^ 1771 := by decide
private theorem cs_w30 : ∀ n : Fin 50, centredStar (densSupG (n.val + 26500)) (centF (n.val + 26500)) = true := by decide
private theorem cl_w30 : ∀ n : Fin 50, centF (n.val + 26500) < 23 := by decide
private theorem bd_w30 : ∀ n : Fin 50, densSupG (n.val + 26500) < 2 ^ 1771 := by decide
private theorem cs_w31 : ∀ n : Fin 50, centredStar (densSupG (n.val + 26550)) (centF (n.val + 26550)) = true := by decide
private theorem cl_w31 : ∀ n : Fin 50, centF (n.val + 26550) < 23 := by decide
private theorem bd_w31 : ∀ n : Fin 50, densSupG (n.val + 26550) < 2 ^ 1771 := by decide
private theorem cs_w32 : ∀ n : Fin 50, centredStar (densSupG (n.val + 26600)) (centF (n.val + 26600)) = true := by decide
private theorem cl_w32 : ∀ n : Fin 50, centF (n.val + 26600) < 23 := by decide
private theorem bd_w32 : ∀ n : Fin 50, densSupG (n.val + 26600) < 2 ^ 1771 := by decide
private theorem cs_w33 : ∀ n : Fin 50, centredStar (densSupG (n.val + 26650)) (centF (n.val + 26650)) = true := by decide
private theorem cl_w33 : ∀ n : Fin 50, centF (n.val + 26650) < 23 := by decide
private theorem bd_w33 : ∀ n : Fin 50, densSupG (n.val + 26650) < 2 ^ 1771 := by decide
private theorem cs_w34 : ∀ n : Fin 50, centredStar (densSupG (n.val + 26700)) (centF (n.val + 26700)) = true := by decide
private theorem cl_w34 : ∀ n : Fin 50, centF (n.val + 26700) < 23 := by decide
private theorem bd_w34 : ∀ n : Fin 50, densSupG (n.val + 26700) < 2 ^ 1771 := by decide
private theorem cs_w35 : ∀ n : Fin 50, centredStar (densSupG (n.val + 26750)) (centF (n.val + 26750)) = true := by decide
private theorem cl_w35 : ∀ n : Fin 50, centF (n.val + 26750) < 23 := by decide
private theorem bd_w35 : ∀ n : Fin 50, densSupG (n.val + 26750) < 2 ^ 1771 := by decide
private theorem cs_w36 : ∀ n : Fin 50, centredStar (densSupG (n.val + 26800)) (centF (n.val + 26800)) = true := by decide
private theorem cl_w36 : ∀ n : Fin 50, centF (n.val + 26800) < 23 := by decide
private theorem bd_w36 : ∀ n : Fin 50, densSupG (n.val + 26800) < 2 ^ 1771 := by decide
private theorem cs_w37 : ∀ n : Fin 50, centredStar (densSupG (n.val + 26850)) (centF (n.val + 26850)) = true := by decide
private theorem cl_w37 : ∀ n : Fin 50, centF (n.val + 26850) < 23 := by decide
private theorem bd_w37 : ∀ n : Fin 50, densSupG (n.val + 26850) < 2 ^ 1771 := by decide
private theorem cs_w38 : ∀ n : Fin 50, centredStar (densSupG (n.val + 26900)) (centF (n.val + 26900)) = true := by decide
private theorem cl_w38 : ∀ n : Fin 50, centF (n.val + 26900) < 23 := by decide
private theorem bd_w38 : ∀ n : Fin 50, densSupG (n.val + 26900) < 2 ^ 1771 := by decide
private theorem cs_w39 : ∀ n : Fin 50, centredStar (densSupG (n.val + 26950)) (centF (n.val + 26950)) = true := by decide
private theorem cl_w39 : ∀ n : Fin 50, centF (n.val + 26950) < 23 := by decide
private theorem bd_w39 : ∀ n : Fin 50, densSupG (n.val + 26950) < 2 ^ 1771 := by decide
private theorem cs_w40 : ∀ n : Fin 50, centredStar (densSupG (n.val + 27000)) (centF (n.val + 27000)) = true := by decide
private theorem cl_w40 : ∀ n : Fin 50, centF (n.val + 27000) < 23 := by decide
private theorem bd_w40 : ∀ n : Fin 50, densSupG (n.val + 27000) < 2 ^ 1771 := by decide
private theorem cs_w41 : ∀ n : Fin 50, centredStar (densSupG (n.val + 27050)) (centF (n.val + 27050)) = true := by decide
private theorem cl_w41 : ∀ n : Fin 50, centF (n.val + 27050) < 23 := by decide
private theorem bd_w41 : ∀ n : Fin 50, densSupG (n.val + 27050) < 2 ^ 1771 := by decide
private theorem cs_w42 : ∀ n : Fin 50, centredStar (densSupG (n.val + 27100)) (centF (n.val + 27100)) = true := by decide
private theorem cl_w42 : ∀ n : Fin 50, centF (n.val + 27100) < 23 := by decide
private theorem bd_w42 : ∀ n : Fin 50, densSupG (n.val + 27100) < 2 ^ 1771 := by decide
private theorem cs_w43 : ∀ n : Fin 50, centredStar (densSupG (n.val + 27150)) (centF (n.val + 27150)) = true := by decide
private theorem cl_w43 : ∀ n : Fin 50, centF (n.val + 27150) < 23 := by decide
private theorem bd_w43 : ∀ n : Fin 50, densSupG (n.val + 27150) < 2 ^ 1771 := by decide
private theorem cs_w44 : ∀ n : Fin 50, centredStar (densSupG (n.val + 27200)) (centF (n.val + 27200)) = true := by decide
private theorem cl_w44 : ∀ n : Fin 50, centF (n.val + 27200) < 23 := by decide
private theorem bd_w44 : ∀ n : Fin 50, densSupG (n.val + 27200) < 2 ^ 1771 := by decide
private theorem cs_w45 : ∀ n : Fin 50, centredStar (densSupG (n.val + 27250)) (centF (n.val + 27250)) = true := by decide
private theorem cl_w45 : ∀ n : Fin 50, centF (n.val + 27250) < 23 := by decide
private theorem bd_w45 : ∀ n : Fin 50, densSupG (n.val + 27250) < 2 ^ 1771 := by decide
private theorem cs_w46 : ∀ n : Fin 50, centredStar (densSupG (n.val + 27300)) (centF (n.val + 27300)) = true := by decide
private theorem cl_w46 : ∀ n : Fin 50, centF (n.val + 27300) < 23 := by decide
private theorem bd_w46 : ∀ n : Fin 50, densSupG (n.val + 27300) < 2 ^ 1771 := by decide
private theorem cs_w47 : ∀ n : Fin 50, centredStar (densSupG (n.val + 27350)) (centF (n.val + 27350)) = true := by decide
private theorem cl_w47 : ∀ n : Fin 50, centF (n.val + 27350) < 23 := by decide
private theorem bd_w47 : ∀ n : Fin 50, densSupG (n.val + 27350) < 2 ^ 1771 := by decide
private theorem cs_w48 : ∀ n : Fin 50, centredStar (densSupG (n.val + 27400)) (centF (n.val + 27400)) = true := by decide
private theorem cl_w48 : ∀ n : Fin 50, centF (n.val + 27400) < 23 := by decide
private theorem bd_w48 : ∀ n : Fin 50, densSupG (n.val + 27400) < 2 ^ 1771 := by decide
private theorem cs_w49 : ∀ n : Fin 50, centredStar (densSupG (n.val + 27450)) (centF (n.val + 27450)) = true := by decide
private theorem cl_w49 : ∀ n : Fin 50, centF (n.val + 27450) < 23 := by decide
private theorem bd_w49 : ∀ n : Fin 50, densSupG (n.val + 27450) < 2 ^ 1771 := by decide
private theorem cs_w50 : ∀ n : Fin 50, centredStar (densSupG (n.val + 27500)) (centF (n.val + 27500)) = true := by decide
private theorem cl_w50 : ∀ n : Fin 50, centF (n.val + 27500) < 23 := by decide
private theorem bd_w50 : ∀ n : Fin 50, densSupG (n.val + 27500) < 2 ^ 1771 := by decide
private theorem cs_w51 : ∀ n : Fin 50, centredStar (densSupG (n.val + 27550)) (centF (n.val + 27550)) = true := by decide
private theorem cl_w51 : ∀ n : Fin 50, centF (n.val + 27550) < 23 := by decide
private theorem bd_w51 : ∀ n : Fin 50, densSupG (n.val + 27550) < 2 ^ 1771 := by decide
private theorem cs_w52 : ∀ n : Fin 50, centredStar (densSupG (n.val + 27600)) (centF (n.val + 27600)) = true := by decide
private theorem cl_w52 : ∀ n : Fin 50, centF (n.val + 27600) < 23 := by decide
private theorem bd_w52 : ∀ n : Fin 50, densSupG (n.val + 27600) < 2 ^ 1771 := by decide
private theorem cs_w53 : ∀ n : Fin 50, centredStar (densSupG (n.val + 27650)) (centF (n.val + 27650)) = true := by decide
private theorem cl_w53 : ∀ n : Fin 50, centF (n.val + 27650) < 23 := by decide
private theorem bd_w53 : ∀ n : Fin 50, densSupG (n.val + 27650) < 2 ^ 1771 := by decide
private theorem cs_w54 : ∀ n : Fin 50, centredStar (densSupG (n.val + 27700)) (centF (n.val + 27700)) = true := by decide
private theorem cl_w54 : ∀ n : Fin 50, centF (n.val + 27700) < 23 := by decide
private theorem bd_w54 : ∀ n : Fin 50, densSupG (n.val + 27700) < 2 ^ 1771 := by decide
private theorem cs_w55 : ∀ n : Fin 50, centredStar (densSupG (n.val + 27750)) (centF (n.val + 27750)) = true := by decide
private theorem cl_w55 : ∀ n : Fin 50, centF (n.val + 27750) < 23 := by decide
private theorem bd_w55 : ∀ n : Fin 50, densSupG (n.val + 27750) < 2 ^ 1771 := by decide
private theorem cs_w56 : ∀ n : Fin 50, centredStar (densSupG (n.val + 27800)) (centF (n.val + 27800)) = true := by decide
private theorem cl_w56 : ∀ n : Fin 50, centF (n.val + 27800) < 23 := by decide
private theorem bd_w56 : ∀ n : Fin 50, densSupG (n.val + 27800) < 2 ^ 1771 := by decide
private theorem cs_w57 : ∀ n : Fin 50, centredStar (densSupG (n.val + 27850)) (centF (n.val + 27850)) = true := by decide
private theorem cl_w57 : ∀ n : Fin 50, centF (n.val + 27850) < 23 := by decide
private theorem bd_w57 : ∀ n : Fin 50, densSupG (n.val + 27850) < 2 ^ 1771 := by decide
private theorem cs_w58 : ∀ n : Fin 50, centredStar (densSupG (n.val + 27900)) (centF (n.val + 27900)) = true := by decide
private theorem cl_w58 : ∀ n : Fin 50, centF (n.val + 27900) < 23 := by decide
private theorem bd_w58 : ∀ n : Fin 50, densSupG (n.val + 27900) < 2 ^ 1771 := by decide
private theorem cs_w59 : ∀ n : Fin 50, centredStar (densSupG (n.val + 27950)) (centF (n.val + 27950)) = true := by decide
private theorem cl_w59 : ∀ n : Fin 50, centF (n.val + 27950) < 23 := by decide
private theorem bd_w59 : ∀ n : Fin 50, densSupG (n.val + 27950) < 2 ^ 1771 := by decide
private theorem cs_w60 : ∀ n : Fin 50, centredStar (densSupG (n.val + 28000)) (centF (n.val + 28000)) = true := by decide
private theorem cl_w60 : ∀ n : Fin 50, centF (n.val + 28000) < 23 := by decide
private theorem bd_w60 : ∀ n : Fin 50, densSupG (n.val + 28000) < 2 ^ 1771 := by decide
private theorem cs_w61 : ∀ n : Fin 50, centredStar (densSupG (n.val + 28050)) (centF (n.val + 28050)) = true := by decide
private theorem cl_w61 : ∀ n : Fin 50, centF (n.val + 28050) < 23 := by decide
private theorem bd_w61 : ∀ n : Fin 50, densSupG (n.val + 28050) < 2 ^ 1771 := by decide
private theorem cs_w62 : ∀ n : Fin 50, centredStar (densSupG (n.val + 28100)) (centF (n.val + 28100)) = true := by decide
private theorem cl_w62 : ∀ n : Fin 50, centF (n.val + 28100) < 23 := by decide
private theorem bd_w62 : ∀ n : Fin 50, densSupG (n.val + 28100) < 2 ^ 1771 := by decide
private theorem cs_w63 : ∀ n : Fin 50, centredStar (densSupG (n.val + 28150)) (centF (n.val + 28150)) = true := by decide
private theorem cl_w63 : ∀ n : Fin 50, centF (n.val + 28150) < 23 := by decide
private theorem bd_w63 : ∀ n : Fin 50, densSupG (n.val + 28150) < 2 ^ 1771 := by decide
private theorem cs_w64 : ∀ n : Fin 50, centredStar (densSupG (n.val + 28200)) (centF (n.val + 28200)) = true := by decide
private theorem cl_w64 : ∀ n : Fin 50, centF (n.val + 28200) < 23 := by decide
private theorem bd_w64 : ∀ n : Fin 50, densSupG (n.val + 28200) < 2 ^ 1771 := by decide
private theorem cs_w65 : ∀ n : Fin 50, centredStar (densSupG (n.val + 28250)) (centF (n.val + 28250)) = true := by decide
private theorem cl_w65 : ∀ n : Fin 50, centF (n.val + 28250) < 23 := by decide
private theorem bd_w65 : ∀ n : Fin 50, densSupG (n.val + 28250) < 2 ^ 1771 := by decide
private theorem cs_w66 : ∀ n : Fin 50, centredStar (densSupG (n.val + 28300)) (centF (n.val + 28300)) = true := by decide
private theorem cl_w66 : ∀ n : Fin 50, centF (n.val + 28300) < 23 := by decide
private theorem bd_w66 : ∀ n : Fin 50, densSupG (n.val + 28300) < 2 ^ 1771 := by decide
private theorem cs_w67 : ∀ n : Fin 50, centredStar (densSupG (n.val + 28350)) (centF (n.val + 28350)) = true := by decide
private theorem cl_w67 : ∀ n : Fin 50, centF (n.val + 28350) < 23 := by decide
private theorem bd_w67 : ∀ n : Fin 50, densSupG (n.val + 28350) < 2 ^ 1771 := by decide
private theorem cs_w68 : ∀ n : Fin 50, centredStar (densSupG (n.val + 28400)) (centF (n.val + 28400)) = true := by decide
private theorem cl_w68 : ∀ n : Fin 50, centF (n.val + 28400) < 23 := by decide
private theorem bd_w68 : ∀ n : Fin 50, densSupG (n.val + 28400) < 2 ^ 1771 := by decide
private theorem cs_w69 : ∀ n : Fin 50, centredStar (densSupG (n.val + 28450)) (centF (n.val + 28450)) = true := by decide
private theorem cl_w69 : ∀ n : Fin 50, centF (n.val + 28450) < 23 := by decide
private theorem bd_w69 : ∀ n : Fin 50, densSupG (n.val + 28450) < 2 ^ 1771 := by decide
private theorem cs_w70 : ∀ n : Fin 50, centredStar (densSupG (n.val + 28500)) (centF (n.val + 28500)) = true := by decide
private theorem cl_w70 : ∀ n : Fin 50, centF (n.val + 28500) < 23 := by decide
private theorem bd_w70 : ∀ n : Fin 50, densSupG (n.val + 28500) < 2 ^ 1771 := by decide
private theorem cs_w71 : ∀ n : Fin 50, centredStar (densSupG (n.val + 28550)) (centF (n.val + 28550)) = true := by decide
private theorem cl_w71 : ∀ n : Fin 50, centF (n.val + 28550) < 23 := by decide
private theorem bd_w71 : ∀ n : Fin 50, densSupG (n.val + 28550) < 2 ^ 1771 := by decide
private theorem cs_w72 : ∀ n : Fin 50, centredStar (densSupG (n.val + 28600)) (centF (n.val + 28600)) = true := by decide
private theorem cl_w72 : ∀ n : Fin 50, centF (n.val + 28600) < 23 := by decide
private theorem bd_w72 : ∀ n : Fin 50, densSupG (n.val + 28600) < 2 ^ 1771 := by decide
private theorem cs_w73 : ∀ n : Fin 50, centredStar (densSupG (n.val + 28650)) (centF (n.val + 28650)) = true := by decide
private theorem cl_w73 : ∀ n : Fin 50, centF (n.val + 28650) < 23 := by decide
private theorem bd_w73 : ∀ n : Fin 50, densSupG (n.val + 28650) < 2 ^ 1771 := by decide
private theorem cs_w74 : ∀ n : Fin 50, centredStar (densSupG (n.val + 28700)) (centF (n.val + 28700)) = true := by decide
private theorem cl_w74 : ∀ n : Fin 50, centF (n.val + 28700) < 23 := by decide
private theorem bd_w74 : ∀ n : Fin 50, densSupG (n.val + 28700) < 2 ^ 1771 := by decide
private theorem cs_w75 : ∀ n : Fin 50, centredStar (densSupG (n.val + 28750)) (centF (n.val + 28750)) = true := by decide
private theorem cl_w75 : ∀ n : Fin 50, centF (n.val + 28750) < 23 := by decide
private theorem bd_w75 : ∀ n : Fin 50, densSupG (n.val + 28750) < 2 ^ 1771 := by decide
private theorem cs_w76 : ∀ n : Fin 50, centredStar (densSupG (n.val + 28800)) (centF (n.val + 28800)) = true := by decide
private theorem cl_w76 : ∀ n : Fin 50, centF (n.val + 28800) < 23 := by decide
private theorem bd_w76 : ∀ n : Fin 50, densSupG (n.val + 28800) < 2 ^ 1771 := by decide
private theorem cs_w77 : ∀ n : Fin 50, centredStar (densSupG (n.val + 28850)) (centF (n.val + 28850)) = true := by decide
private theorem cl_w77 : ∀ n : Fin 50, centF (n.val + 28850) < 23 := by decide
private theorem bd_w77 : ∀ n : Fin 50, densSupG (n.val + 28850) < 2 ^ 1771 := by decide
private theorem cs_w78 : ∀ n : Fin 50, centredStar (densSupG (n.val + 28900)) (centF (n.val + 28900)) = true := by decide
private theorem cl_w78 : ∀ n : Fin 50, centF (n.val + 28900) < 23 := by decide
private theorem bd_w78 : ∀ n : Fin 50, densSupG (n.val + 28900) < 2 ^ 1771 := by decide
private theorem cs_w79 : ∀ n : Fin 50, centredStar (densSupG (n.val + 28950)) (centF (n.val + 28950)) = true := by decide
private theorem cl_w79 : ∀ n : Fin 50, centF (n.val + 28950) < 23 := by decide
private theorem bd_w79 : ∀ n : Fin 50, densSupG (n.val + 28950) < 2 ^ 1771 := by decide
private theorem cs_w80 : ∀ n : Fin 50, centredStar (densSupG (n.val + 29000)) (centF (n.val + 29000)) = true := by decide
private theorem cl_w80 : ∀ n : Fin 50, centF (n.val + 29000) < 23 := by decide
private theorem bd_w80 : ∀ n : Fin 50, densSupG (n.val + 29000) < 2 ^ 1771 := by decide
private theorem cs_w81 : ∀ n : Fin 50, centredStar (densSupG (n.val + 29050)) (centF (n.val + 29050)) = true := by decide
private theorem cl_w81 : ∀ n : Fin 50, centF (n.val + 29050) < 23 := by decide
private theorem bd_w81 : ∀ n : Fin 50, densSupG (n.val + 29050) < 2 ^ 1771 := by decide
private theorem cs_w82 : ∀ n : Fin 50, centredStar (densSupG (n.val + 29100)) (centF (n.val + 29100)) = true := by decide
private theorem cl_w82 : ∀ n : Fin 50, centF (n.val + 29100) < 23 := by decide
private theorem bd_w82 : ∀ n : Fin 50, densSupG (n.val + 29100) < 2 ^ 1771 := by decide
private theorem cs_w83 : ∀ n : Fin 50, centredStar (densSupG (n.val + 29150)) (centF (n.val + 29150)) = true := by decide
private theorem cl_w83 : ∀ n : Fin 50, centF (n.val + 29150) < 23 := by decide
private theorem bd_w83 : ∀ n : Fin 50, densSupG (n.val + 29150) < 2 ^ 1771 := by decide
private theorem cs_w84 : ∀ n : Fin 50, centredStar (densSupG (n.val + 29200)) (centF (n.val + 29200)) = true := by decide
private theorem cl_w84 : ∀ n : Fin 50, centF (n.val + 29200) < 23 := by decide
private theorem bd_w84 : ∀ n : Fin 50, densSupG (n.val + 29200) < 2 ^ 1771 := by decide
private theorem cs_w85 : ∀ n : Fin 50, centredStar (densSupG (n.val + 29250)) (centF (n.val + 29250)) = true := by decide
private theorem cl_w85 : ∀ n : Fin 50, centF (n.val + 29250) < 23 := by decide
private theorem bd_w85 : ∀ n : Fin 50, densSupG (n.val + 29250) < 2 ^ 1771 := by decide
private theorem cs_w86 : ∀ n : Fin 50, centredStar (densSupG (n.val + 29300)) (centF (n.val + 29300)) = true := by decide
private theorem cl_w86 : ∀ n : Fin 50, centF (n.val + 29300) < 23 := by decide
private theorem bd_w86 : ∀ n : Fin 50, densSupG (n.val + 29300) < 2 ^ 1771 := by decide
private theorem cs_w87 : ∀ n : Fin 50, centredStar (densSupG (n.val + 29350)) (centF (n.val + 29350)) = true := by decide
private theorem cl_w87 : ∀ n : Fin 50, centF (n.val + 29350) < 23 := by decide
private theorem bd_w87 : ∀ n : Fin 50, densSupG (n.val + 29350) < 2 ^ 1771 := by decide
private theorem cs_w88 : ∀ n : Fin 50, centredStar (densSupG (n.val + 29400)) (centF (n.val + 29400)) = true := by decide
private theorem cl_w88 : ∀ n : Fin 50, centF (n.val + 29400) < 23 := by decide
private theorem bd_w88 : ∀ n : Fin 50, densSupG (n.val + 29400) < 2 ^ 1771 := by decide
private theorem cs_w89 : ∀ n : Fin 50, centredStar (densSupG (n.val + 29450)) (centF (n.val + 29450)) = true := by decide
private theorem cl_w89 : ∀ n : Fin 50, centF (n.val + 29450) < 23 := by decide
private theorem bd_w89 : ∀ n : Fin 50, densSupG (n.val + 29450) < 2 ^ 1771 := by decide
private theorem cs_w90 : ∀ n : Fin 50, centredStar (densSupG (n.val + 29500)) (centF (n.val + 29500)) = true := by decide
private theorem cl_w90 : ∀ n : Fin 50, centF (n.val + 29500) < 23 := by decide
private theorem bd_w90 : ∀ n : Fin 50, densSupG (n.val + 29500) < 2 ^ 1771 := by decide
private theorem cs_w91 : ∀ n : Fin 50, centredStar (densSupG (n.val + 29550)) (centF (n.val + 29550)) = true := by decide
private theorem cl_w91 : ∀ n : Fin 50, centF (n.val + 29550) < 23 := by decide
private theorem bd_w91 : ∀ n : Fin 50, densSupG (n.val + 29550) < 2 ^ 1771 := by decide
private theorem cs_w92 : ∀ n : Fin 50, centredStar (densSupG (n.val + 29600)) (centF (n.val + 29600)) = true := by decide
private theorem cl_w92 : ∀ n : Fin 50, centF (n.val + 29600) < 23 := by decide
private theorem bd_w92 : ∀ n : Fin 50, densSupG (n.val + 29600) < 2 ^ 1771 := by decide
private theorem cs_w93 : ∀ n : Fin 50, centredStar (densSupG (n.val + 29650)) (centF (n.val + 29650)) = true := by decide
private theorem cl_w93 : ∀ n : Fin 50, centF (n.val + 29650) < 23 := by decide
private theorem bd_w93 : ∀ n : Fin 50, densSupG (n.val + 29650) < 2 ^ 1771 := by decide
private theorem cs_w94 : ∀ n : Fin 50, centredStar (densSupG (n.val + 29700)) (centF (n.val + 29700)) = true := by decide
private theorem cl_w94 : ∀ n : Fin 50, centF (n.val + 29700) < 23 := by decide
private theorem bd_w94 : ∀ n : Fin 50, densSupG (n.val + 29700) < 2 ^ 1771 := by decide
private theorem cs_w95 : ∀ n : Fin 50, centredStar (densSupG (n.val + 29750)) (centF (n.val + 29750)) = true := by decide
private theorem cl_w95 : ∀ n : Fin 50, centF (n.val + 29750) < 23 := by decide
private theorem bd_w95 : ∀ n : Fin 50, densSupG (n.val + 29750) < 2 ^ 1771 := by decide
private theorem cs_w96 : ∀ n : Fin 50, centredStar (densSupG (n.val + 29800)) (centF (n.val + 29800)) = true := by decide
private theorem cl_w96 : ∀ n : Fin 50, centF (n.val + 29800) < 23 := by decide
private theorem bd_w96 : ∀ n : Fin 50, densSupG (n.val + 29800) < 2 ^ 1771 := by decide
private theorem cs_w97 : ∀ n : Fin 50, centredStar (densSupG (n.val + 29850)) (centF (n.val + 29850)) = true := by decide
private theorem cl_w97 : ∀ n : Fin 50, centF (n.val + 29850) < 23 := by decide
private theorem bd_w97 : ∀ n : Fin 50, densSupG (n.val + 29850) < 2 ^ 1771 := by decide
private theorem cs_w98 : ∀ n : Fin 50, centredStar (densSupG (n.val + 29900)) (centF (n.val + 29900)) = true := by decide
private theorem cl_w98 : ∀ n : Fin 50, centF (n.val + 29900) < 23 := by decide
private theorem bd_w98 : ∀ n : Fin 50, densSupG (n.val + 29900) < 2 ^ 1771 := by decide
private theorem cs_w99 : ∀ n : Fin 50, centredStar (densSupG (n.val + 29950)) (centF (n.val + 29950)) = true := by decide
private theorem cl_w99 : ∀ n : Fin 50, centF (n.val + 29950) < 23 := by decide
private theorem bd_w99 : ∀ n : Fin 50, densSupG (n.val + 29950) < 2 ^ 1771 := by decide

theorem centredStar_range : ∀ n, 25000 ≤ n → n < 30000 → centredStar (densSupG n) (centF n) = true := by
  intro n hlo hhi
  by_cases h0 : n < 25050
  · have hr : n - 25000 < 50 := by omega
    have heq : n = (n - 25000) + 25000 := by omega
    rw [heq]
    exact cs_w0 ⟨n - 25000, hr⟩
  ·
    by_cases h1 : n < 25100
    · have hr : n - 25050 < 50 := by omega
      have heq : n = (n - 25050) + 25050 := by omega
      rw [heq]
      exact cs_w1 ⟨n - 25050, hr⟩
    ·
      by_cases h2 : n < 25150
      · have hr : n - 25100 < 50 := by omega
        have heq : n = (n - 25100) + 25100 := by omega
        rw [heq]
        exact cs_w2 ⟨n - 25100, hr⟩
      ·
        by_cases h3 : n < 25200
        · have hr : n - 25150 < 50 := by omega
          have heq : n = (n - 25150) + 25150 := by omega
          rw [heq]
          exact cs_w3 ⟨n - 25150, hr⟩
        ·
          by_cases h4 : n < 25250
          · have hr : n - 25200 < 50 := by omega
            have heq : n = (n - 25200) + 25200 := by omega
            rw [heq]
            exact cs_w4 ⟨n - 25200, hr⟩
          ·
            by_cases h5 : n < 25300
            · have hr : n - 25250 < 50 := by omega
              have heq : n = (n - 25250) + 25250 := by omega
              rw [heq]
              exact cs_w5 ⟨n - 25250, hr⟩
            ·
              by_cases h6 : n < 25350
              · have hr : n - 25300 < 50 := by omega
                have heq : n = (n - 25300) + 25300 := by omega
                rw [heq]
                exact cs_w6 ⟨n - 25300, hr⟩
              ·
                by_cases h7 : n < 25400
                · have hr : n - 25350 < 50 := by omega
                  have heq : n = (n - 25350) + 25350 := by omega
                  rw [heq]
                  exact cs_w7 ⟨n - 25350, hr⟩
                ·
                  by_cases h8 : n < 25450
                  · have hr : n - 25400 < 50 := by omega
                    have heq : n = (n - 25400) + 25400 := by omega
                    rw [heq]
                    exact cs_w8 ⟨n - 25400, hr⟩
                  ·
                    by_cases h9 : n < 25500
                    · have hr : n - 25450 < 50 := by omega
                      have heq : n = (n - 25450) + 25450 := by omega
                      rw [heq]
                      exact cs_w9 ⟨n - 25450, hr⟩
                    ·
                      by_cases h10 : n < 25550
                      · have hr : n - 25500 < 50 := by omega
                        have heq : n = (n - 25500) + 25500 := by omega
                        rw [heq]
                        exact cs_w10 ⟨n - 25500, hr⟩
                      ·
                        by_cases h11 : n < 25600
                        · have hr : n - 25550 < 50 := by omega
                          have heq : n = (n - 25550) + 25550 := by omega
                          rw [heq]
                          exact cs_w11 ⟨n - 25550, hr⟩
                        ·
                          by_cases h12 : n < 25650
                          · have hr : n - 25600 < 50 := by omega
                            have heq : n = (n - 25600) + 25600 := by omega
                            rw [heq]
                            exact cs_w12 ⟨n - 25600, hr⟩
                          ·
                            by_cases h13 : n < 25700
                            · have hr : n - 25650 < 50 := by omega
                              have heq : n = (n - 25650) + 25650 := by omega
                              rw [heq]
                              exact cs_w13 ⟨n - 25650, hr⟩
                            ·
                              by_cases h14 : n < 25750
                              · have hr : n - 25700 < 50 := by omega
                                have heq : n = (n - 25700) + 25700 := by omega
                                rw [heq]
                                exact cs_w14 ⟨n - 25700, hr⟩
                              ·
                                by_cases h15 : n < 25800
                                · have hr : n - 25750 < 50 := by omega
                                  have heq : n = (n - 25750) + 25750 := by omega
                                  rw [heq]
                                  exact cs_w15 ⟨n - 25750, hr⟩
                                ·
                                  by_cases h16 : n < 25850
                                  · have hr : n - 25800 < 50 := by omega
                                    have heq : n = (n - 25800) + 25800 := by omega
                                    rw [heq]
                                    exact cs_w16 ⟨n - 25800, hr⟩
                                  ·
                                    by_cases h17 : n < 25900
                                    · have hr : n - 25850 < 50 := by omega
                                      have heq : n = (n - 25850) + 25850 := by omega
                                      rw [heq]
                                      exact cs_w17 ⟨n - 25850, hr⟩
                                    ·
                                      by_cases h18 : n < 25950
                                      · have hr : n - 25900 < 50 := by omega
                                        have heq : n = (n - 25900) + 25900 := by omega
                                        rw [heq]
                                        exact cs_w18 ⟨n - 25900, hr⟩
                                      ·
                                        by_cases h19 : n < 26000
                                        · have hr : n - 25950 < 50 := by omega
                                          have heq : n = (n - 25950) + 25950 := by omega
                                          rw [heq]
                                          exact cs_w19 ⟨n - 25950, hr⟩
                                        ·
                                          by_cases h20 : n < 26050
                                          · have hr : n - 26000 < 50 := by omega
                                            have heq : n = (n - 26000) + 26000 := by omega
                                            rw [heq]
                                            exact cs_w20 ⟨n - 26000, hr⟩
                                          ·
                                            by_cases h21 : n < 26100
                                            · have hr : n - 26050 < 50 := by omega
                                              have heq : n = (n - 26050) + 26050 := by omega
                                              rw [heq]
                                              exact cs_w21 ⟨n - 26050, hr⟩
                                            ·
                                              by_cases h22 : n < 26150
                                              · have hr : n - 26100 < 50 := by omega
                                                have heq : n = (n - 26100) + 26100 := by omega
                                                rw [heq]
                                                exact cs_w22 ⟨n - 26100, hr⟩
                                              ·
                                                by_cases h23 : n < 26200
                                                · have hr : n - 26150 < 50 := by omega
                                                  have heq : n = (n - 26150) + 26150 := by omega
                                                  rw [heq]
                                                  exact cs_w23 ⟨n - 26150, hr⟩
                                                ·
                                                  by_cases h24 : n < 26250
                                                  · have hr : n - 26200 < 50 := by omega
                                                    have heq : n = (n - 26200) + 26200 := by omega
                                                    rw [heq]
                                                    exact cs_w24 ⟨n - 26200, hr⟩
                                                  ·
                                                    by_cases h25 : n < 26300
                                                    · have hr : n - 26250 < 50 := by omega
                                                      have heq : n = (n - 26250) + 26250 := by omega
                                                      rw [heq]
                                                      exact cs_w25 ⟨n - 26250, hr⟩
                                                    ·
                                                      by_cases h26 : n < 26350
                                                      · have hr : n - 26300 < 50 := by omega
                                                        have heq : n = (n - 26300) + 26300 := by omega
                                                        rw [heq]
                                                        exact cs_w26 ⟨n - 26300, hr⟩
                                                      ·
                                                        by_cases h27 : n < 26400
                                                        · have hr : n - 26350 < 50 := by omega
                                                          have heq : n = (n - 26350) + 26350 := by omega
                                                          rw [heq]
                                                          exact cs_w27 ⟨n - 26350, hr⟩
                                                        ·
                                                          by_cases h28 : n < 26450
                                                          · have hr : n - 26400 < 50 := by omega
                                                            have heq : n = (n - 26400) + 26400 := by omega
                                                            rw [heq]
                                                            exact cs_w28 ⟨n - 26400, hr⟩
                                                          ·
                                                            by_cases h29 : n < 26500
                                                            · have hr : n - 26450 < 50 := by omega
                                                              have heq : n = (n - 26450) + 26450 := by omega
                                                              rw [heq]
                                                              exact cs_w29 ⟨n - 26450, hr⟩
                                                            ·
                                                              by_cases h30 : n < 26550
                                                              · have hr : n - 26500 < 50 := by omega
                                                                have heq : n = (n - 26500) + 26500 := by omega
                                                                rw [heq]
                                                                exact cs_w30 ⟨n - 26500, hr⟩
                                                              ·
                                                                by_cases h31 : n < 26600
                                                                · have hr : n - 26550 < 50 := by omega
                                                                  have heq : n = (n - 26550) + 26550 := by omega
                                                                  rw [heq]
                                                                  exact cs_w31 ⟨n - 26550, hr⟩
                                                                ·
                                                                  by_cases h32 : n < 26650
                                                                  · have hr : n - 26600 < 50 := by omega
                                                                    have heq : n = (n - 26600) + 26600 := by omega
                                                                    rw [heq]
                                                                    exact cs_w32 ⟨n - 26600, hr⟩
                                                                  ·
                                                                    by_cases h33 : n < 26700
                                                                    · have hr : n - 26650 < 50 := by omega
                                                                      have heq : n = (n - 26650) + 26650 := by omega
                                                                      rw [heq]
                                                                      exact cs_w33 ⟨n - 26650, hr⟩
                                                                    ·
                                                                      by_cases h34 : n < 26750
                                                                      · have hr : n - 26700 < 50 := by omega
                                                                        have heq : n = (n - 26700) + 26700 := by omega
                                                                        rw [heq]
                                                                        exact cs_w34 ⟨n - 26700, hr⟩
                                                                      ·
                                                                        by_cases h35 : n < 26800
                                                                        · have hr : n - 26750 < 50 := by omega
                                                                          have heq : n = (n - 26750) + 26750 := by omega
                                                                          rw [heq]
                                                                          exact cs_w35 ⟨n - 26750, hr⟩
                                                                        ·
                                                                          by_cases h36 : n < 26850
                                                                          · have hr : n - 26800 < 50 := by omega
                                                                            have heq : n = (n - 26800) + 26800 := by omega
                                                                            rw [heq]
                                                                            exact cs_w36 ⟨n - 26800, hr⟩
                                                                          ·
                                                                            by_cases h37 : n < 26900
                                                                            · have hr : n - 26850 < 50 := by omega
                                                                              have heq : n = (n - 26850) + 26850 := by omega
                                                                              rw [heq]
                                                                              exact cs_w37 ⟨n - 26850, hr⟩
                                                                            ·
                                                                              by_cases h38 : n < 26950
                                                                              · have hr : n - 26900 < 50 := by omega
                                                                                have heq : n = (n - 26900) + 26900 := by omega
                                                                                rw [heq]
                                                                                exact cs_w38 ⟨n - 26900, hr⟩
                                                                              ·
                                                                                by_cases h39 : n < 27000
                                                                                · have hr : n - 26950 < 50 := by omega
                                                                                  have heq : n = (n - 26950) + 26950 := by omega
                                                                                  rw [heq]
                                                                                  exact cs_w39 ⟨n - 26950, hr⟩
                                                                                ·
                                                                                  by_cases h40 : n < 27050
                                                                                  · have hr : n - 27000 < 50 := by omega
                                                                                    have heq : n = (n - 27000) + 27000 := by omega
                                                                                    rw [heq]
                                                                                    exact cs_w40 ⟨n - 27000, hr⟩
                                                                                  ·
                                                                                    by_cases h41 : n < 27100
                                                                                    · have hr : n - 27050 < 50 := by omega
                                                                                      have heq : n = (n - 27050) + 27050 := by omega
                                                                                      rw [heq]
                                                                                      exact cs_w41 ⟨n - 27050, hr⟩
                                                                                    ·
                                                                                      by_cases h42 : n < 27150
                                                                                      · have hr : n - 27100 < 50 := by omega
                                                                                        have heq : n = (n - 27100) + 27100 := by omega
                                                                                        rw [heq]
                                                                                        exact cs_w42 ⟨n - 27100, hr⟩
                                                                                      ·
                                                                                        by_cases h43 : n < 27200
                                                                                        · have hr : n - 27150 < 50 := by omega
                                                                                          have heq : n = (n - 27150) + 27150 := by omega
                                                                                          rw [heq]
                                                                                          exact cs_w43 ⟨n - 27150, hr⟩
                                                                                        ·
                                                                                          by_cases h44 : n < 27250
                                                                                          · have hr : n - 27200 < 50 := by omega
                                                                                            have heq : n = (n - 27200) + 27200 := by omega
                                                                                            rw [heq]
                                                                                            exact cs_w44 ⟨n - 27200, hr⟩
                                                                                          ·
                                                                                            by_cases h45 : n < 27300
                                                                                            · have hr : n - 27250 < 50 := by omega
                                                                                              have heq : n = (n - 27250) + 27250 := by omega
                                                                                              rw [heq]
                                                                                              exact cs_w45 ⟨n - 27250, hr⟩
                                                                                            ·
                                                                                              by_cases h46 : n < 27350
                                                                                              · have hr : n - 27300 < 50 := by omega
                                                                                                have heq : n = (n - 27300) + 27300 := by omega
                                                                                                rw [heq]
                                                                                                exact cs_w46 ⟨n - 27300, hr⟩
                                                                                              ·
                                                                                                by_cases h47 : n < 27400
                                                                                                · have hr : n - 27350 < 50 := by omega
                                                                                                  have heq : n = (n - 27350) + 27350 := by omega
                                                                                                  rw [heq]
                                                                                                  exact cs_w47 ⟨n - 27350, hr⟩
                                                                                                ·
                                                                                                  by_cases h48 : n < 27450
                                                                                                  · have hr : n - 27400 < 50 := by omega
                                                                                                    have heq : n = (n - 27400) + 27400 := by omega
                                                                                                    rw [heq]
                                                                                                    exact cs_w48 ⟨n - 27400, hr⟩
                                                                                                  ·
                                                                                                    by_cases h49 : n < 27500
                                                                                                    · have hr : n - 27450 < 50 := by omega
                                                                                                      have heq : n = (n - 27450) + 27450 := by omega
                                                                                                      rw [heq]
                                                                                                      exact cs_w49 ⟨n - 27450, hr⟩
                                                                                                    ·
                                                                                                      by_cases h50 : n < 27550
                                                                                                      · have hr : n - 27500 < 50 := by omega
                                                                                                        have heq : n = (n - 27500) + 27500 := by omega
                                                                                                        rw [heq]
                                                                                                        exact cs_w50 ⟨n - 27500, hr⟩
                                                                                                      ·
                                                                                                        by_cases h51 : n < 27600
                                                                                                        · have hr : n - 27550 < 50 := by omega
                                                                                                          have heq : n = (n - 27550) + 27550 := by omega
                                                                                                          rw [heq]
                                                                                                          exact cs_w51 ⟨n - 27550, hr⟩
                                                                                                        ·
                                                                                                          by_cases h52 : n < 27650
                                                                                                          · have hr : n - 27600 < 50 := by omega
                                                                                                            have heq : n = (n - 27600) + 27600 := by omega
                                                                                                            rw [heq]
                                                                                                            exact cs_w52 ⟨n - 27600, hr⟩
                                                                                                          ·
                                                                                                            by_cases h53 : n < 27700
                                                                                                            · have hr : n - 27650 < 50 := by omega
                                                                                                              have heq : n = (n - 27650) + 27650 := by omega
                                                                                                              rw [heq]
                                                                                                              exact cs_w53 ⟨n - 27650, hr⟩
                                                                                                            ·
                                                                                                              by_cases h54 : n < 27750
                                                                                                              · have hr : n - 27700 < 50 := by omega
                                                                                                                have heq : n = (n - 27700) + 27700 := by omega
                                                                                                                rw [heq]
                                                                                                                exact cs_w54 ⟨n - 27700, hr⟩
                                                                                                              ·
                                                                                                                by_cases h55 : n < 27800
                                                                                                                · have hr : n - 27750 < 50 := by omega
                                                                                                                  have heq : n = (n - 27750) + 27750 := by omega
                                                                                                                  rw [heq]
                                                                                                                  exact cs_w55 ⟨n - 27750, hr⟩
                                                                                                                ·
                                                                                                                  by_cases h56 : n < 27850
                                                                                                                  · have hr : n - 27800 < 50 := by omega
                                                                                                                    have heq : n = (n - 27800) + 27800 := by omega
                                                                                                                    rw [heq]
                                                                                                                    exact cs_w56 ⟨n - 27800, hr⟩
                                                                                                                  ·
                                                                                                                    by_cases h57 : n < 27900
                                                                                                                    · have hr : n - 27850 < 50 := by omega
                                                                                                                      have heq : n = (n - 27850) + 27850 := by omega
                                                                                                                      rw [heq]
                                                                                                                      exact cs_w57 ⟨n - 27850, hr⟩
                                                                                                                    ·
                                                                                                                      by_cases h58 : n < 27950
                                                                                                                      · have hr : n - 27900 < 50 := by omega
                                                                                                                        have heq : n = (n - 27900) + 27900 := by omega
                                                                                                                        rw [heq]
                                                                                                                        exact cs_w58 ⟨n - 27900, hr⟩
                                                                                                                      ·
                                                                                                                        by_cases h59 : n < 28000
                                                                                                                        · have hr : n - 27950 < 50 := by omega
                                                                                                                          have heq : n = (n - 27950) + 27950 := by omega
                                                                                                                          rw [heq]
                                                                                                                          exact cs_w59 ⟨n - 27950, hr⟩
                                                                                                                        ·
                                                                                                                          by_cases h60 : n < 28050
                                                                                                                          · have hr : n - 28000 < 50 := by omega
                                                                                                                            have heq : n = (n - 28000) + 28000 := by omega
                                                                                                                            rw [heq]
                                                                                                                            exact cs_w60 ⟨n - 28000, hr⟩
                                                                                                                          ·
                                                                                                                            by_cases h61 : n < 28100
                                                                                                                            · have hr : n - 28050 < 50 := by omega
                                                                                                                              have heq : n = (n - 28050) + 28050 := by omega
                                                                                                                              rw [heq]
                                                                                                                              exact cs_w61 ⟨n - 28050, hr⟩
                                                                                                                            ·
                                                                                                                              by_cases h62 : n < 28150
                                                                                                                              · have hr : n - 28100 < 50 := by omega
                                                                                                                                have heq : n = (n - 28100) + 28100 := by omega
                                                                                                                                rw [heq]
                                                                                                                                exact cs_w62 ⟨n - 28100, hr⟩
                                                                                                                              ·
                                                                                                                                by_cases h63 : n < 28200
                                                                                                                                · have hr : n - 28150 < 50 := by omega
                                                                                                                                  have heq : n = (n - 28150) + 28150 := by omega
                                                                                                                                  rw [heq]
                                                                                                                                  exact cs_w63 ⟨n - 28150, hr⟩
                                                                                                                                ·
                                                                                                                                  by_cases h64 : n < 28250
                                                                                                                                  · have hr : n - 28200 < 50 := by omega
                                                                                                                                    have heq : n = (n - 28200) + 28200 := by omega
                                                                                                                                    rw [heq]
                                                                                                                                    exact cs_w64 ⟨n - 28200, hr⟩
                                                                                                                                  ·
                                                                                                                                    by_cases h65 : n < 28300
                                                                                                                                    · have hr : n - 28250 < 50 := by omega
                                                                                                                                      have heq : n = (n - 28250) + 28250 := by omega
                                                                                                                                      rw [heq]
                                                                                                                                      exact cs_w65 ⟨n - 28250, hr⟩
                                                                                                                                    ·
                                                                                                                                      by_cases h66 : n < 28350
                                                                                                                                      · have hr : n - 28300 < 50 := by omega
                                                                                                                                        have heq : n = (n - 28300) + 28300 := by omega
                                                                                                                                        rw [heq]
                                                                                                                                        exact cs_w66 ⟨n - 28300, hr⟩
                                                                                                                                      ·
                                                                                                                                        by_cases h67 : n < 28400
                                                                                                                                        · have hr : n - 28350 < 50 := by omega
                                                                                                                                          have heq : n = (n - 28350) + 28350 := by omega
                                                                                                                                          rw [heq]
                                                                                                                                          exact cs_w67 ⟨n - 28350, hr⟩
                                                                                                                                        ·
                                                                                                                                          by_cases h68 : n < 28450
                                                                                                                                          · have hr : n - 28400 < 50 := by omega
                                                                                                                                            have heq : n = (n - 28400) + 28400 := by omega
                                                                                                                                            rw [heq]
                                                                                                                                            exact cs_w68 ⟨n - 28400, hr⟩
                                                                                                                                          ·
                                                                                                                                            by_cases h69 : n < 28500
                                                                                                                                            · have hr : n - 28450 < 50 := by omega
                                                                                                                                              have heq : n = (n - 28450) + 28450 := by omega
                                                                                                                                              rw [heq]
                                                                                                                                              exact cs_w69 ⟨n - 28450, hr⟩
                                                                                                                                            ·
                                                                                                                                              by_cases h70 : n < 28550
                                                                                                                                              · have hr : n - 28500 < 50 := by omega
                                                                                                                                                have heq : n = (n - 28500) + 28500 := by omega
                                                                                                                                                rw [heq]
                                                                                                                                                exact cs_w70 ⟨n - 28500, hr⟩
                                                                                                                                              ·
                                                                                                                                                by_cases h71 : n < 28600
                                                                                                                                                · have hr : n - 28550 < 50 := by omega
                                                                                                                                                  have heq : n = (n - 28550) + 28550 := by omega
                                                                                                                                                  rw [heq]
                                                                                                                                                  exact cs_w71 ⟨n - 28550, hr⟩
                                                                                                                                                ·
                                                                                                                                                  by_cases h72 : n < 28650
                                                                                                                                                  · have hr : n - 28600 < 50 := by omega
                                                                                                                                                    have heq : n = (n - 28600) + 28600 := by omega
                                                                                                                                                    rw [heq]
                                                                                                                                                    exact cs_w72 ⟨n - 28600, hr⟩
                                                                                                                                                  ·
                                                                                                                                                    by_cases h73 : n < 28700
                                                                                                                                                    · have hr : n - 28650 < 50 := by omega
                                                                                                                                                      have heq : n = (n - 28650) + 28650 := by omega
                                                                                                                                                      rw [heq]
                                                                                                                                                      exact cs_w73 ⟨n - 28650, hr⟩
                                                                                                                                                    ·
                                                                                                                                                      by_cases h74 : n < 28750
                                                                                                                                                      · have hr : n - 28700 < 50 := by omega
                                                                                                                                                        have heq : n = (n - 28700) + 28700 := by omega
                                                                                                                                                        rw [heq]
                                                                                                                                                        exact cs_w74 ⟨n - 28700, hr⟩
                                                                                                                                                      ·
                                                                                                                                                        by_cases h75 : n < 28800
                                                                                                                                                        · have hr : n - 28750 < 50 := by omega
                                                                                                                                                          have heq : n = (n - 28750) + 28750 := by omega
                                                                                                                                                          rw [heq]
                                                                                                                                                          exact cs_w75 ⟨n - 28750, hr⟩
                                                                                                                                                        ·
                                                                                                                                                          by_cases h76 : n < 28850
                                                                                                                                                          · have hr : n - 28800 < 50 := by omega
                                                                                                                                                            have heq : n = (n - 28800) + 28800 := by omega
                                                                                                                                                            rw [heq]
                                                                                                                                                            exact cs_w76 ⟨n - 28800, hr⟩
                                                                                                                                                          ·
                                                                                                                                                            by_cases h77 : n < 28900
                                                                                                                                                            · have hr : n - 28850 < 50 := by omega
                                                                                                                                                              have heq : n = (n - 28850) + 28850 := by omega
                                                                                                                                                              rw [heq]
                                                                                                                                                              exact cs_w77 ⟨n - 28850, hr⟩
                                                                                                                                                            ·
                                                                                                                                                              by_cases h78 : n < 28950
                                                                                                                                                              · have hr : n - 28900 < 50 := by omega
                                                                                                                                                                have heq : n = (n - 28900) + 28900 := by omega
                                                                                                                                                                rw [heq]
                                                                                                                                                                exact cs_w78 ⟨n - 28900, hr⟩
                                                                                                                                                              ·
                                                                                                                                                                by_cases h79 : n < 29000
                                                                                                                                                                · have hr : n - 28950 < 50 := by omega
                                                                                                                                                                  have heq : n = (n - 28950) + 28950 := by omega
                                                                                                                                                                  rw [heq]
                                                                                                                                                                  exact cs_w79 ⟨n - 28950, hr⟩
                                                                                                                                                                ·
                                                                                                                                                                  by_cases h80 : n < 29050
                                                                                                                                                                  · have hr : n - 29000 < 50 := by omega
                                                                                                                                                                    have heq : n = (n - 29000) + 29000 := by omega
                                                                                                                                                                    rw [heq]
                                                                                                                                                                    exact cs_w80 ⟨n - 29000, hr⟩
                                                                                                                                                                  ·
                                                                                                                                                                    by_cases h81 : n < 29100
                                                                                                                                                                    · have hr : n - 29050 < 50 := by omega
                                                                                                                                                                      have heq : n = (n - 29050) + 29050 := by omega
                                                                                                                                                                      rw [heq]
                                                                                                                                                                      exact cs_w81 ⟨n - 29050, hr⟩
                                                                                                                                                                    ·
                                                                                                                                                                      by_cases h82 : n < 29150
                                                                                                                                                                      · have hr : n - 29100 < 50 := by omega
                                                                                                                                                                        have heq : n = (n - 29100) + 29100 := by omega
                                                                                                                                                                        rw [heq]
                                                                                                                                                                        exact cs_w82 ⟨n - 29100, hr⟩
                                                                                                                                                                      ·
                                                                                                                                                                        by_cases h83 : n < 29200
                                                                                                                                                                        · have hr : n - 29150 < 50 := by omega
                                                                                                                                                                          have heq : n = (n - 29150) + 29150 := by omega
                                                                                                                                                                          rw [heq]
                                                                                                                                                                          exact cs_w83 ⟨n - 29150, hr⟩
                                                                                                                                                                        ·
                                                                                                                                                                          by_cases h84 : n < 29250
                                                                                                                                                                          · have hr : n - 29200 < 50 := by omega
                                                                                                                                                                            have heq : n = (n - 29200) + 29200 := by omega
                                                                                                                                                                            rw [heq]
                                                                                                                                                                            exact cs_w84 ⟨n - 29200, hr⟩
                                                                                                                                                                          ·
                                                                                                                                                                            by_cases h85 : n < 29300
                                                                                                                                                                            · have hr : n - 29250 < 50 := by omega
                                                                                                                                                                              have heq : n = (n - 29250) + 29250 := by omega
                                                                                                                                                                              rw [heq]
                                                                                                                                                                              exact cs_w85 ⟨n - 29250, hr⟩
                                                                                                                                                                            ·
                                                                                                                                                                              by_cases h86 : n < 29350
                                                                                                                                                                              · have hr : n - 29300 < 50 := by omega
                                                                                                                                                                                have heq : n = (n - 29300) + 29300 := by omega
                                                                                                                                                                                rw [heq]
                                                                                                                                                                                exact cs_w86 ⟨n - 29300, hr⟩
                                                                                                                                                                              ·
                                                                                                                                                                                by_cases h87 : n < 29400
                                                                                                                                                                                · have hr : n - 29350 < 50 := by omega
                                                                                                                                                                                  have heq : n = (n - 29350) + 29350 := by omega
                                                                                                                                                                                  rw [heq]
                                                                                                                                                                                  exact cs_w87 ⟨n - 29350, hr⟩
                                                                                                                                                                                ·
                                                                                                                                                                                  by_cases h88 : n < 29450
                                                                                                                                                                                  · have hr : n - 29400 < 50 := by omega
                                                                                                                                                                                    have heq : n = (n - 29400) + 29400 := by omega
                                                                                                                                                                                    rw [heq]
                                                                                                                                                                                    exact cs_w88 ⟨n - 29400, hr⟩
                                                                                                                                                                                  ·
                                                                                                                                                                                    by_cases h89 : n < 29500
                                                                                                                                                                                    · have hr : n - 29450 < 50 := by omega
                                                                                                                                                                                      have heq : n = (n - 29450) + 29450 := by omega
                                                                                                                                                                                      rw [heq]
                                                                                                                                                                                      exact cs_w89 ⟨n - 29450, hr⟩
                                                                                                                                                                                    ·
                                                                                                                                                                                      by_cases h90 : n < 29550
                                                                                                                                                                                      · have hr : n - 29500 < 50 := by omega
                                                                                                                                                                                        have heq : n = (n - 29500) + 29500 := by omega
                                                                                                                                                                                        rw [heq]
                                                                                                                                                                                        exact cs_w90 ⟨n - 29500, hr⟩
                                                                                                                                                                                      ·
                                                                                                                                                                                        by_cases h91 : n < 29600
                                                                                                                                                                                        · have hr : n - 29550 < 50 := by omega
                                                                                                                                                                                          have heq : n = (n - 29550) + 29550 := by omega
                                                                                                                                                                                          rw [heq]
                                                                                                                                                                                          exact cs_w91 ⟨n - 29550, hr⟩
                                                                                                                                                                                        ·
                                                                                                                                                                                          by_cases h92 : n < 29650
                                                                                                                                                                                          · have hr : n - 29600 < 50 := by omega
                                                                                                                                                                                            have heq : n = (n - 29600) + 29600 := by omega
                                                                                                                                                                                            rw [heq]
                                                                                                                                                                                            exact cs_w92 ⟨n - 29600, hr⟩
                                                                                                                                                                                          ·
                                                                                                                                                                                            by_cases h93 : n < 29700
                                                                                                                                                                                            · have hr : n - 29650 < 50 := by omega
                                                                                                                                                                                              have heq : n = (n - 29650) + 29650 := by omega
                                                                                                                                                                                              rw [heq]
                                                                                                                                                                                              exact cs_w93 ⟨n - 29650, hr⟩
                                                                                                                                                                                            ·
                                                                                                                                                                                              by_cases h94 : n < 29750
                                                                                                                                                                                              · have hr : n - 29700 < 50 := by omega
                                                                                                                                                                                                have heq : n = (n - 29700) + 29700 := by omega
                                                                                                                                                                                                rw [heq]
                                                                                                                                                                                                exact cs_w94 ⟨n - 29700, hr⟩
                                                                                                                                                                                              ·
                                                                                                                                                                                                by_cases h95 : n < 29800
                                                                                                                                                                                                · have hr : n - 29750 < 50 := by omega
                                                                                                                                                                                                  have heq : n = (n - 29750) + 29750 := by omega
                                                                                                                                                                                                  rw [heq]
                                                                                                                                                                                                  exact cs_w95 ⟨n - 29750, hr⟩
                                                                                                                                                                                                ·
                                                                                                                                                                                                  by_cases h96 : n < 29850
                                                                                                                                                                                                  · have hr : n - 29800 < 50 := by omega
                                                                                                                                                                                                    have heq : n = (n - 29800) + 29800 := by omega
                                                                                                                                                                                                    rw [heq]
                                                                                                                                                                                                    exact cs_w96 ⟨n - 29800, hr⟩
                                                                                                                                                                                                  ·
                                                                                                                                                                                                    by_cases h97 : n < 29900
                                                                                                                                                                                                    · have hr : n - 29850 < 50 := by omega
                                                                                                                                                                                                      have heq : n = (n - 29850) + 29850 := by omega
                                                                                                                                                                                                      rw [heq]
                                                                                                                                                                                                      exact cs_w97 ⟨n - 29850, hr⟩
                                                                                                                                                                                                    ·
                                                                                                                                                                                                      by_cases h98 : n < 29950
                                                                                                                                                                                                      · have hr : n - 29900 < 50 := by omega
                                                                                                                                                                                                        have heq : n = (n - 29900) + 29900 := by omega
                                                                                                                                                                                                        rw [heq]
                                                                                                                                                                                                        exact cs_w98 ⟨n - 29900, hr⟩
                                                                                                                                                                                                      ·
                                                                                                                                                                                                        have hr : n - 29950 < 50 := by omega
                                                                                                                                                                                                        have heq : n = (n - 29950) + 29950 := by omega
                                                                                                                                                                                                        rw [heq]
                                                                                                                                                                                                        exact cs_w99 ⟨n - 29950, hr⟩

theorem centF_lt_range : ∀ n, 25000 ≤ n → n < 30000 → centF n < 23 := by
  intro n hlo hhi
  by_cases h0 : n < 25050
  · have hr : n - 25000 < 50 := by omega
    have heq : n = (n - 25000) + 25000 := by omega
    rw [heq]
    exact cl_w0 ⟨n - 25000, hr⟩
  ·
    by_cases h1 : n < 25100
    · have hr : n - 25050 < 50 := by omega
      have heq : n = (n - 25050) + 25050 := by omega
      rw [heq]
      exact cl_w1 ⟨n - 25050, hr⟩
    ·
      by_cases h2 : n < 25150
      · have hr : n - 25100 < 50 := by omega
        have heq : n = (n - 25100) + 25100 := by omega
        rw [heq]
        exact cl_w2 ⟨n - 25100, hr⟩
      ·
        by_cases h3 : n < 25200
        · have hr : n - 25150 < 50 := by omega
          have heq : n = (n - 25150) + 25150 := by omega
          rw [heq]
          exact cl_w3 ⟨n - 25150, hr⟩
        ·
          by_cases h4 : n < 25250
          · have hr : n - 25200 < 50 := by omega
            have heq : n = (n - 25200) + 25200 := by omega
            rw [heq]
            exact cl_w4 ⟨n - 25200, hr⟩
          ·
            by_cases h5 : n < 25300
            · have hr : n - 25250 < 50 := by omega
              have heq : n = (n - 25250) + 25250 := by omega
              rw [heq]
              exact cl_w5 ⟨n - 25250, hr⟩
            ·
              by_cases h6 : n < 25350
              · have hr : n - 25300 < 50 := by omega
                have heq : n = (n - 25300) + 25300 := by omega
                rw [heq]
                exact cl_w6 ⟨n - 25300, hr⟩
              ·
                by_cases h7 : n < 25400
                · have hr : n - 25350 < 50 := by omega
                  have heq : n = (n - 25350) + 25350 := by omega
                  rw [heq]
                  exact cl_w7 ⟨n - 25350, hr⟩
                ·
                  by_cases h8 : n < 25450
                  · have hr : n - 25400 < 50 := by omega
                    have heq : n = (n - 25400) + 25400 := by omega
                    rw [heq]
                    exact cl_w8 ⟨n - 25400, hr⟩
                  ·
                    by_cases h9 : n < 25500
                    · have hr : n - 25450 < 50 := by omega
                      have heq : n = (n - 25450) + 25450 := by omega
                      rw [heq]
                      exact cl_w9 ⟨n - 25450, hr⟩
                    ·
                      by_cases h10 : n < 25550
                      · have hr : n - 25500 < 50 := by omega
                        have heq : n = (n - 25500) + 25500 := by omega
                        rw [heq]
                        exact cl_w10 ⟨n - 25500, hr⟩
                      ·
                        by_cases h11 : n < 25600
                        · have hr : n - 25550 < 50 := by omega
                          have heq : n = (n - 25550) + 25550 := by omega
                          rw [heq]
                          exact cl_w11 ⟨n - 25550, hr⟩
                        ·
                          by_cases h12 : n < 25650
                          · have hr : n - 25600 < 50 := by omega
                            have heq : n = (n - 25600) + 25600 := by omega
                            rw [heq]
                            exact cl_w12 ⟨n - 25600, hr⟩
                          ·
                            by_cases h13 : n < 25700
                            · have hr : n - 25650 < 50 := by omega
                              have heq : n = (n - 25650) + 25650 := by omega
                              rw [heq]
                              exact cl_w13 ⟨n - 25650, hr⟩
                            ·
                              by_cases h14 : n < 25750
                              · have hr : n - 25700 < 50 := by omega
                                have heq : n = (n - 25700) + 25700 := by omega
                                rw [heq]
                                exact cl_w14 ⟨n - 25700, hr⟩
                              ·
                                by_cases h15 : n < 25800
                                · have hr : n - 25750 < 50 := by omega
                                  have heq : n = (n - 25750) + 25750 := by omega
                                  rw [heq]
                                  exact cl_w15 ⟨n - 25750, hr⟩
                                ·
                                  by_cases h16 : n < 25850
                                  · have hr : n - 25800 < 50 := by omega
                                    have heq : n = (n - 25800) + 25800 := by omega
                                    rw [heq]
                                    exact cl_w16 ⟨n - 25800, hr⟩
                                  ·
                                    by_cases h17 : n < 25900
                                    · have hr : n - 25850 < 50 := by omega
                                      have heq : n = (n - 25850) + 25850 := by omega
                                      rw [heq]
                                      exact cl_w17 ⟨n - 25850, hr⟩
                                    ·
                                      by_cases h18 : n < 25950
                                      · have hr : n - 25900 < 50 := by omega
                                        have heq : n = (n - 25900) + 25900 := by omega
                                        rw [heq]
                                        exact cl_w18 ⟨n - 25900, hr⟩
                                      ·
                                        by_cases h19 : n < 26000
                                        · have hr : n - 25950 < 50 := by omega
                                          have heq : n = (n - 25950) + 25950 := by omega
                                          rw [heq]
                                          exact cl_w19 ⟨n - 25950, hr⟩
                                        ·
                                          by_cases h20 : n < 26050
                                          · have hr : n - 26000 < 50 := by omega
                                            have heq : n = (n - 26000) + 26000 := by omega
                                            rw [heq]
                                            exact cl_w20 ⟨n - 26000, hr⟩
                                          ·
                                            by_cases h21 : n < 26100
                                            · have hr : n - 26050 < 50 := by omega
                                              have heq : n = (n - 26050) + 26050 := by omega
                                              rw [heq]
                                              exact cl_w21 ⟨n - 26050, hr⟩
                                            ·
                                              by_cases h22 : n < 26150
                                              · have hr : n - 26100 < 50 := by omega
                                                have heq : n = (n - 26100) + 26100 := by omega
                                                rw [heq]
                                                exact cl_w22 ⟨n - 26100, hr⟩
                                              ·
                                                by_cases h23 : n < 26200
                                                · have hr : n - 26150 < 50 := by omega
                                                  have heq : n = (n - 26150) + 26150 := by omega
                                                  rw [heq]
                                                  exact cl_w23 ⟨n - 26150, hr⟩
                                                ·
                                                  by_cases h24 : n < 26250
                                                  · have hr : n - 26200 < 50 := by omega
                                                    have heq : n = (n - 26200) + 26200 := by omega
                                                    rw [heq]
                                                    exact cl_w24 ⟨n - 26200, hr⟩
                                                  ·
                                                    by_cases h25 : n < 26300
                                                    · have hr : n - 26250 < 50 := by omega
                                                      have heq : n = (n - 26250) + 26250 := by omega
                                                      rw [heq]
                                                      exact cl_w25 ⟨n - 26250, hr⟩
                                                    ·
                                                      by_cases h26 : n < 26350
                                                      · have hr : n - 26300 < 50 := by omega
                                                        have heq : n = (n - 26300) + 26300 := by omega
                                                        rw [heq]
                                                        exact cl_w26 ⟨n - 26300, hr⟩
                                                      ·
                                                        by_cases h27 : n < 26400
                                                        · have hr : n - 26350 < 50 := by omega
                                                          have heq : n = (n - 26350) + 26350 := by omega
                                                          rw [heq]
                                                          exact cl_w27 ⟨n - 26350, hr⟩
                                                        ·
                                                          by_cases h28 : n < 26450
                                                          · have hr : n - 26400 < 50 := by omega
                                                            have heq : n = (n - 26400) + 26400 := by omega
                                                            rw [heq]
                                                            exact cl_w28 ⟨n - 26400, hr⟩
                                                          ·
                                                            by_cases h29 : n < 26500
                                                            · have hr : n - 26450 < 50 := by omega
                                                              have heq : n = (n - 26450) + 26450 := by omega
                                                              rw [heq]
                                                              exact cl_w29 ⟨n - 26450, hr⟩
                                                            ·
                                                              by_cases h30 : n < 26550
                                                              · have hr : n - 26500 < 50 := by omega
                                                                have heq : n = (n - 26500) + 26500 := by omega
                                                                rw [heq]
                                                                exact cl_w30 ⟨n - 26500, hr⟩
                                                              ·
                                                                by_cases h31 : n < 26600
                                                                · have hr : n - 26550 < 50 := by omega
                                                                  have heq : n = (n - 26550) + 26550 := by omega
                                                                  rw [heq]
                                                                  exact cl_w31 ⟨n - 26550, hr⟩
                                                                ·
                                                                  by_cases h32 : n < 26650
                                                                  · have hr : n - 26600 < 50 := by omega
                                                                    have heq : n = (n - 26600) + 26600 := by omega
                                                                    rw [heq]
                                                                    exact cl_w32 ⟨n - 26600, hr⟩
                                                                  ·
                                                                    by_cases h33 : n < 26700
                                                                    · have hr : n - 26650 < 50 := by omega
                                                                      have heq : n = (n - 26650) + 26650 := by omega
                                                                      rw [heq]
                                                                      exact cl_w33 ⟨n - 26650, hr⟩
                                                                    ·
                                                                      by_cases h34 : n < 26750
                                                                      · have hr : n - 26700 < 50 := by omega
                                                                        have heq : n = (n - 26700) + 26700 := by omega
                                                                        rw [heq]
                                                                        exact cl_w34 ⟨n - 26700, hr⟩
                                                                      ·
                                                                        by_cases h35 : n < 26800
                                                                        · have hr : n - 26750 < 50 := by omega
                                                                          have heq : n = (n - 26750) + 26750 := by omega
                                                                          rw [heq]
                                                                          exact cl_w35 ⟨n - 26750, hr⟩
                                                                        ·
                                                                          by_cases h36 : n < 26850
                                                                          · have hr : n - 26800 < 50 := by omega
                                                                            have heq : n = (n - 26800) + 26800 := by omega
                                                                            rw [heq]
                                                                            exact cl_w36 ⟨n - 26800, hr⟩
                                                                          ·
                                                                            by_cases h37 : n < 26900
                                                                            · have hr : n - 26850 < 50 := by omega
                                                                              have heq : n = (n - 26850) + 26850 := by omega
                                                                              rw [heq]
                                                                              exact cl_w37 ⟨n - 26850, hr⟩
                                                                            ·
                                                                              by_cases h38 : n < 26950
                                                                              · have hr : n - 26900 < 50 := by omega
                                                                                have heq : n = (n - 26900) + 26900 := by omega
                                                                                rw [heq]
                                                                                exact cl_w38 ⟨n - 26900, hr⟩
                                                                              ·
                                                                                by_cases h39 : n < 27000
                                                                                · have hr : n - 26950 < 50 := by omega
                                                                                  have heq : n = (n - 26950) + 26950 := by omega
                                                                                  rw [heq]
                                                                                  exact cl_w39 ⟨n - 26950, hr⟩
                                                                                ·
                                                                                  by_cases h40 : n < 27050
                                                                                  · have hr : n - 27000 < 50 := by omega
                                                                                    have heq : n = (n - 27000) + 27000 := by omega
                                                                                    rw [heq]
                                                                                    exact cl_w40 ⟨n - 27000, hr⟩
                                                                                  ·
                                                                                    by_cases h41 : n < 27100
                                                                                    · have hr : n - 27050 < 50 := by omega
                                                                                      have heq : n = (n - 27050) + 27050 := by omega
                                                                                      rw [heq]
                                                                                      exact cl_w41 ⟨n - 27050, hr⟩
                                                                                    ·
                                                                                      by_cases h42 : n < 27150
                                                                                      · have hr : n - 27100 < 50 := by omega
                                                                                        have heq : n = (n - 27100) + 27100 := by omega
                                                                                        rw [heq]
                                                                                        exact cl_w42 ⟨n - 27100, hr⟩
                                                                                      ·
                                                                                        by_cases h43 : n < 27200
                                                                                        · have hr : n - 27150 < 50 := by omega
                                                                                          have heq : n = (n - 27150) + 27150 := by omega
                                                                                          rw [heq]
                                                                                          exact cl_w43 ⟨n - 27150, hr⟩
                                                                                        ·
                                                                                          by_cases h44 : n < 27250
                                                                                          · have hr : n - 27200 < 50 := by omega
                                                                                            have heq : n = (n - 27200) + 27200 := by omega
                                                                                            rw [heq]
                                                                                            exact cl_w44 ⟨n - 27200, hr⟩
                                                                                          ·
                                                                                            by_cases h45 : n < 27300
                                                                                            · have hr : n - 27250 < 50 := by omega
                                                                                              have heq : n = (n - 27250) + 27250 := by omega
                                                                                              rw [heq]
                                                                                              exact cl_w45 ⟨n - 27250, hr⟩
                                                                                            ·
                                                                                              by_cases h46 : n < 27350
                                                                                              · have hr : n - 27300 < 50 := by omega
                                                                                                have heq : n = (n - 27300) + 27300 := by omega
                                                                                                rw [heq]
                                                                                                exact cl_w46 ⟨n - 27300, hr⟩
                                                                                              ·
                                                                                                by_cases h47 : n < 27400
                                                                                                · have hr : n - 27350 < 50 := by omega
                                                                                                  have heq : n = (n - 27350) + 27350 := by omega
                                                                                                  rw [heq]
                                                                                                  exact cl_w47 ⟨n - 27350, hr⟩
                                                                                                ·
                                                                                                  by_cases h48 : n < 27450
                                                                                                  · have hr : n - 27400 < 50 := by omega
                                                                                                    have heq : n = (n - 27400) + 27400 := by omega
                                                                                                    rw [heq]
                                                                                                    exact cl_w48 ⟨n - 27400, hr⟩
                                                                                                  ·
                                                                                                    by_cases h49 : n < 27500
                                                                                                    · have hr : n - 27450 < 50 := by omega
                                                                                                      have heq : n = (n - 27450) + 27450 := by omega
                                                                                                      rw [heq]
                                                                                                      exact cl_w49 ⟨n - 27450, hr⟩
                                                                                                    ·
                                                                                                      by_cases h50 : n < 27550
                                                                                                      · have hr : n - 27500 < 50 := by omega
                                                                                                        have heq : n = (n - 27500) + 27500 := by omega
                                                                                                        rw [heq]
                                                                                                        exact cl_w50 ⟨n - 27500, hr⟩
                                                                                                      ·
                                                                                                        by_cases h51 : n < 27600
                                                                                                        · have hr : n - 27550 < 50 := by omega
                                                                                                          have heq : n = (n - 27550) + 27550 := by omega
                                                                                                          rw [heq]
                                                                                                          exact cl_w51 ⟨n - 27550, hr⟩
                                                                                                        ·
                                                                                                          by_cases h52 : n < 27650
                                                                                                          · have hr : n - 27600 < 50 := by omega
                                                                                                            have heq : n = (n - 27600) + 27600 := by omega
                                                                                                            rw [heq]
                                                                                                            exact cl_w52 ⟨n - 27600, hr⟩
                                                                                                          ·
                                                                                                            by_cases h53 : n < 27700
                                                                                                            · have hr : n - 27650 < 50 := by omega
                                                                                                              have heq : n = (n - 27650) + 27650 := by omega
                                                                                                              rw [heq]
                                                                                                              exact cl_w53 ⟨n - 27650, hr⟩
                                                                                                            ·
                                                                                                              by_cases h54 : n < 27750
                                                                                                              · have hr : n - 27700 < 50 := by omega
                                                                                                                have heq : n = (n - 27700) + 27700 := by omega
                                                                                                                rw [heq]
                                                                                                                exact cl_w54 ⟨n - 27700, hr⟩
                                                                                                              ·
                                                                                                                by_cases h55 : n < 27800
                                                                                                                · have hr : n - 27750 < 50 := by omega
                                                                                                                  have heq : n = (n - 27750) + 27750 := by omega
                                                                                                                  rw [heq]
                                                                                                                  exact cl_w55 ⟨n - 27750, hr⟩
                                                                                                                ·
                                                                                                                  by_cases h56 : n < 27850
                                                                                                                  · have hr : n - 27800 < 50 := by omega
                                                                                                                    have heq : n = (n - 27800) + 27800 := by omega
                                                                                                                    rw [heq]
                                                                                                                    exact cl_w56 ⟨n - 27800, hr⟩
                                                                                                                  ·
                                                                                                                    by_cases h57 : n < 27900
                                                                                                                    · have hr : n - 27850 < 50 := by omega
                                                                                                                      have heq : n = (n - 27850) + 27850 := by omega
                                                                                                                      rw [heq]
                                                                                                                      exact cl_w57 ⟨n - 27850, hr⟩
                                                                                                                    ·
                                                                                                                      by_cases h58 : n < 27950
                                                                                                                      · have hr : n - 27900 < 50 := by omega
                                                                                                                        have heq : n = (n - 27900) + 27900 := by omega
                                                                                                                        rw [heq]
                                                                                                                        exact cl_w58 ⟨n - 27900, hr⟩
                                                                                                                      ·
                                                                                                                        by_cases h59 : n < 28000
                                                                                                                        · have hr : n - 27950 < 50 := by omega
                                                                                                                          have heq : n = (n - 27950) + 27950 := by omega
                                                                                                                          rw [heq]
                                                                                                                          exact cl_w59 ⟨n - 27950, hr⟩
                                                                                                                        ·
                                                                                                                          by_cases h60 : n < 28050
                                                                                                                          · have hr : n - 28000 < 50 := by omega
                                                                                                                            have heq : n = (n - 28000) + 28000 := by omega
                                                                                                                            rw [heq]
                                                                                                                            exact cl_w60 ⟨n - 28000, hr⟩
                                                                                                                          ·
                                                                                                                            by_cases h61 : n < 28100
                                                                                                                            · have hr : n - 28050 < 50 := by omega
                                                                                                                              have heq : n = (n - 28050) + 28050 := by omega
                                                                                                                              rw [heq]
                                                                                                                              exact cl_w61 ⟨n - 28050, hr⟩
                                                                                                                            ·
                                                                                                                              by_cases h62 : n < 28150
                                                                                                                              · have hr : n - 28100 < 50 := by omega
                                                                                                                                have heq : n = (n - 28100) + 28100 := by omega
                                                                                                                                rw [heq]
                                                                                                                                exact cl_w62 ⟨n - 28100, hr⟩
                                                                                                                              ·
                                                                                                                                by_cases h63 : n < 28200
                                                                                                                                · have hr : n - 28150 < 50 := by omega
                                                                                                                                  have heq : n = (n - 28150) + 28150 := by omega
                                                                                                                                  rw [heq]
                                                                                                                                  exact cl_w63 ⟨n - 28150, hr⟩
                                                                                                                                ·
                                                                                                                                  by_cases h64 : n < 28250
                                                                                                                                  · have hr : n - 28200 < 50 := by omega
                                                                                                                                    have heq : n = (n - 28200) + 28200 := by omega
                                                                                                                                    rw [heq]
                                                                                                                                    exact cl_w64 ⟨n - 28200, hr⟩
                                                                                                                                  ·
                                                                                                                                    by_cases h65 : n < 28300
                                                                                                                                    · have hr : n - 28250 < 50 := by omega
                                                                                                                                      have heq : n = (n - 28250) + 28250 := by omega
                                                                                                                                      rw [heq]
                                                                                                                                      exact cl_w65 ⟨n - 28250, hr⟩
                                                                                                                                    ·
                                                                                                                                      by_cases h66 : n < 28350
                                                                                                                                      · have hr : n - 28300 < 50 := by omega
                                                                                                                                        have heq : n = (n - 28300) + 28300 := by omega
                                                                                                                                        rw [heq]
                                                                                                                                        exact cl_w66 ⟨n - 28300, hr⟩
                                                                                                                                      ·
                                                                                                                                        by_cases h67 : n < 28400
                                                                                                                                        · have hr : n - 28350 < 50 := by omega
                                                                                                                                          have heq : n = (n - 28350) + 28350 := by omega
                                                                                                                                          rw [heq]
                                                                                                                                          exact cl_w67 ⟨n - 28350, hr⟩
                                                                                                                                        ·
                                                                                                                                          by_cases h68 : n < 28450
                                                                                                                                          · have hr : n - 28400 < 50 := by omega
                                                                                                                                            have heq : n = (n - 28400) + 28400 := by omega
                                                                                                                                            rw [heq]
                                                                                                                                            exact cl_w68 ⟨n - 28400, hr⟩
                                                                                                                                          ·
                                                                                                                                            by_cases h69 : n < 28500
                                                                                                                                            · have hr : n - 28450 < 50 := by omega
                                                                                                                                              have heq : n = (n - 28450) + 28450 := by omega
                                                                                                                                              rw [heq]
                                                                                                                                              exact cl_w69 ⟨n - 28450, hr⟩
                                                                                                                                            ·
                                                                                                                                              by_cases h70 : n < 28550
                                                                                                                                              · have hr : n - 28500 < 50 := by omega
                                                                                                                                                have heq : n = (n - 28500) + 28500 := by omega
                                                                                                                                                rw [heq]
                                                                                                                                                exact cl_w70 ⟨n - 28500, hr⟩
                                                                                                                                              ·
                                                                                                                                                by_cases h71 : n < 28600
                                                                                                                                                · have hr : n - 28550 < 50 := by omega
                                                                                                                                                  have heq : n = (n - 28550) + 28550 := by omega
                                                                                                                                                  rw [heq]
                                                                                                                                                  exact cl_w71 ⟨n - 28550, hr⟩
                                                                                                                                                ·
                                                                                                                                                  by_cases h72 : n < 28650
                                                                                                                                                  · have hr : n - 28600 < 50 := by omega
                                                                                                                                                    have heq : n = (n - 28600) + 28600 := by omega
                                                                                                                                                    rw [heq]
                                                                                                                                                    exact cl_w72 ⟨n - 28600, hr⟩
                                                                                                                                                  ·
                                                                                                                                                    by_cases h73 : n < 28700
                                                                                                                                                    · have hr : n - 28650 < 50 := by omega
                                                                                                                                                      have heq : n = (n - 28650) + 28650 := by omega
                                                                                                                                                      rw [heq]
                                                                                                                                                      exact cl_w73 ⟨n - 28650, hr⟩
                                                                                                                                                    ·
                                                                                                                                                      by_cases h74 : n < 28750
                                                                                                                                                      · have hr : n - 28700 < 50 := by omega
                                                                                                                                                        have heq : n = (n - 28700) + 28700 := by omega
                                                                                                                                                        rw [heq]
                                                                                                                                                        exact cl_w74 ⟨n - 28700, hr⟩
                                                                                                                                                      ·
                                                                                                                                                        by_cases h75 : n < 28800
                                                                                                                                                        · have hr : n - 28750 < 50 := by omega
                                                                                                                                                          have heq : n = (n - 28750) + 28750 := by omega
                                                                                                                                                          rw [heq]
                                                                                                                                                          exact cl_w75 ⟨n - 28750, hr⟩
                                                                                                                                                        ·
                                                                                                                                                          by_cases h76 : n < 28850
                                                                                                                                                          · have hr : n - 28800 < 50 := by omega
                                                                                                                                                            have heq : n = (n - 28800) + 28800 := by omega
                                                                                                                                                            rw [heq]
                                                                                                                                                            exact cl_w76 ⟨n - 28800, hr⟩
                                                                                                                                                          ·
                                                                                                                                                            by_cases h77 : n < 28900
                                                                                                                                                            · have hr : n - 28850 < 50 := by omega
                                                                                                                                                              have heq : n = (n - 28850) + 28850 := by omega
                                                                                                                                                              rw [heq]
                                                                                                                                                              exact cl_w77 ⟨n - 28850, hr⟩
                                                                                                                                                            ·
                                                                                                                                                              by_cases h78 : n < 28950
                                                                                                                                                              · have hr : n - 28900 < 50 := by omega
                                                                                                                                                                have heq : n = (n - 28900) + 28900 := by omega
                                                                                                                                                                rw [heq]
                                                                                                                                                                exact cl_w78 ⟨n - 28900, hr⟩
                                                                                                                                                              ·
                                                                                                                                                                by_cases h79 : n < 29000
                                                                                                                                                                · have hr : n - 28950 < 50 := by omega
                                                                                                                                                                  have heq : n = (n - 28950) + 28950 := by omega
                                                                                                                                                                  rw [heq]
                                                                                                                                                                  exact cl_w79 ⟨n - 28950, hr⟩
                                                                                                                                                                ·
                                                                                                                                                                  by_cases h80 : n < 29050
                                                                                                                                                                  · have hr : n - 29000 < 50 := by omega
                                                                                                                                                                    have heq : n = (n - 29000) + 29000 := by omega
                                                                                                                                                                    rw [heq]
                                                                                                                                                                    exact cl_w80 ⟨n - 29000, hr⟩
                                                                                                                                                                  ·
                                                                                                                                                                    by_cases h81 : n < 29100
                                                                                                                                                                    · have hr : n - 29050 < 50 := by omega
                                                                                                                                                                      have heq : n = (n - 29050) + 29050 := by omega
                                                                                                                                                                      rw [heq]
                                                                                                                                                                      exact cl_w81 ⟨n - 29050, hr⟩
                                                                                                                                                                    ·
                                                                                                                                                                      by_cases h82 : n < 29150
                                                                                                                                                                      · have hr : n - 29100 < 50 := by omega
                                                                                                                                                                        have heq : n = (n - 29100) + 29100 := by omega
                                                                                                                                                                        rw [heq]
                                                                                                                                                                        exact cl_w82 ⟨n - 29100, hr⟩
                                                                                                                                                                      ·
                                                                                                                                                                        by_cases h83 : n < 29200
                                                                                                                                                                        · have hr : n - 29150 < 50 := by omega
                                                                                                                                                                          have heq : n = (n - 29150) + 29150 := by omega
                                                                                                                                                                          rw [heq]
                                                                                                                                                                          exact cl_w83 ⟨n - 29150, hr⟩
                                                                                                                                                                        ·
                                                                                                                                                                          by_cases h84 : n < 29250
                                                                                                                                                                          · have hr : n - 29200 < 50 := by omega
                                                                                                                                                                            have heq : n = (n - 29200) + 29200 := by omega
                                                                                                                                                                            rw [heq]
                                                                                                                                                                            exact cl_w84 ⟨n - 29200, hr⟩
                                                                                                                                                                          ·
                                                                                                                                                                            by_cases h85 : n < 29300
                                                                                                                                                                            · have hr : n - 29250 < 50 := by omega
                                                                                                                                                                              have heq : n = (n - 29250) + 29250 := by omega
                                                                                                                                                                              rw [heq]
                                                                                                                                                                              exact cl_w85 ⟨n - 29250, hr⟩
                                                                                                                                                                            ·
                                                                                                                                                                              by_cases h86 : n < 29350
                                                                                                                                                                              · have hr : n - 29300 < 50 := by omega
                                                                                                                                                                                have heq : n = (n - 29300) + 29300 := by omega
                                                                                                                                                                                rw [heq]
                                                                                                                                                                                exact cl_w86 ⟨n - 29300, hr⟩
                                                                                                                                                                              ·
                                                                                                                                                                                by_cases h87 : n < 29400
                                                                                                                                                                                · have hr : n - 29350 < 50 := by omega
                                                                                                                                                                                  have heq : n = (n - 29350) + 29350 := by omega
                                                                                                                                                                                  rw [heq]
                                                                                                                                                                                  exact cl_w87 ⟨n - 29350, hr⟩
                                                                                                                                                                                ·
                                                                                                                                                                                  by_cases h88 : n < 29450
                                                                                                                                                                                  · have hr : n - 29400 < 50 := by omega
                                                                                                                                                                                    have heq : n = (n - 29400) + 29400 := by omega
                                                                                                                                                                                    rw [heq]
                                                                                                                                                                                    exact cl_w88 ⟨n - 29400, hr⟩
                                                                                                                                                                                  ·
                                                                                                                                                                                    by_cases h89 : n < 29500
                                                                                                                                                                                    · have hr : n - 29450 < 50 := by omega
                                                                                                                                                                                      have heq : n = (n - 29450) + 29450 := by omega
                                                                                                                                                                                      rw [heq]
                                                                                                                                                                                      exact cl_w89 ⟨n - 29450, hr⟩
                                                                                                                                                                                    ·
                                                                                                                                                                                      by_cases h90 : n < 29550
                                                                                                                                                                                      · have hr : n - 29500 < 50 := by omega
                                                                                                                                                                                        have heq : n = (n - 29500) + 29500 := by omega
                                                                                                                                                                                        rw [heq]
                                                                                                                                                                                        exact cl_w90 ⟨n - 29500, hr⟩
                                                                                                                                                                                      ·
                                                                                                                                                                                        by_cases h91 : n < 29600
                                                                                                                                                                                        · have hr : n - 29550 < 50 := by omega
                                                                                                                                                                                          have heq : n = (n - 29550) + 29550 := by omega
                                                                                                                                                                                          rw [heq]
                                                                                                                                                                                          exact cl_w91 ⟨n - 29550, hr⟩
                                                                                                                                                                                        ·
                                                                                                                                                                                          by_cases h92 : n < 29650
                                                                                                                                                                                          · have hr : n - 29600 < 50 := by omega
                                                                                                                                                                                            have heq : n = (n - 29600) + 29600 := by omega
                                                                                                                                                                                            rw [heq]
                                                                                                                                                                                            exact cl_w92 ⟨n - 29600, hr⟩
                                                                                                                                                                                          ·
                                                                                                                                                                                            by_cases h93 : n < 29700
                                                                                                                                                                                            · have hr : n - 29650 < 50 := by omega
                                                                                                                                                                                              have heq : n = (n - 29650) + 29650 := by omega
                                                                                                                                                                                              rw [heq]
                                                                                                                                                                                              exact cl_w93 ⟨n - 29650, hr⟩
                                                                                                                                                                                            ·
                                                                                                                                                                                              by_cases h94 : n < 29750
                                                                                                                                                                                              · have hr : n - 29700 < 50 := by omega
                                                                                                                                                                                                have heq : n = (n - 29700) + 29700 := by omega
                                                                                                                                                                                                rw [heq]
                                                                                                                                                                                                exact cl_w94 ⟨n - 29700, hr⟩
                                                                                                                                                                                              ·
                                                                                                                                                                                                by_cases h95 : n < 29800
                                                                                                                                                                                                · have hr : n - 29750 < 50 := by omega
                                                                                                                                                                                                  have heq : n = (n - 29750) + 29750 := by omega
                                                                                                                                                                                                  rw [heq]
                                                                                                                                                                                                  exact cl_w95 ⟨n - 29750, hr⟩
                                                                                                                                                                                                ·
                                                                                                                                                                                                  by_cases h96 : n < 29850
                                                                                                                                                                                                  · have hr : n - 29800 < 50 := by omega
                                                                                                                                                                                                    have heq : n = (n - 29800) + 29800 := by omega
                                                                                                                                                                                                    rw [heq]
                                                                                                                                                                                                    exact cl_w96 ⟨n - 29800, hr⟩
                                                                                                                                                                                                  ·
                                                                                                                                                                                                    by_cases h97 : n < 29900
                                                                                                                                                                                                    · have hr : n - 29850 < 50 := by omega
                                                                                                                                                                                                      have heq : n = (n - 29850) + 29850 := by omega
                                                                                                                                                                                                      rw [heq]
                                                                                                                                                                                                      exact cl_w97 ⟨n - 29850, hr⟩
                                                                                                                                                                                                    ·
                                                                                                                                                                                                      by_cases h98 : n < 29950
                                                                                                                                                                                                      · have hr : n - 29900 < 50 := by omega
                                                                                                                                                                                                        have heq : n = (n - 29900) + 29900 := by omega
                                                                                                                                                                                                        rw [heq]
                                                                                                                                                                                                        exact cl_w98 ⟨n - 29900, hr⟩
                                                                                                                                                                                                      ·
                                                                                                                                                                                                        have hr : n - 29950 < 50 := by omega
                                                                                                                                                                                                        have heq : n = (n - 29950) + 29950 := by omega
                                                                                                                                                                                                        rw [heq]
                                                                                                                                                                                                        exact cl_w99 ⟨n - 29950, hr⟩

theorem densSupG_lt_range : ∀ n, 25000 ≤ n → n < 30000 → densSupG n < 2 ^ 1771 := by
  intro n hlo hhi
  by_cases h0 : n < 25050
  · have hr : n - 25000 < 50 := by omega
    have heq : n = (n - 25000) + 25000 := by omega
    rw [heq]
    exact bd_w0 ⟨n - 25000, hr⟩
  ·
    by_cases h1 : n < 25100
    · have hr : n - 25050 < 50 := by omega
      have heq : n = (n - 25050) + 25050 := by omega
      rw [heq]
      exact bd_w1 ⟨n - 25050, hr⟩
    ·
      by_cases h2 : n < 25150
      · have hr : n - 25100 < 50 := by omega
        have heq : n = (n - 25100) + 25100 := by omega
        rw [heq]
        exact bd_w2 ⟨n - 25100, hr⟩
      ·
        by_cases h3 : n < 25200
        · have hr : n - 25150 < 50 := by omega
          have heq : n = (n - 25150) + 25150 := by omega
          rw [heq]
          exact bd_w3 ⟨n - 25150, hr⟩
        ·
          by_cases h4 : n < 25250
          · have hr : n - 25200 < 50 := by omega
            have heq : n = (n - 25200) + 25200 := by omega
            rw [heq]
            exact bd_w4 ⟨n - 25200, hr⟩
          ·
            by_cases h5 : n < 25300
            · have hr : n - 25250 < 50 := by omega
              have heq : n = (n - 25250) + 25250 := by omega
              rw [heq]
              exact bd_w5 ⟨n - 25250, hr⟩
            ·
              by_cases h6 : n < 25350
              · have hr : n - 25300 < 50 := by omega
                have heq : n = (n - 25300) + 25300 := by omega
                rw [heq]
                exact bd_w6 ⟨n - 25300, hr⟩
              ·
                by_cases h7 : n < 25400
                · have hr : n - 25350 < 50 := by omega
                  have heq : n = (n - 25350) + 25350 := by omega
                  rw [heq]
                  exact bd_w7 ⟨n - 25350, hr⟩
                ·
                  by_cases h8 : n < 25450
                  · have hr : n - 25400 < 50 := by omega
                    have heq : n = (n - 25400) + 25400 := by omega
                    rw [heq]
                    exact bd_w8 ⟨n - 25400, hr⟩
                  ·
                    by_cases h9 : n < 25500
                    · have hr : n - 25450 < 50 := by omega
                      have heq : n = (n - 25450) + 25450 := by omega
                      rw [heq]
                      exact bd_w9 ⟨n - 25450, hr⟩
                    ·
                      by_cases h10 : n < 25550
                      · have hr : n - 25500 < 50 := by omega
                        have heq : n = (n - 25500) + 25500 := by omega
                        rw [heq]
                        exact bd_w10 ⟨n - 25500, hr⟩
                      ·
                        by_cases h11 : n < 25600
                        · have hr : n - 25550 < 50 := by omega
                          have heq : n = (n - 25550) + 25550 := by omega
                          rw [heq]
                          exact bd_w11 ⟨n - 25550, hr⟩
                        ·
                          by_cases h12 : n < 25650
                          · have hr : n - 25600 < 50 := by omega
                            have heq : n = (n - 25600) + 25600 := by omega
                            rw [heq]
                            exact bd_w12 ⟨n - 25600, hr⟩
                          ·
                            by_cases h13 : n < 25700
                            · have hr : n - 25650 < 50 := by omega
                              have heq : n = (n - 25650) + 25650 := by omega
                              rw [heq]
                              exact bd_w13 ⟨n - 25650, hr⟩
                            ·
                              by_cases h14 : n < 25750
                              · have hr : n - 25700 < 50 := by omega
                                have heq : n = (n - 25700) + 25700 := by omega
                                rw [heq]
                                exact bd_w14 ⟨n - 25700, hr⟩
                              ·
                                by_cases h15 : n < 25800
                                · have hr : n - 25750 < 50 := by omega
                                  have heq : n = (n - 25750) + 25750 := by omega
                                  rw [heq]
                                  exact bd_w15 ⟨n - 25750, hr⟩
                                ·
                                  by_cases h16 : n < 25850
                                  · have hr : n - 25800 < 50 := by omega
                                    have heq : n = (n - 25800) + 25800 := by omega
                                    rw [heq]
                                    exact bd_w16 ⟨n - 25800, hr⟩
                                  ·
                                    by_cases h17 : n < 25900
                                    · have hr : n - 25850 < 50 := by omega
                                      have heq : n = (n - 25850) + 25850 := by omega
                                      rw [heq]
                                      exact bd_w17 ⟨n - 25850, hr⟩
                                    ·
                                      by_cases h18 : n < 25950
                                      · have hr : n - 25900 < 50 := by omega
                                        have heq : n = (n - 25900) + 25900 := by omega
                                        rw [heq]
                                        exact bd_w18 ⟨n - 25900, hr⟩
                                      ·
                                        by_cases h19 : n < 26000
                                        · have hr : n - 25950 < 50 := by omega
                                          have heq : n = (n - 25950) + 25950 := by omega
                                          rw [heq]
                                          exact bd_w19 ⟨n - 25950, hr⟩
                                        ·
                                          by_cases h20 : n < 26050
                                          · have hr : n - 26000 < 50 := by omega
                                            have heq : n = (n - 26000) + 26000 := by omega
                                            rw [heq]
                                            exact bd_w20 ⟨n - 26000, hr⟩
                                          ·
                                            by_cases h21 : n < 26100
                                            · have hr : n - 26050 < 50 := by omega
                                              have heq : n = (n - 26050) + 26050 := by omega
                                              rw [heq]
                                              exact bd_w21 ⟨n - 26050, hr⟩
                                            ·
                                              by_cases h22 : n < 26150
                                              · have hr : n - 26100 < 50 := by omega
                                                have heq : n = (n - 26100) + 26100 := by omega
                                                rw [heq]
                                                exact bd_w22 ⟨n - 26100, hr⟩
                                              ·
                                                by_cases h23 : n < 26200
                                                · have hr : n - 26150 < 50 := by omega
                                                  have heq : n = (n - 26150) + 26150 := by omega
                                                  rw [heq]
                                                  exact bd_w23 ⟨n - 26150, hr⟩
                                                ·
                                                  by_cases h24 : n < 26250
                                                  · have hr : n - 26200 < 50 := by omega
                                                    have heq : n = (n - 26200) + 26200 := by omega
                                                    rw [heq]
                                                    exact bd_w24 ⟨n - 26200, hr⟩
                                                  ·
                                                    by_cases h25 : n < 26300
                                                    · have hr : n - 26250 < 50 := by omega
                                                      have heq : n = (n - 26250) + 26250 := by omega
                                                      rw [heq]
                                                      exact bd_w25 ⟨n - 26250, hr⟩
                                                    ·
                                                      by_cases h26 : n < 26350
                                                      · have hr : n - 26300 < 50 := by omega
                                                        have heq : n = (n - 26300) + 26300 := by omega
                                                        rw [heq]
                                                        exact bd_w26 ⟨n - 26300, hr⟩
                                                      ·
                                                        by_cases h27 : n < 26400
                                                        · have hr : n - 26350 < 50 := by omega
                                                          have heq : n = (n - 26350) + 26350 := by omega
                                                          rw [heq]
                                                          exact bd_w27 ⟨n - 26350, hr⟩
                                                        ·
                                                          by_cases h28 : n < 26450
                                                          · have hr : n - 26400 < 50 := by omega
                                                            have heq : n = (n - 26400) + 26400 := by omega
                                                            rw [heq]
                                                            exact bd_w28 ⟨n - 26400, hr⟩
                                                          ·
                                                            by_cases h29 : n < 26500
                                                            · have hr : n - 26450 < 50 := by omega
                                                              have heq : n = (n - 26450) + 26450 := by omega
                                                              rw [heq]
                                                              exact bd_w29 ⟨n - 26450, hr⟩
                                                            ·
                                                              by_cases h30 : n < 26550
                                                              · have hr : n - 26500 < 50 := by omega
                                                                have heq : n = (n - 26500) + 26500 := by omega
                                                                rw [heq]
                                                                exact bd_w30 ⟨n - 26500, hr⟩
                                                              ·
                                                                by_cases h31 : n < 26600
                                                                · have hr : n - 26550 < 50 := by omega
                                                                  have heq : n = (n - 26550) + 26550 := by omega
                                                                  rw [heq]
                                                                  exact bd_w31 ⟨n - 26550, hr⟩
                                                                ·
                                                                  by_cases h32 : n < 26650
                                                                  · have hr : n - 26600 < 50 := by omega
                                                                    have heq : n = (n - 26600) + 26600 := by omega
                                                                    rw [heq]
                                                                    exact bd_w32 ⟨n - 26600, hr⟩
                                                                  ·
                                                                    by_cases h33 : n < 26700
                                                                    · have hr : n - 26650 < 50 := by omega
                                                                      have heq : n = (n - 26650) + 26650 := by omega
                                                                      rw [heq]
                                                                      exact bd_w33 ⟨n - 26650, hr⟩
                                                                    ·
                                                                      by_cases h34 : n < 26750
                                                                      · have hr : n - 26700 < 50 := by omega
                                                                        have heq : n = (n - 26700) + 26700 := by omega
                                                                        rw [heq]
                                                                        exact bd_w34 ⟨n - 26700, hr⟩
                                                                      ·
                                                                        by_cases h35 : n < 26800
                                                                        · have hr : n - 26750 < 50 := by omega
                                                                          have heq : n = (n - 26750) + 26750 := by omega
                                                                          rw [heq]
                                                                          exact bd_w35 ⟨n - 26750, hr⟩
                                                                        ·
                                                                          by_cases h36 : n < 26850
                                                                          · have hr : n - 26800 < 50 := by omega
                                                                            have heq : n = (n - 26800) + 26800 := by omega
                                                                            rw [heq]
                                                                            exact bd_w36 ⟨n - 26800, hr⟩
                                                                          ·
                                                                            by_cases h37 : n < 26900
                                                                            · have hr : n - 26850 < 50 := by omega
                                                                              have heq : n = (n - 26850) + 26850 := by omega
                                                                              rw [heq]
                                                                              exact bd_w37 ⟨n - 26850, hr⟩
                                                                            ·
                                                                              by_cases h38 : n < 26950
                                                                              · have hr : n - 26900 < 50 := by omega
                                                                                have heq : n = (n - 26900) + 26900 := by omega
                                                                                rw [heq]
                                                                                exact bd_w38 ⟨n - 26900, hr⟩
                                                                              ·
                                                                                by_cases h39 : n < 27000
                                                                                · have hr : n - 26950 < 50 := by omega
                                                                                  have heq : n = (n - 26950) + 26950 := by omega
                                                                                  rw [heq]
                                                                                  exact bd_w39 ⟨n - 26950, hr⟩
                                                                                ·
                                                                                  by_cases h40 : n < 27050
                                                                                  · have hr : n - 27000 < 50 := by omega
                                                                                    have heq : n = (n - 27000) + 27000 := by omega
                                                                                    rw [heq]
                                                                                    exact bd_w40 ⟨n - 27000, hr⟩
                                                                                  ·
                                                                                    by_cases h41 : n < 27100
                                                                                    · have hr : n - 27050 < 50 := by omega
                                                                                      have heq : n = (n - 27050) + 27050 := by omega
                                                                                      rw [heq]
                                                                                      exact bd_w41 ⟨n - 27050, hr⟩
                                                                                    ·
                                                                                      by_cases h42 : n < 27150
                                                                                      · have hr : n - 27100 < 50 := by omega
                                                                                        have heq : n = (n - 27100) + 27100 := by omega
                                                                                        rw [heq]
                                                                                        exact bd_w42 ⟨n - 27100, hr⟩
                                                                                      ·
                                                                                        by_cases h43 : n < 27200
                                                                                        · have hr : n - 27150 < 50 := by omega
                                                                                          have heq : n = (n - 27150) + 27150 := by omega
                                                                                          rw [heq]
                                                                                          exact bd_w43 ⟨n - 27150, hr⟩
                                                                                        ·
                                                                                          by_cases h44 : n < 27250
                                                                                          · have hr : n - 27200 < 50 := by omega
                                                                                            have heq : n = (n - 27200) + 27200 := by omega
                                                                                            rw [heq]
                                                                                            exact bd_w44 ⟨n - 27200, hr⟩
                                                                                          ·
                                                                                            by_cases h45 : n < 27300
                                                                                            · have hr : n - 27250 < 50 := by omega
                                                                                              have heq : n = (n - 27250) + 27250 := by omega
                                                                                              rw [heq]
                                                                                              exact bd_w45 ⟨n - 27250, hr⟩
                                                                                            ·
                                                                                              by_cases h46 : n < 27350
                                                                                              · have hr : n - 27300 < 50 := by omega
                                                                                                have heq : n = (n - 27300) + 27300 := by omega
                                                                                                rw [heq]
                                                                                                exact bd_w46 ⟨n - 27300, hr⟩
                                                                                              ·
                                                                                                by_cases h47 : n < 27400
                                                                                                · have hr : n - 27350 < 50 := by omega
                                                                                                  have heq : n = (n - 27350) + 27350 := by omega
                                                                                                  rw [heq]
                                                                                                  exact bd_w47 ⟨n - 27350, hr⟩
                                                                                                ·
                                                                                                  by_cases h48 : n < 27450
                                                                                                  · have hr : n - 27400 < 50 := by omega
                                                                                                    have heq : n = (n - 27400) + 27400 := by omega
                                                                                                    rw [heq]
                                                                                                    exact bd_w48 ⟨n - 27400, hr⟩
                                                                                                  ·
                                                                                                    by_cases h49 : n < 27500
                                                                                                    · have hr : n - 27450 < 50 := by omega
                                                                                                      have heq : n = (n - 27450) + 27450 := by omega
                                                                                                      rw [heq]
                                                                                                      exact bd_w49 ⟨n - 27450, hr⟩
                                                                                                    ·
                                                                                                      by_cases h50 : n < 27550
                                                                                                      · have hr : n - 27500 < 50 := by omega
                                                                                                        have heq : n = (n - 27500) + 27500 := by omega
                                                                                                        rw [heq]
                                                                                                        exact bd_w50 ⟨n - 27500, hr⟩
                                                                                                      ·
                                                                                                        by_cases h51 : n < 27600
                                                                                                        · have hr : n - 27550 < 50 := by omega
                                                                                                          have heq : n = (n - 27550) + 27550 := by omega
                                                                                                          rw [heq]
                                                                                                          exact bd_w51 ⟨n - 27550, hr⟩
                                                                                                        ·
                                                                                                          by_cases h52 : n < 27650
                                                                                                          · have hr : n - 27600 < 50 := by omega
                                                                                                            have heq : n = (n - 27600) + 27600 := by omega
                                                                                                            rw [heq]
                                                                                                            exact bd_w52 ⟨n - 27600, hr⟩
                                                                                                          ·
                                                                                                            by_cases h53 : n < 27700
                                                                                                            · have hr : n - 27650 < 50 := by omega
                                                                                                              have heq : n = (n - 27650) + 27650 := by omega
                                                                                                              rw [heq]
                                                                                                              exact bd_w53 ⟨n - 27650, hr⟩
                                                                                                            ·
                                                                                                              by_cases h54 : n < 27750
                                                                                                              · have hr : n - 27700 < 50 := by omega
                                                                                                                have heq : n = (n - 27700) + 27700 := by omega
                                                                                                                rw [heq]
                                                                                                                exact bd_w54 ⟨n - 27700, hr⟩
                                                                                                              ·
                                                                                                                by_cases h55 : n < 27800
                                                                                                                · have hr : n - 27750 < 50 := by omega
                                                                                                                  have heq : n = (n - 27750) + 27750 := by omega
                                                                                                                  rw [heq]
                                                                                                                  exact bd_w55 ⟨n - 27750, hr⟩
                                                                                                                ·
                                                                                                                  by_cases h56 : n < 27850
                                                                                                                  · have hr : n - 27800 < 50 := by omega
                                                                                                                    have heq : n = (n - 27800) + 27800 := by omega
                                                                                                                    rw [heq]
                                                                                                                    exact bd_w56 ⟨n - 27800, hr⟩
                                                                                                                  ·
                                                                                                                    by_cases h57 : n < 27900
                                                                                                                    · have hr : n - 27850 < 50 := by omega
                                                                                                                      have heq : n = (n - 27850) + 27850 := by omega
                                                                                                                      rw [heq]
                                                                                                                      exact bd_w57 ⟨n - 27850, hr⟩
                                                                                                                    ·
                                                                                                                      by_cases h58 : n < 27950
                                                                                                                      · have hr : n - 27900 < 50 := by omega
                                                                                                                        have heq : n = (n - 27900) + 27900 := by omega
                                                                                                                        rw [heq]
                                                                                                                        exact bd_w58 ⟨n - 27900, hr⟩
                                                                                                                      ·
                                                                                                                        by_cases h59 : n < 28000
                                                                                                                        · have hr : n - 27950 < 50 := by omega
                                                                                                                          have heq : n = (n - 27950) + 27950 := by omega
                                                                                                                          rw [heq]
                                                                                                                          exact bd_w59 ⟨n - 27950, hr⟩
                                                                                                                        ·
                                                                                                                          by_cases h60 : n < 28050
                                                                                                                          · have hr : n - 28000 < 50 := by omega
                                                                                                                            have heq : n = (n - 28000) + 28000 := by omega
                                                                                                                            rw [heq]
                                                                                                                            exact bd_w60 ⟨n - 28000, hr⟩
                                                                                                                          ·
                                                                                                                            by_cases h61 : n < 28100
                                                                                                                            · have hr : n - 28050 < 50 := by omega
                                                                                                                              have heq : n = (n - 28050) + 28050 := by omega
                                                                                                                              rw [heq]
                                                                                                                              exact bd_w61 ⟨n - 28050, hr⟩
                                                                                                                            ·
                                                                                                                              by_cases h62 : n < 28150
                                                                                                                              · have hr : n - 28100 < 50 := by omega
                                                                                                                                have heq : n = (n - 28100) + 28100 := by omega
                                                                                                                                rw [heq]
                                                                                                                                exact bd_w62 ⟨n - 28100, hr⟩
                                                                                                                              ·
                                                                                                                                by_cases h63 : n < 28200
                                                                                                                                · have hr : n - 28150 < 50 := by omega
                                                                                                                                  have heq : n = (n - 28150) + 28150 := by omega
                                                                                                                                  rw [heq]
                                                                                                                                  exact bd_w63 ⟨n - 28150, hr⟩
                                                                                                                                ·
                                                                                                                                  by_cases h64 : n < 28250
                                                                                                                                  · have hr : n - 28200 < 50 := by omega
                                                                                                                                    have heq : n = (n - 28200) + 28200 := by omega
                                                                                                                                    rw [heq]
                                                                                                                                    exact bd_w64 ⟨n - 28200, hr⟩
                                                                                                                                  ·
                                                                                                                                    by_cases h65 : n < 28300
                                                                                                                                    · have hr : n - 28250 < 50 := by omega
                                                                                                                                      have heq : n = (n - 28250) + 28250 := by omega
                                                                                                                                      rw [heq]
                                                                                                                                      exact bd_w65 ⟨n - 28250, hr⟩
                                                                                                                                    ·
                                                                                                                                      by_cases h66 : n < 28350
                                                                                                                                      · have hr : n - 28300 < 50 := by omega
                                                                                                                                        have heq : n = (n - 28300) + 28300 := by omega
                                                                                                                                        rw [heq]
                                                                                                                                        exact bd_w66 ⟨n - 28300, hr⟩
                                                                                                                                      ·
                                                                                                                                        by_cases h67 : n < 28400
                                                                                                                                        · have hr : n - 28350 < 50 := by omega
                                                                                                                                          have heq : n = (n - 28350) + 28350 := by omega
                                                                                                                                          rw [heq]
                                                                                                                                          exact bd_w67 ⟨n - 28350, hr⟩
                                                                                                                                        ·
                                                                                                                                          by_cases h68 : n < 28450
                                                                                                                                          · have hr : n - 28400 < 50 := by omega
                                                                                                                                            have heq : n = (n - 28400) + 28400 := by omega
                                                                                                                                            rw [heq]
                                                                                                                                            exact bd_w68 ⟨n - 28400, hr⟩
                                                                                                                                          ·
                                                                                                                                            by_cases h69 : n < 28500
                                                                                                                                            · have hr : n - 28450 < 50 := by omega
                                                                                                                                              have heq : n = (n - 28450) + 28450 := by omega
                                                                                                                                              rw [heq]
                                                                                                                                              exact bd_w69 ⟨n - 28450, hr⟩
                                                                                                                                            ·
                                                                                                                                              by_cases h70 : n < 28550
                                                                                                                                              · have hr : n - 28500 < 50 := by omega
                                                                                                                                                have heq : n = (n - 28500) + 28500 := by omega
                                                                                                                                                rw [heq]
                                                                                                                                                exact bd_w70 ⟨n - 28500, hr⟩
                                                                                                                                              ·
                                                                                                                                                by_cases h71 : n < 28600
                                                                                                                                                · have hr : n - 28550 < 50 := by omega
                                                                                                                                                  have heq : n = (n - 28550) + 28550 := by omega
                                                                                                                                                  rw [heq]
                                                                                                                                                  exact bd_w71 ⟨n - 28550, hr⟩
                                                                                                                                                ·
                                                                                                                                                  by_cases h72 : n < 28650
                                                                                                                                                  · have hr : n - 28600 < 50 := by omega
                                                                                                                                                    have heq : n = (n - 28600) + 28600 := by omega
                                                                                                                                                    rw [heq]
                                                                                                                                                    exact bd_w72 ⟨n - 28600, hr⟩
                                                                                                                                                  ·
                                                                                                                                                    by_cases h73 : n < 28700
                                                                                                                                                    · have hr : n - 28650 < 50 := by omega
                                                                                                                                                      have heq : n = (n - 28650) + 28650 := by omega
                                                                                                                                                      rw [heq]
                                                                                                                                                      exact bd_w73 ⟨n - 28650, hr⟩
                                                                                                                                                    ·
                                                                                                                                                      by_cases h74 : n < 28750
                                                                                                                                                      · have hr : n - 28700 < 50 := by omega
                                                                                                                                                        have heq : n = (n - 28700) + 28700 := by omega
                                                                                                                                                        rw [heq]
                                                                                                                                                        exact bd_w74 ⟨n - 28700, hr⟩
                                                                                                                                                      ·
                                                                                                                                                        by_cases h75 : n < 28800
                                                                                                                                                        · have hr : n - 28750 < 50 := by omega
                                                                                                                                                          have heq : n = (n - 28750) + 28750 := by omega
                                                                                                                                                          rw [heq]
                                                                                                                                                          exact bd_w75 ⟨n - 28750, hr⟩
                                                                                                                                                        ·
                                                                                                                                                          by_cases h76 : n < 28850
                                                                                                                                                          · have hr : n - 28800 < 50 := by omega
                                                                                                                                                            have heq : n = (n - 28800) + 28800 := by omega
                                                                                                                                                            rw [heq]
                                                                                                                                                            exact bd_w76 ⟨n - 28800, hr⟩
                                                                                                                                                          ·
                                                                                                                                                            by_cases h77 : n < 28900
                                                                                                                                                            · have hr : n - 28850 < 50 := by omega
                                                                                                                                                              have heq : n = (n - 28850) + 28850 := by omega
                                                                                                                                                              rw [heq]
                                                                                                                                                              exact bd_w77 ⟨n - 28850, hr⟩
                                                                                                                                                            ·
                                                                                                                                                              by_cases h78 : n < 28950
                                                                                                                                                              · have hr : n - 28900 < 50 := by omega
                                                                                                                                                                have heq : n = (n - 28900) + 28900 := by omega
                                                                                                                                                                rw [heq]
                                                                                                                                                                exact bd_w78 ⟨n - 28900, hr⟩
                                                                                                                                                              ·
                                                                                                                                                                by_cases h79 : n < 29000
                                                                                                                                                                · have hr : n - 28950 < 50 := by omega
                                                                                                                                                                  have heq : n = (n - 28950) + 28950 := by omega
                                                                                                                                                                  rw [heq]
                                                                                                                                                                  exact bd_w79 ⟨n - 28950, hr⟩
                                                                                                                                                                ·
                                                                                                                                                                  by_cases h80 : n < 29050
                                                                                                                                                                  · have hr : n - 29000 < 50 := by omega
                                                                                                                                                                    have heq : n = (n - 29000) + 29000 := by omega
                                                                                                                                                                    rw [heq]
                                                                                                                                                                    exact bd_w80 ⟨n - 29000, hr⟩
                                                                                                                                                                  ·
                                                                                                                                                                    by_cases h81 : n < 29100
                                                                                                                                                                    · have hr : n - 29050 < 50 := by omega
                                                                                                                                                                      have heq : n = (n - 29050) + 29050 := by omega
                                                                                                                                                                      rw [heq]
                                                                                                                                                                      exact bd_w81 ⟨n - 29050, hr⟩
                                                                                                                                                                    ·
                                                                                                                                                                      by_cases h82 : n < 29150
                                                                                                                                                                      · have hr : n - 29100 < 50 := by omega
                                                                                                                                                                        have heq : n = (n - 29100) + 29100 := by omega
                                                                                                                                                                        rw [heq]
                                                                                                                                                                        exact bd_w82 ⟨n - 29100, hr⟩
                                                                                                                                                                      ·
                                                                                                                                                                        by_cases h83 : n < 29200
                                                                                                                                                                        · have hr : n - 29150 < 50 := by omega
                                                                                                                                                                          have heq : n = (n - 29150) + 29150 := by omega
                                                                                                                                                                          rw [heq]
                                                                                                                                                                          exact bd_w83 ⟨n - 29150, hr⟩
                                                                                                                                                                        ·
                                                                                                                                                                          by_cases h84 : n < 29250
                                                                                                                                                                          · have hr : n - 29200 < 50 := by omega
                                                                                                                                                                            have heq : n = (n - 29200) + 29200 := by omega
                                                                                                                                                                            rw [heq]
                                                                                                                                                                            exact bd_w84 ⟨n - 29200, hr⟩
                                                                                                                                                                          ·
                                                                                                                                                                            by_cases h85 : n < 29300
                                                                                                                                                                            · have hr : n - 29250 < 50 := by omega
                                                                                                                                                                              have heq : n = (n - 29250) + 29250 := by omega
                                                                                                                                                                              rw [heq]
                                                                                                                                                                              exact bd_w85 ⟨n - 29250, hr⟩
                                                                                                                                                                            ·
                                                                                                                                                                              by_cases h86 : n < 29350
                                                                                                                                                                              · have hr : n - 29300 < 50 := by omega
                                                                                                                                                                                have heq : n = (n - 29300) + 29300 := by omega
                                                                                                                                                                                rw [heq]
                                                                                                                                                                                exact bd_w86 ⟨n - 29300, hr⟩
                                                                                                                                                                              ·
                                                                                                                                                                                by_cases h87 : n < 29400
                                                                                                                                                                                · have hr : n - 29350 < 50 := by omega
                                                                                                                                                                                  have heq : n = (n - 29350) + 29350 := by omega
                                                                                                                                                                                  rw [heq]
                                                                                                                                                                                  exact bd_w87 ⟨n - 29350, hr⟩
                                                                                                                                                                                ·
                                                                                                                                                                                  by_cases h88 : n < 29450
                                                                                                                                                                                  · have hr : n - 29400 < 50 := by omega
                                                                                                                                                                                    have heq : n = (n - 29400) + 29400 := by omega
                                                                                                                                                                                    rw [heq]
                                                                                                                                                                                    exact bd_w88 ⟨n - 29400, hr⟩
                                                                                                                                                                                  ·
                                                                                                                                                                                    by_cases h89 : n < 29500
                                                                                                                                                                                    · have hr : n - 29450 < 50 := by omega
                                                                                                                                                                                      have heq : n = (n - 29450) + 29450 := by omega
                                                                                                                                                                                      rw [heq]
                                                                                                                                                                                      exact bd_w89 ⟨n - 29450, hr⟩
                                                                                                                                                                                    ·
                                                                                                                                                                                      by_cases h90 : n < 29550
                                                                                                                                                                                      · have hr : n - 29500 < 50 := by omega
                                                                                                                                                                                        have heq : n = (n - 29500) + 29500 := by omega
                                                                                                                                                                                        rw [heq]
                                                                                                                                                                                        exact bd_w90 ⟨n - 29500, hr⟩
                                                                                                                                                                                      ·
                                                                                                                                                                                        by_cases h91 : n < 29600
                                                                                                                                                                                        · have hr : n - 29550 < 50 := by omega
                                                                                                                                                                                          have heq : n = (n - 29550) + 29550 := by omega
                                                                                                                                                                                          rw [heq]
                                                                                                                                                                                          exact bd_w91 ⟨n - 29550, hr⟩
                                                                                                                                                                                        ·
                                                                                                                                                                                          by_cases h92 : n < 29650
                                                                                                                                                                                          · have hr : n - 29600 < 50 := by omega
                                                                                                                                                                                            have heq : n = (n - 29600) + 29600 := by omega
                                                                                                                                                                                            rw [heq]
                                                                                                                                                                                            exact bd_w92 ⟨n - 29600, hr⟩
                                                                                                                                                                                          ·
                                                                                                                                                                                            by_cases h93 : n < 29700
                                                                                                                                                                                            · have hr : n - 29650 < 50 := by omega
                                                                                                                                                                                              have heq : n = (n - 29650) + 29650 := by omega
                                                                                                                                                                                              rw [heq]
                                                                                                                                                                                              exact bd_w93 ⟨n - 29650, hr⟩
                                                                                                                                                                                            ·
                                                                                                                                                                                              by_cases h94 : n < 29750
                                                                                                                                                                                              · have hr : n - 29700 < 50 := by omega
                                                                                                                                                                                                have heq : n = (n - 29700) + 29700 := by omega
                                                                                                                                                                                                rw [heq]
                                                                                                                                                                                                exact bd_w94 ⟨n - 29700, hr⟩
                                                                                                                                                                                              ·
                                                                                                                                                                                                by_cases h95 : n < 29800
                                                                                                                                                                                                · have hr : n - 29750 < 50 := by omega
                                                                                                                                                                                                  have heq : n = (n - 29750) + 29750 := by omega
                                                                                                                                                                                                  rw [heq]
                                                                                                                                                                                                  exact bd_w95 ⟨n - 29750, hr⟩
                                                                                                                                                                                                ·
                                                                                                                                                                                                  by_cases h96 : n < 29850
                                                                                                                                                                                                  · have hr : n - 29800 < 50 := by omega
                                                                                                                                                                                                    have heq : n = (n - 29800) + 29800 := by omega
                                                                                                                                                                                                    rw [heq]
                                                                                                                                                                                                    exact bd_w96 ⟨n - 29800, hr⟩
                                                                                                                                                                                                  ·
                                                                                                                                                                                                    by_cases h97 : n < 29900
                                                                                                                                                                                                    · have hr : n - 29850 < 50 := by omega
                                                                                                                                                                                                      have heq : n = (n - 29850) + 29850 := by omega
                                                                                                                                                                                                      rw [heq]
                                                                                                                                                                                                      exact bd_w97 ⟨n - 29850, hr⟩
                                                                                                                                                                                                    ·
                                                                                                                                                                                                      by_cases h98 : n < 29950
                                                                                                                                                                                                      · have hr : n - 29900 < 50 := by omega
                                                                                                                                                                                                        have heq : n = (n - 29900) + 29900 := by omega
                                                                                                                                                                                                        rw [heq]
                                                                                                                                                                                                        exact bd_w98 ⟨n - 29900, hr⟩
                                                                                                                                                                                                      ·
                                                                                                                                                                                                        have hr : n - 29950 < 50 := by omega
                                                                                                                                                                                                        have heq : n = (n - 29950) + 29950 := by omega
                                                                                                                                                                                                        rw [heq]
                                                                                                                                                                                                        exact bd_w99 ⟨n - 29950, hr⟩

end IntMul.Kappa.R8.Bit.Oppbank.CentBound5


