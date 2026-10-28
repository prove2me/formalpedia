-- Prove2me | Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankCentBound4
-- name    : IntMul_Kappa_R8_Data_BitOppbankCentBound4
-- status  : Definition
-- author  : @Ethan Cheung Wang
-- created : 2026-10-28T19:49:53.621791+00:00
-- url     : https://prove2.me/theorems/99d41503-5153-48d1-9c6b-ecf5bbb7ca5e
-- title:
--   HasCentre certificates dens nodes [20000,25000)
-- statement:
--   # Densified centre certificates, pack 4
--
--   For every densified node index $n$ with $20000\le n<25000$,
--   $$
--   \mathrm{centredStar}(\mathrm{densSupG}\,n,\mathrm{centF}\,n)=\mathsf{true},\quad
--   \mathrm{centF}\,n<23,\quad
--   \mathrm{densSupG}\,n < 2^{1771}.
--   $$
--   Proved by decide on Fin 50 windows (no native_decide).
-- source:
--   R8 BitOppbank AllDensCentred; jfstack_23 densified supports

-- CentBound pack 4: densified HasCentre certificates on n ∈ [20000, 25000)
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

namespace IntMul.Kappa.R8.Bit.Oppbank.CentBound4

private theorem cs_w0 : ∀ n : Fin 50, centredStar (densSupG (n.val + 20000)) (centF (n.val + 20000)) = true := by decide
private theorem cl_w0 : ∀ n : Fin 50, centF (n.val + 20000) < 23 := by decide
private theorem bd_w0 : ∀ n : Fin 50, densSupG (n.val + 20000) < 2 ^ 1771 := by decide
private theorem cs_w1 : ∀ n : Fin 50, centredStar (densSupG (n.val + 20050)) (centF (n.val + 20050)) = true := by decide
private theorem cl_w1 : ∀ n : Fin 50, centF (n.val + 20050) < 23 := by decide
private theorem bd_w1 : ∀ n : Fin 50, densSupG (n.val + 20050) < 2 ^ 1771 := by decide
private theorem cs_w2 : ∀ n : Fin 50, centredStar (densSupG (n.val + 20100)) (centF (n.val + 20100)) = true := by decide
private theorem cl_w2 : ∀ n : Fin 50, centF (n.val + 20100) < 23 := by decide
private theorem bd_w2 : ∀ n : Fin 50, densSupG (n.val + 20100) < 2 ^ 1771 := by decide
private theorem cs_w3 : ∀ n : Fin 50, centredStar (densSupG (n.val + 20150)) (centF (n.val + 20150)) = true := by decide
private theorem cl_w3 : ∀ n : Fin 50, centF (n.val + 20150) < 23 := by decide
private theorem bd_w3 : ∀ n : Fin 50, densSupG (n.val + 20150) < 2 ^ 1771 := by decide
private theorem cs_w4 : ∀ n : Fin 50, centredStar (densSupG (n.val + 20200)) (centF (n.val + 20200)) = true := by decide
private theorem cl_w4 : ∀ n : Fin 50, centF (n.val + 20200) < 23 := by decide
private theorem bd_w4 : ∀ n : Fin 50, densSupG (n.val + 20200) < 2 ^ 1771 := by decide
private theorem cs_w5 : ∀ n : Fin 50, centredStar (densSupG (n.val + 20250)) (centF (n.val + 20250)) = true := by decide
private theorem cl_w5 : ∀ n : Fin 50, centF (n.val + 20250) < 23 := by decide
private theorem bd_w5 : ∀ n : Fin 50, densSupG (n.val + 20250) < 2 ^ 1771 := by decide
private theorem cs_w6 : ∀ n : Fin 50, centredStar (densSupG (n.val + 20300)) (centF (n.val + 20300)) = true := by decide
private theorem cl_w6 : ∀ n : Fin 50, centF (n.val + 20300) < 23 := by decide
private theorem bd_w6 : ∀ n : Fin 50, densSupG (n.val + 20300) < 2 ^ 1771 := by decide
private theorem cs_w7 : ∀ n : Fin 50, centredStar (densSupG (n.val + 20350)) (centF (n.val + 20350)) = true := by decide
private theorem cl_w7 : ∀ n : Fin 50, centF (n.val + 20350) < 23 := by decide
private theorem bd_w7 : ∀ n : Fin 50, densSupG (n.val + 20350) < 2 ^ 1771 := by decide
private theorem cs_w8 : ∀ n : Fin 50, centredStar (densSupG (n.val + 20400)) (centF (n.val + 20400)) = true := by decide
private theorem cl_w8 : ∀ n : Fin 50, centF (n.val + 20400) < 23 := by decide
private theorem bd_w8 : ∀ n : Fin 50, densSupG (n.val + 20400) < 2 ^ 1771 := by decide
private theorem cs_w9 : ∀ n : Fin 50, centredStar (densSupG (n.val + 20450)) (centF (n.val + 20450)) = true := by decide
private theorem cl_w9 : ∀ n : Fin 50, centF (n.val + 20450) < 23 := by decide
private theorem bd_w9 : ∀ n : Fin 50, densSupG (n.val + 20450) < 2 ^ 1771 := by decide
private theorem cs_w10 : ∀ n : Fin 50, centredStar (densSupG (n.val + 20500)) (centF (n.val + 20500)) = true := by decide
private theorem cl_w10 : ∀ n : Fin 50, centF (n.val + 20500) < 23 := by decide
private theorem bd_w10 : ∀ n : Fin 50, densSupG (n.val + 20500) < 2 ^ 1771 := by decide
private theorem cs_w11 : ∀ n : Fin 50, centredStar (densSupG (n.val + 20550)) (centF (n.val + 20550)) = true := by decide
private theorem cl_w11 : ∀ n : Fin 50, centF (n.val + 20550) < 23 := by decide
private theorem bd_w11 : ∀ n : Fin 50, densSupG (n.val + 20550) < 2 ^ 1771 := by decide
private theorem cs_w12 : ∀ n : Fin 50, centredStar (densSupG (n.val + 20600)) (centF (n.val + 20600)) = true := by decide
private theorem cl_w12 : ∀ n : Fin 50, centF (n.val + 20600) < 23 := by decide
private theorem bd_w12 : ∀ n : Fin 50, densSupG (n.val + 20600) < 2 ^ 1771 := by decide
private theorem cs_w13 : ∀ n : Fin 50, centredStar (densSupG (n.val + 20650)) (centF (n.val + 20650)) = true := by decide
private theorem cl_w13 : ∀ n : Fin 50, centF (n.val + 20650) < 23 := by decide
private theorem bd_w13 : ∀ n : Fin 50, densSupG (n.val + 20650) < 2 ^ 1771 := by decide
private theorem cs_w14 : ∀ n : Fin 50, centredStar (densSupG (n.val + 20700)) (centF (n.val + 20700)) = true := by decide
private theorem cl_w14 : ∀ n : Fin 50, centF (n.val + 20700) < 23 := by decide
private theorem bd_w14 : ∀ n : Fin 50, densSupG (n.val + 20700) < 2 ^ 1771 := by decide
private theorem cs_w15 : ∀ n : Fin 50, centredStar (densSupG (n.val + 20750)) (centF (n.val + 20750)) = true := by decide
private theorem cl_w15 : ∀ n : Fin 50, centF (n.val + 20750) < 23 := by decide
private theorem bd_w15 : ∀ n : Fin 50, densSupG (n.val + 20750) < 2 ^ 1771 := by decide
private theorem cs_w16 : ∀ n : Fin 50, centredStar (densSupG (n.val + 20800)) (centF (n.val + 20800)) = true := by decide
private theorem cl_w16 : ∀ n : Fin 50, centF (n.val + 20800) < 23 := by decide
private theorem bd_w16 : ∀ n : Fin 50, densSupG (n.val + 20800) < 2 ^ 1771 := by decide
private theorem cs_w17 : ∀ n : Fin 50, centredStar (densSupG (n.val + 20850)) (centF (n.val + 20850)) = true := by decide
private theorem cl_w17 : ∀ n : Fin 50, centF (n.val + 20850) < 23 := by decide
private theorem bd_w17 : ∀ n : Fin 50, densSupG (n.val + 20850) < 2 ^ 1771 := by decide
private theorem cs_w18 : ∀ n : Fin 50, centredStar (densSupG (n.val + 20900)) (centF (n.val + 20900)) = true := by decide
private theorem cl_w18 : ∀ n : Fin 50, centF (n.val + 20900) < 23 := by decide
private theorem bd_w18 : ∀ n : Fin 50, densSupG (n.val + 20900) < 2 ^ 1771 := by decide
private theorem cs_w19 : ∀ n : Fin 50, centredStar (densSupG (n.val + 20950)) (centF (n.val + 20950)) = true := by decide
private theorem cl_w19 : ∀ n : Fin 50, centF (n.val + 20950) < 23 := by decide
private theorem bd_w19 : ∀ n : Fin 50, densSupG (n.val + 20950) < 2 ^ 1771 := by decide
private theorem cs_w20 : ∀ n : Fin 50, centredStar (densSupG (n.val + 21000)) (centF (n.val + 21000)) = true := by decide
private theorem cl_w20 : ∀ n : Fin 50, centF (n.val + 21000) < 23 := by decide
private theorem bd_w20 : ∀ n : Fin 50, densSupG (n.val + 21000) < 2 ^ 1771 := by decide
private theorem cs_w21 : ∀ n : Fin 50, centredStar (densSupG (n.val + 21050)) (centF (n.val + 21050)) = true := by decide
private theorem cl_w21 : ∀ n : Fin 50, centF (n.val + 21050) < 23 := by decide
private theorem bd_w21 : ∀ n : Fin 50, densSupG (n.val + 21050) < 2 ^ 1771 := by decide
private theorem cs_w22 : ∀ n : Fin 50, centredStar (densSupG (n.val + 21100)) (centF (n.val + 21100)) = true := by decide
private theorem cl_w22 : ∀ n : Fin 50, centF (n.val + 21100) < 23 := by decide
private theorem bd_w22 : ∀ n : Fin 50, densSupG (n.val + 21100) < 2 ^ 1771 := by decide
private theorem cs_w23 : ∀ n : Fin 50, centredStar (densSupG (n.val + 21150)) (centF (n.val + 21150)) = true := by decide
private theorem cl_w23 : ∀ n : Fin 50, centF (n.val + 21150) < 23 := by decide
private theorem bd_w23 : ∀ n : Fin 50, densSupG (n.val + 21150) < 2 ^ 1771 := by decide
private theorem cs_w24 : ∀ n : Fin 50, centredStar (densSupG (n.val + 21200)) (centF (n.val + 21200)) = true := by decide
private theorem cl_w24 : ∀ n : Fin 50, centF (n.val + 21200) < 23 := by decide
private theorem bd_w24 : ∀ n : Fin 50, densSupG (n.val + 21200) < 2 ^ 1771 := by decide
private theorem cs_w25 : ∀ n : Fin 50, centredStar (densSupG (n.val + 21250)) (centF (n.val + 21250)) = true := by decide
private theorem cl_w25 : ∀ n : Fin 50, centF (n.val + 21250) < 23 := by decide
private theorem bd_w25 : ∀ n : Fin 50, densSupG (n.val + 21250) < 2 ^ 1771 := by decide
private theorem cs_w26 : ∀ n : Fin 50, centredStar (densSupG (n.val + 21300)) (centF (n.val + 21300)) = true := by decide
private theorem cl_w26 : ∀ n : Fin 50, centF (n.val + 21300) < 23 := by decide
private theorem bd_w26 : ∀ n : Fin 50, densSupG (n.val + 21300) < 2 ^ 1771 := by decide
private theorem cs_w27 : ∀ n : Fin 50, centredStar (densSupG (n.val + 21350)) (centF (n.val + 21350)) = true := by decide
private theorem cl_w27 : ∀ n : Fin 50, centF (n.val + 21350) < 23 := by decide
private theorem bd_w27 : ∀ n : Fin 50, densSupG (n.val + 21350) < 2 ^ 1771 := by decide
private theorem cs_w28 : ∀ n : Fin 50, centredStar (densSupG (n.val + 21400)) (centF (n.val + 21400)) = true := by decide
private theorem cl_w28 : ∀ n : Fin 50, centF (n.val + 21400) < 23 := by decide
private theorem bd_w28 : ∀ n : Fin 50, densSupG (n.val + 21400) < 2 ^ 1771 := by decide
private theorem cs_w29 : ∀ n : Fin 50, centredStar (densSupG (n.val + 21450)) (centF (n.val + 21450)) = true := by decide
private theorem cl_w29 : ∀ n : Fin 50, centF (n.val + 21450) < 23 := by decide
private theorem bd_w29 : ∀ n : Fin 50, densSupG (n.val + 21450) < 2 ^ 1771 := by decide
private theorem cs_w30 : ∀ n : Fin 50, centredStar (densSupG (n.val + 21500)) (centF (n.val + 21500)) = true := by decide
private theorem cl_w30 : ∀ n : Fin 50, centF (n.val + 21500) < 23 := by decide
private theorem bd_w30 : ∀ n : Fin 50, densSupG (n.val + 21500) < 2 ^ 1771 := by decide
private theorem cs_w31 : ∀ n : Fin 50, centredStar (densSupG (n.val + 21550)) (centF (n.val + 21550)) = true := by decide
private theorem cl_w31 : ∀ n : Fin 50, centF (n.val + 21550) < 23 := by decide
private theorem bd_w31 : ∀ n : Fin 50, densSupG (n.val + 21550) < 2 ^ 1771 := by decide
private theorem cs_w32 : ∀ n : Fin 50, centredStar (densSupG (n.val + 21600)) (centF (n.val + 21600)) = true := by decide
private theorem cl_w32 : ∀ n : Fin 50, centF (n.val + 21600) < 23 := by decide
private theorem bd_w32 : ∀ n : Fin 50, densSupG (n.val + 21600) < 2 ^ 1771 := by decide
private theorem cs_w33 : ∀ n : Fin 50, centredStar (densSupG (n.val + 21650)) (centF (n.val + 21650)) = true := by decide
private theorem cl_w33 : ∀ n : Fin 50, centF (n.val + 21650) < 23 := by decide
private theorem bd_w33 : ∀ n : Fin 50, densSupG (n.val + 21650) < 2 ^ 1771 := by decide
private theorem cs_w34 : ∀ n : Fin 50, centredStar (densSupG (n.val + 21700)) (centF (n.val + 21700)) = true := by decide
private theorem cl_w34 : ∀ n : Fin 50, centF (n.val + 21700) < 23 := by decide
private theorem bd_w34 : ∀ n : Fin 50, densSupG (n.val + 21700) < 2 ^ 1771 := by decide
private theorem cs_w35 : ∀ n : Fin 50, centredStar (densSupG (n.val + 21750)) (centF (n.val + 21750)) = true := by decide
private theorem cl_w35 : ∀ n : Fin 50, centF (n.val + 21750) < 23 := by decide
private theorem bd_w35 : ∀ n : Fin 50, densSupG (n.val + 21750) < 2 ^ 1771 := by decide
private theorem cs_w36 : ∀ n : Fin 50, centredStar (densSupG (n.val + 21800)) (centF (n.val + 21800)) = true := by decide
private theorem cl_w36 : ∀ n : Fin 50, centF (n.val + 21800) < 23 := by decide
private theorem bd_w36 : ∀ n : Fin 50, densSupG (n.val + 21800) < 2 ^ 1771 := by decide
private theorem cs_w37 : ∀ n : Fin 50, centredStar (densSupG (n.val + 21850)) (centF (n.val + 21850)) = true := by decide
private theorem cl_w37 : ∀ n : Fin 50, centF (n.val + 21850) < 23 := by decide
private theorem bd_w37 : ∀ n : Fin 50, densSupG (n.val + 21850) < 2 ^ 1771 := by decide
private theorem cs_w38 : ∀ n : Fin 50, centredStar (densSupG (n.val + 21900)) (centF (n.val + 21900)) = true := by decide
private theorem cl_w38 : ∀ n : Fin 50, centF (n.val + 21900) < 23 := by decide
private theorem bd_w38 : ∀ n : Fin 50, densSupG (n.val + 21900) < 2 ^ 1771 := by decide
private theorem cs_w39 : ∀ n : Fin 50, centredStar (densSupG (n.val + 21950)) (centF (n.val + 21950)) = true := by decide
private theorem cl_w39 : ∀ n : Fin 50, centF (n.val + 21950) < 23 := by decide
private theorem bd_w39 : ∀ n : Fin 50, densSupG (n.val + 21950) < 2 ^ 1771 := by decide
private theorem cs_w40 : ∀ n : Fin 50, centredStar (densSupG (n.val + 22000)) (centF (n.val + 22000)) = true := by decide
private theorem cl_w40 : ∀ n : Fin 50, centF (n.val + 22000) < 23 := by decide
private theorem bd_w40 : ∀ n : Fin 50, densSupG (n.val + 22000) < 2 ^ 1771 := by decide
private theorem cs_w41 : ∀ n : Fin 50, centredStar (densSupG (n.val + 22050)) (centF (n.val + 22050)) = true := by decide
private theorem cl_w41 : ∀ n : Fin 50, centF (n.val + 22050) < 23 := by decide
private theorem bd_w41 : ∀ n : Fin 50, densSupG (n.val + 22050) < 2 ^ 1771 := by decide
private theorem cs_w42 : ∀ n : Fin 50, centredStar (densSupG (n.val + 22100)) (centF (n.val + 22100)) = true := by decide
private theorem cl_w42 : ∀ n : Fin 50, centF (n.val + 22100) < 23 := by decide
private theorem bd_w42 : ∀ n : Fin 50, densSupG (n.val + 22100) < 2 ^ 1771 := by decide
private theorem cs_w43 : ∀ n : Fin 50, centredStar (densSupG (n.val + 22150)) (centF (n.val + 22150)) = true := by decide
private theorem cl_w43 : ∀ n : Fin 50, centF (n.val + 22150) < 23 := by decide
private theorem bd_w43 : ∀ n : Fin 50, densSupG (n.val + 22150) < 2 ^ 1771 := by decide
private theorem cs_w44 : ∀ n : Fin 50, centredStar (densSupG (n.val + 22200)) (centF (n.val + 22200)) = true := by decide
private theorem cl_w44 : ∀ n : Fin 50, centF (n.val + 22200) < 23 := by decide
private theorem bd_w44 : ∀ n : Fin 50, densSupG (n.val + 22200) < 2 ^ 1771 := by decide
private theorem cs_w45 : ∀ n : Fin 50, centredStar (densSupG (n.val + 22250)) (centF (n.val + 22250)) = true := by decide
private theorem cl_w45 : ∀ n : Fin 50, centF (n.val + 22250) < 23 := by decide
private theorem bd_w45 : ∀ n : Fin 50, densSupG (n.val + 22250) < 2 ^ 1771 := by decide
private theorem cs_w46 : ∀ n : Fin 50, centredStar (densSupG (n.val + 22300)) (centF (n.val + 22300)) = true := by decide
private theorem cl_w46 : ∀ n : Fin 50, centF (n.val + 22300) < 23 := by decide
private theorem bd_w46 : ∀ n : Fin 50, densSupG (n.val + 22300) < 2 ^ 1771 := by decide
private theorem cs_w47 : ∀ n : Fin 50, centredStar (densSupG (n.val + 22350)) (centF (n.val + 22350)) = true := by decide
private theorem cl_w47 : ∀ n : Fin 50, centF (n.val + 22350) < 23 := by decide
private theorem bd_w47 : ∀ n : Fin 50, densSupG (n.val + 22350) < 2 ^ 1771 := by decide
private theorem cs_w48 : ∀ n : Fin 50, centredStar (densSupG (n.val + 22400)) (centF (n.val + 22400)) = true := by decide
private theorem cl_w48 : ∀ n : Fin 50, centF (n.val + 22400) < 23 := by decide
private theorem bd_w48 : ∀ n : Fin 50, densSupG (n.val + 22400) < 2 ^ 1771 := by decide
private theorem cs_w49 : ∀ n : Fin 50, centredStar (densSupG (n.val + 22450)) (centF (n.val + 22450)) = true := by decide
private theorem cl_w49 : ∀ n : Fin 50, centF (n.val + 22450) < 23 := by decide
private theorem bd_w49 : ∀ n : Fin 50, densSupG (n.val + 22450) < 2 ^ 1771 := by decide
private theorem cs_w50 : ∀ n : Fin 50, centredStar (densSupG (n.val + 22500)) (centF (n.val + 22500)) = true := by decide
private theorem cl_w50 : ∀ n : Fin 50, centF (n.val + 22500) < 23 := by decide
private theorem bd_w50 : ∀ n : Fin 50, densSupG (n.val + 22500) < 2 ^ 1771 := by decide
private theorem cs_w51 : ∀ n : Fin 50, centredStar (densSupG (n.val + 22550)) (centF (n.val + 22550)) = true := by decide
private theorem cl_w51 : ∀ n : Fin 50, centF (n.val + 22550) < 23 := by decide
private theorem bd_w51 : ∀ n : Fin 50, densSupG (n.val + 22550) < 2 ^ 1771 := by decide
private theorem cs_w52 : ∀ n : Fin 50, centredStar (densSupG (n.val + 22600)) (centF (n.val + 22600)) = true := by decide
private theorem cl_w52 : ∀ n : Fin 50, centF (n.val + 22600) < 23 := by decide
private theorem bd_w52 : ∀ n : Fin 50, densSupG (n.val + 22600) < 2 ^ 1771 := by decide
private theorem cs_w53 : ∀ n : Fin 50, centredStar (densSupG (n.val + 22650)) (centF (n.val + 22650)) = true := by decide
private theorem cl_w53 : ∀ n : Fin 50, centF (n.val + 22650) < 23 := by decide
private theorem bd_w53 : ∀ n : Fin 50, densSupG (n.val + 22650) < 2 ^ 1771 := by decide
private theorem cs_w54 : ∀ n : Fin 50, centredStar (densSupG (n.val + 22700)) (centF (n.val + 22700)) = true := by decide
private theorem cl_w54 : ∀ n : Fin 50, centF (n.val + 22700) < 23 := by decide
private theorem bd_w54 : ∀ n : Fin 50, densSupG (n.val + 22700) < 2 ^ 1771 := by decide
private theorem cs_w55 : ∀ n : Fin 50, centredStar (densSupG (n.val + 22750)) (centF (n.val + 22750)) = true := by decide
private theorem cl_w55 : ∀ n : Fin 50, centF (n.val + 22750) < 23 := by decide
private theorem bd_w55 : ∀ n : Fin 50, densSupG (n.val + 22750) < 2 ^ 1771 := by decide
private theorem cs_w56 : ∀ n : Fin 50, centredStar (densSupG (n.val + 22800)) (centF (n.val + 22800)) = true := by decide
private theorem cl_w56 : ∀ n : Fin 50, centF (n.val + 22800) < 23 := by decide
private theorem bd_w56 : ∀ n : Fin 50, densSupG (n.val + 22800) < 2 ^ 1771 := by decide
private theorem cs_w57 : ∀ n : Fin 50, centredStar (densSupG (n.val + 22850)) (centF (n.val + 22850)) = true := by decide
private theorem cl_w57 : ∀ n : Fin 50, centF (n.val + 22850) < 23 := by decide
private theorem bd_w57 : ∀ n : Fin 50, densSupG (n.val + 22850) < 2 ^ 1771 := by decide
private theorem cs_w58 : ∀ n : Fin 50, centredStar (densSupG (n.val + 22900)) (centF (n.val + 22900)) = true := by decide
private theorem cl_w58 : ∀ n : Fin 50, centF (n.val + 22900) < 23 := by decide
private theorem bd_w58 : ∀ n : Fin 50, densSupG (n.val + 22900) < 2 ^ 1771 := by decide
private theorem cs_w59 : ∀ n : Fin 50, centredStar (densSupG (n.val + 22950)) (centF (n.val + 22950)) = true := by decide
private theorem cl_w59 : ∀ n : Fin 50, centF (n.val + 22950) < 23 := by decide
private theorem bd_w59 : ∀ n : Fin 50, densSupG (n.val + 22950) < 2 ^ 1771 := by decide
private theorem cs_w60 : ∀ n : Fin 50, centredStar (densSupG (n.val + 23000)) (centF (n.val + 23000)) = true := by decide
private theorem cl_w60 : ∀ n : Fin 50, centF (n.val + 23000) < 23 := by decide
private theorem bd_w60 : ∀ n : Fin 50, densSupG (n.val + 23000) < 2 ^ 1771 := by decide
private theorem cs_w61 : ∀ n : Fin 50, centredStar (densSupG (n.val + 23050)) (centF (n.val + 23050)) = true := by decide
private theorem cl_w61 : ∀ n : Fin 50, centF (n.val + 23050) < 23 := by decide
private theorem bd_w61 : ∀ n : Fin 50, densSupG (n.val + 23050) < 2 ^ 1771 := by decide
private theorem cs_w62 : ∀ n : Fin 50, centredStar (densSupG (n.val + 23100)) (centF (n.val + 23100)) = true := by decide
private theorem cl_w62 : ∀ n : Fin 50, centF (n.val + 23100) < 23 := by decide
private theorem bd_w62 : ∀ n : Fin 50, densSupG (n.val + 23100) < 2 ^ 1771 := by decide
private theorem cs_w63 : ∀ n : Fin 50, centredStar (densSupG (n.val + 23150)) (centF (n.val + 23150)) = true := by decide
private theorem cl_w63 : ∀ n : Fin 50, centF (n.val + 23150) < 23 := by decide
private theorem bd_w63 : ∀ n : Fin 50, densSupG (n.val + 23150) < 2 ^ 1771 := by decide
private theorem cs_w64 : ∀ n : Fin 50, centredStar (densSupG (n.val + 23200)) (centF (n.val + 23200)) = true := by decide
private theorem cl_w64 : ∀ n : Fin 50, centF (n.val + 23200) < 23 := by decide
private theorem bd_w64 : ∀ n : Fin 50, densSupG (n.val + 23200) < 2 ^ 1771 := by decide
private theorem cs_w65 : ∀ n : Fin 50, centredStar (densSupG (n.val + 23250)) (centF (n.val + 23250)) = true := by decide
private theorem cl_w65 : ∀ n : Fin 50, centF (n.val + 23250) < 23 := by decide
private theorem bd_w65 : ∀ n : Fin 50, densSupG (n.val + 23250) < 2 ^ 1771 := by decide
private theorem cs_w66 : ∀ n : Fin 50, centredStar (densSupG (n.val + 23300)) (centF (n.val + 23300)) = true := by decide
private theorem cl_w66 : ∀ n : Fin 50, centF (n.val + 23300) < 23 := by decide
private theorem bd_w66 : ∀ n : Fin 50, densSupG (n.val + 23300) < 2 ^ 1771 := by decide
private theorem cs_w67 : ∀ n : Fin 50, centredStar (densSupG (n.val + 23350)) (centF (n.val + 23350)) = true := by decide
private theorem cl_w67 : ∀ n : Fin 50, centF (n.val + 23350) < 23 := by decide
private theorem bd_w67 : ∀ n : Fin 50, densSupG (n.val + 23350) < 2 ^ 1771 := by decide
private theorem cs_w68 : ∀ n : Fin 50, centredStar (densSupG (n.val + 23400)) (centF (n.val + 23400)) = true := by decide
private theorem cl_w68 : ∀ n : Fin 50, centF (n.val + 23400) < 23 := by decide
private theorem bd_w68 : ∀ n : Fin 50, densSupG (n.val + 23400) < 2 ^ 1771 := by decide
private theorem cs_w69 : ∀ n : Fin 50, centredStar (densSupG (n.val + 23450)) (centF (n.val + 23450)) = true := by decide
private theorem cl_w69 : ∀ n : Fin 50, centF (n.val + 23450) < 23 := by decide
private theorem bd_w69 : ∀ n : Fin 50, densSupG (n.val + 23450) < 2 ^ 1771 := by decide
private theorem cs_w70 : ∀ n : Fin 50, centredStar (densSupG (n.val + 23500)) (centF (n.val + 23500)) = true := by decide
private theorem cl_w70 : ∀ n : Fin 50, centF (n.val + 23500) < 23 := by decide
private theorem bd_w70 : ∀ n : Fin 50, densSupG (n.val + 23500) < 2 ^ 1771 := by decide
private theorem cs_w71 : ∀ n : Fin 50, centredStar (densSupG (n.val + 23550)) (centF (n.val + 23550)) = true := by decide
private theorem cl_w71 : ∀ n : Fin 50, centF (n.val + 23550) < 23 := by decide
private theorem bd_w71 : ∀ n : Fin 50, densSupG (n.val + 23550) < 2 ^ 1771 := by decide
private theorem cs_w72 : ∀ n : Fin 50, centredStar (densSupG (n.val + 23600)) (centF (n.val + 23600)) = true := by decide
private theorem cl_w72 : ∀ n : Fin 50, centF (n.val + 23600) < 23 := by decide
private theorem bd_w72 : ∀ n : Fin 50, densSupG (n.val + 23600) < 2 ^ 1771 := by decide
private theorem cs_w73 : ∀ n : Fin 50, centredStar (densSupG (n.val + 23650)) (centF (n.val + 23650)) = true := by decide
private theorem cl_w73 : ∀ n : Fin 50, centF (n.val + 23650) < 23 := by decide
private theorem bd_w73 : ∀ n : Fin 50, densSupG (n.val + 23650) < 2 ^ 1771 := by decide
private theorem cs_w74 : ∀ n : Fin 50, centredStar (densSupG (n.val + 23700)) (centF (n.val + 23700)) = true := by decide
private theorem cl_w74 : ∀ n : Fin 50, centF (n.val + 23700) < 23 := by decide
private theorem bd_w74 : ∀ n : Fin 50, densSupG (n.val + 23700) < 2 ^ 1771 := by decide
private theorem cs_w75 : ∀ n : Fin 50, centredStar (densSupG (n.val + 23750)) (centF (n.val + 23750)) = true := by decide
private theorem cl_w75 : ∀ n : Fin 50, centF (n.val + 23750) < 23 := by decide
private theorem bd_w75 : ∀ n : Fin 50, densSupG (n.val + 23750) < 2 ^ 1771 := by decide
private theorem cs_w76 : ∀ n : Fin 50, centredStar (densSupG (n.val + 23800)) (centF (n.val + 23800)) = true := by decide
private theorem cl_w76 : ∀ n : Fin 50, centF (n.val + 23800) < 23 := by decide
private theorem bd_w76 : ∀ n : Fin 50, densSupG (n.val + 23800) < 2 ^ 1771 := by decide
private theorem cs_w77 : ∀ n : Fin 50, centredStar (densSupG (n.val + 23850)) (centF (n.val + 23850)) = true := by decide
private theorem cl_w77 : ∀ n : Fin 50, centF (n.val + 23850) < 23 := by decide
private theorem bd_w77 : ∀ n : Fin 50, densSupG (n.val + 23850) < 2 ^ 1771 := by decide
private theorem cs_w78 : ∀ n : Fin 50, centredStar (densSupG (n.val + 23900)) (centF (n.val + 23900)) = true := by decide
private theorem cl_w78 : ∀ n : Fin 50, centF (n.val + 23900) < 23 := by decide
private theorem bd_w78 : ∀ n : Fin 50, densSupG (n.val + 23900) < 2 ^ 1771 := by decide
private theorem cs_w79 : ∀ n : Fin 50, centredStar (densSupG (n.val + 23950)) (centF (n.val + 23950)) = true := by decide
private theorem cl_w79 : ∀ n : Fin 50, centF (n.val + 23950) < 23 := by decide
private theorem bd_w79 : ∀ n : Fin 50, densSupG (n.val + 23950) < 2 ^ 1771 := by decide
private theorem cs_w80 : ∀ n : Fin 50, centredStar (densSupG (n.val + 24000)) (centF (n.val + 24000)) = true := by decide
private theorem cl_w80 : ∀ n : Fin 50, centF (n.val + 24000) < 23 := by decide
private theorem bd_w80 : ∀ n : Fin 50, densSupG (n.val + 24000) < 2 ^ 1771 := by decide
private theorem cs_w81 : ∀ n : Fin 50, centredStar (densSupG (n.val + 24050)) (centF (n.val + 24050)) = true := by decide
private theorem cl_w81 : ∀ n : Fin 50, centF (n.val + 24050) < 23 := by decide
private theorem bd_w81 : ∀ n : Fin 50, densSupG (n.val + 24050) < 2 ^ 1771 := by decide
private theorem cs_w82 : ∀ n : Fin 50, centredStar (densSupG (n.val + 24100)) (centF (n.val + 24100)) = true := by decide
private theorem cl_w82 : ∀ n : Fin 50, centF (n.val + 24100) < 23 := by decide
private theorem bd_w82 : ∀ n : Fin 50, densSupG (n.val + 24100) < 2 ^ 1771 := by decide
private theorem cs_w83 : ∀ n : Fin 50, centredStar (densSupG (n.val + 24150)) (centF (n.val + 24150)) = true := by decide
private theorem cl_w83 : ∀ n : Fin 50, centF (n.val + 24150) < 23 := by decide
private theorem bd_w83 : ∀ n : Fin 50, densSupG (n.val + 24150) < 2 ^ 1771 := by decide
private theorem cs_w84 : ∀ n : Fin 50, centredStar (densSupG (n.val + 24200)) (centF (n.val + 24200)) = true := by decide
private theorem cl_w84 : ∀ n : Fin 50, centF (n.val + 24200) < 23 := by decide
private theorem bd_w84 : ∀ n : Fin 50, densSupG (n.val + 24200) < 2 ^ 1771 := by decide
private theorem cs_w85 : ∀ n : Fin 50, centredStar (densSupG (n.val + 24250)) (centF (n.val + 24250)) = true := by decide
private theorem cl_w85 : ∀ n : Fin 50, centF (n.val + 24250) < 23 := by decide
private theorem bd_w85 : ∀ n : Fin 50, densSupG (n.val + 24250) < 2 ^ 1771 := by decide
private theorem cs_w86 : ∀ n : Fin 50, centredStar (densSupG (n.val + 24300)) (centF (n.val + 24300)) = true := by decide
private theorem cl_w86 : ∀ n : Fin 50, centF (n.val + 24300) < 23 := by decide
private theorem bd_w86 : ∀ n : Fin 50, densSupG (n.val + 24300) < 2 ^ 1771 := by decide
private theorem cs_w87 : ∀ n : Fin 50, centredStar (densSupG (n.val + 24350)) (centF (n.val + 24350)) = true := by decide
private theorem cl_w87 : ∀ n : Fin 50, centF (n.val + 24350) < 23 := by decide
private theorem bd_w87 : ∀ n : Fin 50, densSupG (n.val + 24350) < 2 ^ 1771 := by decide
private theorem cs_w88 : ∀ n : Fin 50, centredStar (densSupG (n.val + 24400)) (centF (n.val + 24400)) = true := by decide
private theorem cl_w88 : ∀ n : Fin 50, centF (n.val + 24400) < 23 := by decide
private theorem bd_w88 : ∀ n : Fin 50, densSupG (n.val + 24400) < 2 ^ 1771 := by decide
private theorem cs_w89 : ∀ n : Fin 50, centredStar (densSupG (n.val + 24450)) (centF (n.val + 24450)) = true := by decide
private theorem cl_w89 : ∀ n : Fin 50, centF (n.val + 24450) < 23 := by decide
private theorem bd_w89 : ∀ n : Fin 50, densSupG (n.val + 24450) < 2 ^ 1771 := by decide
private theorem cs_w90 : ∀ n : Fin 50, centredStar (densSupG (n.val + 24500)) (centF (n.val + 24500)) = true := by decide
private theorem cl_w90 : ∀ n : Fin 50, centF (n.val + 24500) < 23 := by decide
private theorem bd_w90 : ∀ n : Fin 50, densSupG (n.val + 24500) < 2 ^ 1771 := by decide
private theorem cs_w91 : ∀ n : Fin 50, centredStar (densSupG (n.val + 24550)) (centF (n.val + 24550)) = true := by decide
private theorem cl_w91 : ∀ n : Fin 50, centF (n.val + 24550) < 23 := by decide
private theorem bd_w91 : ∀ n : Fin 50, densSupG (n.val + 24550) < 2 ^ 1771 := by decide
private theorem cs_w92 : ∀ n : Fin 50, centredStar (densSupG (n.val + 24600)) (centF (n.val + 24600)) = true := by decide
private theorem cl_w92 : ∀ n : Fin 50, centF (n.val + 24600) < 23 := by decide
private theorem bd_w92 : ∀ n : Fin 50, densSupG (n.val + 24600) < 2 ^ 1771 := by decide
private theorem cs_w93 : ∀ n : Fin 50, centredStar (densSupG (n.val + 24650)) (centF (n.val + 24650)) = true := by decide
private theorem cl_w93 : ∀ n : Fin 50, centF (n.val + 24650) < 23 := by decide
private theorem bd_w93 : ∀ n : Fin 50, densSupG (n.val + 24650) < 2 ^ 1771 := by decide
private theorem cs_w94 : ∀ n : Fin 50, centredStar (densSupG (n.val + 24700)) (centF (n.val + 24700)) = true := by decide
private theorem cl_w94 : ∀ n : Fin 50, centF (n.val + 24700) < 23 := by decide
private theorem bd_w94 : ∀ n : Fin 50, densSupG (n.val + 24700) < 2 ^ 1771 := by decide
private theorem cs_w95 : ∀ n : Fin 50, centredStar (densSupG (n.val + 24750)) (centF (n.val + 24750)) = true := by decide
private theorem cl_w95 : ∀ n : Fin 50, centF (n.val + 24750) < 23 := by decide
private theorem bd_w95 : ∀ n : Fin 50, densSupG (n.val + 24750) < 2 ^ 1771 := by decide
private theorem cs_w96 : ∀ n : Fin 50, centredStar (densSupG (n.val + 24800)) (centF (n.val + 24800)) = true := by decide
private theorem cl_w96 : ∀ n : Fin 50, centF (n.val + 24800) < 23 := by decide
private theorem bd_w96 : ∀ n : Fin 50, densSupG (n.val + 24800) < 2 ^ 1771 := by decide
private theorem cs_w97 : ∀ n : Fin 50, centredStar (densSupG (n.val + 24850)) (centF (n.val + 24850)) = true := by decide
private theorem cl_w97 : ∀ n : Fin 50, centF (n.val + 24850) < 23 := by decide
private theorem bd_w97 : ∀ n : Fin 50, densSupG (n.val + 24850) < 2 ^ 1771 := by decide
private theorem cs_w98 : ∀ n : Fin 50, centredStar (densSupG (n.val + 24900)) (centF (n.val + 24900)) = true := by decide
private theorem cl_w98 : ∀ n : Fin 50, centF (n.val + 24900) < 23 := by decide
private theorem bd_w98 : ∀ n : Fin 50, densSupG (n.val + 24900) < 2 ^ 1771 := by decide
private theorem cs_w99 : ∀ n : Fin 50, centredStar (densSupG (n.val + 24950)) (centF (n.val + 24950)) = true := by decide
private theorem cl_w99 : ∀ n : Fin 50, centF (n.val + 24950) < 23 := by decide
private theorem bd_w99 : ∀ n : Fin 50, densSupG (n.val + 24950) < 2 ^ 1771 := by decide

theorem centredStar_range : ∀ n, 20000 ≤ n → n < 25000 → centredStar (densSupG n) (centF n) = true := by
  intro n hlo hhi
  by_cases h0 : n < 20050
  · have hr : n - 20000 < 50 := by omega
    have heq : n = (n - 20000) + 20000 := by omega
    rw [heq]
    exact cs_w0 ⟨n - 20000, hr⟩
  ·
    by_cases h1 : n < 20100
    · have hr : n - 20050 < 50 := by omega
      have heq : n = (n - 20050) + 20050 := by omega
      rw [heq]
      exact cs_w1 ⟨n - 20050, hr⟩
    ·
      by_cases h2 : n < 20150
      · have hr : n - 20100 < 50 := by omega
        have heq : n = (n - 20100) + 20100 := by omega
        rw [heq]
        exact cs_w2 ⟨n - 20100, hr⟩
      ·
        by_cases h3 : n < 20200
        · have hr : n - 20150 < 50 := by omega
          have heq : n = (n - 20150) + 20150 := by omega
          rw [heq]
          exact cs_w3 ⟨n - 20150, hr⟩
        ·
          by_cases h4 : n < 20250
          · have hr : n - 20200 < 50 := by omega
            have heq : n = (n - 20200) + 20200 := by omega
            rw [heq]
            exact cs_w4 ⟨n - 20200, hr⟩
          ·
            by_cases h5 : n < 20300
            · have hr : n - 20250 < 50 := by omega
              have heq : n = (n - 20250) + 20250 := by omega
              rw [heq]
              exact cs_w5 ⟨n - 20250, hr⟩
            ·
              by_cases h6 : n < 20350
              · have hr : n - 20300 < 50 := by omega
                have heq : n = (n - 20300) + 20300 := by omega
                rw [heq]
                exact cs_w6 ⟨n - 20300, hr⟩
              ·
                by_cases h7 : n < 20400
                · have hr : n - 20350 < 50 := by omega
                  have heq : n = (n - 20350) + 20350 := by omega
                  rw [heq]
                  exact cs_w7 ⟨n - 20350, hr⟩
                ·
                  by_cases h8 : n < 20450
                  · have hr : n - 20400 < 50 := by omega
                    have heq : n = (n - 20400) + 20400 := by omega
                    rw [heq]
                    exact cs_w8 ⟨n - 20400, hr⟩
                  ·
                    by_cases h9 : n < 20500
                    · have hr : n - 20450 < 50 := by omega
                      have heq : n = (n - 20450) + 20450 := by omega
                      rw [heq]
                      exact cs_w9 ⟨n - 20450, hr⟩
                    ·
                      by_cases h10 : n < 20550
                      · have hr : n - 20500 < 50 := by omega
                        have heq : n = (n - 20500) + 20500 := by omega
                        rw [heq]
                        exact cs_w10 ⟨n - 20500, hr⟩
                      ·
                        by_cases h11 : n < 20600
                        · have hr : n - 20550 < 50 := by omega
                          have heq : n = (n - 20550) + 20550 := by omega
                          rw [heq]
                          exact cs_w11 ⟨n - 20550, hr⟩
                        ·
                          by_cases h12 : n < 20650
                          · have hr : n - 20600 < 50 := by omega
                            have heq : n = (n - 20600) + 20600 := by omega
                            rw [heq]
                            exact cs_w12 ⟨n - 20600, hr⟩
                          ·
                            by_cases h13 : n < 20700
                            · have hr : n - 20650 < 50 := by omega
                              have heq : n = (n - 20650) + 20650 := by omega
                              rw [heq]
                              exact cs_w13 ⟨n - 20650, hr⟩
                            ·
                              by_cases h14 : n < 20750
                              · have hr : n - 20700 < 50 := by omega
                                have heq : n = (n - 20700) + 20700 := by omega
                                rw [heq]
                                exact cs_w14 ⟨n - 20700, hr⟩
                              ·
                                by_cases h15 : n < 20800
                                · have hr : n - 20750 < 50 := by omega
                                  have heq : n = (n - 20750) + 20750 := by omega
                                  rw [heq]
                                  exact cs_w15 ⟨n - 20750, hr⟩
                                ·
                                  by_cases h16 : n < 20850
                                  · have hr : n - 20800 < 50 := by omega
                                    have heq : n = (n - 20800) + 20800 := by omega
                                    rw [heq]
                                    exact cs_w16 ⟨n - 20800, hr⟩
                                  ·
                                    by_cases h17 : n < 20900
                                    · have hr : n - 20850 < 50 := by omega
                                      have heq : n = (n - 20850) + 20850 := by omega
                                      rw [heq]
                                      exact cs_w17 ⟨n - 20850, hr⟩
                                    ·
                                      by_cases h18 : n < 20950
                                      · have hr : n - 20900 < 50 := by omega
                                        have heq : n = (n - 20900) + 20900 := by omega
                                        rw [heq]
                                        exact cs_w18 ⟨n - 20900, hr⟩
                                      ·
                                        by_cases h19 : n < 21000
                                        · have hr : n - 20950 < 50 := by omega
                                          have heq : n = (n - 20950) + 20950 := by omega
                                          rw [heq]
                                          exact cs_w19 ⟨n - 20950, hr⟩
                                        ·
                                          by_cases h20 : n < 21050
                                          · have hr : n - 21000 < 50 := by omega
                                            have heq : n = (n - 21000) + 21000 := by omega
                                            rw [heq]
                                            exact cs_w20 ⟨n - 21000, hr⟩
                                          ·
                                            by_cases h21 : n < 21100
                                            · have hr : n - 21050 < 50 := by omega
                                              have heq : n = (n - 21050) + 21050 := by omega
                                              rw [heq]
                                              exact cs_w21 ⟨n - 21050, hr⟩
                                            ·
                                              by_cases h22 : n < 21150
                                              · have hr : n - 21100 < 50 := by omega
                                                have heq : n = (n - 21100) + 21100 := by omega
                                                rw [heq]
                                                exact cs_w22 ⟨n - 21100, hr⟩
                                              ·
                                                by_cases h23 : n < 21200
                                                · have hr : n - 21150 < 50 := by omega
                                                  have heq : n = (n - 21150) + 21150 := by omega
                                                  rw [heq]
                                                  exact cs_w23 ⟨n - 21150, hr⟩
                                                ·
                                                  by_cases h24 : n < 21250
                                                  · have hr : n - 21200 < 50 := by omega
                                                    have heq : n = (n - 21200) + 21200 := by omega
                                                    rw [heq]
                                                    exact cs_w24 ⟨n - 21200, hr⟩
                                                  ·
                                                    by_cases h25 : n < 21300
                                                    · have hr : n - 21250 < 50 := by omega
                                                      have heq : n = (n - 21250) + 21250 := by omega
                                                      rw [heq]
                                                      exact cs_w25 ⟨n - 21250, hr⟩
                                                    ·
                                                      by_cases h26 : n < 21350
                                                      · have hr : n - 21300 < 50 := by omega
                                                        have heq : n = (n - 21300) + 21300 := by omega
                                                        rw [heq]
                                                        exact cs_w26 ⟨n - 21300, hr⟩
                                                      ·
                                                        by_cases h27 : n < 21400
                                                        · have hr : n - 21350 < 50 := by omega
                                                          have heq : n = (n - 21350) + 21350 := by omega
                                                          rw [heq]
                                                          exact cs_w27 ⟨n - 21350, hr⟩
                                                        ·
                                                          by_cases h28 : n < 21450
                                                          · have hr : n - 21400 < 50 := by omega
                                                            have heq : n = (n - 21400) + 21400 := by omega
                                                            rw [heq]
                                                            exact cs_w28 ⟨n - 21400, hr⟩
                                                          ·
                                                            by_cases h29 : n < 21500
                                                            · have hr : n - 21450 < 50 := by omega
                                                              have heq : n = (n - 21450) + 21450 := by omega
                                                              rw [heq]
                                                              exact cs_w29 ⟨n - 21450, hr⟩
                                                            ·
                                                              by_cases h30 : n < 21550
                                                              · have hr : n - 21500 < 50 := by omega
                                                                have heq : n = (n - 21500) + 21500 := by omega
                                                                rw [heq]
                                                                exact cs_w30 ⟨n - 21500, hr⟩
                                                              ·
                                                                by_cases h31 : n < 21600
                                                                · have hr : n - 21550 < 50 := by omega
                                                                  have heq : n = (n - 21550) + 21550 := by omega
                                                                  rw [heq]
                                                                  exact cs_w31 ⟨n - 21550, hr⟩
                                                                ·
                                                                  by_cases h32 : n < 21650
                                                                  · have hr : n - 21600 < 50 := by omega
                                                                    have heq : n = (n - 21600) + 21600 := by omega
                                                                    rw [heq]
                                                                    exact cs_w32 ⟨n - 21600, hr⟩
                                                                  ·
                                                                    by_cases h33 : n < 21700
                                                                    · have hr : n - 21650 < 50 := by omega
                                                                      have heq : n = (n - 21650) + 21650 := by omega
                                                                      rw [heq]
                                                                      exact cs_w33 ⟨n - 21650, hr⟩
                                                                    ·
                                                                      by_cases h34 : n < 21750
                                                                      · have hr : n - 21700 < 50 := by omega
                                                                        have heq : n = (n - 21700) + 21700 := by omega
                                                                        rw [heq]
                                                                        exact cs_w34 ⟨n - 21700, hr⟩
                                                                      ·
                                                                        by_cases h35 : n < 21800
                                                                        · have hr : n - 21750 < 50 := by omega
                                                                          have heq : n = (n - 21750) + 21750 := by omega
                                                                          rw [heq]
                                                                          exact cs_w35 ⟨n - 21750, hr⟩
                                                                        ·
                                                                          by_cases h36 : n < 21850
                                                                          · have hr : n - 21800 < 50 := by omega
                                                                            have heq : n = (n - 21800) + 21800 := by omega
                                                                            rw [heq]
                                                                            exact cs_w36 ⟨n - 21800, hr⟩
                                                                          ·
                                                                            by_cases h37 : n < 21900
                                                                            · have hr : n - 21850 < 50 := by omega
                                                                              have heq : n = (n - 21850) + 21850 := by omega
                                                                              rw [heq]
                                                                              exact cs_w37 ⟨n - 21850, hr⟩
                                                                            ·
                                                                              by_cases h38 : n < 21950
                                                                              · have hr : n - 21900 < 50 := by omega
                                                                                have heq : n = (n - 21900) + 21900 := by omega
                                                                                rw [heq]
                                                                                exact cs_w38 ⟨n - 21900, hr⟩
                                                                              ·
                                                                                by_cases h39 : n < 22000
                                                                                · have hr : n - 21950 < 50 := by omega
                                                                                  have heq : n = (n - 21950) + 21950 := by omega
                                                                                  rw [heq]
                                                                                  exact cs_w39 ⟨n - 21950, hr⟩
                                                                                ·
                                                                                  by_cases h40 : n < 22050
                                                                                  · have hr : n - 22000 < 50 := by omega
                                                                                    have heq : n = (n - 22000) + 22000 := by omega
                                                                                    rw [heq]
                                                                                    exact cs_w40 ⟨n - 22000, hr⟩
                                                                                  ·
                                                                                    by_cases h41 : n < 22100
                                                                                    · have hr : n - 22050 < 50 := by omega
                                                                                      have heq : n = (n - 22050) + 22050 := by omega
                                                                                      rw [heq]
                                                                                      exact cs_w41 ⟨n - 22050, hr⟩
                                                                                    ·
                                                                                      by_cases h42 : n < 22150
                                                                                      · have hr : n - 22100 < 50 := by omega
                                                                                        have heq : n = (n - 22100) + 22100 := by omega
                                                                                        rw [heq]
                                                                                        exact cs_w42 ⟨n - 22100, hr⟩
                                                                                      ·
                                                                                        by_cases h43 : n < 22200
                                                                                        · have hr : n - 22150 < 50 := by omega
                                                                                          have heq : n = (n - 22150) + 22150 := by omega
                                                                                          rw [heq]
                                                                                          exact cs_w43 ⟨n - 22150, hr⟩
                                                                                        ·
                                                                                          by_cases h44 : n < 22250
                                                                                          · have hr : n - 22200 < 50 := by omega
                                                                                            have heq : n = (n - 22200) + 22200 := by omega
                                                                                            rw [heq]
                                                                                            exact cs_w44 ⟨n - 22200, hr⟩
                                                                                          ·
                                                                                            by_cases h45 : n < 22300
                                                                                            · have hr : n - 22250 < 50 := by omega
                                                                                              have heq : n = (n - 22250) + 22250 := by omega
                                                                                              rw [heq]
                                                                                              exact cs_w45 ⟨n - 22250, hr⟩
                                                                                            ·
                                                                                              by_cases h46 : n < 22350
                                                                                              · have hr : n - 22300 < 50 := by omega
                                                                                                have heq : n = (n - 22300) + 22300 := by omega
                                                                                                rw [heq]
                                                                                                exact cs_w46 ⟨n - 22300, hr⟩
                                                                                              ·
                                                                                                by_cases h47 : n < 22400
                                                                                                · have hr : n - 22350 < 50 := by omega
                                                                                                  have heq : n = (n - 22350) + 22350 := by omega
                                                                                                  rw [heq]
                                                                                                  exact cs_w47 ⟨n - 22350, hr⟩
                                                                                                ·
                                                                                                  by_cases h48 : n < 22450
                                                                                                  · have hr : n - 22400 < 50 := by omega
                                                                                                    have heq : n = (n - 22400) + 22400 := by omega
                                                                                                    rw [heq]
                                                                                                    exact cs_w48 ⟨n - 22400, hr⟩
                                                                                                  ·
                                                                                                    by_cases h49 : n < 22500
                                                                                                    · have hr : n - 22450 < 50 := by omega
                                                                                                      have heq : n = (n - 22450) + 22450 := by omega
                                                                                                      rw [heq]
                                                                                                      exact cs_w49 ⟨n - 22450, hr⟩
                                                                                                    ·
                                                                                                      by_cases h50 : n < 22550
                                                                                                      · have hr : n - 22500 < 50 := by omega
                                                                                                        have heq : n = (n - 22500) + 22500 := by omega
                                                                                                        rw [heq]
                                                                                                        exact cs_w50 ⟨n - 22500, hr⟩
                                                                                                      ·
                                                                                                        by_cases h51 : n < 22600
                                                                                                        · have hr : n - 22550 < 50 := by omega
                                                                                                          have heq : n = (n - 22550) + 22550 := by omega
                                                                                                          rw [heq]
                                                                                                          exact cs_w51 ⟨n - 22550, hr⟩
                                                                                                        ·
                                                                                                          by_cases h52 : n < 22650
                                                                                                          · have hr : n - 22600 < 50 := by omega
                                                                                                            have heq : n = (n - 22600) + 22600 := by omega
                                                                                                            rw [heq]
                                                                                                            exact cs_w52 ⟨n - 22600, hr⟩
                                                                                                          ·
                                                                                                            by_cases h53 : n < 22700
                                                                                                            · have hr : n - 22650 < 50 := by omega
                                                                                                              have heq : n = (n - 22650) + 22650 := by omega
                                                                                                              rw [heq]
                                                                                                              exact cs_w53 ⟨n - 22650, hr⟩
                                                                                                            ·
                                                                                                              by_cases h54 : n < 22750
                                                                                                              · have hr : n - 22700 < 50 := by omega
                                                                                                                have heq : n = (n - 22700) + 22700 := by omega
                                                                                                                rw [heq]
                                                                                                                exact cs_w54 ⟨n - 22700, hr⟩
                                                                                                              ·
                                                                                                                by_cases h55 : n < 22800
                                                                                                                · have hr : n - 22750 < 50 := by omega
                                                                                                                  have heq : n = (n - 22750) + 22750 := by omega
                                                                                                                  rw [heq]
                                                                                                                  exact cs_w55 ⟨n - 22750, hr⟩
                                                                                                                ·
                                                                                                                  by_cases h56 : n < 22850
                                                                                                                  · have hr : n - 22800 < 50 := by omega
                                                                                                                    have heq : n = (n - 22800) + 22800 := by omega
                                                                                                                    rw [heq]
                                                                                                                    exact cs_w56 ⟨n - 22800, hr⟩
                                                                                                                  ·
                                                                                                                    by_cases h57 : n < 22900
                                                                                                                    · have hr : n - 22850 < 50 := by omega
                                                                                                                      have heq : n = (n - 22850) + 22850 := by omega
                                                                                                                      rw [heq]
                                                                                                                      exact cs_w57 ⟨n - 22850, hr⟩
                                                                                                                    ·
                                                                                                                      by_cases h58 : n < 22950
                                                                                                                      · have hr : n - 22900 < 50 := by omega
                                                                                                                        have heq : n = (n - 22900) + 22900 := by omega
                                                                                                                        rw [heq]
                                                                                                                        exact cs_w58 ⟨n - 22900, hr⟩
                                                                                                                      ·
                                                                                                                        by_cases h59 : n < 23000
                                                                                                                        · have hr : n - 22950 < 50 := by omega
                                                                                                                          have heq : n = (n - 22950) + 22950 := by omega
                                                                                                                          rw [heq]
                                                                                                                          exact cs_w59 ⟨n - 22950, hr⟩
                                                                                                                        ·
                                                                                                                          by_cases h60 : n < 23050
                                                                                                                          · have hr : n - 23000 < 50 := by omega
                                                                                                                            have heq : n = (n - 23000) + 23000 := by omega
                                                                                                                            rw [heq]
                                                                                                                            exact cs_w60 ⟨n - 23000, hr⟩
                                                                                                                          ·
                                                                                                                            by_cases h61 : n < 23100
                                                                                                                            · have hr : n - 23050 < 50 := by omega
                                                                                                                              have heq : n = (n - 23050) + 23050 := by omega
                                                                                                                              rw [heq]
                                                                                                                              exact cs_w61 ⟨n - 23050, hr⟩
                                                                                                                            ·
                                                                                                                              by_cases h62 : n < 23150
                                                                                                                              · have hr : n - 23100 < 50 := by omega
                                                                                                                                have heq : n = (n - 23100) + 23100 := by omega
                                                                                                                                rw [heq]
                                                                                                                                exact cs_w62 ⟨n - 23100, hr⟩
                                                                                                                              ·
                                                                                                                                by_cases h63 : n < 23200
                                                                                                                                · have hr : n - 23150 < 50 := by omega
                                                                                                                                  have heq : n = (n - 23150) + 23150 := by omega
                                                                                                                                  rw [heq]
                                                                                                                                  exact cs_w63 ⟨n - 23150, hr⟩
                                                                                                                                ·
                                                                                                                                  by_cases h64 : n < 23250
                                                                                                                                  · have hr : n - 23200 < 50 := by omega
                                                                                                                                    have heq : n = (n - 23200) + 23200 := by omega
                                                                                                                                    rw [heq]
                                                                                                                                    exact cs_w64 ⟨n - 23200, hr⟩
                                                                                                                                  ·
                                                                                                                                    by_cases h65 : n < 23300
                                                                                                                                    · have hr : n - 23250 < 50 := by omega
                                                                                                                                      have heq : n = (n - 23250) + 23250 := by omega
                                                                                                                                      rw [heq]
                                                                                                                                      exact cs_w65 ⟨n - 23250, hr⟩
                                                                                                                                    ·
                                                                                                                                      by_cases h66 : n < 23350
                                                                                                                                      · have hr : n - 23300 < 50 := by omega
                                                                                                                                        have heq : n = (n - 23300) + 23300 := by omega
                                                                                                                                        rw [heq]
                                                                                                                                        exact cs_w66 ⟨n - 23300, hr⟩
                                                                                                                                      ·
                                                                                                                                        by_cases h67 : n < 23400
                                                                                                                                        · have hr : n - 23350 < 50 := by omega
                                                                                                                                          have heq : n = (n - 23350) + 23350 := by omega
                                                                                                                                          rw [heq]
                                                                                                                                          exact cs_w67 ⟨n - 23350, hr⟩
                                                                                                                                        ·
                                                                                                                                          by_cases h68 : n < 23450
                                                                                                                                          · have hr : n - 23400 < 50 := by omega
                                                                                                                                            have heq : n = (n - 23400) + 23400 := by omega
                                                                                                                                            rw [heq]
                                                                                                                                            exact cs_w68 ⟨n - 23400, hr⟩
                                                                                                                                          ·
                                                                                                                                            by_cases h69 : n < 23500
                                                                                                                                            · have hr : n - 23450 < 50 := by omega
                                                                                                                                              have heq : n = (n - 23450) + 23450 := by omega
                                                                                                                                              rw [heq]
                                                                                                                                              exact cs_w69 ⟨n - 23450, hr⟩
                                                                                                                                            ·
                                                                                                                                              by_cases h70 : n < 23550
                                                                                                                                              · have hr : n - 23500 < 50 := by omega
                                                                                                                                                have heq : n = (n - 23500) + 23500 := by omega
                                                                                                                                                rw [heq]
                                                                                                                                                exact cs_w70 ⟨n - 23500, hr⟩
                                                                                                                                              ·
                                                                                                                                                by_cases h71 : n < 23600
                                                                                                                                                · have hr : n - 23550 < 50 := by omega
                                                                                                                                                  have heq : n = (n - 23550) + 23550 := by omega
                                                                                                                                                  rw [heq]
                                                                                                                                                  exact cs_w71 ⟨n - 23550, hr⟩
                                                                                                                                                ·
                                                                                                                                                  by_cases h72 : n < 23650
                                                                                                                                                  · have hr : n - 23600 < 50 := by omega
                                                                                                                                                    have heq : n = (n - 23600) + 23600 := by omega
                                                                                                                                                    rw [heq]
                                                                                                                                                    exact cs_w72 ⟨n - 23600, hr⟩
                                                                                                                                                  ·
                                                                                                                                                    by_cases h73 : n < 23700
                                                                                                                                                    · have hr : n - 23650 < 50 := by omega
                                                                                                                                                      have heq : n = (n - 23650) + 23650 := by omega
                                                                                                                                                      rw [heq]
                                                                                                                                                      exact cs_w73 ⟨n - 23650, hr⟩
                                                                                                                                                    ·
                                                                                                                                                      by_cases h74 : n < 23750
                                                                                                                                                      · have hr : n - 23700 < 50 := by omega
                                                                                                                                                        have heq : n = (n - 23700) + 23700 := by omega
                                                                                                                                                        rw [heq]
                                                                                                                                                        exact cs_w74 ⟨n - 23700, hr⟩
                                                                                                                                                      ·
                                                                                                                                                        by_cases h75 : n < 23800
                                                                                                                                                        · have hr : n - 23750 < 50 := by omega
                                                                                                                                                          have heq : n = (n - 23750) + 23750 := by omega
                                                                                                                                                          rw [heq]
                                                                                                                                                          exact cs_w75 ⟨n - 23750, hr⟩
                                                                                                                                                        ·
                                                                                                                                                          by_cases h76 : n < 23850
                                                                                                                                                          · have hr : n - 23800 < 50 := by omega
                                                                                                                                                            have heq : n = (n - 23800) + 23800 := by omega
                                                                                                                                                            rw [heq]
                                                                                                                                                            exact cs_w76 ⟨n - 23800, hr⟩
                                                                                                                                                          ·
                                                                                                                                                            by_cases h77 : n < 23900
                                                                                                                                                            · have hr : n - 23850 < 50 := by omega
                                                                                                                                                              have heq : n = (n - 23850) + 23850 := by omega
                                                                                                                                                              rw [heq]
                                                                                                                                                              exact cs_w77 ⟨n - 23850, hr⟩
                                                                                                                                                            ·
                                                                                                                                                              by_cases h78 : n < 23950
                                                                                                                                                              · have hr : n - 23900 < 50 := by omega
                                                                                                                                                                have heq : n = (n - 23900) + 23900 := by omega
                                                                                                                                                                rw [heq]
                                                                                                                                                                exact cs_w78 ⟨n - 23900, hr⟩
                                                                                                                                                              ·
                                                                                                                                                                by_cases h79 : n < 24000
                                                                                                                                                                · have hr : n - 23950 < 50 := by omega
                                                                                                                                                                  have heq : n = (n - 23950) + 23950 := by omega
                                                                                                                                                                  rw [heq]
                                                                                                                                                                  exact cs_w79 ⟨n - 23950, hr⟩
                                                                                                                                                                ·
                                                                                                                                                                  by_cases h80 : n < 24050
                                                                                                                                                                  · have hr : n - 24000 < 50 := by omega
                                                                                                                                                                    have heq : n = (n - 24000) + 24000 := by omega
                                                                                                                                                                    rw [heq]
                                                                                                                                                                    exact cs_w80 ⟨n - 24000, hr⟩
                                                                                                                                                                  ·
                                                                                                                                                                    by_cases h81 : n < 24100
                                                                                                                                                                    · have hr : n - 24050 < 50 := by omega
                                                                                                                                                                      have heq : n = (n - 24050) + 24050 := by omega
                                                                                                                                                                      rw [heq]
                                                                                                                                                                      exact cs_w81 ⟨n - 24050, hr⟩
                                                                                                                                                                    ·
                                                                                                                                                                      by_cases h82 : n < 24150
                                                                                                                                                                      · have hr : n - 24100 < 50 := by omega
                                                                                                                                                                        have heq : n = (n - 24100) + 24100 := by omega
                                                                                                                                                                        rw [heq]
                                                                                                                                                                        exact cs_w82 ⟨n - 24100, hr⟩
                                                                                                                                                                      ·
                                                                                                                                                                        by_cases h83 : n < 24200
                                                                                                                                                                        · have hr : n - 24150 < 50 := by omega
                                                                                                                                                                          have heq : n = (n - 24150) + 24150 := by omega
                                                                                                                                                                          rw [heq]
                                                                                                                                                                          exact cs_w83 ⟨n - 24150, hr⟩
                                                                                                                                                                        ·
                                                                                                                                                                          by_cases h84 : n < 24250
                                                                                                                                                                          · have hr : n - 24200 < 50 := by omega
                                                                                                                                                                            have heq : n = (n - 24200) + 24200 := by omega
                                                                                                                                                                            rw [heq]
                                                                                                                                                                            exact cs_w84 ⟨n - 24200, hr⟩
                                                                                                                                                                          ·
                                                                                                                                                                            by_cases h85 : n < 24300
                                                                                                                                                                            · have hr : n - 24250 < 50 := by omega
                                                                                                                                                                              have heq : n = (n - 24250) + 24250 := by omega
                                                                                                                                                                              rw [heq]
                                                                                                                                                                              exact cs_w85 ⟨n - 24250, hr⟩
                                                                                                                                                                            ·
                                                                                                                                                                              by_cases h86 : n < 24350
                                                                                                                                                                              · have hr : n - 24300 < 50 := by omega
                                                                                                                                                                                have heq : n = (n - 24300) + 24300 := by omega
                                                                                                                                                                                rw [heq]
                                                                                                                                                                                exact cs_w86 ⟨n - 24300, hr⟩
                                                                                                                                                                              ·
                                                                                                                                                                                by_cases h87 : n < 24400
                                                                                                                                                                                · have hr : n - 24350 < 50 := by omega
                                                                                                                                                                                  have heq : n = (n - 24350) + 24350 := by omega
                                                                                                                                                                                  rw [heq]
                                                                                                                                                                                  exact cs_w87 ⟨n - 24350, hr⟩
                                                                                                                                                                                ·
                                                                                                                                                                                  by_cases h88 : n < 24450
                                                                                                                                                                                  · have hr : n - 24400 < 50 := by omega
                                                                                                                                                                                    have heq : n = (n - 24400) + 24400 := by omega
                                                                                                                                                                                    rw [heq]
                                                                                                                                                                                    exact cs_w88 ⟨n - 24400, hr⟩
                                                                                                                                                                                  ·
                                                                                                                                                                                    by_cases h89 : n < 24500
                                                                                                                                                                                    · have hr : n - 24450 < 50 := by omega
                                                                                                                                                                                      have heq : n = (n - 24450) + 24450 := by omega
                                                                                                                                                                                      rw [heq]
                                                                                                                                                                                      exact cs_w89 ⟨n - 24450, hr⟩
                                                                                                                                                                                    ·
                                                                                                                                                                                      by_cases h90 : n < 24550
                                                                                                                                                                                      · have hr : n - 24500 < 50 := by omega
                                                                                                                                                                                        have heq : n = (n - 24500) + 24500 := by omega
                                                                                                                                                                                        rw [heq]
                                                                                                                                                                                        exact cs_w90 ⟨n - 24500, hr⟩
                                                                                                                                                                                      ·
                                                                                                                                                                                        by_cases h91 : n < 24600
                                                                                                                                                                                        · have hr : n - 24550 < 50 := by omega
                                                                                                                                                                                          have heq : n = (n - 24550) + 24550 := by omega
                                                                                                                                                                                          rw [heq]
                                                                                                                                                                                          exact cs_w91 ⟨n - 24550, hr⟩
                                                                                                                                                                                        ·
                                                                                                                                                                                          by_cases h92 : n < 24650
                                                                                                                                                                                          · have hr : n - 24600 < 50 := by omega
                                                                                                                                                                                            have heq : n = (n - 24600) + 24600 := by omega
                                                                                                                                                                                            rw [heq]
                                                                                                                                                                                            exact cs_w92 ⟨n - 24600, hr⟩
                                                                                                                                                                                          ·
                                                                                                                                                                                            by_cases h93 : n < 24700
                                                                                                                                                                                            · have hr : n - 24650 < 50 := by omega
                                                                                                                                                                                              have heq : n = (n - 24650) + 24650 := by omega
                                                                                                                                                                                              rw [heq]
                                                                                                                                                                                              exact cs_w93 ⟨n - 24650, hr⟩
                                                                                                                                                                                            ·
                                                                                                                                                                                              by_cases h94 : n < 24750
                                                                                                                                                                                              · have hr : n - 24700 < 50 := by omega
                                                                                                                                                                                                have heq : n = (n - 24700) + 24700 := by omega
                                                                                                                                                                                                rw [heq]
                                                                                                                                                                                                exact cs_w94 ⟨n - 24700, hr⟩
                                                                                                                                                                                              ·
                                                                                                                                                                                                by_cases h95 : n < 24800
                                                                                                                                                                                                · have hr : n - 24750 < 50 := by omega
                                                                                                                                                                                                  have heq : n = (n - 24750) + 24750 := by omega
                                                                                                                                                                                                  rw [heq]
                                                                                                                                                                                                  exact cs_w95 ⟨n - 24750, hr⟩
                                                                                                                                                                                                ·
                                                                                                                                                                                                  by_cases h96 : n < 24850
                                                                                                                                                                                                  · have hr : n - 24800 < 50 := by omega
                                                                                                                                                                                                    have heq : n = (n - 24800) + 24800 := by omega
                                                                                                                                                                                                    rw [heq]
                                                                                                                                                                                                    exact cs_w96 ⟨n - 24800, hr⟩
                                                                                                                                                                                                  ·
                                                                                                                                                                                                    by_cases h97 : n < 24900
                                                                                                                                                                                                    · have hr : n - 24850 < 50 := by omega
                                                                                                                                                                                                      have heq : n = (n - 24850) + 24850 := by omega
                                                                                                                                                                                                      rw [heq]
                                                                                                                                                                                                      exact cs_w97 ⟨n - 24850, hr⟩
                                                                                                                                                                                                    ·
                                                                                                                                                                                                      by_cases h98 : n < 24950
                                                                                                                                                                                                      · have hr : n - 24900 < 50 := by omega
                                                                                                                                                                                                        have heq : n = (n - 24900) + 24900 := by omega
                                                                                                                                                                                                        rw [heq]
                                                                                                                                                                                                        exact cs_w98 ⟨n - 24900, hr⟩
                                                                                                                                                                                                      ·
                                                                                                                                                                                                        have hr : n - 24950 < 50 := by omega
                                                                                                                                                                                                        have heq : n = (n - 24950) + 24950 := by omega
                                                                                                                                                                                                        rw [heq]
                                                                                                                                                                                                        exact cs_w99 ⟨n - 24950, hr⟩

theorem centF_lt_range : ∀ n, 20000 ≤ n → n < 25000 → centF n < 23 := by
  intro n hlo hhi
  by_cases h0 : n < 20050
  · have hr : n - 20000 < 50 := by omega
    have heq : n = (n - 20000) + 20000 := by omega
    rw [heq]
    exact cl_w0 ⟨n - 20000, hr⟩
  ·
    by_cases h1 : n < 20100
    · have hr : n - 20050 < 50 := by omega
      have heq : n = (n - 20050) + 20050 := by omega
      rw [heq]
      exact cl_w1 ⟨n - 20050, hr⟩
    ·
      by_cases h2 : n < 20150
      · have hr : n - 20100 < 50 := by omega
        have heq : n = (n - 20100) + 20100 := by omega
        rw [heq]
        exact cl_w2 ⟨n - 20100, hr⟩
      ·
        by_cases h3 : n < 20200
        · have hr : n - 20150 < 50 := by omega
          have heq : n = (n - 20150) + 20150 := by omega
          rw [heq]
          exact cl_w3 ⟨n - 20150, hr⟩
        ·
          by_cases h4 : n < 20250
          · have hr : n - 20200 < 50 := by omega
            have heq : n = (n - 20200) + 20200 := by omega
            rw [heq]
            exact cl_w4 ⟨n - 20200, hr⟩
          ·
            by_cases h5 : n < 20300
            · have hr : n - 20250 < 50 := by omega
              have heq : n = (n - 20250) + 20250 := by omega
              rw [heq]
              exact cl_w5 ⟨n - 20250, hr⟩
            ·
              by_cases h6 : n < 20350
              · have hr : n - 20300 < 50 := by omega
                have heq : n = (n - 20300) + 20300 := by omega
                rw [heq]
                exact cl_w6 ⟨n - 20300, hr⟩
              ·
                by_cases h7 : n < 20400
                · have hr : n - 20350 < 50 := by omega
                  have heq : n = (n - 20350) + 20350 := by omega
                  rw [heq]
                  exact cl_w7 ⟨n - 20350, hr⟩
                ·
                  by_cases h8 : n < 20450
                  · have hr : n - 20400 < 50 := by omega
                    have heq : n = (n - 20400) + 20400 := by omega
                    rw [heq]
                    exact cl_w8 ⟨n - 20400, hr⟩
                  ·
                    by_cases h9 : n < 20500
                    · have hr : n - 20450 < 50 := by omega
                      have heq : n = (n - 20450) + 20450 := by omega
                      rw [heq]
                      exact cl_w9 ⟨n - 20450, hr⟩
                    ·
                      by_cases h10 : n < 20550
                      · have hr : n - 20500 < 50 := by omega
                        have heq : n = (n - 20500) + 20500 := by omega
                        rw [heq]
                        exact cl_w10 ⟨n - 20500, hr⟩
                      ·
                        by_cases h11 : n < 20600
                        · have hr : n - 20550 < 50 := by omega
                          have heq : n = (n - 20550) + 20550 := by omega
                          rw [heq]
                          exact cl_w11 ⟨n - 20550, hr⟩
                        ·
                          by_cases h12 : n < 20650
                          · have hr : n - 20600 < 50 := by omega
                            have heq : n = (n - 20600) + 20600 := by omega
                            rw [heq]
                            exact cl_w12 ⟨n - 20600, hr⟩
                          ·
                            by_cases h13 : n < 20700
                            · have hr : n - 20650 < 50 := by omega
                              have heq : n = (n - 20650) + 20650 := by omega
                              rw [heq]
                              exact cl_w13 ⟨n - 20650, hr⟩
                            ·
                              by_cases h14 : n < 20750
                              · have hr : n - 20700 < 50 := by omega
                                have heq : n = (n - 20700) + 20700 := by omega
                                rw [heq]
                                exact cl_w14 ⟨n - 20700, hr⟩
                              ·
                                by_cases h15 : n < 20800
                                · have hr : n - 20750 < 50 := by omega
                                  have heq : n = (n - 20750) + 20750 := by omega
                                  rw [heq]
                                  exact cl_w15 ⟨n - 20750, hr⟩
                                ·
                                  by_cases h16 : n < 20850
                                  · have hr : n - 20800 < 50 := by omega
                                    have heq : n = (n - 20800) + 20800 := by omega
                                    rw [heq]
                                    exact cl_w16 ⟨n - 20800, hr⟩
                                  ·
                                    by_cases h17 : n < 20900
                                    · have hr : n - 20850 < 50 := by omega
                                      have heq : n = (n - 20850) + 20850 := by omega
                                      rw [heq]
                                      exact cl_w17 ⟨n - 20850, hr⟩
                                    ·
                                      by_cases h18 : n < 20950
                                      · have hr : n - 20900 < 50 := by omega
                                        have heq : n = (n - 20900) + 20900 := by omega
                                        rw [heq]
                                        exact cl_w18 ⟨n - 20900, hr⟩
                                      ·
                                        by_cases h19 : n < 21000
                                        · have hr : n - 20950 < 50 := by omega
                                          have heq : n = (n - 20950) + 20950 := by omega
                                          rw [heq]
                                          exact cl_w19 ⟨n - 20950, hr⟩
                                        ·
                                          by_cases h20 : n < 21050
                                          · have hr : n - 21000 < 50 := by omega
                                            have heq : n = (n - 21000) + 21000 := by omega
                                            rw [heq]
                                            exact cl_w20 ⟨n - 21000, hr⟩
                                          ·
                                            by_cases h21 : n < 21100
                                            · have hr : n - 21050 < 50 := by omega
                                              have heq : n = (n - 21050) + 21050 := by omega
                                              rw [heq]
                                              exact cl_w21 ⟨n - 21050, hr⟩
                                            ·
                                              by_cases h22 : n < 21150
                                              · have hr : n - 21100 < 50 := by omega
                                                have heq : n = (n - 21100) + 21100 := by omega
                                                rw [heq]
                                                exact cl_w22 ⟨n - 21100, hr⟩
                                              ·
                                                by_cases h23 : n < 21200
                                                · have hr : n - 21150 < 50 := by omega
                                                  have heq : n = (n - 21150) + 21150 := by omega
                                                  rw [heq]
                                                  exact cl_w23 ⟨n - 21150, hr⟩
                                                ·
                                                  by_cases h24 : n < 21250
                                                  · have hr : n - 21200 < 50 := by omega
                                                    have heq : n = (n - 21200) + 21200 := by omega
                                                    rw [heq]
                                                    exact cl_w24 ⟨n - 21200, hr⟩
                                                  ·
                                                    by_cases h25 : n < 21300
                                                    · have hr : n - 21250 < 50 := by omega
                                                      have heq : n = (n - 21250) + 21250 := by omega
                                                      rw [heq]
                                                      exact cl_w25 ⟨n - 21250, hr⟩
                                                    ·
                                                      by_cases h26 : n < 21350
                                                      · have hr : n - 21300 < 50 := by omega
                                                        have heq : n = (n - 21300) + 21300 := by omega
                                                        rw [heq]
                                                        exact cl_w26 ⟨n - 21300, hr⟩
                                                      ·
                                                        by_cases h27 : n < 21400
                                                        · have hr : n - 21350 < 50 := by omega
                                                          have heq : n = (n - 21350) + 21350 := by omega
                                                          rw [heq]
                                                          exact cl_w27 ⟨n - 21350, hr⟩
                                                        ·
                                                          by_cases h28 : n < 21450
                                                          · have hr : n - 21400 < 50 := by omega
                                                            have heq : n = (n - 21400) + 21400 := by omega
                                                            rw [heq]
                                                            exact cl_w28 ⟨n - 21400, hr⟩
                                                          ·
                                                            by_cases h29 : n < 21500
                                                            · have hr : n - 21450 < 50 := by omega
                                                              have heq : n = (n - 21450) + 21450 := by omega
                                                              rw [heq]
                                                              exact cl_w29 ⟨n - 21450, hr⟩
                                                            ·
                                                              by_cases h30 : n < 21550
                                                              · have hr : n - 21500 < 50 := by omega
                                                                have heq : n = (n - 21500) + 21500 := by omega
                                                                rw [heq]
                                                                exact cl_w30 ⟨n - 21500, hr⟩
                                                              ·
                                                                by_cases h31 : n < 21600
                                                                · have hr : n - 21550 < 50 := by omega
                                                                  have heq : n = (n - 21550) + 21550 := by omega
                                                                  rw [heq]
                                                                  exact cl_w31 ⟨n - 21550, hr⟩
                                                                ·
                                                                  by_cases h32 : n < 21650
                                                                  · have hr : n - 21600 < 50 := by omega
                                                                    have heq : n = (n - 21600) + 21600 := by omega
                                                                    rw [heq]
                                                                    exact cl_w32 ⟨n - 21600, hr⟩
                                                                  ·
                                                                    by_cases h33 : n < 21700
                                                                    · have hr : n - 21650 < 50 := by omega
                                                                      have heq : n = (n - 21650) + 21650 := by omega
                                                                      rw [heq]
                                                                      exact cl_w33 ⟨n - 21650, hr⟩
                                                                    ·
                                                                      by_cases h34 : n < 21750
                                                                      · have hr : n - 21700 < 50 := by omega
                                                                        have heq : n = (n - 21700) + 21700 := by omega
                                                                        rw [heq]
                                                                        exact cl_w34 ⟨n - 21700, hr⟩
                                                                      ·
                                                                        by_cases h35 : n < 21800
                                                                        · have hr : n - 21750 < 50 := by omega
                                                                          have heq : n = (n - 21750) + 21750 := by omega
                                                                          rw [heq]
                                                                          exact cl_w35 ⟨n - 21750, hr⟩
                                                                        ·
                                                                          by_cases h36 : n < 21850
                                                                          · have hr : n - 21800 < 50 := by omega
                                                                            have heq : n = (n - 21800) + 21800 := by omega
                                                                            rw [heq]
                                                                            exact cl_w36 ⟨n - 21800, hr⟩
                                                                          ·
                                                                            by_cases h37 : n < 21900
                                                                            · have hr : n - 21850 < 50 := by omega
                                                                              have heq : n = (n - 21850) + 21850 := by omega
                                                                              rw [heq]
                                                                              exact cl_w37 ⟨n - 21850, hr⟩
                                                                            ·
                                                                              by_cases h38 : n < 21950
                                                                              · have hr : n - 21900 < 50 := by omega
                                                                                have heq : n = (n - 21900) + 21900 := by omega
                                                                                rw [heq]
                                                                                exact cl_w38 ⟨n - 21900, hr⟩
                                                                              ·
                                                                                by_cases h39 : n < 22000
                                                                                · have hr : n - 21950 < 50 := by omega
                                                                                  have heq : n = (n - 21950) + 21950 := by omega
                                                                                  rw [heq]
                                                                                  exact cl_w39 ⟨n - 21950, hr⟩
                                                                                ·
                                                                                  by_cases h40 : n < 22050
                                                                                  · have hr : n - 22000 < 50 := by omega
                                                                                    have heq : n = (n - 22000) + 22000 := by omega
                                                                                    rw [heq]
                                                                                    exact cl_w40 ⟨n - 22000, hr⟩
                                                                                  ·
                                                                                    by_cases h41 : n < 22100
                                                                                    · have hr : n - 22050 < 50 := by omega
                                                                                      have heq : n = (n - 22050) + 22050 := by omega
                                                                                      rw [heq]
                                                                                      exact cl_w41 ⟨n - 22050, hr⟩
                                                                                    ·
                                                                                      by_cases h42 : n < 22150
                                                                                      · have hr : n - 22100 < 50 := by omega
                                                                                        have heq : n = (n - 22100) + 22100 := by omega
                                                                                        rw [heq]
                                                                                        exact cl_w42 ⟨n - 22100, hr⟩
                                                                                      ·
                                                                                        by_cases h43 : n < 22200
                                                                                        · have hr : n - 22150 < 50 := by omega
                                                                                          have heq : n = (n - 22150) + 22150 := by omega
                                                                                          rw [heq]
                                                                                          exact cl_w43 ⟨n - 22150, hr⟩
                                                                                        ·
                                                                                          by_cases h44 : n < 22250
                                                                                          · have hr : n - 22200 < 50 := by omega
                                                                                            have heq : n = (n - 22200) + 22200 := by omega
                                                                                            rw [heq]
                                                                                            exact cl_w44 ⟨n - 22200, hr⟩
                                                                                          ·
                                                                                            by_cases h45 : n < 22300
                                                                                            · have hr : n - 22250 < 50 := by omega
                                                                                              have heq : n = (n - 22250) + 22250 := by omega
                                                                                              rw [heq]
                                                                                              exact cl_w45 ⟨n - 22250, hr⟩
                                                                                            ·
                                                                                              by_cases h46 : n < 22350
                                                                                              · have hr : n - 22300 < 50 := by omega
                                                                                                have heq : n = (n - 22300) + 22300 := by omega
                                                                                                rw [heq]
                                                                                                exact cl_w46 ⟨n - 22300, hr⟩
                                                                                              ·
                                                                                                by_cases h47 : n < 22400
                                                                                                · have hr : n - 22350 < 50 := by omega
                                                                                                  have heq : n = (n - 22350) + 22350 := by omega
                                                                                                  rw [heq]
                                                                                                  exact cl_w47 ⟨n - 22350, hr⟩
                                                                                                ·
                                                                                                  by_cases h48 : n < 22450
                                                                                                  · have hr : n - 22400 < 50 := by omega
                                                                                                    have heq : n = (n - 22400) + 22400 := by omega
                                                                                                    rw [heq]
                                                                                                    exact cl_w48 ⟨n - 22400, hr⟩
                                                                                                  ·
                                                                                                    by_cases h49 : n < 22500
                                                                                                    · have hr : n - 22450 < 50 := by omega
                                                                                                      have heq : n = (n - 22450) + 22450 := by omega
                                                                                                      rw [heq]
                                                                                                      exact cl_w49 ⟨n - 22450, hr⟩
                                                                                                    ·
                                                                                                      by_cases h50 : n < 22550
                                                                                                      · have hr : n - 22500 < 50 := by omega
                                                                                                        have heq : n = (n - 22500) + 22500 := by omega
                                                                                                        rw [heq]
                                                                                                        exact cl_w50 ⟨n - 22500, hr⟩
                                                                                                      ·
                                                                                                        by_cases h51 : n < 22600
                                                                                                        · have hr : n - 22550 < 50 := by omega
                                                                                                          have heq : n = (n - 22550) + 22550 := by omega
                                                                                                          rw [heq]
                                                                                                          exact cl_w51 ⟨n - 22550, hr⟩
                                                                                                        ·
                                                                                                          by_cases h52 : n < 22650
                                                                                                          · have hr : n - 22600 < 50 := by omega
                                                                                                            have heq : n = (n - 22600) + 22600 := by omega
                                                                                                            rw [heq]
                                                                                                            exact cl_w52 ⟨n - 22600, hr⟩
                                                                                                          ·
                                                                                                            by_cases h53 : n < 22700
                                                                                                            · have hr : n - 22650 < 50 := by omega
                                                                                                              have heq : n = (n - 22650) + 22650 := by omega
                                                                                                              rw [heq]
                                                                                                              exact cl_w53 ⟨n - 22650, hr⟩
                                                                                                            ·
                                                                                                              by_cases h54 : n < 22750
                                                                                                              · have hr : n - 22700 < 50 := by omega
                                                                                                                have heq : n = (n - 22700) + 22700 := by omega
                                                                                                                rw [heq]
                                                                                                                exact cl_w54 ⟨n - 22700, hr⟩
                                                                                                              ·
                                                                                                                by_cases h55 : n < 22800
                                                                                                                · have hr : n - 22750 < 50 := by omega
                                                                                                                  have heq : n = (n - 22750) + 22750 := by omega
                                                                                                                  rw [heq]
                                                                                                                  exact cl_w55 ⟨n - 22750, hr⟩
                                                                                                                ·
                                                                                                                  by_cases h56 : n < 22850
                                                                                                                  · have hr : n - 22800 < 50 := by omega
                                                                                                                    have heq : n = (n - 22800) + 22800 := by omega
                                                                                                                    rw [heq]
                                                                                                                    exact cl_w56 ⟨n - 22800, hr⟩
                                                                                                                  ·
                                                                                                                    by_cases h57 : n < 22900
                                                                                                                    · have hr : n - 22850 < 50 := by omega
                                                                                                                      have heq : n = (n - 22850) + 22850 := by omega
                                                                                                                      rw [heq]
                                                                                                                      exact cl_w57 ⟨n - 22850, hr⟩
                                                                                                                    ·
                                                                                                                      by_cases h58 : n < 22950
                                                                                                                      · have hr : n - 22900 < 50 := by omega
                                                                                                                        have heq : n = (n - 22900) + 22900 := by omega
                                                                                                                        rw [heq]
                                                                                                                        exact cl_w58 ⟨n - 22900, hr⟩
                                                                                                                      ·
                                                                                                                        by_cases h59 : n < 23000
                                                                                                                        · have hr : n - 22950 < 50 := by omega
                                                                                                                          have heq : n = (n - 22950) + 22950 := by omega
                                                                                                                          rw [heq]
                                                                                                                          exact cl_w59 ⟨n - 22950, hr⟩
                                                                                                                        ·
                                                                                                                          by_cases h60 : n < 23050
                                                                                                                          · have hr : n - 23000 < 50 := by omega
                                                                                                                            have heq : n = (n - 23000) + 23000 := by omega
                                                                                                                            rw [heq]
                                                                                                                            exact cl_w60 ⟨n - 23000, hr⟩
                                                                                                                          ·
                                                                                                                            by_cases h61 : n < 23100
                                                                                                                            · have hr : n - 23050 < 50 := by omega
                                                                                                                              have heq : n = (n - 23050) + 23050 := by omega
                                                                                                                              rw [heq]
                                                                                                                              exact cl_w61 ⟨n - 23050, hr⟩
                                                                                                                            ·
                                                                                                                              by_cases h62 : n < 23150
                                                                                                                              · have hr : n - 23100 < 50 := by omega
                                                                                                                                have heq : n = (n - 23100) + 23100 := by omega
                                                                                                                                rw [heq]
                                                                                                                                exact cl_w62 ⟨n - 23100, hr⟩
                                                                                                                              ·
                                                                                                                                by_cases h63 : n < 23200
                                                                                                                                · have hr : n - 23150 < 50 := by omega
                                                                                                                                  have heq : n = (n - 23150) + 23150 := by omega
                                                                                                                                  rw [heq]
                                                                                                                                  exact cl_w63 ⟨n - 23150, hr⟩
                                                                                                                                ·
                                                                                                                                  by_cases h64 : n < 23250
                                                                                                                                  · have hr : n - 23200 < 50 := by omega
                                                                                                                                    have heq : n = (n - 23200) + 23200 := by omega
                                                                                                                                    rw [heq]
                                                                                                                                    exact cl_w64 ⟨n - 23200, hr⟩
                                                                                                                                  ·
                                                                                                                                    by_cases h65 : n < 23300
                                                                                                                                    · have hr : n - 23250 < 50 := by omega
                                                                                                                                      have heq : n = (n - 23250) + 23250 := by omega
                                                                                                                                      rw [heq]
                                                                                                                                      exact cl_w65 ⟨n - 23250, hr⟩
                                                                                                                                    ·
                                                                                                                                      by_cases h66 : n < 23350
                                                                                                                                      · have hr : n - 23300 < 50 := by omega
                                                                                                                                        have heq : n = (n - 23300) + 23300 := by omega
                                                                                                                                        rw [heq]
                                                                                                                                        exact cl_w66 ⟨n - 23300, hr⟩
                                                                                                                                      ·
                                                                                                                                        by_cases h67 : n < 23400
                                                                                                                                        · have hr : n - 23350 < 50 := by omega
                                                                                                                                          have heq : n = (n - 23350) + 23350 := by omega
                                                                                                                                          rw [heq]
                                                                                                                                          exact cl_w67 ⟨n - 23350, hr⟩
                                                                                                                                        ·
                                                                                                                                          by_cases h68 : n < 23450
                                                                                                                                          · have hr : n - 23400 < 50 := by omega
                                                                                                                                            have heq : n = (n - 23400) + 23400 := by omega
                                                                                                                                            rw [heq]
                                                                                                                                            exact cl_w68 ⟨n - 23400, hr⟩
                                                                                                                                          ·
                                                                                                                                            by_cases h69 : n < 23500
                                                                                                                                            · have hr : n - 23450 < 50 := by omega
                                                                                                                                              have heq : n = (n - 23450) + 23450 := by omega
                                                                                                                                              rw [heq]
                                                                                                                                              exact cl_w69 ⟨n - 23450, hr⟩
                                                                                                                                            ·
                                                                                                                                              by_cases h70 : n < 23550
                                                                                                                                              · have hr : n - 23500 < 50 := by omega
                                                                                                                                                have heq : n = (n - 23500) + 23500 := by omega
                                                                                                                                                rw [heq]
                                                                                                                                                exact cl_w70 ⟨n - 23500, hr⟩
                                                                                                                                              ·
                                                                                                                                                by_cases h71 : n < 23600
                                                                                                                                                · have hr : n - 23550 < 50 := by omega
                                                                                                                                                  have heq : n = (n - 23550) + 23550 := by omega
                                                                                                                                                  rw [heq]
                                                                                                                                                  exact cl_w71 ⟨n - 23550, hr⟩
                                                                                                                                                ·
                                                                                                                                                  by_cases h72 : n < 23650
                                                                                                                                                  · have hr : n - 23600 < 50 := by omega
                                                                                                                                                    have heq : n = (n - 23600) + 23600 := by omega
                                                                                                                                                    rw [heq]
                                                                                                                                                    exact cl_w72 ⟨n - 23600, hr⟩
                                                                                                                                                  ·
                                                                                                                                                    by_cases h73 : n < 23700
                                                                                                                                                    · have hr : n - 23650 < 50 := by omega
                                                                                                                                                      have heq : n = (n - 23650) + 23650 := by omega
                                                                                                                                                      rw [heq]
                                                                                                                                                      exact cl_w73 ⟨n - 23650, hr⟩
                                                                                                                                                    ·
                                                                                                                                                      by_cases h74 : n < 23750
                                                                                                                                                      · have hr : n - 23700 < 50 := by omega
                                                                                                                                                        have heq : n = (n - 23700) + 23700 := by omega
                                                                                                                                                        rw [heq]
                                                                                                                                                        exact cl_w74 ⟨n - 23700, hr⟩
                                                                                                                                                      ·
                                                                                                                                                        by_cases h75 : n < 23800
                                                                                                                                                        · have hr : n - 23750 < 50 := by omega
                                                                                                                                                          have heq : n = (n - 23750) + 23750 := by omega
                                                                                                                                                          rw [heq]
                                                                                                                                                          exact cl_w75 ⟨n - 23750, hr⟩
                                                                                                                                                        ·
                                                                                                                                                          by_cases h76 : n < 23850
                                                                                                                                                          · have hr : n - 23800 < 50 := by omega
                                                                                                                                                            have heq : n = (n - 23800) + 23800 := by omega
                                                                                                                                                            rw [heq]
                                                                                                                                                            exact cl_w76 ⟨n - 23800, hr⟩
                                                                                                                                                          ·
                                                                                                                                                            by_cases h77 : n < 23900
                                                                                                                                                            · have hr : n - 23850 < 50 := by omega
                                                                                                                                                              have heq : n = (n - 23850) + 23850 := by omega
                                                                                                                                                              rw [heq]
                                                                                                                                                              exact cl_w77 ⟨n - 23850, hr⟩
                                                                                                                                                            ·
                                                                                                                                                              by_cases h78 : n < 23950
                                                                                                                                                              · have hr : n - 23900 < 50 := by omega
                                                                                                                                                                have heq : n = (n - 23900) + 23900 := by omega
                                                                                                                                                                rw [heq]
                                                                                                                                                                exact cl_w78 ⟨n - 23900, hr⟩
                                                                                                                                                              ·
                                                                                                                                                                by_cases h79 : n < 24000
                                                                                                                                                                · have hr : n - 23950 < 50 := by omega
                                                                                                                                                                  have heq : n = (n - 23950) + 23950 := by omega
                                                                                                                                                                  rw [heq]
                                                                                                                                                                  exact cl_w79 ⟨n - 23950, hr⟩
                                                                                                                                                                ·
                                                                                                                                                                  by_cases h80 : n < 24050
                                                                                                                                                                  · have hr : n - 24000 < 50 := by omega
                                                                                                                                                                    have heq : n = (n - 24000) + 24000 := by omega
                                                                                                                                                                    rw [heq]
                                                                                                                                                                    exact cl_w80 ⟨n - 24000, hr⟩
                                                                                                                                                                  ·
                                                                                                                                                                    by_cases h81 : n < 24100
                                                                                                                                                                    · have hr : n - 24050 < 50 := by omega
                                                                                                                                                                      have heq : n = (n - 24050) + 24050 := by omega
                                                                                                                                                                      rw [heq]
                                                                                                                                                                      exact cl_w81 ⟨n - 24050, hr⟩
                                                                                                                                                                    ·
                                                                                                                                                                      by_cases h82 : n < 24150
                                                                                                                                                                      · have hr : n - 24100 < 50 := by omega
                                                                                                                                                                        have heq : n = (n - 24100) + 24100 := by omega
                                                                                                                                                                        rw [heq]
                                                                                                                                                                        exact cl_w82 ⟨n - 24100, hr⟩
                                                                                                                                                                      ·
                                                                                                                                                                        by_cases h83 : n < 24200
                                                                                                                                                                        · have hr : n - 24150 < 50 := by omega
                                                                                                                                                                          have heq : n = (n - 24150) + 24150 := by omega
                                                                                                                                                                          rw [heq]
                                                                                                                                                                          exact cl_w83 ⟨n - 24150, hr⟩
                                                                                                                                                                        ·
                                                                                                                                                                          by_cases h84 : n < 24250
                                                                                                                                                                          · have hr : n - 24200 < 50 := by omega
                                                                                                                                                                            have heq : n = (n - 24200) + 24200 := by omega
                                                                                                                                                                            rw [heq]
                                                                                                                                                                            exact cl_w84 ⟨n - 24200, hr⟩
                                                                                                                                                                          ·
                                                                                                                                                                            by_cases h85 : n < 24300
                                                                                                                                                                            · have hr : n - 24250 < 50 := by omega
                                                                                                                                                                              have heq : n = (n - 24250) + 24250 := by omega
                                                                                                                                                                              rw [heq]
                                                                                                                                                                              exact cl_w85 ⟨n - 24250, hr⟩
                                                                                                                                                                            ·
                                                                                                                                                                              by_cases h86 : n < 24350
                                                                                                                                                                              · have hr : n - 24300 < 50 := by omega
                                                                                                                                                                                have heq : n = (n - 24300) + 24300 := by omega
                                                                                                                                                                                rw [heq]
                                                                                                                                                                                exact cl_w86 ⟨n - 24300, hr⟩
                                                                                                                                                                              ·
                                                                                                                                                                                by_cases h87 : n < 24400
                                                                                                                                                                                · have hr : n - 24350 < 50 := by omega
                                                                                                                                                                                  have heq : n = (n - 24350) + 24350 := by omega
                                                                                                                                                                                  rw [heq]
                                                                                                                                                                                  exact cl_w87 ⟨n - 24350, hr⟩
                                                                                                                                                                                ·
                                                                                                                                                                                  by_cases h88 : n < 24450
                                                                                                                                                                                  · have hr : n - 24400 < 50 := by omega
                                                                                                                                                                                    have heq : n = (n - 24400) + 24400 := by omega
                                                                                                                                                                                    rw [heq]
                                                                                                                                                                                    exact cl_w88 ⟨n - 24400, hr⟩
                                                                                                                                                                                  ·
                                                                                                                                                                                    by_cases h89 : n < 24500
                                                                                                                                                                                    · have hr : n - 24450 < 50 := by omega
                                                                                                                                                                                      have heq : n = (n - 24450) + 24450 := by omega
                                                                                                                                                                                      rw [heq]
                                                                                                                                                                                      exact cl_w89 ⟨n - 24450, hr⟩
                                                                                                                                                                                    ·
                                                                                                                                                                                      by_cases h90 : n < 24550
                                                                                                                                                                                      · have hr : n - 24500 < 50 := by omega
                                                                                                                                                                                        have heq : n = (n - 24500) + 24500 := by omega
                                                                                                                                                                                        rw [heq]
                                                                                                                                                                                        exact cl_w90 ⟨n - 24500, hr⟩
                                                                                                                                                                                      ·
                                                                                                                                                                                        by_cases h91 : n < 24600
                                                                                                                                                                                        · have hr : n - 24550 < 50 := by omega
                                                                                                                                                                                          have heq : n = (n - 24550) + 24550 := by omega
                                                                                                                                                                                          rw [heq]
                                                                                                                                                                                          exact cl_w91 ⟨n - 24550, hr⟩
                                                                                                                                                                                        ·
                                                                                                                                                                                          by_cases h92 : n < 24650
                                                                                                                                                                                          · have hr : n - 24600 < 50 := by omega
                                                                                                                                                                                            have heq : n = (n - 24600) + 24600 := by omega
                                                                                                                                                                                            rw [heq]
                                                                                                                                                                                            exact cl_w92 ⟨n - 24600, hr⟩
                                                                                                                                                                                          ·
                                                                                                                                                                                            by_cases h93 : n < 24700
                                                                                                                                                                                            · have hr : n - 24650 < 50 := by omega
                                                                                                                                                                                              have heq : n = (n - 24650) + 24650 := by omega
                                                                                                                                                                                              rw [heq]
                                                                                                                                                                                              exact cl_w93 ⟨n - 24650, hr⟩
                                                                                                                                                                                            ·
                                                                                                                                                                                              by_cases h94 : n < 24750
                                                                                                                                                                                              · have hr : n - 24700 < 50 := by omega
                                                                                                                                                                                                have heq : n = (n - 24700) + 24700 := by omega
                                                                                                                                                                                                rw [heq]
                                                                                                                                                                                                exact cl_w94 ⟨n - 24700, hr⟩
                                                                                                                                                                                              ·
                                                                                                                                                                                                by_cases h95 : n < 24800
                                                                                                                                                                                                · have hr : n - 24750 < 50 := by omega
                                                                                                                                                                                                  have heq : n = (n - 24750) + 24750 := by omega
                                                                                                                                                                                                  rw [heq]
                                                                                                                                                                                                  exact cl_w95 ⟨n - 24750, hr⟩
                                                                                                                                                                                                ·
                                                                                                                                                                                                  by_cases h96 : n < 24850
                                                                                                                                                                                                  · have hr : n - 24800 < 50 := by omega
                                                                                                                                                                                                    have heq : n = (n - 24800) + 24800 := by omega
                                                                                                                                                                                                    rw [heq]
                                                                                                                                                                                                    exact cl_w96 ⟨n - 24800, hr⟩
                                                                                                                                                                                                  ·
                                                                                                                                                                                                    by_cases h97 : n < 24900
                                                                                                                                                                                                    · have hr : n - 24850 < 50 := by omega
                                                                                                                                                                                                      have heq : n = (n - 24850) + 24850 := by omega
                                                                                                                                                                                                      rw [heq]
                                                                                                                                                                                                      exact cl_w97 ⟨n - 24850, hr⟩
                                                                                                                                                                                                    ·
                                                                                                                                                                                                      by_cases h98 : n < 24950
                                                                                                                                                                                                      · have hr : n - 24900 < 50 := by omega
                                                                                                                                                                                                        have heq : n = (n - 24900) + 24900 := by omega
                                                                                                                                                                                                        rw [heq]
                                                                                                                                                                                                        exact cl_w98 ⟨n - 24900, hr⟩
                                                                                                                                                                                                      ·
                                                                                                                                                                                                        have hr : n - 24950 < 50 := by omega
                                                                                                                                                                                                        have heq : n = (n - 24950) + 24950 := by omega
                                                                                                                                                                                                        rw [heq]
                                                                                                                                                                                                        exact cl_w99 ⟨n - 24950, hr⟩

theorem densSupG_lt_range : ∀ n, 20000 ≤ n → n < 25000 → densSupG n < 2 ^ 1771 := by
  intro n hlo hhi
  by_cases h0 : n < 20050
  · have hr : n - 20000 < 50 := by omega
    have heq : n = (n - 20000) + 20000 := by omega
    rw [heq]
    exact bd_w0 ⟨n - 20000, hr⟩
  ·
    by_cases h1 : n < 20100
    · have hr : n - 20050 < 50 := by omega
      have heq : n = (n - 20050) + 20050 := by omega
      rw [heq]
      exact bd_w1 ⟨n - 20050, hr⟩
    ·
      by_cases h2 : n < 20150
      · have hr : n - 20100 < 50 := by omega
        have heq : n = (n - 20100) + 20100 := by omega
        rw [heq]
        exact bd_w2 ⟨n - 20100, hr⟩
      ·
        by_cases h3 : n < 20200
        · have hr : n - 20150 < 50 := by omega
          have heq : n = (n - 20150) + 20150 := by omega
          rw [heq]
          exact bd_w3 ⟨n - 20150, hr⟩
        ·
          by_cases h4 : n < 20250
          · have hr : n - 20200 < 50 := by omega
            have heq : n = (n - 20200) + 20200 := by omega
            rw [heq]
            exact bd_w4 ⟨n - 20200, hr⟩
          ·
            by_cases h5 : n < 20300
            · have hr : n - 20250 < 50 := by omega
              have heq : n = (n - 20250) + 20250 := by omega
              rw [heq]
              exact bd_w5 ⟨n - 20250, hr⟩
            ·
              by_cases h6 : n < 20350
              · have hr : n - 20300 < 50 := by omega
                have heq : n = (n - 20300) + 20300 := by omega
                rw [heq]
                exact bd_w6 ⟨n - 20300, hr⟩
              ·
                by_cases h7 : n < 20400
                · have hr : n - 20350 < 50 := by omega
                  have heq : n = (n - 20350) + 20350 := by omega
                  rw [heq]
                  exact bd_w7 ⟨n - 20350, hr⟩
                ·
                  by_cases h8 : n < 20450
                  · have hr : n - 20400 < 50 := by omega
                    have heq : n = (n - 20400) + 20400 := by omega
                    rw [heq]
                    exact bd_w8 ⟨n - 20400, hr⟩
                  ·
                    by_cases h9 : n < 20500
                    · have hr : n - 20450 < 50 := by omega
                      have heq : n = (n - 20450) + 20450 := by omega
                      rw [heq]
                      exact bd_w9 ⟨n - 20450, hr⟩
                    ·
                      by_cases h10 : n < 20550
                      · have hr : n - 20500 < 50 := by omega
                        have heq : n = (n - 20500) + 20500 := by omega
                        rw [heq]
                        exact bd_w10 ⟨n - 20500, hr⟩
                      ·
                        by_cases h11 : n < 20600
                        · have hr : n - 20550 < 50 := by omega
                          have heq : n = (n - 20550) + 20550 := by omega
                          rw [heq]
                          exact bd_w11 ⟨n - 20550, hr⟩
                        ·
                          by_cases h12 : n < 20650
                          · have hr : n - 20600 < 50 := by omega
                            have heq : n = (n - 20600) + 20600 := by omega
                            rw [heq]
                            exact bd_w12 ⟨n - 20600, hr⟩
                          ·
                            by_cases h13 : n < 20700
                            · have hr : n - 20650 < 50 := by omega
                              have heq : n = (n - 20650) + 20650 := by omega
                              rw [heq]
                              exact bd_w13 ⟨n - 20650, hr⟩
                            ·
                              by_cases h14 : n < 20750
                              · have hr : n - 20700 < 50 := by omega
                                have heq : n = (n - 20700) + 20700 := by omega
                                rw [heq]
                                exact bd_w14 ⟨n - 20700, hr⟩
                              ·
                                by_cases h15 : n < 20800
                                · have hr : n - 20750 < 50 := by omega
                                  have heq : n = (n - 20750) + 20750 := by omega
                                  rw [heq]
                                  exact bd_w15 ⟨n - 20750, hr⟩
                                ·
                                  by_cases h16 : n < 20850
                                  · have hr : n - 20800 < 50 := by omega
                                    have heq : n = (n - 20800) + 20800 := by omega
                                    rw [heq]
                                    exact bd_w16 ⟨n - 20800, hr⟩
                                  ·
                                    by_cases h17 : n < 20900
                                    · have hr : n - 20850 < 50 := by omega
                                      have heq : n = (n - 20850) + 20850 := by omega
                                      rw [heq]
                                      exact bd_w17 ⟨n - 20850, hr⟩
                                    ·
                                      by_cases h18 : n < 20950
                                      · have hr : n - 20900 < 50 := by omega
                                        have heq : n = (n - 20900) + 20900 := by omega
                                        rw [heq]
                                        exact bd_w18 ⟨n - 20900, hr⟩
                                      ·
                                        by_cases h19 : n < 21000
                                        · have hr : n - 20950 < 50 := by omega
                                          have heq : n = (n - 20950) + 20950 := by omega
                                          rw [heq]
                                          exact bd_w19 ⟨n - 20950, hr⟩
                                        ·
                                          by_cases h20 : n < 21050
                                          · have hr : n - 21000 < 50 := by omega
                                            have heq : n = (n - 21000) + 21000 := by omega
                                            rw [heq]
                                            exact bd_w20 ⟨n - 21000, hr⟩
                                          ·
                                            by_cases h21 : n < 21100
                                            · have hr : n - 21050 < 50 := by omega
                                              have heq : n = (n - 21050) + 21050 := by omega
                                              rw [heq]
                                              exact bd_w21 ⟨n - 21050, hr⟩
                                            ·
                                              by_cases h22 : n < 21150
                                              · have hr : n - 21100 < 50 := by omega
                                                have heq : n = (n - 21100) + 21100 := by omega
                                                rw [heq]
                                                exact bd_w22 ⟨n - 21100, hr⟩
                                              ·
                                                by_cases h23 : n < 21200
                                                · have hr : n - 21150 < 50 := by omega
                                                  have heq : n = (n - 21150) + 21150 := by omega
                                                  rw [heq]
                                                  exact bd_w23 ⟨n - 21150, hr⟩
                                                ·
                                                  by_cases h24 : n < 21250
                                                  · have hr : n - 21200 < 50 := by omega
                                                    have heq : n = (n - 21200) + 21200 := by omega
                                                    rw [heq]
                                                    exact bd_w24 ⟨n - 21200, hr⟩
                                                  ·
                                                    by_cases h25 : n < 21300
                                                    · have hr : n - 21250 < 50 := by omega
                                                      have heq : n = (n - 21250) + 21250 := by omega
                                                      rw [heq]
                                                      exact bd_w25 ⟨n - 21250, hr⟩
                                                    ·
                                                      by_cases h26 : n < 21350
                                                      · have hr : n - 21300 < 50 := by omega
                                                        have heq : n = (n - 21300) + 21300 := by omega
                                                        rw [heq]
                                                        exact bd_w26 ⟨n - 21300, hr⟩
                                                      ·
                                                        by_cases h27 : n < 21400
                                                        · have hr : n - 21350 < 50 := by omega
                                                          have heq : n = (n - 21350) + 21350 := by omega
                                                          rw [heq]
                                                          exact bd_w27 ⟨n - 21350, hr⟩
                                                        ·
                                                          by_cases h28 : n < 21450
                                                          · have hr : n - 21400 < 50 := by omega
                                                            have heq : n = (n - 21400) + 21400 := by omega
                                                            rw [heq]
                                                            exact bd_w28 ⟨n - 21400, hr⟩
                                                          ·
                                                            by_cases h29 : n < 21500
                                                            · have hr : n - 21450 < 50 := by omega
                                                              have heq : n = (n - 21450) + 21450 := by omega
                                                              rw [heq]
                                                              exact bd_w29 ⟨n - 21450, hr⟩
                                                            ·
                                                              by_cases h30 : n < 21550
                                                              · have hr : n - 21500 < 50 := by omega
                                                                have heq : n = (n - 21500) + 21500 := by omega
                                                                rw [heq]
                                                                exact bd_w30 ⟨n - 21500, hr⟩
                                                              ·
                                                                by_cases h31 : n < 21600
                                                                · have hr : n - 21550 < 50 := by omega
                                                                  have heq : n = (n - 21550) + 21550 := by omega
                                                                  rw [heq]
                                                                  exact bd_w31 ⟨n - 21550, hr⟩
                                                                ·
                                                                  by_cases h32 : n < 21650
                                                                  · have hr : n - 21600 < 50 := by omega
                                                                    have heq : n = (n - 21600) + 21600 := by omega
                                                                    rw [heq]
                                                                    exact bd_w32 ⟨n - 21600, hr⟩
                                                                  ·
                                                                    by_cases h33 : n < 21700
                                                                    · have hr : n - 21650 < 50 := by omega
                                                                      have heq : n = (n - 21650) + 21650 := by omega
                                                                      rw [heq]
                                                                      exact bd_w33 ⟨n - 21650, hr⟩
                                                                    ·
                                                                      by_cases h34 : n < 21750
                                                                      · have hr : n - 21700 < 50 := by omega
                                                                        have heq : n = (n - 21700) + 21700 := by omega
                                                                        rw [heq]
                                                                        exact bd_w34 ⟨n - 21700, hr⟩
                                                                      ·
                                                                        by_cases h35 : n < 21800
                                                                        · have hr : n - 21750 < 50 := by omega
                                                                          have heq : n = (n - 21750) + 21750 := by omega
                                                                          rw [heq]
                                                                          exact bd_w35 ⟨n - 21750, hr⟩
                                                                        ·
                                                                          by_cases h36 : n < 21850
                                                                          · have hr : n - 21800 < 50 := by omega
                                                                            have heq : n = (n - 21800) + 21800 := by omega
                                                                            rw [heq]
                                                                            exact bd_w36 ⟨n - 21800, hr⟩
                                                                          ·
                                                                            by_cases h37 : n < 21900
                                                                            · have hr : n - 21850 < 50 := by omega
                                                                              have heq : n = (n - 21850) + 21850 := by omega
                                                                              rw [heq]
                                                                              exact bd_w37 ⟨n - 21850, hr⟩
                                                                            ·
                                                                              by_cases h38 : n < 21950
                                                                              · have hr : n - 21900 < 50 := by omega
                                                                                have heq : n = (n - 21900) + 21900 := by omega
                                                                                rw [heq]
                                                                                exact bd_w38 ⟨n - 21900, hr⟩
                                                                              ·
                                                                                by_cases h39 : n < 22000
                                                                                · have hr : n - 21950 < 50 := by omega
                                                                                  have heq : n = (n - 21950) + 21950 := by omega
                                                                                  rw [heq]
                                                                                  exact bd_w39 ⟨n - 21950, hr⟩
                                                                                ·
                                                                                  by_cases h40 : n < 22050
                                                                                  · have hr : n - 22000 < 50 := by omega
                                                                                    have heq : n = (n - 22000) + 22000 := by omega
                                                                                    rw [heq]
                                                                                    exact bd_w40 ⟨n - 22000, hr⟩
                                                                                  ·
                                                                                    by_cases h41 : n < 22100
                                                                                    · have hr : n - 22050 < 50 := by omega
                                                                                      have heq : n = (n - 22050) + 22050 := by omega
                                                                                      rw [heq]
                                                                                      exact bd_w41 ⟨n - 22050, hr⟩
                                                                                    ·
                                                                                      by_cases h42 : n < 22150
                                                                                      · have hr : n - 22100 < 50 := by omega
                                                                                        have heq : n = (n - 22100) + 22100 := by omega
                                                                                        rw [heq]
                                                                                        exact bd_w42 ⟨n - 22100, hr⟩
                                                                                      ·
                                                                                        by_cases h43 : n < 22200
                                                                                        · have hr : n - 22150 < 50 := by omega
                                                                                          have heq : n = (n - 22150) + 22150 := by omega
                                                                                          rw [heq]
                                                                                          exact bd_w43 ⟨n - 22150, hr⟩
                                                                                        ·
                                                                                          by_cases h44 : n < 22250
                                                                                          · have hr : n - 22200 < 50 := by omega
                                                                                            have heq : n = (n - 22200) + 22200 := by omega
                                                                                            rw [heq]
                                                                                            exact bd_w44 ⟨n - 22200, hr⟩
                                                                                          ·
                                                                                            by_cases h45 : n < 22300
                                                                                            · have hr : n - 22250 < 50 := by omega
                                                                                              have heq : n = (n - 22250) + 22250 := by omega
                                                                                              rw [heq]
                                                                                              exact bd_w45 ⟨n - 22250, hr⟩
                                                                                            ·
                                                                                              by_cases h46 : n < 22350
                                                                                              · have hr : n - 22300 < 50 := by omega
                                                                                                have heq : n = (n - 22300) + 22300 := by omega
                                                                                                rw [heq]
                                                                                                exact bd_w46 ⟨n - 22300, hr⟩
                                                                                              ·
                                                                                                by_cases h47 : n < 22400
                                                                                                · have hr : n - 22350 < 50 := by omega
                                                                                                  have heq : n = (n - 22350) + 22350 := by omega
                                                                                                  rw [heq]
                                                                                                  exact bd_w47 ⟨n - 22350, hr⟩
                                                                                                ·
                                                                                                  by_cases h48 : n < 22450
                                                                                                  · have hr : n - 22400 < 50 := by omega
                                                                                                    have heq : n = (n - 22400) + 22400 := by omega
                                                                                                    rw [heq]
                                                                                                    exact bd_w48 ⟨n - 22400, hr⟩
                                                                                                  ·
                                                                                                    by_cases h49 : n < 22500
                                                                                                    · have hr : n - 22450 < 50 := by omega
                                                                                                      have heq : n = (n - 22450) + 22450 := by omega
                                                                                                      rw [heq]
                                                                                                      exact bd_w49 ⟨n - 22450, hr⟩
                                                                                                    ·
                                                                                                      by_cases h50 : n < 22550
                                                                                                      · have hr : n - 22500 < 50 := by omega
                                                                                                        have heq : n = (n - 22500) + 22500 := by omega
                                                                                                        rw [heq]
                                                                                                        exact bd_w50 ⟨n - 22500, hr⟩
                                                                                                      ·
                                                                                                        by_cases h51 : n < 22600
                                                                                                        · have hr : n - 22550 < 50 := by omega
                                                                                                          have heq : n = (n - 22550) + 22550 := by omega
                                                                                                          rw [heq]
                                                                                                          exact bd_w51 ⟨n - 22550, hr⟩
                                                                                                        ·
                                                                                                          by_cases h52 : n < 22650
                                                                                                          · have hr : n - 22600 < 50 := by omega
                                                                                                            have heq : n = (n - 22600) + 22600 := by omega
                                                                                                            rw [heq]
                                                                                                            exact bd_w52 ⟨n - 22600, hr⟩
                                                                                                          ·
                                                                                                            by_cases h53 : n < 22700
                                                                                                            · have hr : n - 22650 < 50 := by omega
                                                                                                              have heq : n = (n - 22650) + 22650 := by omega
                                                                                                              rw [heq]
                                                                                                              exact bd_w53 ⟨n - 22650, hr⟩
                                                                                                            ·
                                                                                                              by_cases h54 : n < 22750
                                                                                                              · have hr : n - 22700 < 50 := by omega
                                                                                                                have heq : n = (n - 22700) + 22700 := by omega
                                                                                                                rw [heq]
                                                                                                                exact bd_w54 ⟨n - 22700, hr⟩
                                                                                                              ·
                                                                                                                by_cases h55 : n < 22800
                                                                                                                · have hr : n - 22750 < 50 := by omega
                                                                                                                  have heq : n = (n - 22750) + 22750 := by omega
                                                                                                                  rw [heq]
                                                                                                                  exact bd_w55 ⟨n - 22750, hr⟩
                                                                                                                ·
                                                                                                                  by_cases h56 : n < 22850
                                                                                                                  · have hr : n - 22800 < 50 := by omega
                                                                                                                    have heq : n = (n - 22800) + 22800 := by omega
                                                                                                                    rw [heq]
                                                                                                                    exact bd_w56 ⟨n - 22800, hr⟩
                                                                                                                  ·
                                                                                                                    by_cases h57 : n < 22900
                                                                                                                    · have hr : n - 22850 < 50 := by omega
                                                                                                                      have heq : n = (n - 22850) + 22850 := by omega
                                                                                                                      rw [heq]
                                                                                                                      exact bd_w57 ⟨n - 22850, hr⟩
                                                                                                                    ·
                                                                                                                      by_cases h58 : n < 22950
                                                                                                                      · have hr : n - 22900 < 50 := by omega
                                                                                                                        have heq : n = (n - 22900) + 22900 := by omega
                                                                                                                        rw [heq]
                                                                                                                        exact bd_w58 ⟨n - 22900, hr⟩
                                                                                                                      ·
                                                                                                                        by_cases h59 : n < 23000
                                                                                                                        · have hr : n - 22950 < 50 := by omega
                                                                                                                          have heq : n = (n - 22950) + 22950 := by omega
                                                                                                                          rw [heq]
                                                                                                                          exact bd_w59 ⟨n - 22950, hr⟩
                                                                                                                        ·
                                                                                                                          by_cases h60 : n < 23050
                                                                                                                          · have hr : n - 23000 < 50 := by omega
                                                                                                                            have heq : n = (n - 23000) + 23000 := by omega
                                                                                                                            rw [heq]
                                                                                                                            exact bd_w60 ⟨n - 23000, hr⟩
                                                                                                                          ·
                                                                                                                            by_cases h61 : n < 23100
                                                                                                                            · have hr : n - 23050 < 50 := by omega
                                                                                                                              have heq : n = (n - 23050) + 23050 := by omega
                                                                                                                              rw [heq]
                                                                                                                              exact bd_w61 ⟨n - 23050, hr⟩
                                                                                                                            ·
                                                                                                                              by_cases h62 : n < 23150
                                                                                                                              · have hr : n - 23100 < 50 := by omega
                                                                                                                                have heq : n = (n - 23100) + 23100 := by omega
                                                                                                                                rw [heq]
                                                                                                                                exact bd_w62 ⟨n - 23100, hr⟩
                                                                                                                              ·
                                                                                                                                by_cases h63 : n < 23200
                                                                                                                                · have hr : n - 23150 < 50 := by omega
                                                                                                                                  have heq : n = (n - 23150) + 23150 := by omega
                                                                                                                                  rw [heq]
                                                                                                                                  exact bd_w63 ⟨n - 23150, hr⟩
                                                                                                                                ·
                                                                                                                                  by_cases h64 : n < 23250
                                                                                                                                  · have hr : n - 23200 < 50 := by omega
                                                                                                                                    have heq : n = (n - 23200) + 23200 := by omega
                                                                                                                                    rw [heq]
                                                                                                                                    exact bd_w64 ⟨n - 23200, hr⟩
                                                                                                                                  ·
                                                                                                                                    by_cases h65 : n < 23300
                                                                                                                                    · have hr : n - 23250 < 50 := by omega
                                                                                                                                      have heq : n = (n - 23250) + 23250 := by omega
                                                                                                                                      rw [heq]
                                                                                                                                      exact bd_w65 ⟨n - 23250, hr⟩
                                                                                                                                    ·
                                                                                                                                      by_cases h66 : n < 23350
                                                                                                                                      · have hr : n - 23300 < 50 := by omega
                                                                                                                                        have heq : n = (n - 23300) + 23300 := by omega
                                                                                                                                        rw [heq]
                                                                                                                                        exact bd_w66 ⟨n - 23300, hr⟩
                                                                                                                                      ·
                                                                                                                                        by_cases h67 : n < 23400
                                                                                                                                        · have hr : n - 23350 < 50 := by omega
                                                                                                                                          have heq : n = (n - 23350) + 23350 := by omega
                                                                                                                                          rw [heq]
                                                                                                                                          exact bd_w67 ⟨n - 23350, hr⟩
                                                                                                                                        ·
                                                                                                                                          by_cases h68 : n < 23450
                                                                                                                                          · have hr : n - 23400 < 50 := by omega
                                                                                                                                            have heq : n = (n - 23400) + 23400 := by omega
                                                                                                                                            rw [heq]
                                                                                                                                            exact bd_w68 ⟨n - 23400, hr⟩
                                                                                                                                          ·
                                                                                                                                            by_cases h69 : n < 23500
                                                                                                                                            · have hr : n - 23450 < 50 := by omega
                                                                                                                                              have heq : n = (n - 23450) + 23450 := by omega
                                                                                                                                              rw [heq]
                                                                                                                                              exact bd_w69 ⟨n - 23450, hr⟩
                                                                                                                                            ·
                                                                                                                                              by_cases h70 : n < 23550
                                                                                                                                              · have hr : n - 23500 < 50 := by omega
                                                                                                                                                have heq : n = (n - 23500) + 23500 := by omega
                                                                                                                                                rw [heq]
                                                                                                                                                exact bd_w70 ⟨n - 23500, hr⟩
                                                                                                                                              ·
                                                                                                                                                by_cases h71 : n < 23600
                                                                                                                                                · have hr : n - 23550 < 50 := by omega
                                                                                                                                                  have heq : n = (n - 23550) + 23550 := by omega
                                                                                                                                                  rw [heq]
                                                                                                                                                  exact bd_w71 ⟨n - 23550, hr⟩
                                                                                                                                                ·
                                                                                                                                                  by_cases h72 : n < 23650
                                                                                                                                                  · have hr : n - 23600 < 50 := by omega
                                                                                                                                                    have heq : n = (n - 23600) + 23600 := by omega
                                                                                                                                                    rw [heq]
                                                                                                                                                    exact bd_w72 ⟨n - 23600, hr⟩
                                                                                                                                                  ·
                                                                                                                                                    by_cases h73 : n < 23700
                                                                                                                                                    · have hr : n - 23650 < 50 := by omega
                                                                                                                                                      have heq : n = (n - 23650) + 23650 := by omega
                                                                                                                                                      rw [heq]
                                                                                                                                                      exact bd_w73 ⟨n - 23650, hr⟩
                                                                                                                                                    ·
                                                                                                                                                      by_cases h74 : n < 23750
                                                                                                                                                      · have hr : n - 23700 < 50 := by omega
                                                                                                                                                        have heq : n = (n - 23700) + 23700 := by omega
                                                                                                                                                        rw [heq]
                                                                                                                                                        exact bd_w74 ⟨n - 23700, hr⟩
                                                                                                                                                      ·
                                                                                                                                                        by_cases h75 : n < 23800
                                                                                                                                                        · have hr : n - 23750 < 50 := by omega
                                                                                                                                                          have heq : n = (n - 23750) + 23750 := by omega
                                                                                                                                                          rw [heq]
                                                                                                                                                          exact bd_w75 ⟨n - 23750, hr⟩
                                                                                                                                                        ·
                                                                                                                                                          by_cases h76 : n < 23850
                                                                                                                                                          · have hr : n - 23800 < 50 := by omega
                                                                                                                                                            have heq : n = (n - 23800) + 23800 := by omega
                                                                                                                                                            rw [heq]
                                                                                                                                                            exact bd_w76 ⟨n - 23800, hr⟩
                                                                                                                                                          ·
                                                                                                                                                            by_cases h77 : n < 23900
                                                                                                                                                            · have hr : n - 23850 < 50 := by omega
                                                                                                                                                              have heq : n = (n - 23850) + 23850 := by omega
                                                                                                                                                              rw [heq]
                                                                                                                                                              exact bd_w77 ⟨n - 23850, hr⟩
                                                                                                                                                            ·
                                                                                                                                                              by_cases h78 : n < 23950
                                                                                                                                                              · have hr : n - 23900 < 50 := by omega
                                                                                                                                                                have heq : n = (n - 23900) + 23900 := by omega
                                                                                                                                                                rw [heq]
                                                                                                                                                                exact bd_w78 ⟨n - 23900, hr⟩
                                                                                                                                                              ·
                                                                                                                                                                by_cases h79 : n < 24000
                                                                                                                                                                · have hr : n - 23950 < 50 := by omega
                                                                                                                                                                  have heq : n = (n - 23950) + 23950 := by omega
                                                                                                                                                                  rw [heq]
                                                                                                                                                                  exact bd_w79 ⟨n - 23950, hr⟩
                                                                                                                                                                ·
                                                                                                                                                                  by_cases h80 : n < 24050
                                                                                                                                                                  · have hr : n - 24000 < 50 := by omega
                                                                                                                                                                    have heq : n = (n - 24000) + 24000 := by omega
                                                                                                                                                                    rw [heq]
                                                                                                                                                                    exact bd_w80 ⟨n - 24000, hr⟩
                                                                                                                                                                  ·
                                                                                                                                                                    by_cases h81 : n < 24100
                                                                                                                                                                    · have hr : n - 24050 < 50 := by omega
                                                                                                                                                                      have heq : n = (n - 24050) + 24050 := by omega
                                                                                                                                                                      rw [heq]
                                                                                                                                                                      exact bd_w81 ⟨n - 24050, hr⟩
                                                                                                                                                                    ·
                                                                                                                                                                      by_cases h82 : n < 24150
                                                                                                                                                                      · have hr : n - 24100 < 50 := by omega
                                                                                                                                                                        have heq : n = (n - 24100) + 24100 := by omega
                                                                                                                                                                        rw [heq]
                                                                                                                                                                        exact bd_w82 ⟨n - 24100, hr⟩
                                                                                                                                                                      ·
                                                                                                                                                                        by_cases h83 : n < 24200
                                                                                                                                                                        · have hr : n - 24150 < 50 := by omega
                                                                                                                                                                          have heq : n = (n - 24150) + 24150 := by omega
                                                                                                                                                                          rw [heq]
                                                                                                                                                                          exact bd_w83 ⟨n - 24150, hr⟩
                                                                                                                                                                        ·
                                                                                                                                                                          by_cases h84 : n < 24250
                                                                                                                                                                          · have hr : n - 24200 < 50 := by omega
                                                                                                                                                                            have heq : n = (n - 24200) + 24200 := by omega
                                                                                                                                                                            rw [heq]
                                                                                                                                                                            exact bd_w84 ⟨n - 24200, hr⟩
                                                                                                                                                                          ·
                                                                                                                                                                            by_cases h85 : n < 24300
                                                                                                                                                                            · have hr : n - 24250 < 50 := by omega
                                                                                                                                                                              have heq : n = (n - 24250) + 24250 := by omega
                                                                                                                                                                              rw [heq]
                                                                                                                                                                              exact bd_w85 ⟨n - 24250, hr⟩
                                                                                                                                                                            ·
                                                                                                                                                                              by_cases h86 : n < 24350
                                                                                                                                                                              · have hr : n - 24300 < 50 := by omega
                                                                                                                                                                                have heq : n = (n - 24300) + 24300 := by omega
                                                                                                                                                                                rw [heq]
                                                                                                                                                                                exact bd_w86 ⟨n - 24300, hr⟩
                                                                                                                                                                              ·
                                                                                                                                                                                by_cases h87 : n < 24400
                                                                                                                                                                                · have hr : n - 24350 < 50 := by omega
                                                                                                                                                                                  have heq : n = (n - 24350) + 24350 := by omega
                                                                                                                                                                                  rw [heq]
                                                                                                                                                                                  exact bd_w87 ⟨n - 24350, hr⟩
                                                                                                                                                                                ·
                                                                                                                                                                                  by_cases h88 : n < 24450
                                                                                                                                                                                  · have hr : n - 24400 < 50 := by omega
                                                                                                                                                                                    have heq : n = (n - 24400) + 24400 := by omega
                                                                                                                                                                                    rw [heq]
                                                                                                                                                                                    exact bd_w88 ⟨n - 24400, hr⟩
                                                                                                                                                                                  ·
                                                                                                                                                                                    by_cases h89 : n < 24500
                                                                                                                                                                                    · have hr : n - 24450 < 50 := by omega
                                                                                                                                                                                      have heq : n = (n - 24450) + 24450 := by omega
                                                                                                                                                                                      rw [heq]
                                                                                                                                                                                      exact bd_w89 ⟨n - 24450, hr⟩
                                                                                                                                                                                    ·
                                                                                                                                                                                      by_cases h90 : n < 24550
                                                                                                                                                                                      · have hr : n - 24500 < 50 := by omega
                                                                                                                                                                                        have heq : n = (n - 24500) + 24500 := by omega
                                                                                                                                                                                        rw [heq]
                                                                                                                                                                                        exact bd_w90 ⟨n - 24500, hr⟩
                                                                                                                                                                                      ·
                                                                                                                                                                                        by_cases h91 : n < 24600
                                                                                                                                                                                        · have hr : n - 24550 < 50 := by omega
                                                                                                                                                                                          have heq : n = (n - 24550) + 24550 := by omega
                                                                                                                                                                                          rw [heq]
                                                                                                                                                                                          exact bd_w91 ⟨n - 24550, hr⟩
                                                                                                                                                                                        ·
                                                                                                                                                                                          by_cases h92 : n < 24650
                                                                                                                                                                                          · have hr : n - 24600 < 50 := by omega
                                                                                                                                                                                            have heq : n = (n - 24600) + 24600 := by omega
                                                                                                                                                                                            rw [heq]
                                                                                                                                                                                            exact bd_w92 ⟨n - 24600, hr⟩
                                                                                                                                                                                          ·
                                                                                                                                                                                            by_cases h93 : n < 24700
                                                                                                                                                                                            · have hr : n - 24650 < 50 := by omega
                                                                                                                                                                                              have heq : n = (n - 24650) + 24650 := by omega
                                                                                                                                                                                              rw [heq]
                                                                                                                                                                                              exact bd_w93 ⟨n - 24650, hr⟩
                                                                                                                                                                                            ·
                                                                                                                                                                                              by_cases h94 : n < 24750
                                                                                                                                                                                              · have hr : n - 24700 < 50 := by omega
                                                                                                                                                                                                have heq : n = (n - 24700) + 24700 := by omega
                                                                                                                                                                                                rw [heq]
                                                                                                                                                                                                exact bd_w94 ⟨n - 24700, hr⟩
                                                                                                                                                                                              ·
                                                                                                                                                                                                by_cases h95 : n < 24800
                                                                                                                                                                                                · have hr : n - 24750 < 50 := by omega
                                                                                                                                                                                                  have heq : n = (n - 24750) + 24750 := by omega
                                                                                                                                                                                                  rw [heq]
                                                                                                                                                                                                  exact bd_w95 ⟨n - 24750, hr⟩
                                                                                                                                                                                                ·
                                                                                                                                                                                                  by_cases h96 : n < 24850
                                                                                                                                                                                                  · have hr : n - 24800 < 50 := by omega
                                                                                                                                                                                                    have heq : n = (n - 24800) + 24800 := by omega
                                                                                                                                                                                                    rw [heq]
                                                                                                                                                                                                    exact bd_w96 ⟨n - 24800, hr⟩
                                                                                                                                                                                                  ·
                                                                                                                                                                                                    by_cases h97 : n < 24900
                                                                                                                                                                                                    · have hr : n - 24850 < 50 := by omega
                                                                                                                                                                                                      have heq : n = (n - 24850) + 24850 := by omega
                                                                                                                                                                                                      rw [heq]
                                                                                                                                                                                                      exact bd_w97 ⟨n - 24850, hr⟩
                                                                                                                                                                                                    ·
                                                                                                                                                                                                      by_cases h98 : n < 24950
                                                                                                                                                                                                      · have hr : n - 24900 < 50 := by omega
                                                                                                                                                                                                        have heq : n = (n - 24900) + 24900 := by omega
                                                                                                                                                                                                        rw [heq]
                                                                                                                                                                                                        exact bd_w98 ⟨n - 24900, hr⟩
                                                                                                                                                                                                      ·
                                                                                                                                                                                                        have hr : n - 24950 < 50 := by omega
                                                                                                                                                                                                        have heq : n = (n - 24950) + 24950 := by omega
                                                                                                                                                                                                        rw [heq]
                                                                                                                                                                                                        exact bd_w99 ⟨n - 24950, hr⟩

end IntMul.Kappa.R8.Bit.Oppbank.CentBound4


