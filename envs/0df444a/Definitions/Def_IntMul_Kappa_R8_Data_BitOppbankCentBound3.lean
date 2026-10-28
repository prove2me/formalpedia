-- Prove2me | Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankCentBound3
-- name    : IntMul_Kappa_R8_Data_BitOppbankCentBound3
-- status  : Definition
-- author  : @Ethan Cheung Wang
-- created : 2026-10-28T19:48:38.926055+00:00
-- url     : https://prove2.me/theorems/7f504aca-5e01-4eda-9655-50f6f14b55ae
-- title:
--   HasCentre certificates dens nodes [15000,20000)
-- statement:
--   # Densified centre certificates, pack 3
--
--   For every densified node index $n$ with $15000\le n<20000$,
--   $$
--   \mathrm{centredStar}(\mathrm{densSupG}\,n,\mathrm{centF}\,n)=\mathsf{true},\quad
--   \mathrm{centF}\,n<23,\quad
--   \mathrm{densSupG}\,n < 2^{1771}.
--   $$
--   Proved by decide on Fin 50 windows (no native_decide).
-- source:
--   R8 BitOppbank AllDensCentred; jfstack_23 densified supports

-- CentBound pack 3: densified HasCentre certificates on n ∈ [15000, 20000)
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

namespace IntMul.Kappa.R8.Bit.Oppbank.CentBound3

private theorem cs_w0 : ∀ n : Fin 50, centredStar (densSupG (n.val + 15000)) (centF (n.val + 15000)) = true := by decide
private theorem cl_w0 : ∀ n : Fin 50, centF (n.val + 15000) < 23 := by decide
private theorem bd_w0 : ∀ n : Fin 50, densSupG (n.val + 15000) < 2 ^ 1771 := by decide
private theorem cs_w1 : ∀ n : Fin 50, centredStar (densSupG (n.val + 15050)) (centF (n.val + 15050)) = true := by decide
private theorem cl_w1 : ∀ n : Fin 50, centF (n.val + 15050) < 23 := by decide
private theorem bd_w1 : ∀ n : Fin 50, densSupG (n.val + 15050) < 2 ^ 1771 := by decide
private theorem cs_w2 : ∀ n : Fin 50, centredStar (densSupG (n.val + 15100)) (centF (n.val + 15100)) = true := by decide
private theorem cl_w2 : ∀ n : Fin 50, centF (n.val + 15100) < 23 := by decide
private theorem bd_w2 : ∀ n : Fin 50, densSupG (n.val + 15100) < 2 ^ 1771 := by decide
private theorem cs_w3 : ∀ n : Fin 50, centredStar (densSupG (n.val + 15150)) (centF (n.val + 15150)) = true := by decide
private theorem cl_w3 : ∀ n : Fin 50, centF (n.val + 15150) < 23 := by decide
private theorem bd_w3 : ∀ n : Fin 50, densSupG (n.val + 15150) < 2 ^ 1771 := by decide
private theorem cs_w4 : ∀ n : Fin 50, centredStar (densSupG (n.val + 15200)) (centF (n.val + 15200)) = true := by decide
private theorem cl_w4 : ∀ n : Fin 50, centF (n.val + 15200) < 23 := by decide
private theorem bd_w4 : ∀ n : Fin 50, densSupG (n.val + 15200) < 2 ^ 1771 := by decide
private theorem cs_w5 : ∀ n : Fin 50, centredStar (densSupG (n.val + 15250)) (centF (n.val + 15250)) = true := by decide
private theorem cl_w5 : ∀ n : Fin 50, centF (n.val + 15250) < 23 := by decide
private theorem bd_w5 : ∀ n : Fin 50, densSupG (n.val + 15250) < 2 ^ 1771 := by decide
private theorem cs_w6 : ∀ n : Fin 50, centredStar (densSupG (n.val + 15300)) (centF (n.val + 15300)) = true := by decide
private theorem cl_w6 : ∀ n : Fin 50, centF (n.val + 15300) < 23 := by decide
private theorem bd_w6 : ∀ n : Fin 50, densSupG (n.val + 15300) < 2 ^ 1771 := by decide
private theorem cs_w7 : ∀ n : Fin 50, centredStar (densSupG (n.val + 15350)) (centF (n.val + 15350)) = true := by decide
private theorem cl_w7 : ∀ n : Fin 50, centF (n.val + 15350) < 23 := by decide
private theorem bd_w7 : ∀ n : Fin 50, densSupG (n.val + 15350) < 2 ^ 1771 := by decide
private theorem cs_w8 : ∀ n : Fin 50, centredStar (densSupG (n.val + 15400)) (centF (n.val + 15400)) = true := by decide
private theorem cl_w8 : ∀ n : Fin 50, centF (n.val + 15400) < 23 := by decide
private theorem bd_w8 : ∀ n : Fin 50, densSupG (n.val + 15400) < 2 ^ 1771 := by decide
private theorem cs_w9 : ∀ n : Fin 50, centredStar (densSupG (n.val + 15450)) (centF (n.val + 15450)) = true := by decide
private theorem cl_w9 : ∀ n : Fin 50, centF (n.val + 15450) < 23 := by decide
private theorem bd_w9 : ∀ n : Fin 50, densSupG (n.val + 15450) < 2 ^ 1771 := by decide
private theorem cs_w10 : ∀ n : Fin 50, centredStar (densSupG (n.val + 15500)) (centF (n.val + 15500)) = true := by decide
private theorem cl_w10 : ∀ n : Fin 50, centF (n.val + 15500) < 23 := by decide
private theorem bd_w10 : ∀ n : Fin 50, densSupG (n.val + 15500) < 2 ^ 1771 := by decide
private theorem cs_w11 : ∀ n : Fin 50, centredStar (densSupG (n.val + 15550)) (centF (n.val + 15550)) = true := by decide
private theorem cl_w11 : ∀ n : Fin 50, centF (n.val + 15550) < 23 := by decide
private theorem bd_w11 : ∀ n : Fin 50, densSupG (n.val + 15550) < 2 ^ 1771 := by decide
private theorem cs_w12 : ∀ n : Fin 50, centredStar (densSupG (n.val + 15600)) (centF (n.val + 15600)) = true := by decide
private theorem cl_w12 : ∀ n : Fin 50, centF (n.val + 15600) < 23 := by decide
private theorem bd_w12 : ∀ n : Fin 50, densSupG (n.val + 15600) < 2 ^ 1771 := by decide
private theorem cs_w13 : ∀ n : Fin 50, centredStar (densSupG (n.val + 15650)) (centF (n.val + 15650)) = true := by decide
private theorem cl_w13 : ∀ n : Fin 50, centF (n.val + 15650) < 23 := by decide
private theorem bd_w13 : ∀ n : Fin 50, densSupG (n.val + 15650) < 2 ^ 1771 := by decide
private theorem cs_w14 : ∀ n : Fin 50, centredStar (densSupG (n.val + 15700)) (centF (n.val + 15700)) = true := by decide
private theorem cl_w14 : ∀ n : Fin 50, centF (n.val + 15700) < 23 := by decide
private theorem bd_w14 : ∀ n : Fin 50, densSupG (n.val + 15700) < 2 ^ 1771 := by decide
private theorem cs_w15 : ∀ n : Fin 50, centredStar (densSupG (n.val + 15750)) (centF (n.val + 15750)) = true := by decide
private theorem cl_w15 : ∀ n : Fin 50, centF (n.val + 15750) < 23 := by decide
private theorem bd_w15 : ∀ n : Fin 50, densSupG (n.val + 15750) < 2 ^ 1771 := by decide
private theorem cs_w16 : ∀ n : Fin 50, centredStar (densSupG (n.val + 15800)) (centF (n.val + 15800)) = true := by decide
private theorem cl_w16 : ∀ n : Fin 50, centF (n.val + 15800) < 23 := by decide
private theorem bd_w16 : ∀ n : Fin 50, densSupG (n.val + 15800) < 2 ^ 1771 := by decide
private theorem cs_w17 : ∀ n : Fin 50, centredStar (densSupG (n.val + 15850)) (centF (n.val + 15850)) = true := by decide
private theorem cl_w17 : ∀ n : Fin 50, centF (n.val + 15850) < 23 := by decide
private theorem bd_w17 : ∀ n : Fin 50, densSupG (n.val + 15850) < 2 ^ 1771 := by decide
private theorem cs_w18 : ∀ n : Fin 50, centredStar (densSupG (n.val + 15900)) (centF (n.val + 15900)) = true := by decide
private theorem cl_w18 : ∀ n : Fin 50, centF (n.val + 15900) < 23 := by decide
private theorem bd_w18 : ∀ n : Fin 50, densSupG (n.val + 15900) < 2 ^ 1771 := by decide
private theorem cs_w19 : ∀ n : Fin 50, centredStar (densSupG (n.val + 15950)) (centF (n.val + 15950)) = true := by decide
private theorem cl_w19 : ∀ n : Fin 50, centF (n.val + 15950) < 23 := by decide
private theorem bd_w19 : ∀ n : Fin 50, densSupG (n.val + 15950) < 2 ^ 1771 := by decide
private theorem cs_w20 : ∀ n : Fin 50, centredStar (densSupG (n.val + 16000)) (centF (n.val + 16000)) = true := by decide
private theorem cl_w20 : ∀ n : Fin 50, centF (n.val + 16000) < 23 := by decide
private theorem bd_w20 : ∀ n : Fin 50, densSupG (n.val + 16000) < 2 ^ 1771 := by decide
private theorem cs_w21 : ∀ n : Fin 50, centredStar (densSupG (n.val + 16050)) (centF (n.val + 16050)) = true := by decide
private theorem cl_w21 : ∀ n : Fin 50, centF (n.val + 16050) < 23 := by decide
private theorem bd_w21 : ∀ n : Fin 50, densSupG (n.val + 16050) < 2 ^ 1771 := by decide
private theorem cs_w22 : ∀ n : Fin 50, centredStar (densSupG (n.val + 16100)) (centF (n.val + 16100)) = true := by decide
private theorem cl_w22 : ∀ n : Fin 50, centF (n.val + 16100) < 23 := by decide
private theorem bd_w22 : ∀ n : Fin 50, densSupG (n.val + 16100) < 2 ^ 1771 := by decide
private theorem cs_w23 : ∀ n : Fin 50, centredStar (densSupG (n.val + 16150)) (centF (n.val + 16150)) = true := by decide
private theorem cl_w23 : ∀ n : Fin 50, centF (n.val + 16150) < 23 := by decide
private theorem bd_w23 : ∀ n : Fin 50, densSupG (n.val + 16150) < 2 ^ 1771 := by decide
private theorem cs_w24 : ∀ n : Fin 50, centredStar (densSupG (n.val + 16200)) (centF (n.val + 16200)) = true := by decide
private theorem cl_w24 : ∀ n : Fin 50, centF (n.val + 16200) < 23 := by decide
private theorem bd_w24 : ∀ n : Fin 50, densSupG (n.val + 16200) < 2 ^ 1771 := by decide
private theorem cs_w25 : ∀ n : Fin 50, centredStar (densSupG (n.val + 16250)) (centF (n.val + 16250)) = true := by decide
private theorem cl_w25 : ∀ n : Fin 50, centF (n.val + 16250) < 23 := by decide
private theorem bd_w25 : ∀ n : Fin 50, densSupG (n.val + 16250) < 2 ^ 1771 := by decide
private theorem cs_w26 : ∀ n : Fin 50, centredStar (densSupG (n.val + 16300)) (centF (n.val + 16300)) = true := by decide
private theorem cl_w26 : ∀ n : Fin 50, centF (n.val + 16300) < 23 := by decide
private theorem bd_w26 : ∀ n : Fin 50, densSupG (n.val + 16300) < 2 ^ 1771 := by decide
private theorem cs_w27 : ∀ n : Fin 50, centredStar (densSupG (n.val + 16350)) (centF (n.val + 16350)) = true := by decide
private theorem cl_w27 : ∀ n : Fin 50, centF (n.val + 16350) < 23 := by decide
private theorem bd_w27 : ∀ n : Fin 50, densSupG (n.val + 16350) < 2 ^ 1771 := by decide
private theorem cs_w28 : ∀ n : Fin 50, centredStar (densSupG (n.val + 16400)) (centF (n.val + 16400)) = true := by decide
private theorem cl_w28 : ∀ n : Fin 50, centF (n.val + 16400) < 23 := by decide
private theorem bd_w28 : ∀ n : Fin 50, densSupG (n.val + 16400) < 2 ^ 1771 := by decide
private theorem cs_w29 : ∀ n : Fin 50, centredStar (densSupG (n.val + 16450)) (centF (n.val + 16450)) = true := by decide
private theorem cl_w29 : ∀ n : Fin 50, centF (n.val + 16450) < 23 := by decide
private theorem bd_w29 : ∀ n : Fin 50, densSupG (n.val + 16450) < 2 ^ 1771 := by decide
private theorem cs_w30 : ∀ n : Fin 50, centredStar (densSupG (n.val + 16500)) (centF (n.val + 16500)) = true := by decide
private theorem cl_w30 : ∀ n : Fin 50, centF (n.val + 16500) < 23 := by decide
private theorem bd_w30 : ∀ n : Fin 50, densSupG (n.val + 16500) < 2 ^ 1771 := by decide
private theorem cs_w31 : ∀ n : Fin 50, centredStar (densSupG (n.val + 16550)) (centF (n.val + 16550)) = true := by decide
private theorem cl_w31 : ∀ n : Fin 50, centF (n.val + 16550) < 23 := by decide
private theorem bd_w31 : ∀ n : Fin 50, densSupG (n.val + 16550) < 2 ^ 1771 := by decide
private theorem cs_w32 : ∀ n : Fin 50, centredStar (densSupG (n.val + 16600)) (centF (n.val + 16600)) = true := by decide
private theorem cl_w32 : ∀ n : Fin 50, centF (n.val + 16600) < 23 := by decide
private theorem bd_w32 : ∀ n : Fin 50, densSupG (n.val + 16600) < 2 ^ 1771 := by decide
private theorem cs_w33 : ∀ n : Fin 50, centredStar (densSupG (n.val + 16650)) (centF (n.val + 16650)) = true := by decide
private theorem cl_w33 : ∀ n : Fin 50, centF (n.val + 16650) < 23 := by decide
private theorem bd_w33 : ∀ n : Fin 50, densSupG (n.val + 16650) < 2 ^ 1771 := by decide
private theorem cs_w34 : ∀ n : Fin 50, centredStar (densSupG (n.val + 16700)) (centF (n.val + 16700)) = true := by decide
private theorem cl_w34 : ∀ n : Fin 50, centF (n.val + 16700) < 23 := by decide
private theorem bd_w34 : ∀ n : Fin 50, densSupG (n.val + 16700) < 2 ^ 1771 := by decide
private theorem cs_w35 : ∀ n : Fin 50, centredStar (densSupG (n.val + 16750)) (centF (n.val + 16750)) = true := by decide
private theorem cl_w35 : ∀ n : Fin 50, centF (n.val + 16750) < 23 := by decide
private theorem bd_w35 : ∀ n : Fin 50, densSupG (n.val + 16750) < 2 ^ 1771 := by decide
private theorem cs_w36 : ∀ n : Fin 50, centredStar (densSupG (n.val + 16800)) (centF (n.val + 16800)) = true := by decide
private theorem cl_w36 : ∀ n : Fin 50, centF (n.val + 16800) < 23 := by decide
private theorem bd_w36 : ∀ n : Fin 50, densSupG (n.val + 16800) < 2 ^ 1771 := by decide
private theorem cs_w37 : ∀ n : Fin 50, centredStar (densSupG (n.val + 16850)) (centF (n.val + 16850)) = true := by decide
private theorem cl_w37 : ∀ n : Fin 50, centF (n.val + 16850) < 23 := by decide
private theorem bd_w37 : ∀ n : Fin 50, densSupG (n.val + 16850) < 2 ^ 1771 := by decide
private theorem cs_w38 : ∀ n : Fin 50, centredStar (densSupG (n.val + 16900)) (centF (n.val + 16900)) = true := by decide
private theorem cl_w38 : ∀ n : Fin 50, centF (n.val + 16900) < 23 := by decide
private theorem bd_w38 : ∀ n : Fin 50, densSupG (n.val + 16900) < 2 ^ 1771 := by decide
private theorem cs_w39 : ∀ n : Fin 50, centredStar (densSupG (n.val + 16950)) (centF (n.val + 16950)) = true := by decide
private theorem cl_w39 : ∀ n : Fin 50, centF (n.val + 16950) < 23 := by decide
private theorem bd_w39 : ∀ n : Fin 50, densSupG (n.val + 16950) < 2 ^ 1771 := by decide
private theorem cs_w40 : ∀ n : Fin 50, centredStar (densSupG (n.val + 17000)) (centF (n.val + 17000)) = true := by decide
private theorem cl_w40 : ∀ n : Fin 50, centF (n.val + 17000) < 23 := by decide
private theorem bd_w40 : ∀ n : Fin 50, densSupG (n.val + 17000) < 2 ^ 1771 := by decide
private theorem cs_w41 : ∀ n : Fin 50, centredStar (densSupG (n.val + 17050)) (centF (n.val + 17050)) = true := by decide
private theorem cl_w41 : ∀ n : Fin 50, centF (n.val + 17050) < 23 := by decide
private theorem bd_w41 : ∀ n : Fin 50, densSupG (n.val + 17050) < 2 ^ 1771 := by decide
private theorem cs_w42 : ∀ n : Fin 50, centredStar (densSupG (n.val + 17100)) (centF (n.val + 17100)) = true := by decide
private theorem cl_w42 : ∀ n : Fin 50, centF (n.val + 17100) < 23 := by decide
private theorem bd_w42 : ∀ n : Fin 50, densSupG (n.val + 17100) < 2 ^ 1771 := by decide
private theorem cs_w43 : ∀ n : Fin 50, centredStar (densSupG (n.val + 17150)) (centF (n.val + 17150)) = true := by decide
private theorem cl_w43 : ∀ n : Fin 50, centF (n.val + 17150) < 23 := by decide
private theorem bd_w43 : ∀ n : Fin 50, densSupG (n.val + 17150) < 2 ^ 1771 := by decide
private theorem cs_w44 : ∀ n : Fin 50, centredStar (densSupG (n.val + 17200)) (centF (n.val + 17200)) = true := by decide
private theorem cl_w44 : ∀ n : Fin 50, centF (n.val + 17200) < 23 := by decide
private theorem bd_w44 : ∀ n : Fin 50, densSupG (n.val + 17200) < 2 ^ 1771 := by decide
private theorem cs_w45 : ∀ n : Fin 50, centredStar (densSupG (n.val + 17250)) (centF (n.val + 17250)) = true := by decide
private theorem cl_w45 : ∀ n : Fin 50, centF (n.val + 17250) < 23 := by decide
private theorem bd_w45 : ∀ n : Fin 50, densSupG (n.val + 17250) < 2 ^ 1771 := by decide
private theorem cs_w46 : ∀ n : Fin 50, centredStar (densSupG (n.val + 17300)) (centF (n.val + 17300)) = true := by decide
private theorem cl_w46 : ∀ n : Fin 50, centF (n.val + 17300) < 23 := by decide
private theorem bd_w46 : ∀ n : Fin 50, densSupG (n.val + 17300) < 2 ^ 1771 := by decide
private theorem cs_w47 : ∀ n : Fin 50, centredStar (densSupG (n.val + 17350)) (centF (n.val + 17350)) = true := by decide
private theorem cl_w47 : ∀ n : Fin 50, centF (n.val + 17350) < 23 := by decide
private theorem bd_w47 : ∀ n : Fin 50, densSupG (n.val + 17350) < 2 ^ 1771 := by decide
private theorem cs_w48 : ∀ n : Fin 50, centredStar (densSupG (n.val + 17400)) (centF (n.val + 17400)) = true := by decide
private theorem cl_w48 : ∀ n : Fin 50, centF (n.val + 17400) < 23 := by decide
private theorem bd_w48 : ∀ n : Fin 50, densSupG (n.val + 17400) < 2 ^ 1771 := by decide
private theorem cs_w49 : ∀ n : Fin 50, centredStar (densSupG (n.val + 17450)) (centF (n.val + 17450)) = true := by decide
private theorem cl_w49 : ∀ n : Fin 50, centF (n.val + 17450) < 23 := by decide
private theorem bd_w49 : ∀ n : Fin 50, densSupG (n.val + 17450) < 2 ^ 1771 := by decide
private theorem cs_w50 : ∀ n : Fin 50, centredStar (densSupG (n.val + 17500)) (centF (n.val + 17500)) = true := by decide
private theorem cl_w50 : ∀ n : Fin 50, centF (n.val + 17500) < 23 := by decide
private theorem bd_w50 : ∀ n : Fin 50, densSupG (n.val + 17500) < 2 ^ 1771 := by decide
private theorem cs_w51 : ∀ n : Fin 50, centredStar (densSupG (n.val + 17550)) (centF (n.val + 17550)) = true := by decide
private theorem cl_w51 : ∀ n : Fin 50, centF (n.val + 17550) < 23 := by decide
private theorem bd_w51 : ∀ n : Fin 50, densSupG (n.val + 17550) < 2 ^ 1771 := by decide
private theorem cs_w52 : ∀ n : Fin 50, centredStar (densSupG (n.val + 17600)) (centF (n.val + 17600)) = true := by decide
private theorem cl_w52 : ∀ n : Fin 50, centF (n.val + 17600) < 23 := by decide
private theorem bd_w52 : ∀ n : Fin 50, densSupG (n.val + 17600) < 2 ^ 1771 := by decide
private theorem cs_w53 : ∀ n : Fin 50, centredStar (densSupG (n.val + 17650)) (centF (n.val + 17650)) = true := by decide
private theorem cl_w53 : ∀ n : Fin 50, centF (n.val + 17650) < 23 := by decide
private theorem bd_w53 : ∀ n : Fin 50, densSupG (n.val + 17650) < 2 ^ 1771 := by decide
private theorem cs_w54 : ∀ n : Fin 50, centredStar (densSupG (n.val + 17700)) (centF (n.val + 17700)) = true := by decide
private theorem cl_w54 : ∀ n : Fin 50, centF (n.val + 17700) < 23 := by decide
private theorem bd_w54 : ∀ n : Fin 50, densSupG (n.val + 17700) < 2 ^ 1771 := by decide
private theorem cs_w55 : ∀ n : Fin 50, centredStar (densSupG (n.val + 17750)) (centF (n.val + 17750)) = true := by decide
private theorem cl_w55 : ∀ n : Fin 50, centF (n.val + 17750) < 23 := by decide
private theorem bd_w55 : ∀ n : Fin 50, densSupG (n.val + 17750) < 2 ^ 1771 := by decide
private theorem cs_w56 : ∀ n : Fin 50, centredStar (densSupG (n.val + 17800)) (centF (n.val + 17800)) = true := by decide
private theorem cl_w56 : ∀ n : Fin 50, centF (n.val + 17800) < 23 := by decide
private theorem bd_w56 : ∀ n : Fin 50, densSupG (n.val + 17800) < 2 ^ 1771 := by decide
private theorem cs_w57 : ∀ n : Fin 50, centredStar (densSupG (n.val + 17850)) (centF (n.val + 17850)) = true := by decide
private theorem cl_w57 : ∀ n : Fin 50, centF (n.val + 17850) < 23 := by decide
private theorem bd_w57 : ∀ n : Fin 50, densSupG (n.val + 17850) < 2 ^ 1771 := by decide
private theorem cs_w58 : ∀ n : Fin 50, centredStar (densSupG (n.val + 17900)) (centF (n.val + 17900)) = true := by decide
private theorem cl_w58 : ∀ n : Fin 50, centF (n.val + 17900) < 23 := by decide
private theorem bd_w58 : ∀ n : Fin 50, densSupG (n.val + 17900) < 2 ^ 1771 := by decide
private theorem cs_w59 : ∀ n : Fin 50, centredStar (densSupG (n.val + 17950)) (centF (n.val + 17950)) = true := by decide
private theorem cl_w59 : ∀ n : Fin 50, centF (n.val + 17950) < 23 := by decide
private theorem bd_w59 : ∀ n : Fin 50, densSupG (n.val + 17950) < 2 ^ 1771 := by decide
private theorem cs_w60 : ∀ n : Fin 50, centredStar (densSupG (n.val + 18000)) (centF (n.val + 18000)) = true := by decide
private theorem cl_w60 : ∀ n : Fin 50, centF (n.val + 18000) < 23 := by decide
private theorem bd_w60 : ∀ n : Fin 50, densSupG (n.val + 18000) < 2 ^ 1771 := by decide
private theorem cs_w61 : ∀ n : Fin 50, centredStar (densSupG (n.val + 18050)) (centF (n.val + 18050)) = true := by decide
private theorem cl_w61 : ∀ n : Fin 50, centF (n.val + 18050) < 23 := by decide
private theorem bd_w61 : ∀ n : Fin 50, densSupG (n.val + 18050) < 2 ^ 1771 := by decide
private theorem cs_w62 : ∀ n : Fin 50, centredStar (densSupG (n.val + 18100)) (centF (n.val + 18100)) = true := by decide
private theorem cl_w62 : ∀ n : Fin 50, centF (n.val + 18100) < 23 := by decide
private theorem bd_w62 : ∀ n : Fin 50, densSupG (n.val + 18100) < 2 ^ 1771 := by decide
private theorem cs_w63 : ∀ n : Fin 50, centredStar (densSupG (n.val + 18150)) (centF (n.val + 18150)) = true := by decide
private theorem cl_w63 : ∀ n : Fin 50, centF (n.val + 18150) < 23 := by decide
private theorem bd_w63 : ∀ n : Fin 50, densSupG (n.val + 18150) < 2 ^ 1771 := by decide
private theorem cs_w64 : ∀ n : Fin 50, centredStar (densSupG (n.val + 18200)) (centF (n.val + 18200)) = true := by decide
private theorem cl_w64 : ∀ n : Fin 50, centF (n.val + 18200) < 23 := by decide
private theorem bd_w64 : ∀ n : Fin 50, densSupG (n.val + 18200) < 2 ^ 1771 := by decide
private theorem cs_w65 : ∀ n : Fin 50, centredStar (densSupG (n.val + 18250)) (centF (n.val + 18250)) = true := by decide
private theorem cl_w65 : ∀ n : Fin 50, centF (n.val + 18250) < 23 := by decide
private theorem bd_w65 : ∀ n : Fin 50, densSupG (n.val + 18250) < 2 ^ 1771 := by decide
private theorem cs_w66 : ∀ n : Fin 50, centredStar (densSupG (n.val + 18300)) (centF (n.val + 18300)) = true := by decide
private theorem cl_w66 : ∀ n : Fin 50, centF (n.val + 18300) < 23 := by decide
private theorem bd_w66 : ∀ n : Fin 50, densSupG (n.val + 18300) < 2 ^ 1771 := by decide
private theorem cs_w67 : ∀ n : Fin 50, centredStar (densSupG (n.val + 18350)) (centF (n.val + 18350)) = true := by decide
private theorem cl_w67 : ∀ n : Fin 50, centF (n.val + 18350) < 23 := by decide
private theorem bd_w67 : ∀ n : Fin 50, densSupG (n.val + 18350) < 2 ^ 1771 := by decide
private theorem cs_w68 : ∀ n : Fin 50, centredStar (densSupG (n.val + 18400)) (centF (n.val + 18400)) = true := by decide
private theorem cl_w68 : ∀ n : Fin 50, centF (n.val + 18400) < 23 := by decide
private theorem bd_w68 : ∀ n : Fin 50, densSupG (n.val + 18400) < 2 ^ 1771 := by decide
private theorem cs_w69 : ∀ n : Fin 50, centredStar (densSupG (n.val + 18450)) (centF (n.val + 18450)) = true := by decide
private theorem cl_w69 : ∀ n : Fin 50, centF (n.val + 18450) < 23 := by decide
private theorem bd_w69 : ∀ n : Fin 50, densSupG (n.val + 18450) < 2 ^ 1771 := by decide
private theorem cs_w70 : ∀ n : Fin 50, centredStar (densSupG (n.val + 18500)) (centF (n.val + 18500)) = true := by decide
private theorem cl_w70 : ∀ n : Fin 50, centF (n.val + 18500) < 23 := by decide
private theorem bd_w70 : ∀ n : Fin 50, densSupG (n.val + 18500) < 2 ^ 1771 := by decide
private theorem cs_w71 : ∀ n : Fin 50, centredStar (densSupG (n.val + 18550)) (centF (n.val + 18550)) = true := by decide
private theorem cl_w71 : ∀ n : Fin 50, centF (n.val + 18550) < 23 := by decide
private theorem bd_w71 : ∀ n : Fin 50, densSupG (n.val + 18550) < 2 ^ 1771 := by decide
private theorem cs_w72 : ∀ n : Fin 50, centredStar (densSupG (n.val + 18600)) (centF (n.val + 18600)) = true := by decide
private theorem cl_w72 : ∀ n : Fin 50, centF (n.val + 18600) < 23 := by decide
private theorem bd_w72 : ∀ n : Fin 50, densSupG (n.val + 18600) < 2 ^ 1771 := by decide
private theorem cs_w73 : ∀ n : Fin 50, centredStar (densSupG (n.val + 18650)) (centF (n.val + 18650)) = true := by decide
private theorem cl_w73 : ∀ n : Fin 50, centF (n.val + 18650) < 23 := by decide
private theorem bd_w73 : ∀ n : Fin 50, densSupG (n.val + 18650) < 2 ^ 1771 := by decide
private theorem cs_w74 : ∀ n : Fin 50, centredStar (densSupG (n.val + 18700)) (centF (n.val + 18700)) = true := by decide
private theorem cl_w74 : ∀ n : Fin 50, centF (n.val + 18700) < 23 := by decide
private theorem bd_w74 : ∀ n : Fin 50, densSupG (n.val + 18700) < 2 ^ 1771 := by decide
private theorem cs_w75 : ∀ n : Fin 50, centredStar (densSupG (n.val + 18750)) (centF (n.val + 18750)) = true := by decide
private theorem cl_w75 : ∀ n : Fin 50, centF (n.val + 18750) < 23 := by decide
private theorem bd_w75 : ∀ n : Fin 50, densSupG (n.val + 18750) < 2 ^ 1771 := by decide
private theorem cs_w76 : ∀ n : Fin 50, centredStar (densSupG (n.val + 18800)) (centF (n.val + 18800)) = true := by decide
private theorem cl_w76 : ∀ n : Fin 50, centF (n.val + 18800) < 23 := by decide
private theorem bd_w76 : ∀ n : Fin 50, densSupG (n.val + 18800) < 2 ^ 1771 := by decide
private theorem cs_w77 : ∀ n : Fin 50, centredStar (densSupG (n.val + 18850)) (centF (n.val + 18850)) = true := by decide
private theorem cl_w77 : ∀ n : Fin 50, centF (n.val + 18850) < 23 := by decide
private theorem bd_w77 : ∀ n : Fin 50, densSupG (n.val + 18850) < 2 ^ 1771 := by decide
private theorem cs_w78 : ∀ n : Fin 50, centredStar (densSupG (n.val + 18900)) (centF (n.val + 18900)) = true := by decide
private theorem cl_w78 : ∀ n : Fin 50, centF (n.val + 18900) < 23 := by decide
private theorem bd_w78 : ∀ n : Fin 50, densSupG (n.val + 18900) < 2 ^ 1771 := by decide
private theorem cs_w79 : ∀ n : Fin 50, centredStar (densSupG (n.val + 18950)) (centF (n.val + 18950)) = true := by decide
private theorem cl_w79 : ∀ n : Fin 50, centF (n.val + 18950) < 23 := by decide
private theorem bd_w79 : ∀ n : Fin 50, densSupG (n.val + 18950) < 2 ^ 1771 := by decide
private theorem cs_w80 : ∀ n : Fin 50, centredStar (densSupG (n.val + 19000)) (centF (n.val + 19000)) = true := by decide
private theorem cl_w80 : ∀ n : Fin 50, centF (n.val + 19000) < 23 := by decide
private theorem bd_w80 : ∀ n : Fin 50, densSupG (n.val + 19000) < 2 ^ 1771 := by decide
private theorem cs_w81 : ∀ n : Fin 50, centredStar (densSupG (n.val + 19050)) (centF (n.val + 19050)) = true := by decide
private theorem cl_w81 : ∀ n : Fin 50, centF (n.val + 19050) < 23 := by decide
private theorem bd_w81 : ∀ n : Fin 50, densSupG (n.val + 19050) < 2 ^ 1771 := by decide
private theorem cs_w82 : ∀ n : Fin 50, centredStar (densSupG (n.val + 19100)) (centF (n.val + 19100)) = true := by decide
private theorem cl_w82 : ∀ n : Fin 50, centF (n.val + 19100) < 23 := by decide
private theorem bd_w82 : ∀ n : Fin 50, densSupG (n.val + 19100) < 2 ^ 1771 := by decide
private theorem cs_w83 : ∀ n : Fin 50, centredStar (densSupG (n.val + 19150)) (centF (n.val + 19150)) = true := by decide
private theorem cl_w83 : ∀ n : Fin 50, centF (n.val + 19150) < 23 := by decide
private theorem bd_w83 : ∀ n : Fin 50, densSupG (n.val + 19150) < 2 ^ 1771 := by decide
private theorem cs_w84 : ∀ n : Fin 50, centredStar (densSupG (n.val + 19200)) (centF (n.val + 19200)) = true := by decide
private theorem cl_w84 : ∀ n : Fin 50, centF (n.val + 19200) < 23 := by decide
private theorem bd_w84 : ∀ n : Fin 50, densSupG (n.val + 19200) < 2 ^ 1771 := by decide
private theorem cs_w85 : ∀ n : Fin 50, centredStar (densSupG (n.val + 19250)) (centF (n.val + 19250)) = true := by decide
private theorem cl_w85 : ∀ n : Fin 50, centF (n.val + 19250) < 23 := by decide
private theorem bd_w85 : ∀ n : Fin 50, densSupG (n.val + 19250) < 2 ^ 1771 := by decide
private theorem cs_w86 : ∀ n : Fin 50, centredStar (densSupG (n.val + 19300)) (centF (n.val + 19300)) = true := by decide
private theorem cl_w86 : ∀ n : Fin 50, centF (n.val + 19300) < 23 := by decide
private theorem bd_w86 : ∀ n : Fin 50, densSupG (n.val + 19300) < 2 ^ 1771 := by decide
private theorem cs_w87 : ∀ n : Fin 50, centredStar (densSupG (n.val + 19350)) (centF (n.val + 19350)) = true := by decide
private theorem cl_w87 : ∀ n : Fin 50, centF (n.val + 19350) < 23 := by decide
private theorem bd_w87 : ∀ n : Fin 50, densSupG (n.val + 19350) < 2 ^ 1771 := by decide
private theorem cs_w88 : ∀ n : Fin 50, centredStar (densSupG (n.val + 19400)) (centF (n.val + 19400)) = true := by decide
private theorem cl_w88 : ∀ n : Fin 50, centF (n.val + 19400) < 23 := by decide
private theorem bd_w88 : ∀ n : Fin 50, densSupG (n.val + 19400) < 2 ^ 1771 := by decide
private theorem cs_w89 : ∀ n : Fin 50, centredStar (densSupG (n.val + 19450)) (centF (n.val + 19450)) = true := by decide
private theorem cl_w89 : ∀ n : Fin 50, centF (n.val + 19450) < 23 := by decide
private theorem bd_w89 : ∀ n : Fin 50, densSupG (n.val + 19450) < 2 ^ 1771 := by decide
private theorem cs_w90 : ∀ n : Fin 50, centredStar (densSupG (n.val + 19500)) (centF (n.val + 19500)) = true := by decide
private theorem cl_w90 : ∀ n : Fin 50, centF (n.val + 19500) < 23 := by decide
private theorem bd_w90 : ∀ n : Fin 50, densSupG (n.val + 19500) < 2 ^ 1771 := by decide
private theorem cs_w91 : ∀ n : Fin 50, centredStar (densSupG (n.val + 19550)) (centF (n.val + 19550)) = true := by decide
private theorem cl_w91 : ∀ n : Fin 50, centF (n.val + 19550) < 23 := by decide
private theorem bd_w91 : ∀ n : Fin 50, densSupG (n.val + 19550) < 2 ^ 1771 := by decide
private theorem cs_w92 : ∀ n : Fin 50, centredStar (densSupG (n.val + 19600)) (centF (n.val + 19600)) = true := by decide
private theorem cl_w92 : ∀ n : Fin 50, centF (n.val + 19600) < 23 := by decide
private theorem bd_w92 : ∀ n : Fin 50, densSupG (n.val + 19600) < 2 ^ 1771 := by decide
private theorem cs_w93 : ∀ n : Fin 50, centredStar (densSupG (n.val + 19650)) (centF (n.val + 19650)) = true := by decide
private theorem cl_w93 : ∀ n : Fin 50, centF (n.val + 19650) < 23 := by decide
private theorem bd_w93 : ∀ n : Fin 50, densSupG (n.val + 19650) < 2 ^ 1771 := by decide
private theorem cs_w94 : ∀ n : Fin 50, centredStar (densSupG (n.val + 19700)) (centF (n.val + 19700)) = true := by decide
private theorem cl_w94 : ∀ n : Fin 50, centF (n.val + 19700) < 23 := by decide
private theorem bd_w94 : ∀ n : Fin 50, densSupG (n.val + 19700) < 2 ^ 1771 := by decide
private theorem cs_w95 : ∀ n : Fin 50, centredStar (densSupG (n.val + 19750)) (centF (n.val + 19750)) = true := by decide
private theorem cl_w95 : ∀ n : Fin 50, centF (n.val + 19750) < 23 := by decide
private theorem bd_w95 : ∀ n : Fin 50, densSupG (n.val + 19750) < 2 ^ 1771 := by decide
private theorem cs_w96 : ∀ n : Fin 50, centredStar (densSupG (n.val + 19800)) (centF (n.val + 19800)) = true := by decide
private theorem cl_w96 : ∀ n : Fin 50, centF (n.val + 19800) < 23 := by decide
private theorem bd_w96 : ∀ n : Fin 50, densSupG (n.val + 19800) < 2 ^ 1771 := by decide
private theorem cs_w97 : ∀ n : Fin 50, centredStar (densSupG (n.val + 19850)) (centF (n.val + 19850)) = true := by decide
private theorem cl_w97 : ∀ n : Fin 50, centF (n.val + 19850) < 23 := by decide
private theorem bd_w97 : ∀ n : Fin 50, densSupG (n.val + 19850) < 2 ^ 1771 := by decide
private theorem cs_w98 : ∀ n : Fin 50, centredStar (densSupG (n.val + 19900)) (centF (n.val + 19900)) = true := by decide
private theorem cl_w98 : ∀ n : Fin 50, centF (n.val + 19900) < 23 := by decide
private theorem bd_w98 : ∀ n : Fin 50, densSupG (n.val + 19900) < 2 ^ 1771 := by decide
private theorem cs_w99 : ∀ n : Fin 50, centredStar (densSupG (n.val + 19950)) (centF (n.val + 19950)) = true := by decide
private theorem cl_w99 : ∀ n : Fin 50, centF (n.val + 19950) < 23 := by decide
private theorem bd_w99 : ∀ n : Fin 50, densSupG (n.val + 19950) < 2 ^ 1771 := by decide

theorem centredStar_range : ∀ n, 15000 ≤ n → n < 20000 → centredStar (densSupG n) (centF n) = true := by
  intro n hlo hhi
  by_cases h0 : n < 15050
  · have hr : n - 15000 < 50 := by omega
    have heq : n = (n - 15000) + 15000 := by omega
    rw [heq]
    exact cs_w0 ⟨n - 15000, hr⟩
  ·
    by_cases h1 : n < 15100
    · have hr : n - 15050 < 50 := by omega
      have heq : n = (n - 15050) + 15050 := by omega
      rw [heq]
      exact cs_w1 ⟨n - 15050, hr⟩
    ·
      by_cases h2 : n < 15150
      · have hr : n - 15100 < 50 := by omega
        have heq : n = (n - 15100) + 15100 := by omega
        rw [heq]
        exact cs_w2 ⟨n - 15100, hr⟩
      ·
        by_cases h3 : n < 15200
        · have hr : n - 15150 < 50 := by omega
          have heq : n = (n - 15150) + 15150 := by omega
          rw [heq]
          exact cs_w3 ⟨n - 15150, hr⟩
        ·
          by_cases h4 : n < 15250
          · have hr : n - 15200 < 50 := by omega
            have heq : n = (n - 15200) + 15200 := by omega
            rw [heq]
            exact cs_w4 ⟨n - 15200, hr⟩
          ·
            by_cases h5 : n < 15300
            · have hr : n - 15250 < 50 := by omega
              have heq : n = (n - 15250) + 15250 := by omega
              rw [heq]
              exact cs_w5 ⟨n - 15250, hr⟩
            ·
              by_cases h6 : n < 15350
              · have hr : n - 15300 < 50 := by omega
                have heq : n = (n - 15300) + 15300 := by omega
                rw [heq]
                exact cs_w6 ⟨n - 15300, hr⟩
              ·
                by_cases h7 : n < 15400
                · have hr : n - 15350 < 50 := by omega
                  have heq : n = (n - 15350) + 15350 := by omega
                  rw [heq]
                  exact cs_w7 ⟨n - 15350, hr⟩
                ·
                  by_cases h8 : n < 15450
                  · have hr : n - 15400 < 50 := by omega
                    have heq : n = (n - 15400) + 15400 := by omega
                    rw [heq]
                    exact cs_w8 ⟨n - 15400, hr⟩
                  ·
                    by_cases h9 : n < 15500
                    · have hr : n - 15450 < 50 := by omega
                      have heq : n = (n - 15450) + 15450 := by omega
                      rw [heq]
                      exact cs_w9 ⟨n - 15450, hr⟩
                    ·
                      by_cases h10 : n < 15550
                      · have hr : n - 15500 < 50 := by omega
                        have heq : n = (n - 15500) + 15500 := by omega
                        rw [heq]
                        exact cs_w10 ⟨n - 15500, hr⟩
                      ·
                        by_cases h11 : n < 15600
                        · have hr : n - 15550 < 50 := by omega
                          have heq : n = (n - 15550) + 15550 := by omega
                          rw [heq]
                          exact cs_w11 ⟨n - 15550, hr⟩
                        ·
                          by_cases h12 : n < 15650
                          · have hr : n - 15600 < 50 := by omega
                            have heq : n = (n - 15600) + 15600 := by omega
                            rw [heq]
                            exact cs_w12 ⟨n - 15600, hr⟩
                          ·
                            by_cases h13 : n < 15700
                            · have hr : n - 15650 < 50 := by omega
                              have heq : n = (n - 15650) + 15650 := by omega
                              rw [heq]
                              exact cs_w13 ⟨n - 15650, hr⟩
                            ·
                              by_cases h14 : n < 15750
                              · have hr : n - 15700 < 50 := by omega
                                have heq : n = (n - 15700) + 15700 := by omega
                                rw [heq]
                                exact cs_w14 ⟨n - 15700, hr⟩
                              ·
                                by_cases h15 : n < 15800
                                · have hr : n - 15750 < 50 := by omega
                                  have heq : n = (n - 15750) + 15750 := by omega
                                  rw [heq]
                                  exact cs_w15 ⟨n - 15750, hr⟩
                                ·
                                  by_cases h16 : n < 15850
                                  · have hr : n - 15800 < 50 := by omega
                                    have heq : n = (n - 15800) + 15800 := by omega
                                    rw [heq]
                                    exact cs_w16 ⟨n - 15800, hr⟩
                                  ·
                                    by_cases h17 : n < 15900
                                    · have hr : n - 15850 < 50 := by omega
                                      have heq : n = (n - 15850) + 15850 := by omega
                                      rw [heq]
                                      exact cs_w17 ⟨n - 15850, hr⟩
                                    ·
                                      by_cases h18 : n < 15950
                                      · have hr : n - 15900 < 50 := by omega
                                        have heq : n = (n - 15900) + 15900 := by omega
                                        rw [heq]
                                        exact cs_w18 ⟨n - 15900, hr⟩
                                      ·
                                        by_cases h19 : n < 16000
                                        · have hr : n - 15950 < 50 := by omega
                                          have heq : n = (n - 15950) + 15950 := by omega
                                          rw [heq]
                                          exact cs_w19 ⟨n - 15950, hr⟩
                                        ·
                                          by_cases h20 : n < 16050
                                          · have hr : n - 16000 < 50 := by omega
                                            have heq : n = (n - 16000) + 16000 := by omega
                                            rw [heq]
                                            exact cs_w20 ⟨n - 16000, hr⟩
                                          ·
                                            by_cases h21 : n < 16100
                                            · have hr : n - 16050 < 50 := by omega
                                              have heq : n = (n - 16050) + 16050 := by omega
                                              rw [heq]
                                              exact cs_w21 ⟨n - 16050, hr⟩
                                            ·
                                              by_cases h22 : n < 16150
                                              · have hr : n - 16100 < 50 := by omega
                                                have heq : n = (n - 16100) + 16100 := by omega
                                                rw [heq]
                                                exact cs_w22 ⟨n - 16100, hr⟩
                                              ·
                                                by_cases h23 : n < 16200
                                                · have hr : n - 16150 < 50 := by omega
                                                  have heq : n = (n - 16150) + 16150 := by omega
                                                  rw [heq]
                                                  exact cs_w23 ⟨n - 16150, hr⟩
                                                ·
                                                  by_cases h24 : n < 16250
                                                  · have hr : n - 16200 < 50 := by omega
                                                    have heq : n = (n - 16200) + 16200 := by omega
                                                    rw [heq]
                                                    exact cs_w24 ⟨n - 16200, hr⟩
                                                  ·
                                                    by_cases h25 : n < 16300
                                                    · have hr : n - 16250 < 50 := by omega
                                                      have heq : n = (n - 16250) + 16250 := by omega
                                                      rw [heq]
                                                      exact cs_w25 ⟨n - 16250, hr⟩
                                                    ·
                                                      by_cases h26 : n < 16350
                                                      · have hr : n - 16300 < 50 := by omega
                                                        have heq : n = (n - 16300) + 16300 := by omega
                                                        rw [heq]
                                                        exact cs_w26 ⟨n - 16300, hr⟩
                                                      ·
                                                        by_cases h27 : n < 16400
                                                        · have hr : n - 16350 < 50 := by omega
                                                          have heq : n = (n - 16350) + 16350 := by omega
                                                          rw [heq]
                                                          exact cs_w27 ⟨n - 16350, hr⟩
                                                        ·
                                                          by_cases h28 : n < 16450
                                                          · have hr : n - 16400 < 50 := by omega
                                                            have heq : n = (n - 16400) + 16400 := by omega
                                                            rw [heq]
                                                            exact cs_w28 ⟨n - 16400, hr⟩
                                                          ·
                                                            by_cases h29 : n < 16500
                                                            · have hr : n - 16450 < 50 := by omega
                                                              have heq : n = (n - 16450) + 16450 := by omega
                                                              rw [heq]
                                                              exact cs_w29 ⟨n - 16450, hr⟩
                                                            ·
                                                              by_cases h30 : n < 16550
                                                              · have hr : n - 16500 < 50 := by omega
                                                                have heq : n = (n - 16500) + 16500 := by omega
                                                                rw [heq]
                                                                exact cs_w30 ⟨n - 16500, hr⟩
                                                              ·
                                                                by_cases h31 : n < 16600
                                                                · have hr : n - 16550 < 50 := by omega
                                                                  have heq : n = (n - 16550) + 16550 := by omega
                                                                  rw [heq]
                                                                  exact cs_w31 ⟨n - 16550, hr⟩
                                                                ·
                                                                  by_cases h32 : n < 16650
                                                                  · have hr : n - 16600 < 50 := by omega
                                                                    have heq : n = (n - 16600) + 16600 := by omega
                                                                    rw [heq]
                                                                    exact cs_w32 ⟨n - 16600, hr⟩
                                                                  ·
                                                                    by_cases h33 : n < 16700
                                                                    · have hr : n - 16650 < 50 := by omega
                                                                      have heq : n = (n - 16650) + 16650 := by omega
                                                                      rw [heq]
                                                                      exact cs_w33 ⟨n - 16650, hr⟩
                                                                    ·
                                                                      by_cases h34 : n < 16750
                                                                      · have hr : n - 16700 < 50 := by omega
                                                                        have heq : n = (n - 16700) + 16700 := by omega
                                                                        rw [heq]
                                                                        exact cs_w34 ⟨n - 16700, hr⟩
                                                                      ·
                                                                        by_cases h35 : n < 16800
                                                                        · have hr : n - 16750 < 50 := by omega
                                                                          have heq : n = (n - 16750) + 16750 := by omega
                                                                          rw [heq]
                                                                          exact cs_w35 ⟨n - 16750, hr⟩
                                                                        ·
                                                                          by_cases h36 : n < 16850
                                                                          · have hr : n - 16800 < 50 := by omega
                                                                            have heq : n = (n - 16800) + 16800 := by omega
                                                                            rw [heq]
                                                                            exact cs_w36 ⟨n - 16800, hr⟩
                                                                          ·
                                                                            by_cases h37 : n < 16900
                                                                            · have hr : n - 16850 < 50 := by omega
                                                                              have heq : n = (n - 16850) + 16850 := by omega
                                                                              rw [heq]
                                                                              exact cs_w37 ⟨n - 16850, hr⟩
                                                                            ·
                                                                              by_cases h38 : n < 16950
                                                                              · have hr : n - 16900 < 50 := by omega
                                                                                have heq : n = (n - 16900) + 16900 := by omega
                                                                                rw [heq]
                                                                                exact cs_w38 ⟨n - 16900, hr⟩
                                                                              ·
                                                                                by_cases h39 : n < 17000
                                                                                · have hr : n - 16950 < 50 := by omega
                                                                                  have heq : n = (n - 16950) + 16950 := by omega
                                                                                  rw [heq]
                                                                                  exact cs_w39 ⟨n - 16950, hr⟩
                                                                                ·
                                                                                  by_cases h40 : n < 17050
                                                                                  · have hr : n - 17000 < 50 := by omega
                                                                                    have heq : n = (n - 17000) + 17000 := by omega
                                                                                    rw [heq]
                                                                                    exact cs_w40 ⟨n - 17000, hr⟩
                                                                                  ·
                                                                                    by_cases h41 : n < 17100
                                                                                    · have hr : n - 17050 < 50 := by omega
                                                                                      have heq : n = (n - 17050) + 17050 := by omega
                                                                                      rw [heq]
                                                                                      exact cs_w41 ⟨n - 17050, hr⟩
                                                                                    ·
                                                                                      by_cases h42 : n < 17150
                                                                                      · have hr : n - 17100 < 50 := by omega
                                                                                        have heq : n = (n - 17100) + 17100 := by omega
                                                                                        rw [heq]
                                                                                        exact cs_w42 ⟨n - 17100, hr⟩
                                                                                      ·
                                                                                        by_cases h43 : n < 17200
                                                                                        · have hr : n - 17150 < 50 := by omega
                                                                                          have heq : n = (n - 17150) + 17150 := by omega
                                                                                          rw [heq]
                                                                                          exact cs_w43 ⟨n - 17150, hr⟩
                                                                                        ·
                                                                                          by_cases h44 : n < 17250
                                                                                          · have hr : n - 17200 < 50 := by omega
                                                                                            have heq : n = (n - 17200) + 17200 := by omega
                                                                                            rw [heq]
                                                                                            exact cs_w44 ⟨n - 17200, hr⟩
                                                                                          ·
                                                                                            by_cases h45 : n < 17300
                                                                                            · have hr : n - 17250 < 50 := by omega
                                                                                              have heq : n = (n - 17250) + 17250 := by omega
                                                                                              rw [heq]
                                                                                              exact cs_w45 ⟨n - 17250, hr⟩
                                                                                            ·
                                                                                              by_cases h46 : n < 17350
                                                                                              · have hr : n - 17300 < 50 := by omega
                                                                                                have heq : n = (n - 17300) + 17300 := by omega
                                                                                                rw [heq]
                                                                                                exact cs_w46 ⟨n - 17300, hr⟩
                                                                                              ·
                                                                                                by_cases h47 : n < 17400
                                                                                                · have hr : n - 17350 < 50 := by omega
                                                                                                  have heq : n = (n - 17350) + 17350 := by omega
                                                                                                  rw [heq]
                                                                                                  exact cs_w47 ⟨n - 17350, hr⟩
                                                                                                ·
                                                                                                  by_cases h48 : n < 17450
                                                                                                  · have hr : n - 17400 < 50 := by omega
                                                                                                    have heq : n = (n - 17400) + 17400 := by omega
                                                                                                    rw [heq]
                                                                                                    exact cs_w48 ⟨n - 17400, hr⟩
                                                                                                  ·
                                                                                                    by_cases h49 : n < 17500
                                                                                                    · have hr : n - 17450 < 50 := by omega
                                                                                                      have heq : n = (n - 17450) + 17450 := by omega
                                                                                                      rw [heq]
                                                                                                      exact cs_w49 ⟨n - 17450, hr⟩
                                                                                                    ·
                                                                                                      by_cases h50 : n < 17550
                                                                                                      · have hr : n - 17500 < 50 := by omega
                                                                                                        have heq : n = (n - 17500) + 17500 := by omega
                                                                                                        rw [heq]
                                                                                                        exact cs_w50 ⟨n - 17500, hr⟩
                                                                                                      ·
                                                                                                        by_cases h51 : n < 17600
                                                                                                        · have hr : n - 17550 < 50 := by omega
                                                                                                          have heq : n = (n - 17550) + 17550 := by omega
                                                                                                          rw [heq]
                                                                                                          exact cs_w51 ⟨n - 17550, hr⟩
                                                                                                        ·
                                                                                                          by_cases h52 : n < 17650
                                                                                                          · have hr : n - 17600 < 50 := by omega
                                                                                                            have heq : n = (n - 17600) + 17600 := by omega
                                                                                                            rw [heq]
                                                                                                            exact cs_w52 ⟨n - 17600, hr⟩
                                                                                                          ·
                                                                                                            by_cases h53 : n < 17700
                                                                                                            · have hr : n - 17650 < 50 := by omega
                                                                                                              have heq : n = (n - 17650) + 17650 := by omega
                                                                                                              rw [heq]
                                                                                                              exact cs_w53 ⟨n - 17650, hr⟩
                                                                                                            ·
                                                                                                              by_cases h54 : n < 17750
                                                                                                              · have hr : n - 17700 < 50 := by omega
                                                                                                                have heq : n = (n - 17700) + 17700 := by omega
                                                                                                                rw [heq]
                                                                                                                exact cs_w54 ⟨n - 17700, hr⟩
                                                                                                              ·
                                                                                                                by_cases h55 : n < 17800
                                                                                                                · have hr : n - 17750 < 50 := by omega
                                                                                                                  have heq : n = (n - 17750) + 17750 := by omega
                                                                                                                  rw [heq]
                                                                                                                  exact cs_w55 ⟨n - 17750, hr⟩
                                                                                                                ·
                                                                                                                  by_cases h56 : n < 17850
                                                                                                                  · have hr : n - 17800 < 50 := by omega
                                                                                                                    have heq : n = (n - 17800) + 17800 := by omega
                                                                                                                    rw [heq]
                                                                                                                    exact cs_w56 ⟨n - 17800, hr⟩
                                                                                                                  ·
                                                                                                                    by_cases h57 : n < 17900
                                                                                                                    · have hr : n - 17850 < 50 := by omega
                                                                                                                      have heq : n = (n - 17850) + 17850 := by omega
                                                                                                                      rw [heq]
                                                                                                                      exact cs_w57 ⟨n - 17850, hr⟩
                                                                                                                    ·
                                                                                                                      by_cases h58 : n < 17950
                                                                                                                      · have hr : n - 17900 < 50 := by omega
                                                                                                                        have heq : n = (n - 17900) + 17900 := by omega
                                                                                                                        rw [heq]
                                                                                                                        exact cs_w58 ⟨n - 17900, hr⟩
                                                                                                                      ·
                                                                                                                        by_cases h59 : n < 18000
                                                                                                                        · have hr : n - 17950 < 50 := by omega
                                                                                                                          have heq : n = (n - 17950) + 17950 := by omega
                                                                                                                          rw [heq]
                                                                                                                          exact cs_w59 ⟨n - 17950, hr⟩
                                                                                                                        ·
                                                                                                                          by_cases h60 : n < 18050
                                                                                                                          · have hr : n - 18000 < 50 := by omega
                                                                                                                            have heq : n = (n - 18000) + 18000 := by omega
                                                                                                                            rw [heq]
                                                                                                                            exact cs_w60 ⟨n - 18000, hr⟩
                                                                                                                          ·
                                                                                                                            by_cases h61 : n < 18100
                                                                                                                            · have hr : n - 18050 < 50 := by omega
                                                                                                                              have heq : n = (n - 18050) + 18050 := by omega
                                                                                                                              rw [heq]
                                                                                                                              exact cs_w61 ⟨n - 18050, hr⟩
                                                                                                                            ·
                                                                                                                              by_cases h62 : n < 18150
                                                                                                                              · have hr : n - 18100 < 50 := by omega
                                                                                                                                have heq : n = (n - 18100) + 18100 := by omega
                                                                                                                                rw [heq]
                                                                                                                                exact cs_w62 ⟨n - 18100, hr⟩
                                                                                                                              ·
                                                                                                                                by_cases h63 : n < 18200
                                                                                                                                · have hr : n - 18150 < 50 := by omega
                                                                                                                                  have heq : n = (n - 18150) + 18150 := by omega
                                                                                                                                  rw [heq]
                                                                                                                                  exact cs_w63 ⟨n - 18150, hr⟩
                                                                                                                                ·
                                                                                                                                  by_cases h64 : n < 18250
                                                                                                                                  · have hr : n - 18200 < 50 := by omega
                                                                                                                                    have heq : n = (n - 18200) + 18200 := by omega
                                                                                                                                    rw [heq]
                                                                                                                                    exact cs_w64 ⟨n - 18200, hr⟩
                                                                                                                                  ·
                                                                                                                                    by_cases h65 : n < 18300
                                                                                                                                    · have hr : n - 18250 < 50 := by omega
                                                                                                                                      have heq : n = (n - 18250) + 18250 := by omega
                                                                                                                                      rw [heq]
                                                                                                                                      exact cs_w65 ⟨n - 18250, hr⟩
                                                                                                                                    ·
                                                                                                                                      by_cases h66 : n < 18350
                                                                                                                                      · have hr : n - 18300 < 50 := by omega
                                                                                                                                        have heq : n = (n - 18300) + 18300 := by omega
                                                                                                                                        rw [heq]
                                                                                                                                        exact cs_w66 ⟨n - 18300, hr⟩
                                                                                                                                      ·
                                                                                                                                        by_cases h67 : n < 18400
                                                                                                                                        · have hr : n - 18350 < 50 := by omega
                                                                                                                                          have heq : n = (n - 18350) + 18350 := by omega
                                                                                                                                          rw [heq]
                                                                                                                                          exact cs_w67 ⟨n - 18350, hr⟩
                                                                                                                                        ·
                                                                                                                                          by_cases h68 : n < 18450
                                                                                                                                          · have hr : n - 18400 < 50 := by omega
                                                                                                                                            have heq : n = (n - 18400) + 18400 := by omega
                                                                                                                                            rw [heq]
                                                                                                                                            exact cs_w68 ⟨n - 18400, hr⟩
                                                                                                                                          ·
                                                                                                                                            by_cases h69 : n < 18500
                                                                                                                                            · have hr : n - 18450 < 50 := by omega
                                                                                                                                              have heq : n = (n - 18450) + 18450 := by omega
                                                                                                                                              rw [heq]
                                                                                                                                              exact cs_w69 ⟨n - 18450, hr⟩
                                                                                                                                            ·
                                                                                                                                              by_cases h70 : n < 18550
                                                                                                                                              · have hr : n - 18500 < 50 := by omega
                                                                                                                                                have heq : n = (n - 18500) + 18500 := by omega
                                                                                                                                                rw [heq]
                                                                                                                                                exact cs_w70 ⟨n - 18500, hr⟩
                                                                                                                                              ·
                                                                                                                                                by_cases h71 : n < 18600
                                                                                                                                                · have hr : n - 18550 < 50 := by omega
                                                                                                                                                  have heq : n = (n - 18550) + 18550 := by omega
                                                                                                                                                  rw [heq]
                                                                                                                                                  exact cs_w71 ⟨n - 18550, hr⟩
                                                                                                                                                ·
                                                                                                                                                  by_cases h72 : n < 18650
                                                                                                                                                  · have hr : n - 18600 < 50 := by omega
                                                                                                                                                    have heq : n = (n - 18600) + 18600 := by omega
                                                                                                                                                    rw [heq]
                                                                                                                                                    exact cs_w72 ⟨n - 18600, hr⟩
                                                                                                                                                  ·
                                                                                                                                                    by_cases h73 : n < 18700
                                                                                                                                                    · have hr : n - 18650 < 50 := by omega
                                                                                                                                                      have heq : n = (n - 18650) + 18650 := by omega
                                                                                                                                                      rw [heq]
                                                                                                                                                      exact cs_w73 ⟨n - 18650, hr⟩
                                                                                                                                                    ·
                                                                                                                                                      by_cases h74 : n < 18750
                                                                                                                                                      · have hr : n - 18700 < 50 := by omega
                                                                                                                                                        have heq : n = (n - 18700) + 18700 := by omega
                                                                                                                                                        rw [heq]
                                                                                                                                                        exact cs_w74 ⟨n - 18700, hr⟩
                                                                                                                                                      ·
                                                                                                                                                        by_cases h75 : n < 18800
                                                                                                                                                        · have hr : n - 18750 < 50 := by omega
                                                                                                                                                          have heq : n = (n - 18750) + 18750 := by omega
                                                                                                                                                          rw [heq]
                                                                                                                                                          exact cs_w75 ⟨n - 18750, hr⟩
                                                                                                                                                        ·
                                                                                                                                                          by_cases h76 : n < 18850
                                                                                                                                                          · have hr : n - 18800 < 50 := by omega
                                                                                                                                                            have heq : n = (n - 18800) + 18800 := by omega
                                                                                                                                                            rw [heq]
                                                                                                                                                            exact cs_w76 ⟨n - 18800, hr⟩
                                                                                                                                                          ·
                                                                                                                                                            by_cases h77 : n < 18900
                                                                                                                                                            · have hr : n - 18850 < 50 := by omega
                                                                                                                                                              have heq : n = (n - 18850) + 18850 := by omega
                                                                                                                                                              rw [heq]
                                                                                                                                                              exact cs_w77 ⟨n - 18850, hr⟩
                                                                                                                                                            ·
                                                                                                                                                              by_cases h78 : n < 18950
                                                                                                                                                              · have hr : n - 18900 < 50 := by omega
                                                                                                                                                                have heq : n = (n - 18900) + 18900 := by omega
                                                                                                                                                                rw [heq]
                                                                                                                                                                exact cs_w78 ⟨n - 18900, hr⟩
                                                                                                                                                              ·
                                                                                                                                                                by_cases h79 : n < 19000
                                                                                                                                                                · have hr : n - 18950 < 50 := by omega
                                                                                                                                                                  have heq : n = (n - 18950) + 18950 := by omega
                                                                                                                                                                  rw [heq]
                                                                                                                                                                  exact cs_w79 ⟨n - 18950, hr⟩
                                                                                                                                                                ·
                                                                                                                                                                  by_cases h80 : n < 19050
                                                                                                                                                                  · have hr : n - 19000 < 50 := by omega
                                                                                                                                                                    have heq : n = (n - 19000) + 19000 := by omega
                                                                                                                                                                    rw [heq]
                                                                                                                                                                    exact cs_w80 ⟨n - 19000, hr⟩
                                                                                                                                                                  ·
                                                                                                                                                                    by_cases h81 : n < 19100
                                                                                                                                                                    · have hr : n - 19050 < 50 := by omega
                                                                                                                                                                      have heq : n = (n - 19050) + 19050 := by omega
                                                                                                                                                                      rw [heq]
                                                                                                                                                                      exact cs_w81 ⟨n - 19050, hr⟩
                                                                                                                                                                    ·
                                                                                                                                                                      by_cases h82 : n < 19150
                                                                                                                                                                      · have hr : n - 19100 < 50 := by omega
                                                                                                                                                                        have heq : n = (n - 19100) + 19100 := by omega
                                                                                                                                                                        rw [heq]
                                                                                                                                                                        exact cs_w82 ⟨n - 19100, hr⟩
                                                                                                                                                                      ·
                                                                                                                                                                        by_cases h83 : n < 19200
                                                                                                                                                                        · have hr : n - 19150 < 50 := by omega
                                                                                                                                                                          have heq : n = (n - 19150) + 19150 := by omega
                                                                                                                                                                          rw [heq]
                                                                                                                                                                          exact cs_w83 ⟨n - 19150, hr⟩
                                                                                                                                                                        ·
                                                                                                                                                                          by_cases h84 : n < 19250
                                                                                                                                                                          · have hr : n - 19200 < 50 := by omega
                                                                                                                                                                            have heq : n = (n - 19200) + 19200 := by omega
                                                                                                                                                                            rw [heq]
                                                                                                                                                                            exact cs_w84 ⟨n - 19200, hr⟩
                                                                                                                                                                          ·
                                                                                                                                                                            by_cases h85 : n < 19300
                                                                                                                                                                            · have hr : n - 19250 < 50 := by omega
                                                                                                                                                                              have heq : n = (n - 19250) + 19250 := by omega
                                                                                                                                                                              rw [heq]
                                                                                                                                                                              exact cs_w85 ⟨n - 19250, hr⟩
                                                                                                                                                                            ·
                                                                                                                                                                              by_cases h86 : n < 19350
                                                                                                                                                                              · have hr : n - 19300 < 50 := by omega
                                                                                                                                                                                have heq : n = (n - 19300) + 19300 := by omega
                                                                                                                                                                                rw [heq]
                                                                                                                                                                                exact cs_w86 ⟨n - 19300, hr⟩
                                                                                                                                                                              ·
                                                                                                                                                                                by_cases h87 : n < 19400
                                                                                                                                                                                · have hr : n - 19350 < 50 := by omega
                                                                                                                                                                                  have heq : n = (n - 19350) + 19350 := by omega
                                                                                                                                                                                  rw [heq]
                                                                                                                                                                                  exact cs_w87 ⟨n - 19350, hr⟩
                                                                                                                                                                                ·
                                                                                                                                                                                  by_cases h88 : n < 19450
                                                                                                                                                                                  · have hr : n - 19400 < 50 := by omega
                                                                                                                                                                                    have heq : n = (n - 19400) + 19400 := by omega
                                                                                                                                                                                    rw [heq]
                                                                                                                                                                                    exact cs_w88 ⟨n - 19400, hr⟩
                                                                                                                                                                                  ·
                                                                                                                                                                                    by_cases h89 : n < 19500
                                                                                                                                                                                    · have hr : n - 19450 < 50 := by omega
                                                                                                                                                                                      have heq : n = (n - 19450) + 19450 := by omega
                                                                                                                                                                                      rw [heq]
                                                                                                                                                                                      exact cs_w89 ⟨n - 19450, hr⟩
                                                                                                                                                                                    ·
                                                                                                                                                                                      by_cases h90 : n < 19550
                                                                                                                                                                                      · have hr : n - 19500 < 50 := by omega
                                                                                                                                                                                        have heq : n = (n - 19500) + 19500 := by omega
                                                                                                                                                                                        rw [heq]
                                                                                                                                                                                        exact cs_w90 ⟨n - 19500, hr⟩
                                                                                                                                                                                      ·
                                                                                                                                                                                        by_cases h91 : n < 19600
                                                                                                                                                                                        · have hr : n - 19550 < 50 := by omega
                                                                                                                                                                                          have heq : n = (n - 19550) + 19550 := by omega
                                                                                                                                                                                          rw [heq]
                                                                                                                                                                                          exact cs_w91 ⟨n - 19550, hr⟩
                                                                                                                                                                                        ·
                                                                                                                                                                                          by_cases h92 : n < 19650
                                                                                                                                                                                          · have hr : n - 19600 < 50 := by omega
                                                                                                                                                                                            have heq : n = (n - 19600) + 19600 := by omega
                                                                                                                                                                                            rw [heq]
                                                                                                                                                                                            exact cs_w92 ⟨n - 19600, hr⟩
                                                                                                                                                                                          ·
                                                                                                                                                                                            by_cases h93 : n < 19700
                                                                                                                                                                                            · have hr : n - 19650 < 50 := by omega
                                                                                                                                                                                              have heq : n = (n - 19650) + 19650 := by omega
                                                                                                                                                                                              rw [heq]
                                                                                                                                                                                              exact cs_w93 ⟨n - 19650, hr⟩
                                                                                                                                                                                            ·
                                                                                                                                                                                              by_cases h94 : n < 19750
                                                                                                                                                                                              · have hr : n - 19700 < 50 := by omega
                                                                                                                                                                                                have heq : n = (n - 19700) + 19700 := by omega
                                                                                                                                                                                                rw [heq]
                                                                                                                                                                                                exact cs_w94 ⟨n - 19700, hr⟩
                                                                                                                                                                                              ·
                                                                                                                                                                                                by_cases h95 : n < 19800
                                                                                                                                                                                                · have hr : n - 19750 < 50 := by omega
                                                                                                                                                                                                  have heq : n = (n - 19750) + 19750 := by omega
                                                                                                                                                                                                  rw [heq]
                                                                                                                                                                                                  exact cs_w95 ⟨n - 19750, hr⟩
                                                                                                                                                                                                ·
                                                                                                                                                                                                  by_cases h96 : n < 19850
                                                                                                                                                                                                  · have hr : n - 19800 < 50 := by omega
                                                                                                                                                                                                    have heq : n = (n - 19800) + 19800 := by omega
                                                                                                                                                                                                    rw [heq]
                                                                                                                                                                                                    exact cs_w96 ⟨n - 19800, hr⟩
                                                                                                                                                                                                  ·
                                                                                                                                                                                                    by_cases h97 : n < 19900
                                                                                                                                                                                                    · have hr : n - 19850 < 50 := by omega
                                                                                                                                                                                                      have heq : n = (n - 19850) + 19850 := by omega
                                                                                                                                                                                                      rw [heq]
                                                                                                                                                                                                      exact cs_w97 ⟨n - 19850, hr⟩
                                                                                                                                                                                                    ·
                                                                                                                                                                                                      by_cases h98 : n < 19950
                                                                                                                                                                                                      · have hr : n - 19900 < 50 := by omega
                                                                                                                                                                                                        have heq : n = (n - 19900) + 19900 := by omega
                                                                                                                                                                                                        rw [heq]
                                                                                                                                                                                                        exact cs_w98 ⟨n - 19900, hr⟩
                                                                                                                                                                                                      ·
                                                                                                                                                                                                        have hr : n - 19950 < 50 := by omega
                                                                                                                                                                                                        have heq : n = (n - 19950) + 19950 := by omega
                                                                                                                                                                                                        rw [heq]
                                                                                                                                                                                                        exact cs_w99 ⟨n - 19950, hr⟩

theorem centF_lt_range : ∀ n, 15000 ≤ n → n < 20000 → centF n < 23 := by
  intro n hlo hhi
  by_cases h0 : n < 15050
  · have hr : n - 15000 < 50 := by omega
    have heq : n = (n - 15000) + 15000 := by omega
    rw [heq]
    exact cl_w0 ⟨n - 15000, hr⟩
  ·
    by_cases h1 : n < 15100
    · have hr : n - 15050 < 50 := by omega
      have heq : n = (n - 15050) + 15050 := by omega
      rw [heq]
      exact cl_w1 ⟨n - 15050, hr⟩
    ·
      by_cases h2 : n < 15150
      · have hr : n - 15100 < 50 := by omega
        have heq : n = (n - 15100) + 15100 := by omega
        rw [heq]
        exact cl_w2 ⟨n - 15100, hr⟩
      ·
        by_cases h3 : n < 15200
        · have hr : n - 15150 < 50 := by omega
          have heq : n = (n - 15150) + 15150 := by omega
          rw [heq]
          exact cl_w3 ⟨n - 15150, hr⟩
        ·
          by_cases h4 : n < 15250
          · have hr : n - 15200 < 50 := by omega
            have heq : n = (n - 15200) + 15200 := by omega
            rw [heq]
            exact cl_w4 ⟨n - 15200, hr⟩
          ·
            by_cases h5 : n < 15300
            · have hr : n - 15250 < 50 := by omega
              have heq : n = (n - 15250) + 15250 := by omega
              rw [heq]
              exact cl_w5 ⟨n - 15250, hr⟩
            ·
              by_cases h6 : n < 15350
              · have hr : n - 15300 < 50 := by omega
                have heq : n = (n - 15300) + 15300 := by omega
                rw [heq]
                exact cl_w6 ⟨n - 15300, hr⟩
              ·
                by_cases h7 : n < 15400
                · have hr : n - 15350 < 50 := by omega
                  have heq : n = (n - 15350) + 15350 := by omega
                  rw [heq]
                  exact cl_w7 ⟨n - 15350, hr⟩
                ·
                  by_cases h8 : n < 15450
                  · have hr : n - 15400 < 50 := by omega
                    have heq : n = (n - 15400) + 15400 := by omega
                    rw [heq]
                    exact cl_w8 ⟨n - 15400, hr⟩
                  ·
                    by_cases h9 : n < 15500
                    · have hr : n - 15450 < 50 := by omega
                      have heq : n = (n - 15450) + 15450 := by omega
                      rw [heq]
                      exact cl_w9 ⟨n - 15450, hr⟩
                    ·
                      by_cases h10 : n < 15550
                      · have hr : n - 15500 < 50 := by omega
                        have heq : n = (n - 15500) + 15500 := by omega
                        rw [heq]
                        exact cl_w10 ⟨n - 15500, hr⟩
                      ·
                        by_cases h11 : n < 15600
                        · have hr : n - 15550 < 50 := by omega
                          have heq : n = (n - 15550) + 15550 := by omega
                          rw [heq]
                          exact cl_w11 ⟨n - 15550, hr⟩
                        ·
                          by_cases h12 : n < 15650
                          · have hr : n - 15600 < 50 := by omega
                            have heq : n = (n - 15600) + 15600 := by omega
                            rw [heq]
                            exact cl_w12 ⟨n - 15600, hr⟩
                          ·
                            by_cases h13 : n < 15700
                            · have hr : n - 15650 < 50 := by omega
                              have heq : n = (n - 15650) + 15650 := by omega
                              rw [heq]
                              exact cl_w13 ⟨n - 15650, hr⟩
                            ·
                              by_cases h14 : n < 15750
                              · have hr : n - 15700 < 50 := by omega
                                have heq : n = (n - 15700) + 15700 := by omega
                                rw [heq]
                                exact cl_w14 ⟨n - 15700, hr⟩
                              ·
                                by_cases h15 : n < 15800
                                · have hr : n - 15750 < 50 := by omega
                                  have heq : n = (n - 15750) + 15750 := by omega
                                  rw [heq]
                                  exact cl_w15 ⟨n - 15750, hr⟩
                                ·
                                  by_cases h16 : n < 15850
                                  · have hr : n - 15800 < 50 := by omega
                                    have heq : n = (n - 15800) + 15800 := by omega
                                    rw [heq]
                                    exact cl_w16 ⟨n - 15800, hr⟩
                                  ·
                                    by_cases h17 : n < 15900
                                    · have hr : n - 15850 < 50 := by omega
                                      have heq : n = (n - 15850) + 15850 := by omega
                                      rw [heq]
                                      exact cl_w17 ⟨n - 15850, hr⟩
                                    ·
                                      by_cases h18 : n < 15950
                                      · have hr : n - 15900 < 50 := by omega
                                        have heq : n = (n - 15900) + 15900 := by omega
                                        rw [heq]
                                        exact cl_w18 ⟨n - 15900, hr⟩
                                      ·
                                        by_cases h19 : n < 16000
                                        · have hr : n - 15950 < 50 := by omega
                                          have heq : n = (n - 15950) + 15950 := by omega
                                          rw [heq]
                                          exact cl_w19 ⟨n - 15950, hr⟩
                                        ·
                                          by_cases h20 : n < 16050
                                          · have hr : n - 16000 < 50 := by omega
                                            have heq : n = (n - 16000) + 16000 := by omega
                                            rw [heq]
                                            exact cl_w20 ⟨n - 16000, hr⟩
                                          ·
                                            by_cases h21 : n < 16100
                                            · have hr : n - 16050 < 50 := by omega
                                              have heq : n = (n - 16050) + 16050 := by omega
                                              rw [heq]
                                              exact cl_w21 ⟨n - 16050, hr⟩
                                            ·
                                              by_cases h22 : n < 16150
                                              · have hr : n - 16100 < 50 := by omega
                                                have heq : n = (n - 16100) + 16100 := by omega
                                                rw [heq]
                                                exact cl_w22 ⟨n - 16100, hr⟩
                                              ·
                                                by_cases h23 : n < 16200
                                                · have hr : n - 16150 < 50 := by omega
                                                  have heq : n = (n - 16150) + 16150 := by omega
                                                  rw [heq]
                                                  exact cl_w23 ⟨n - 16150, hr⟩
                                                ·
                                                  by_cases h24 : n < 16250
                                                  · have hr : n - 16200 < 50 := by omega
                                                    have heq : n = (n - 16200) + 16200 := by omega
                                                    rw [heq]
                                                    exact cl_w24 ⟨n - 16200, hr⟩
                                                  ·
                                                    by_cases h25 : n < 16300
                                                    · have hr : n - 16250 < 50 := by omega
                                                      have heq : n = (n - 16250) + 16250 := by omega
                                                      rw [heq]
                                                      exact cl_w25 ⟨n - 16250, hr⟩
                                                    ·
                                                      by_cases h26 : n < 16350
                                                      · have hr : n - 16300 < 50 := by omega
                                                        have heq : n = (n - 16300) + 16300 := by omega
                                                        rw [heq]
                                                        exact cl_w26 ⟨n - 16300, hr⟩
                                                      ·
                                                        by_cases h27 : n < 16400
                                                        · have hr : n - 16350 < 50 := by omega
                                                          have heq : n = (n - 16350) + 16350 := by omega
                                                          rw [heq]
                                                          exact cl_w27 ⟨n - 16350, hr⟩
                                                        ·
                                                          by_cases h28 : n < 16450
                                                          · have hr : n - 16400 < 50 := by omega
                                                            have heq : n = (n - 16400) + 16400 := by omega
                                                            rw [heq]
                                                            exact cl_w28 ⟨n - 16400, hr⟩
                                                          ·
                                                            by_cases h29 : n < 16500
                                                            · have hr : n - 16450 < 50 := by omega
                                                              have heq : n = (n - 16450) + 16450 := by omega
                                                              rw [heq]
                                                              exact cl_w29 ⟨n - 16450, hr⟩
                                                            ·
                                                              by_cases h30 : n < 16550
                                                              · have hr : n - 16500 < 50 := by omega
                                                                have heq : n = (n - 16500) + 16500 := by omega
                                                                rw [heq]
                                                                exact cl_w30 ⟨n - 16500, hr⟩
                                                              ·
                                                                by_cases h31 : n < 16600
                                                                · have hr : n - 16550 < 50 := by omega
                                                                  have heq : n = (n - 16550) + 16550 := by omega
                                                                  rw [heq]
                                                                  exact cl_w31 ⟨n - 16550, hr⟩
                                                                ·
                                                                  by_cases h32 : n < 16650
                                                                  · have hr : n - 16600 < 50 := by omega
                                                                    have heq : n = (n - 16600) + 16600 := by omega
                                                                    rw [heq]
                                                                    exact cl_w32 ⟨n - 16600, hr⟩
                                                                  ·
                                                                    by_cases h33 : n < 16700
                                                                    · have hr : n - 16650 < 50 := by omega
                                                                      have heq : n = (n - 16650) + 16650 := by omega
                                                                      rw [heq]
                                                                      exact cl_w33 ⟨n - 16650, hr⟩
                                                                    ·
                                                                      by_cases h34 : n < 16750
                                                                      · have hr : n - 16700 < 50 := by omega
                                                                        have heq : n = (n - 16700) + 16700 := by omega
                                                                        rw [heq]
                                                                        exact cl_w34 ⟨n - 16700, hr⟩
                                                                      ·
                                                                        by_cases h35 : n < 16800
                                                                        · have hr : n - 16750 < 50 := by omega
                                                                          have heq : n = (n - 16750) + 16750 := by omega
                                                                          rw [heq]
                                                                          exact cl_w35 ⟨n - 16750, hr⟩
                                                                        ·
                                                                          by_cases h36 : n < 16850
                                                                          · have hr : n - 16800 < 50 := by omega
                                                                            have heq : n = (n - 16800) + 16800 := by omega
                                                                            rw [heq]
                                                                            exact cl_w36 ⟨n - 16800, hr⟩
                                                                          ·
                                                                            by_cases h37 : n < 16900
                                                                            · have hr : n - 16850 < 50 := by omega
                                                                              have heq : n = (n - 16850) + 16850 := by omega
                                                                              rw [heq]
                                                                              exact cl_w37 ⟨n - 16850, hr⟩
                                                                            ·
                                                                              by_cases h38 : n < 16950
                                                                              · have hr : n - 16900 < 50 := by omega
                                                                                have heq : n = (n - 16900) + 16900 := by omega
                                                                                rw [heq]
                                                                                exact cl_w38 ⟨n - 16900, hr⟩
                                                                              ·
                                                                                by_cases h39 : n < 17000
                                                                                · have hr : n - 16950 < 50 := by omega
                                                                                  have heq : n = (n - 16950) + 16950 := by omega
                                                                                  rw [heq]
                                                                                  exact cl_w39 ⟨n - 16950, hr⟩
                                                                                ·
                                                                                  by_cases h40 : n < 17050
                                                                                  · have hr : n - 17000 < 50 := by omega
                                                                                    have heq : n = (n - 17000) + 17000 := by omega
                                                                                    rw [heq]
                                                                                    exact cl_w40 ⟨n - 17000, hr⟩
                                                                                  ·
                                                                                    by_cases h41 : n < 17100
                                                                                    · have hr : n - 17050 < 50 := by omega
                                                                                      have heq : n = (n - 17050) + 17050 := by omega
                                                                                      rw [heq]
                                                                                      exact cl_w41 ⟨n - 17050, hr⟩
                                                                                    ·
                                                                                      by_cases h42 : n < 17150
                                                                                      · have hr : n - 17100 < 50 := by omega
                                                                                        have heq : n = (n - 17100) + 17100 := by omega
                                                                                        rw [heq]
                                                                                        exact cl_w42 ⟨n - 17100, hr⟩
                                                                                      ·
                                                                                        by_cases h43 : n < 17200
                                                                                        · have hr : n - 17150 < 50 := by omega
                                                                                          have heq : n = (n - 17150) + 17150 := by omega
                                                                                          rw [heq]
                                                                                          exact cl_w43 ⟨n - 17150, hr⟩
                                                                                        ·
                                                                                          by_cases h44 : n < 17250
                                                                                          · have hr : n - 17200 < 50 := by omega
                                                                                            have heq : n = (n - 17200) + 17200 := by omega
                                                                                            rw [heq]
                                                                                            exact cl_w44 ⟨n - 17200, hr⟩
                                                                                          ·
                                                                                            by_cases h45 : n < 17300
                                                                                            · have hr : n - 17250 < 50 := by omega
                                                                                              have heq : n = (n - 17250) + 17250 := by omega
                                                                                              rw [heq]
                                                                                              exact cl_w45 ⟨n - 17250, hr⟩
                                                                                            ·
                                                                                              by_cases h46 : n < 17350
                                                                                              · have hr : n - 17300 < 50 := by omega
                                                                                                have heq : n = (n - 17300) + 17300 := by omega
                                                                                                rw [heq]
                                                                                                exact cl_w46 ⟨n - 17300, hr⟩
                                                                                              ·
                                                                                                by_cases h47 : n < 17400
                                                                                                · have hr : n - 17350 < 50 := by omega
                                                                                                  have heq : n = (n - 17350) + 17350 := by omega
                                                                                                  rw [heq]
                                                                                                  exact cl_w47 ⟨n - 17350, hr⟩
                                                                                                ·
                                                                                                  by_cases h48 : n < 17450
                                                                                                  · have hr : n - 17400 < 50 := by omega
                                                                                                    have heq : n = (n - 17400) + 17400 := by omega
                                                                                                    rw [heq]
                                                                                                    exact cl_w48 ⟨n - 17400, hr⟩
                                                                                                  ·
                                                                                                    by_cases h49 : n < 17500
                                                                                                    · have hr : n - 17450 < 50 := by omega
                                                                                                      have heq : n = (n - 17450) + 17450 := by omega
                                                                                                      rw [heq]
                                                                                                      exact cl_w49 ⟨n - 17450, hr⟩
                                                                                                    ·
                                                                                                      by_cases h50 : n < 17550
                                                                                                      · have hr : n - 17500 < 50 := by omega
                                                                                                        have heq : n = (n - 17500) + 17500 := by omega
                                                                                                        rw [heq]
                                                                                                        exact cl_w50 ⟨n - 17500, hr⟩
                                                                                                      ·
                                                                                                        by_cases h51 : n < 17600
                                                                                                        · have hr : n - 17550 < 50 := by omega
                                                                                                          have heq : n = (n - 17550) + 17550 := by omega
                                                                                                          rw [heq]
                                                                                                          exact cl_w51 ⟨n - 17550, hr⟩
                                                                                                        ·
                                                                                                          by_cases h52 : n < 17650
                                                                                                          · have hr : n - 17600 < 50 := by omega
                                                                                                            have heq : n = (n - 17600) + 17600 := by omega
                                                                                                            rw [heq]
                                                                                                            exact cl_w52 ⟨n - 17600, hr⟩
                                                                                                          ·
                                                                                                            by_cases h53 : n < 17700
                                                                                                            · have hr : n - 17650 < 50 := by omega
                                                                                                              have heq : n = (n - 17650) + 17650 := by omega
                                                                                                              rw [heq]
                                                                                                              exact cl_w53 ⟨n - 17650, hr⟩
                                                                                                            ·
                                                                                                              by_cases h54 : n < 17750
                                                                                                              · have hr : n - 17700 < 50 := by omega
                                                                                                                have heq : n = (n - 17700) + 17700 := by omega
                                                                                                                rw [heq]
                                                                                                                exact cl_w54 ⟨n - 17700, hr⟩
                                                                                                              ·
                                                                                                                by_cases h55 : n < 17800
                                                                                                                · have hr : n - 17750 < 50 := by omega
                                                                                                                  have heq : n = (n - 17750) + 17750 := by omega
                                                                                                                  rw [heq]
                                                                                                                  exact cl_w55 ⟨n - 17750, hr⟩
                                                                                                                ·
                                                                                                                  by_cases h56 : n < 17850
                                                                                                                  · have hr : n - 17800 < 50 := by omega
                                                                                                                    have heq : n = (n - 17800) + 17800 := by omega
                                                                                                                    rw [heq]
                                                                                                                    exact cl_w56 ⟨n - 17800, hr⟩
                                                                                                                  ·
                                                                                                                    by_cases h57 : n < 17900
                                                                                                                    · have hr : n - 17850 < 50 := by omega
                                                                                                                      have heq : n = (n - 17850) + 17850 := by omega
                                                                                                                      rw [heq]
                                                                                                                      exact cl_w57 ⟨n - 17850, hr⟩
                                                                                                                    ·
                                                                                                                      by_cases h58 : n < 17950
                                                                                                                      · have hr : n - 17900 < 50 := by omega
                                                                                                                        have heq : n = (n - 17900) + 17900 := by omega
                                                                                                                        rw [heq]
                                                                                                                        exact cl_w58 ⟨n - 17900, hr⟩
                                                                                                                      ·
                                                                                                                        by_cases h59 : n < 18000
                                                                                                                        · have hr : n - 17950 < 50 := by omega
                                                                                                                          have heq : n = (n - 17950) + 17950 := by omega
                                                                                                                          rw [heq]
                                                                                                                          exact cl_w59 ⟨n - 17950, hr⟩
                                                                                                                        ·
                                                                                                                          by_cases h60 : n < 18050
                                                                                                                          · have hr : n - 18000 < 50 := by omega
                                                                                                                            have heq : n = (n - 18000) + 18000 := by omega
                                                                                                                            rw [heq]
                                                                                                                            exact cl_w60 ⟨n - 18000, hr⟩
                                                                                                                          ·
                                                                                                                            by_cases h61 : n < 18100
                                                                                                                            · have hr : n - 18050 < 50 := by omega
                                                                                                                              have heq : n = (n - 18050) + 18050 := by omega
                                                                                                                              rw [heq]
                                                                                                                              exact cl_w61 ⟨n - 18050, hr⟩
                                                                                                                            ·
                                                                                                                              by_cases h62 : n < 18150
                                                                                                                              · have hr : n - 18100 < 50 := by omega
                                                                                                                                have heq : n = (n - 18100) + 18100 := by omega
                                                                                                                                rw [heq]
                                                                                                                                exact cl_w62 ⟨n - 18100, hr⟩
                                                                                                                              ·
                                                                                                                                by_cases h63 : n < 18200
                                                                                                                                · have hr : n - 18150 < 50 := by omega
                                                                                                                                  have heq : n = (n - 18150) + 18150 := by omega
                                                                                                                                  rw [heq]
                                                                                                                                  exact cl_w63 ⟨n - 18150, hr⟩
                                                                                                                                ·
                                                                                                                                  by_cases h64 : n < 18250
                                                                                                                                  · have hr : n - 18200 < 50 := by omega
                                                                                                                                    have heq : n = (n - 18200) + 18200 := by omega
                                                                                                                                    rw [heq]
                                                                                                                                    exact cl_w64 ⟨n - 18200, hr⟩
                                                                                                                                  ·
                                                                                                                                    by_cases h65 : n < 18300
                                                                                                                                    · have hr : n - 18250 < 50 := by omega
                                                                                                                                      have heq : n = (n - 18250) + 18250 := by omega
                                                                                                                                      rw [heq]
                                                                                                                                      exact cl_w65 ⟨n - 18250, hr⟩
                                                                                                                                    ·
                                                                                                                                      by_cases h66 : n < 18350
                                                                                                                                      · have hr : n - 18300 < 50 := by omega
                                                                                                                                        have heq : n = (n - 18300) + 18300 := by omega
                                                                                                                                        rw [heq]
                                                                                                                                        exact cl_w66 ⟨n - 18300, hr⟩
                                                                                                                                      ·
                                                                                                                                        by_cases h67 : n < 18400
                                                                                                                                        · have hr : n - 18350 < 50 := by omega
                                                                                                                                          have heq : n = (n - 18350) + 18350 := by omega
                                                                                                                                          rw [heq]
                                                                                                                                          exact cl_w67 ⟨n - 18350, hr⟩
                                                                                                                                        ·
                                                                                                                                          by_cases h68 : n < 18450
                                                                                                                                          · have hr : n - 18400 < 50 := by omega
                                                                                                                                            have heq : n = (n - 18400) + 18400 := by omega
                                                                                                                                            rw [heq]
                                                                                                                                            exact cl_w68 ⟨n - 18400, hr⟩
                                                                                                                                          ·
                                                                                                                                            by_cases h69 : n < 18500
                                                                                                                                            · have hr : n - 18450 < 50 := by omega
                                                                                                                                              have heq : n = (n - 18450) + 18450 := by omega
                                                                                                                                              rw [heq]
                                                                                                                                              exact cl_w69 ⟨n - 18450, hr⟩
                                                                                                                                            ·
                                                                                                                                              by_cases h70 : n < 18550
                                                                                                                                              · have hr : n - 18500 < 50 := by omega
                                                                                                                                                have heq : n = (n - 18500) + 18500 := by omega
                                                                                                                                                rw [heq]
                                                                                                                                                exact cl_w70 ⟨n - 18500, hr⟩
                                                                                                                                              ·
                                                                                                                                                by_cases h71 : n < 18600
                                                                                                                                                · have hr : n - 18550 < 50 := by omega
                                                                                                                                                  have heq : n = (n - 18550) + 18550 := by omega
                                                                                                                                                  rw [heq]
                                                                                                                                                  exact cl_w71 ⟨n - 18550, hr⟩
                                                                                                                                                ·
                                                                                                                                                  by_cases h72 : n < 18650
                                                                                                                                                  · have hr : n - 18600 < 50 := by omega
                                                                                                                                                    have heq : n = (n - 18600) + 18600 := by omega
                                                                                                                                                    rw [heq]
                                                                                                                                                    exact cl_w72 ⟨n - 18600, hr⟩
                                                                                                                                                  ·
                                                                                                                                                    by_cases h73 : n < 18700
                                                                                                                                                    · have hr : n - 18650 < 50 := by omega
                                                                                                                                                      have heq : n = (n - 18650) + 18650 := by omega
                                                                                                                                                      rw [heq]
                                                                                                                                                      exact cl_w73 ⟨n - 18650, hr⟩
                                                                                                                                                    ·
                                                                                                                                                      by_cases h74 : n < 18750
                                                                                                                                                      · have hr : n - 18700 < 50 := by omega
                                                                                                                                                        have heq : n = (n - 18700) + 18700 := by omega
                                                                                                                                                        rw [heq]
                                                                                                                                                        exact cl_w74 ⟨n - 18700, hr⟩
                                                                                                                                                      ·
                                                                                                                                                        by_cases h75 : n < 18800
                                                                                                                                                        · have hr : n - 18750 < 50 := by omega
                                                                                                                                                          have heq : n = (n - 18750) + 18750 := by omega
                                                                                                                                                          rw [heq]
                                                                                                                                                          exact cl_w75 ⟨n - 18750, hr⟩
                                                                                                                                                        ·
                                                                                                                                                          by_cases h76 : n < 18850
                                                                                                                                                          · have hr : n - 18800 < 50 := by omega
                                                                                                                                                            have heq : n = (n - 18800) + 18800 := by omega
                                                                                                                                                            rw [heq]
                                                                                                                                                            exact cl_w76 ⟨n - 18800, hr⟩
                                                                                                                                                          ·
                                                                                                                                                            by_cases h77 : n < 18900
                                                                                                                                                            · have hr : n - 18850 < 50 := by omega
                                                                                                                                                              have heq : n = (n - 18850) + 18850 := by omega
                                                                                                                                                              rw [heq]
                                                                                                                                                              exact cl_w77 ⟨n - 18850, hr⟩
                                                                                                                                                            ·
                                                                                                                                                              by_cases h78 : n < 18950
                                                                                                                                                              · have hr : n - 18900 < 50 := by omega
                                                                                                                                                                have heq : n = (n - 18900) + 18900 := by omega
                                                                                                                                                                rw [heq]
                                                                                                                                                                exact cl_w78 ⟨n - 18900, hr⟩
                                                                                                                                                              ·
                                                                                                                                                                by_cases h79 : n < 19000
                                                                                                                                                                · have hr : n - 18950 < 50 := by omega
                                                                                                                                                                  have heq : n = (n - 18950) + 18950 := by omega
                                                                                                                                                                  rw [heq]
                                                                                                                                                                  exact cl_w79 ⟨n - 18950, hr⟩
                                                                                                                                                                ·
                                                                                                                                                                  by_cases h80 : n < 19050
                                                                                                                                                                  · have hr : n - 19000 < 50 := by omega
                                                                                                                                                                    have heq : n = (n - 19000) + 19000 := by omega
                                                                                                                                                                    rw [heq]
                                                                                                                                                                    exact cl_w80 ⟨n - 19000, hr⟩
                                                                                                                                                                  ·
                                                                                                                                                                    by_cases h81 : n < 19100
                                                                                                                                                                    · have hr : n - 19050 < 50 := by omega
                                                                                                                                                                      have heq : n = (n - 19050) + 19050 := by omega
                                                                                                                                                                      rw [heq]
                                                                                                                                                                      exact cl_w81 ⟨n - 19050, hr⟩
                                                                                                                                                                    ·
                                                                                                                                                                      by_cases h82 : n < 19150
                                                                                                                                                                      · have hr : n - 19100 < 50 := by omega
                                                                                                                                                                        have heq : n = (n - 19100) + 19100 := by omega
                                                                                                                                                                        rw [heq]
                                                                                                                                                                        exact cl_w82 ⟨n - 19100, hr⟩
                                                                                                                                                                      ·
                                                                                                                                                                        by_cases h83 : n < 19200
                                                                                                                                                                        · have hr : n - 19150 < 50 := by omega
                                                                                                                                                                          have heq : n = (n - 19150) + 19150 := by omega
                                                                                                                                                                          rw [heq]
                                                                                                                                                                          exact cl_w83 ⟨n - 19150, hr⟩
                                                                                                                                                                        ·
                                                                                                                                                                          by_cases h84 : n < 19250
                                                                                                                                                                          · have hr : n - 19200 < 50 := by omega
                                                                                                                                                                            have heq : n = (n - 19200) + 19200 := by omega
                                                                                                                                                                            rw [heq]
                                                                                                                                                                            exact cl_w84 ⟨n - 19200, hr⟩
                                                                                                                                                                          ·
                                                                                                                                                                            by_cases h85 : n < 19300
                                                                                                                                                                            · have hr : n - 19250 < 50 := by omega
                                                                                                                                                                              have heq : n = (n - 19250) + 19250 := by omega
                                                                                                                                                                              rw [heq]
                                                                                                                                                                              exact cl_w85 ⟨n - 19250, hr⟩
                                                                                                                                                                            ·
                                                                                                                                                                              by_cases h86 : n < 19350
                                                                                                                                                                              · have hr : n - 19300 < 50 := by omega
                                                                                                                                                                                have heq : n = (n - 19300) + 19300 := by omega
                                                                                                                                                                                rw [heq]
                                                                                                                                                                                exact cl_w86 ⟨n - 19300, hr⟩
                                                                                                                                                                              ·
                                                                                                                                                                                by_cases h87 : n < 19400
                                                                                                                                                                                · have hr : n - 19350 < 50 := by omega
                                                                                                                                                                                  have heq : n = (n - 19350) + 19350 := by omega
                                                                                                                                                                                  rw [heq]
                                                                                                                                                                                  exact cl_w87 ⟨n - 19350, hr⟩
                                                                                                                                                                                ·
                                                                                                                                                                                  by_cases h88 : n < 19450
                                                                                                                                                                                  · have hr : n - 19400 < 50 := by omega
                                                                                                                                                                                    have heq : n = (n - 19400) + 19400 := by omega
                                                                                                                                                                                    rw [heq]
                                                                                                                                                                                    exact cl_w88 ⟨n - 19400, hr⟩
                                                                                                                                                                                  ·
                                                                                                                                                                                    by_cases h89 : n < 19500
                                                                                                                                                                                    · have hr : n - 19450 < 50 := by omega
                                                                                                                                                                                      have heq : n = (n - 19450) + 19450 := by omega
                                                                                                                                                                                      rw [heq]
                                                                                                                                                                                      exact cl_w89 ⟨n - 19450, hr⟩
                                                                                                                                                                                    ·
                                                                                                                                                                                      by_cases h90 : n < 19550
                                                                                                                                                                                      · have hr : n - 19500 < 50 := by omega
                                                                                                                                                                                        have heq : n = (n - 19500) + 19500 := by omega
                                                                                                                                                                                        rw [heq]
                                                                                                                                                                                        exact cl_w90 ⟨n - 19500, hr⟩
                                                                                                                                                                                      ·
                                                                                                                                                                                        by_cases h91 : n < 19600
                                                                                                                                                                                        · have hr : n - 19550 < 50 := by omega
                                                                                                                                                                                          have heq : n = (n - 19550) + 19550 := by omega
                                                                                                                                                                                          rw [heq]
                                                                                                                                                                                          exact cl_w91 ⟨n - 19550, hr⟩
                                                                                                                                                                                        ·
                                                                                                                                                                                          by_cases h92 : n < 19650
                                                                                                                                                                                          · have hr : n - 19600 < 50 := by omega
                                                                                                                                                                                            have heq : n = (n - 19600) + 19600 := by omega
                                                                                                                                                                                            rw [heq]
                                                                                                                                                                                            exact cl_w92 ⟨n - 19600, hr⟩
                                                                                                                                                                                          ·
                                                                                                                                                                                            by_cases h93 : n < 19700
                                                                                                                                                                                            · have hr : n - 19650 < 50 := by omega
                                                                                                                                                                                              have heq : n = (n - 19650) + 19650 := by omega
                                                                                                                                                                                              rw [heq]
                                                                                                                                                                                              exact cl_w93 ⟨n - 19650, hr⟩
                                                                                                                                                                                            ·
                                                                                                                                                                                              by_cases h94 : n < 19750
                                                                                                                                                                                              · have hr : n - 19700 < 50 := by omega
                                                                                                                                                                                                have heq : n = (n - 19700) + 19700 := by omega
                                                                                                                                                                                                rw [heq]
                                                                                                                                                                                                exact cl_w94 ⟨n - 19700, hr⟩
                                                                                                                                                                                              ·
                                                                                                                                                                                                by_cases h95 : n < 19800
                                                                                                                                                                                                · have hr : n - 19750 < 50 := by omega
                                                                                                                                                                                                  have heq : n = (n - 19750) + 19750 := by omega
                                                                                                                                                                                                  rw [heq]
                                                                                                                                                                                                  exact cl_w95 ⟨n - 19750, hr⟩
                                                                                                                                                                                                ·
                                                                                                                                                                                                  by_cases h96 : n < 19850
                                                                                                                                                                                                  · have hr : n - 19800 < 50 := by omega
                                                                                                                                                                                                    have heq : n = (n - 19800) + 19800 := by omega
                                                                                                                                                                                                    rw [heq]
                                                                                                                                                                                                    exact cl_w96 ⟨n - 19800, hr⟩
                                                                                                                                                                                                  ·
                                                                                                                                                                                                    by_cases h97 : n < 19900
                                                                                                                                                                                                    · have hr : n - 19850 < 50 := by omega
                                                                                                                                                                                                      have heq : n = (n - 19850) + 19850 := by omega
                                                                                                                                                                                                      rw [heq]
                                                                                                                                                                                                      exact cl_w97 ⟨n - 19850, hr⟩
                                                                                                                                                                                                    ·
                                                                                                                                                                                                      by_cases h98 : n < 19950
                                                                                                                                                                                                      · have hr : n - 19900 < 50 := by omega
                                                                                                                                                                                                        have heq : n = (n - 19900) + 19900 := by omega
                                                                                                                                                                                                        rw [heq]
                                                                                                                                                                                                        exact cl_w98 ⟨n - 19900, hr⟩
                                                                                                                                                                                                      ·
                                                                                                                                                                                                        have hr : n - 19950 < 50 := by omega
                                                                                                                                                                                                        have heq : n = (n - 19950) + 19950 := by omega
                                                                                                                                                                                                        rw [heq]
                                                                                                                                                                                                        exact cl_w99 ⟨n - 19950, hr⟩

theorem densSupG_lt_range : ∀ n, 15000 ≤ n → n < 20000 → densSupG n < 2 ^ 1771 := by
  intro n hlo hhi
  by_cases h0 : n < 15050
  · have hr : n - 15000 < 50 := by omega
    have heq : n = (n - 15000) + 15000 := by omega
    rw [heq]
    exact bd_w0 ⟨n - 15000, hr⟩
  ·
    by_cases h1 : n < 15100
    · have hr : n - 15050 < 50 := by omega
      have heq : n = (n - 15050) + 15050 := by omega
      rw [heq]
      exact bd_w1 ⟨n - 15050, hr⟩
    ·
      by_cases h2 : n < 15150
      · have hr : n - 15100 < 50 := by omega
        have heq : n = (n - 15100) + 15100 := by omega
        rw [heq]
        exact bd_w2 ⟨n - 15100, hr⟩
      ·
        by_cases h3 : n < 15200
        · have hr : n - 15150 < 50 := by omega
          have heq : n = (n - 15150) + 15150 := by omega
          rw [heq]
          exact bd_w3 ⟨n - 15150, hr⟩
        ·
          by_cases h4 : n < 15250
          · have hr : n - 15200 < 50 := by omega
            have heq : n = (n - 15200) + 15200 := by omega
            rw [heq]
            exact bd_w4 ⟨n - 15200, hr⟩
          ·
            by_cases h5 : n < 15300
            · have hr : n - 15250 < 50 := by omega
              have heq : n = (n - 15250) + 15250 := by omega
              rw [heq]
              exact bd_w5 ⟨n - 15250, hr⟩
            ·
              by_cases h6 : n < 15350
              · have hr : n - 15300 < 50 := by omega
                have heq : n = (n - 15300) + 15300 := by omega
                rw [heq]
                exact bd_w6 ⟨n - 15300, hr⟩
              ·
                by_cases h7 : n < 15400
                · have hr : n - 15350 < 50 := by omega
                  have heq : n = (n - 15350) + 15350 := by omega
                  rw [heq]
                  exact bd_w7 ⟨n - 15350, hr⟩
                ·
                  by_cases h8 : n < 15450
                  · have hr : n - 15400 < 50 := by omega
                    have heq : n = (n - 15400) + 15400 := by omega
                    rw [heq]
                    exact bd_w8 ⟨n - 15400, hr⟩
                  ·
                    by_cases h9 : n < 15500
                    · have hr : n - 15450 < 50 := by omega
                      have heq : n = (n - 15450) + 15450 := by omega
                      rw [heq]
                      exact bd_w9 ⟨n - 15450, hr⟩
                    ·
                      by_cases h10 : n < 15550
                      · have hr : n - 15500 < 50 := by omega
                        have heq : n = (n - 15500) + 15500 := by omega
                        rw [heq]
                        exact bd_w10 ⟨n - 15500, hr⟩
                      ·
                        by_cases h11 : n < 15600
                        · have hr : n - 15550 < 50 := by omega
                          have heq : n = (n - 15550) + 15550 := by omega
                          rw [heq]
                          exact bd_w11 ⟨n - 15550, hr⟩
                        ·
                          by_cases h12 : n < 15650
                          · have hr : n - 15600 < 50 := by omega
                            have heq : n = (n - 15600) + 15600 := by omega
                            rw [heq]
                            exact bd_w12 ⟨n - 15600, hr⟩
                          ·
                            by_cases h13 : n < 15700
                            · have hr : n - 15650 < 50 := by omega
                              have heq : n = (n - 15650) + 15650 := by omega
                              rw [heq]
                              exact bd_w13 ⟨n - 15650, hr⟩
                            ·
                              by_cases h14 : n < 15750
                              · have hr : n - 15700 < 50 := by omega
                                have heq : n = (n - 15700) + 15700 := by omega
                                rw [heq]
                                exact bd_w14 ⟨n - 15700, hr⟩
                              ·
                                by_cases h15 : n < 15800
                                · have hr : n - 15750 < 50 := by omega
                                  have heq : n = (n - 15750) + 15750 := by omega
                                  rw [heq]
                                  exact bd_w15 ⟨n - 15750, hr⟩
                                ·
                                  by_cases h16 : n < 15850
                                  · have hr : n - 15800 < 50 := by omega
                                    have heq : n = (n - 15800) + 15800 := by omega
                                    rw [heq]
                                    exact bd_w16 ⟨n - 15800, hr⟩
                                  ·
                                    by_cases h17 : n < 15900
                                    · have hr : n - 15850 < 50 := by omega
                                      have heq : n = (n - 15850) + 15850 := by omega
                                      rw [heq]
                                      exact bd_w17 ⟨n - 15850, hr⟩
                                    ·
                                      by_cases h18 : n < 15950
                                      · have hr : n - 15900 < 50 := by omega
                                        have heq : n = (n - 15900) + 15900 := by omega
                                        rw [heq]
                                        exact bd_w18 ⟨n - 15900, hr⟩
                                      ·
                                        by_cases h19 : n < 16000
                                        · have hr : n - 15950 < 50 := by omega
                                          have heq : n = (n - 15950) + 15950 := by omega
                                          rw [heq]
                                          exact bd_w19 ⟨n - 15950, hr⟩
                                        ·
                                          by_cases h20 : n < 16050
                                          · have hr : n - 16000 < 50 := by omega
                                            have heq : n = (n - 16000) + 16000 := by omega
                                            rw [heq]
                                            exact bd_w20 ⟨n - 16000, hr⟩
                                          ·
                                            by_cases h21 : n < 16100
                                            · have hr : n - 16050 < 50 := by omega
                                              have heq : n = (n - 16050) + 16050 := by omega
                                              rw [heq]
                                              exact bd_w21 ⟨n - 16050, hr⟩
                                            ·
                                              by_cases h22 : n < 16150
                                              · have hr : n - 16100 < 50 := by omega
                                                have heq : n = (n - 16100) + 16100 := by omega
                                                rw [heq]
                                                exact bd_w22 ⟨n - 16100, hr⟩
                                              ·
                                                by_cases h23 : n < 16200
                                                · have hr : n - 16150 < 50 := by omega
                                                  have heq : n = (n - 16150) + 16150 := by omega
                                                  rw [heq]
                                                  exact bd_w23 ⟨n - 16150, hr⟩
                                                ·
                                                  by_cases h24 : n < 16250
                                                  · have hr : n - 16200 < 50 := by omega
                                                    have heq : n = (n - 16200) + 16200 := by omega
                                                    rw [heq]
                                                    exact bd_w24 ⟨n - 16200, hr⟩
                                                  ·
                                                    by_cases h25 : n < 16300
                                                    · have hr : n - 16250 < 50 := by omega
                                                      have heq : n = (n - 16250) + 16250 := by omega
                                                      rw [heq]
                                                      exact bd_w25 ⟨n - 16250, hr⟩
                                                    ·
                                                      by_cases h26 : n < 16350
                                                      · have hr : n - 16300 < 50 := by omega
                                                        have heq : n = (n - 16300) + 16300 := by omega
                                                        rw [heq]
                                                        exact bd_w26 ⟨n - 16300, hr⟩
                                                      ·
                                                        by_cases h27 : n < 16400
                                                        · have hr : n - 16350 < 50 := by omega
                                                          have heq : n = (n - 16350) + 16350 := by omega
                                                          rw [heq]
                                                          exact bd_w27 ⟨n - 16350, hr⟩
                                                        ·
                                                          by_cases h28 : n < 16450
                                                          · have hr : n - 16400 < 50 := by omega
                                                            have heq : n = (n - 16400) + 16400 := by omega
                                                            rw [heq]
                                                            exact bd_w28 ⟨n - 16400, hr⟩
                                                          ·
                                                            by_cases h29 : n < 16500
                                                            · have hr : n - 16450 < 50 := by omega
                                                              have heq : n = (n - 16450) + 16450 := by omega
                                                              rw [heq]
                                                              exact bd_w29 ⟨n - 16450, hr⟩
                                                            ·
                                                              by_cases h30 : n < 16550
                                                              · have hr : n - 16500 < 50 := by omega
                                                                have heq : n = (n - 16500) + 16500 := by omega
                                                                rw [heq]
                                                                exact bd_w30 ⟨n - 16500, hr⟩
                                                              ·
                                                                by_cases h31 : n < 16600
                                                                · have hr : n - 16550 < 50 := by omega
                                                                  have heq : n = (n - 16550) + 16550 := by omega
                                                                  rw [heq]
                                                                  exact bd_w31 ⟨n - 16550, hr⟩
                                                                ·
                                                                  by_cases h32 : n < 16650
                                                                  · have hr : n - 16600 < 50 := by omega
                                                                    have heq : n = (n - 16600) + 16600 := by omega
                                                                    rw [heq]
                                                                    exact bd_w32 ⟨n - 16600, hr⟩
                                                                  ·
                                                                    by_cases h33 : n < 16700
                                                                    · have hr : n - 16650 < 50 := by omega
                                                                      have heq : n = (n - 16650) + 16650 := by omega
                                                                      rw [heq]
                                                                      exact bd_w33 ⟨n - 16650, hr⟩
                                                                    ·
                                                                      by_cases h34 : n < 16750
                                                                      · have hr : n - 16700 < 50 := by omega
                                                                        have heq : n = (n - 16700) + 16700 := by omega
                                                                        rw [heq]
                                                                        exact bd_w34 ⟨n - 16700, hr⟩
                                                                      ·
                                                                        by_cases h35 : n < 16800
                                                                        · have hr : n - 16750 < 50 := by omega
                                                                          have heq : n = (n - 16750) + 16750 := by omega
                                                                          rw [heq]
                                                                          exact bd_w35 ⟨n - 16750, hr⟩
                                                                        ·
                                                                          by_cases h36 : n < 16850
                                                                          · have hr : n - 16800 < 50 := by omega
                                                                            have heq : n = (n - 16800) + 16800 := by omega
                                                                            rw [heq]
                                                                            exact bd_w36 ⟨n - 16800, hr⟩
                                                                          ·
                                                                            by_cases h37 : n < 16900
                                                                            · have hr : n - 16850 < 50 := by omega
                                                                              have heq : n = (n - 16850) + 16850 := by omega
                                                                              rw [heq]
                                                                              exact bd_w37 ⟨n - 16850, hr⟩
                                                                            ·
                                                                              by_cases h38 : n < 16950
                                                                              · have hr : n - 16900 < 50 := by omega
                                                                                have heq : n = (n - 16900) + 16900 := by omega
                                                                                rw [heq]
                                                                                exact bd_w38 ⟨n - 16900, hr⟩
                                                                              ·
                                                                                by_cases h39 : n < 17000
                                                                                · have hr : n - 16950 < 50 := by omega
                                                                                  have heq : n = (n - 16950) + 16950 := by omega
                                                                                  rw [heq]
                                                                                  exact bd_w39 ⟨n - 16950, hr⟩
                                                                                ·
                                                                                  by_cases h40 : n < 17050
                                                                                  · have hr : n - 17000 < 50 := by omega
                                                                                    have heq : n = (n - 17000) + 17000 := by omega
                                                                                    rw [heq]
                                                                                    exact bd_w40 ⟨n - 17000, hr⟩
                                                                                  ·
                                                                                    by_cases h41 : n < 17100
                                                                                    · have hr : n - 17050 < 50 := by omega
                                                                                      have heq : n = (n - 17050) + 17050 := by omega
                                                                                      rw [heq]
                                                                                      exact bd_w41 ⟨n - 17050, hr⟩
                                                                                    ·
                                                                                      by_cases h42 : n < 17150
                                                                                      · have hr : n - 17100 < 50 := by omega
                                                                                        have heq : n = (n - 17100) + 17100 := by omega
                                                                                        rw [heq]
                                                                                        exact bd_w42 ⟨n - 17100, hr⟩
                                                                                      ·
                                                                                        by_cases h43 : n < 17200
                                                                                        · have hr : n - 17150 < 50 := by omega
                                                                                          have heq : n = (n - 17150) + 17150 := by omega
                                                                                          rw [heq]
                                                                                          exact bd_w43 ⟨n - 17150, hr⟩
                                                                                        ·
                                                                                          by_cases h44 : n < 17250
                                                                                          · have hr : n - 17200 < 50 := by omega
                                                                                            have heq : n = (n - 17200) + 17200 := by omega
                                                                                            rw [heq]
                                                                                            exact bd_w44 ⟨n - 17200, hr⟩
                                                                                          ·
                                                                                            by_cases h45 : n < 17300
                                                                                            · have hr : n - 17250 < 50 := by omega
                                                                                              have heq : n = (n - 17250) + 17250 := by omega
                                                                                              rw [heq]
                                                                                              exact bd_w45 ⟨n - 17250, hr⟩
                                                                                            ·
                                                                                              by_cases h46 : n < 17350
                                                                                              · have hr : n - 17300 < 50 := by omega
                                                                                                have heq : n = (n - 17300) + 17300 := by omega
                                                                                                rw [heq]
                                                                                                exact bd_w46 ⟨n - 17300, hr⟩
                                                                                              ·
                                                                                                by_cases h47 : n < 17400
                                                                                                · have hr : n - 17350 < 50 := by omega
                                                                                                  have heq : n = (n - 17350) + 17350 := by omega
                                                                                                  rw [heq]
                                                                                                  exact bd_w47 ⟨n - 17350, hr⟩
                                                                                                ·
                                                                                                  by_cases h48 : n < 17450
                                                                                                  · have hr : n - 17400 < 50 := by omega
                                                                                                    have heq : n = (n - 17400) + 17400 := by omega
                                                                                                    rw [heq]
                                                                                                    exact bd_w48 ⟨n - 17400, hr⟩
                                                                                                  ·
                                                                                                    by_cases h49 : n < 17500
                                                                                                    · have hr : n - 17450 < 50 := by omega
                                                                                                      have heq : n = (n - 17450) + 17450 := by omega
                                                                                                      rw [heq]
                                                                                                      exact bd_w49 ⟨n - 17450, hr⟩
                                                                                                    ·
                                                                                                      by_cases h50 : n < 17550
                                                                                                      · have hr : n - 17500 < 50 := by omega
                                                                                                        have heq : n = (n - 17500) + 17500 := by omega
                                                                                                        rw [heq]
                                                                                                        exact bd_w50 ⟨n - 17500, hr⟩
                                                                                                      ·
                                                                                                        by_cases h51 : n < 17600
                                                                                                        · have hr : n - 17550 < 50 := by omega
                                                                                                          have heq : n = (n - 17550) + 17550 := by omega
                                                                                                          rw [heq]
                                                                                                          exact bd_w51 ⟨n - 17550, hr⟩
                                                                                                        ·
                                                                                                          by_cases h52 : n < 17650
                                                                                                          · have hr : n - 17600 < 50 := by omega
                                                                                                            have heq : n = (n - 17600) + 17600 := by omega
                                                                                                            rw [heq]
                                                                                                            exact bd_w52 ⟨n - 17600, hr⟩
                                                                                                          ·
                                                                                                            by_cases h53 : n < 17700
                                                                                                            · have hr : n - 17650 < 50 := by omega
                                                                                                              have heq : n = (n - 17650) + 17650 := by omega
                                                                                                              rw [heq]
                                                                                                              exact bd_w53 ⟨n - 17650, hr⟩
                                                                                                            ·
                                                                                                              by_cases h54 : n < 17750
                                                                                                              · have hr : n - 17700 < 50 := by omega
                                                                                                                have heq : n = (n - 17700) + 17700 := by omega
                                                                                                                rw [heq]
                                                                                                                exact bd_w54 ⟨n - 17700, hr⟩
                                                                                                              ·
                                                                                                                by_cases h55 : n < 17800
                                                                                                                · have hr : n - 17750 < 50 := by omega
                                                                                                                  have heq : n = (n - 17750) + 17750 := by omega
                                                                                                                  rw [heq]
                                                                                                                  exact bd_w55 ⟨n - 17750, hr⟩
                                                                                                                ·
                                                                                                                  by_cases h56 : n < 17850
                                                                                                                  · have hr : n - 17800 < 50 := by omega
                                                                                                                    have heq : n = (n - 17800) + 17800 := by omega
                                                                                                                    rw [heq]
                                                                                                                    exact bd_w56 ⟨n - 17800, hr⟩
                                                                                                                  ·
                                                                                                                    by_cases h57 : n < 17900
                                                                                                                    · have hr : n - 17850 < 50 := by omega
                                                                                                                      have heq : n = (n - 17850) + 17850 := by omega
                                                                                                                      rw [heq]
                                                                                                                      exact bd_w57 ⟨n - 17850, hr⟩
                                                                                                                    ·
                                                                                                                      by_cases h58 : n < 17950
                                                                                                                      · have hr : n - 17900 < 50 := by omega
                                                                                                                        have heq : n = (n - 17900) + 17900 := by omega
                                                                                                                        rw [heq]
                                                                                                                        exact bd_w58 ⟨n - 17900, hr⟩
                                                                                                                      ·
                                                                                                                        by_cases h59 : n < 18000
                                                                                                                        · have hr : n - 17950 < 50 := by omega
                                                                                                                          have heq : n = (n - 17950) + 17950 := by omega
                                                                                                                          rw [heq]
                                                                                                                          exact bd_w59 ⟨n - 17950, hr⟩
                                                                                                                        ·
                                                                                                                          by_cases h60 : n < 18050
                                                                                                                          · have hr : n - 18000 < 50 := by omega
                                                                                                                            have heq : n = (n - 18000) + 18000 := by omega
                                                                                                                            rw [heq]
                                                                                                                            exact bd_w60 ⟨n - 18000, hr⟩
                                                                                                                          ·
                                                                                                                            by_cases h61 : n < 18100
                                                                                                                            · have hr : n - 18050 < 50 := by omega
                                                                                                                              have heq : n = (n - 18050) + 18050 := by omega
                                                                                                                              rw [heq]
                                                                                                                              exact bd_w61 ⟨n - 18050, hr⟩
                                                                                                                            ·
                                                                                                                              by_cases h62 : n < 18150
                                                                                                                              · have hr : n - 18100 < 50 := by omega
                                                                                                                                have heq : n = (n - 18100) + 18100 := by omega
                                                                                                                                rw [heq]
                                                                                                                                exact bd_w62 ⟨n - 18100, hr⟩
                                                                                                                              ·
                                                                                                                                by_cases h63 : n < 18200
                                                                                                                                · have hr : n - 18150 < 50 := by omega
                                                                                                                                  have heq : n = (n - 18150) + 18150 := by omega
                                                                                                                                  rw [heq]
                                                                                                                                  exact bd_w63 ⟨n - 18150, hr⟩
                                                                                                                                ·
                                                                                                                                  by_cases h64 : n < 18250
                                                                                                                                  · have hr : n - 18200 < 50 := by omega
                                                                                                                                    have heq : n = (n - 18200) + 18200 := by omega
                                                                                                                                    rw [heq]
                                                                                                                                    exact bd_w64 ⟨n - 18200, hr⟩
                                                                                                                                  ·
                                                                                                                                    by_cases h65 : n < 18300
                                                                                                                                    · have hr : n - 18250 < 50 := by omega
                                                                                                                                      have heq : n = (n - 18250) + 18250 := by omega
                                                                                                                                      rw [heq]
                                                                                                                                      exact bd_w65 ⟨n - 18250, hr⟩
                                                                                                                                    ·
                                                                                                                                      by_cases h66 : n < 18350
                                                                                                                                      · have hr : n - 18300 < 50 := by omega
                                                                                                                                        have heq : n = (n - 18300) + 18300 := by omega
                                                                                                                                        rw [heq]
                                                                                                                                        exact bd_w66 ⟨n - 18300, hr⟩
                                                                                                                                      ·
                                                                                                                                        by_cases h67 : n < 18400
                                                                                                                                        · have hr : n - 18350 < 50 := by omega
                                                                                                                                          have heq : n = (n - 18350) + 18350 := by omega
                                                                                                                                          rw [heq]
                                                                                                                                          exact bd_w67 ⟨n - 18350, hr⟩
                                                                                                                                        ·
                                                                                                                                          by_cases h68 : n < 18450
                                                                                                                                          · have hr : n - 18400 < 50 := by omega
                                                                                                                                            have heq : n = (n - 18400) + 18400 := by omega
                                                                                                                                            rw [heq]
                                                                                                                                            exact bd_w68 ⟨n - 18400, hr⟩
                                                                                                                                          ·
                                                                                                                                            by_cases h69 : n < 18500
                                                                                                                                            · have hr : n - 18450 < 50 := by omega
                                                                                                                                              have heq : n = (n - 18450) + 18450 := by omega
                                                                                                                                              rw [heq]
                                                                                                                                              exact bd_w69 ⟨n - 18450, hr⟩
                                                                                                                                            ·
                                                                                                                                              by_cases h70 : n < 18550
                                                                                                                                              · have hr : n - 18500 < 50 := by omega
                                                                                                                                                have heq : n = (n - 18500) + 18500 := by omega
                                                                                                                                                rw [heq]
                                                                                                                                                exact bd_w70 ⟨n - 18500, hr⟩
                                                                                                                                              ·
                                                                                                                                                by_cases h71 : n < 18600
                                                                                                                                                · have hr : n - 18550 < 50 := by omega
                                                                                                                                                  have heq : n = (n - 18550) + 18550 := by omega
                                                                                                                                                  rw [heq]
                                                                                                                                                  exact bd_w71 ⟨n - 18550, hr⟩
                                                                                                                                                ·
                                                                                                                                                  by_cases h72 : n < 18650
                                                                                                                                                  · have hr : n - 18600 < 50 := by omega
                                                                                                                                                    have heq : n = (n - 18600) + 18600 := by omega
                                                                                                                                                    rw [heq]
                                                                                                                                                    exact bd_w72 ⟨n - 18600, hr⟩
                                                                                                                                                  ·
                                                                                                                                                    by_cases h73 : n < 18700
                                                                                                                                                    · have hr : n - 18650 < 50 := by omega
                                                                                                                                                      have heq : n = (n - 18650) + 18650 := by omega
                                                                                                                                                      rw [heq]
                                                                                                                                                      exact bd_w73 ⟨n - 18650, hr⟩
                                                                                                                                                    ·
                                                                                                                                                      by_cases h74 : n < 18750
                                                                                                                                                      · have hr : n - 18700 < 50 := by omega
                                                                                                                                                        have heq : n = (n - 18700) + 18700 := by omega
                                                                                                                                                        rw [heq]
                                                                                                                                                        exact bd_w74 ⟨n - 18700, hr⟩
                                                                                                                                                      ·
                                                                                                                                                        by_cases h75 : n < 18800
                                                                                                                                                        · have hr : n - 18750 < 50 := by omega
                                                                                                                                                          have heq : n = (n - 18750) + 18750 := by omega
                                                                                                                                                          rw [heq]
                                                                                                                                                          exact bd_w75 ⟨n - 18750, hr⟩
                                                                                                                                                        ·
                                                                                                                                                          by_cases h76 : n < 18850
                                                                                                                                                          · have hr : n - 18800 < 50 := by omega
                                                                                                                                                            have heq : n = (n - 18800) + 18800 := by omega
                                                                                                                                                            rw [heq]
                                                                                                                                                            exact bd_w76 ⟨n - 18800, hr⟩
                                                                                                                                                          ·
                                                                                                                                                            by_cases h77 : n < 18900
                                                                                                                                                            · have hr : n - 18850 < 50 := by omega
                                                                                                                                                              have heq : n = (n - 18850) + 18850 := by omega
                                                                                                                                                              rw [heq]
                                                                                                                                                              exact bd_w77 ⟨n - 18850, hr⟩
                                                                                                                                                            ·
                                                                                                                                                              by_cases h78 : n < 18950
                                                                                                                                                              · have hr : n - 18900 < 50 := by omega
                                                                                                                                                                have heq : n = (n - 18900) + 18900 := by omega
                                                                                                                                                                rw [heq]
                                                                                                                                                                exact bd_w78 ⟨n - 18900, hr⟩
                                                                                                                                                              ·
                                                                                                                                                                by_cases h79 : n < 19000
                                                                                                                                                                · have hr : n - 18950 < 50 := by omega
                                                                                                                                                                  have heq : n = (n - 18950) + 18950 := by omega
                                                                                                                                                                  rw [heq]
                                                                                                                                                                  exact bd_w79 ⟨n - 18950, hr⟩
                                                                                                                                                                ·
                                                                                                                                                                  by_cases h80 : n < 19050
                                                                                                                                                                  · have hr : n - 19000 < 50 := by omega
                                                                                                                                                                    have heq : n = (n - 19000) + 19000 := by omega
                                                                                                                                                                    rw [heq]
                                                                                                                                                                    exact bd_w80 ⟨n - 19000, hr⟩
                                                                                                                                                                  ·
                                                                                                                                                                    by_cases h81 : n < 19100
                                                                                                                                                                    · have hr : n - 19050 < 50 := by omega
                                                                                                                                                                      have heq : n = (n - 19050) + 19050 := by omega
                                                                                                                                                                      rw [heq]
                                                                                                                                                                      exact bd_w81 ⟨n - 19050, hr⟩
                                                                                                                                                                    ·
                                                                                                                                                                      by_cases h82 : n < 19150
                                                                                                                                                                      · have hr : n - 19100 < 50 := by omega
                                                                                                                                                                        have heq : n = (n - 19100) + 19100 := by omega
                                                                                                                                                                        rw [heq]
                                                                                                                                                                        exact bd_w82 ⟨n - 19100, hr⟩
                                                                                                                                                                      ·
                                                                                                                                                                        by_cases h83 : n < 19200
                                                                                                                                                                        · have hr : n - 19150 < 50 := by omega
                                                                                                                                                                          have heq : n = (n - 19150) + 19150 := by omega
                                                                                                                                                                          rw [heq]
                                                                                                                                                                          exact bd_w83 ⟨n - 19150, hr⟩
                                                                                                                                                                        ·
                                                                                                                                                                          by_cases h84 : n < 19250
                                                                                                                                                                          · have hr : n - 19200 < 50 := by omega
                                                                                                                                                                            have heq : n = (n - 19200) + 19200 := by omega
                                                                                                                                                                            rw [heq]
                                                                                                                                                                            exact bd_w84 ⟨n - 19200, hr⟩
                                                                                                                                                                          ·
                                                                                                                                                                            by_cases h85 : n < 19300
                                                                                                                                                                            · have hr : n - 19250 < 50 := by omega
                                                                                                                                                                              have heq : n = (n - 19250) + 19250 := by omega
                                                                                                                                                                              rw [heq]
                                                                                                                                                                              exact bd_w85 ⟨n - 19250, hr⟩
                                                                                                                                                                            ·
                                                                                                                                                                              by_cases h86 : n < 19350
                                                                                                                                                                              · have hr : n - 19300 < 50 := by omega
                                                                                                                                                                                have heq : n = (n - 19300) + 19300 := by omega
                                                                                                                                                                                rw [heq]
                                                                                                                                                                                exact bd_w86 ⟨n - 19300, hr⟩
                                                                                                                                                                              ·
                                                                                                                                                                                by_cases h87 : n < 19400
                                                                                                                                                                                · have hr : n - 19350 < 50 := by omega
                                                                                                                                                                                  have heq : n = (n - 19350) + 19350 := by omega
                                                                                                                                                                                  rw [heq]
                                                                                                                                                                                  exact bd_w87 ⟨n - 19350, hr⟩
                                                                                                                                                                                ·
                                                                                                                                                                                  by_cases h88 : n < 19450
                                                                                                                                                                                  · have hr : n - 19400 < 50 := by omega
                                                                                                                                                                                    have heq : n = (n - 19400) + 19400 := by omega
                                                                                                                                                                                    rw [heq]
                                                                                                                                                                                    exact bd_w88 ⟨n - 19400, hr⟩
                                                                                                                                                                                  ·
                                                                                                                                                                                    by_cases h89 : n < 19500
                                                                                                                                                                                    · have hr : n - 19450 < 50 := by omega
                                                                                                                                                                                      have heq : n = (n - 19450) + 19450 := by omega
                                                                                                                                                                                      rw [heq]
                                                                                                                                                                                      exact bd_w89 ⟨n - 19450, hr⟩
                                                                                                                                                                                    ·
                                                                                                                                                                                      by_cases h90 : n < 19550
                                                                                                                                                                                      · have hr : n - 19500 < 50 := by omega
                                                                                                                                                                                        have heq : n = (n - 19500) + 19500 := by omega
                                                                                                                                                                                        rw [heq]
                                                                                                                                                                                        exact bd_w90 ⟨n - 19500, hr⟩
                                                                                                                                                                                      ·
                                                                                                                                                                                        by_cases h91 : n < 19600
                                                                                                                                                                                        · have hr : n - 19550 < 50 := by omega
                                                                                                                                                                                          have heq : n = (n - 19550) + 19550 := by omega
                                                                                                                                                                                          rw [heq]
                                                                                                                                                                                          exact bd_w91 ⟨n - 19550, hr⟩
                                                                                                                                                                                        ·
                                                                                                                                                                                          by_cases h92 : n < 19650
                                                                                                                                                                                          · have hr : n - 19600 < 50 := by omega
                                                                                                                                                                                            have heq : n = (n - 19600) + 19600 := by omega
                                                                                                                                                                                            rw [heq]
                                                                                                                                                                                            exact bd_w92 ⟨n - 19600, hr⟩
                                                                                                                                                                                          ·
                                                                                                                                                                                            by_cases h93 : n < 19700
                                                                                                                                                                                            · have hr : n - 19650 < 50 := by omega
                                                                                                                                                                                              have heq : n = (n - 19650) + 19650 := by omega
                                                                                                                                                                                              rw [heq]
                                                                                                                                                                                              exact bd_w93 ⟨n - 19650, hr⟩
                                                                                                                                                                                            ·
                                                                                                                                                                                              by_cases h94 : n < 19750
                                                                                                                                                                                              · have hr : n - 19700 < 50 := by omega
                                                                                                                                                                                                have heq : n = (n - 19700) + 19700 := by omega
                                                                                                                                                                                                rw [heq]
                                                                                                                                                                                                exact bd_w94 ⟨n - 19700, hr⟩
                                                                                                                                                                                              ·
                                                                                                                                                                                                by_cases h95 : n < 19800
                                                                                                                                                                                                · have hr : n - 19750 < 50 := by omega
                                                                                                                                                                                                  have heq : n = (n - 19750) + 19750 := by omega
                                                                                                                                                                                                  rw [heq]
                                                                                                                                                                                                  exact bd_w95 ⟨n - 19750, hr⟩
                                                                                                                                                                                                ·
                                                                                                                                                                                                  by_cases h96 : n < 19850
                                                                                                                                                                                                  · have hr : n - 19800 < 50 := by omega
                                                                                                                                                                                                    have heq : n = (n - 19800) + 19800 := by omega
                                                                                                                                                                                                    rw [heq]
                                                                                                                                                                                                    exact bd_w96 ⟨n - 19800, hr⟩
                                                                                                                                                                                                  ·
                                                                                                                                                                                                    by_cases h97 : n < 19900
                                                                                                                                                                                                    · have hr : n - 19850 < 50 := by omega
                                                                                                                                                                                                      have heq : n = (n - 19850) + 19850 := by omega
                                                                                                                                                                                                      rw [heq]
                                                                                                                                                                                                      exact bd_w97 ⟨n - 19850, hr⟩
                                                                                                                                                                                                    ·
                                                                                                                                                                                                      by_cases h98 : n < 19950
                                                                                                                                                                                                      · have hr : n - 19900 < 50 := by omega
                                                                                                                                                                                                        have heq : n = (n - 19900) + 19900 := by omega
                                                                                                                                                                                                        rw [heq]
                                                                                                                                                                                                        exact bd_w98 ⟨n - 19900, hr⟩
                                                                                                                                                                                                      ·
                                                                                                                                                                                                        have hr : n - 19950 < 50 := by omega
                                                                                                                                                                                                        have heq : n = (n - 19950) + 19950 := by omega
                                                                                                                                                                                                        rw [heq]
                                                                                                                                                                                                        exact bd_w99 ⟨n - 19950, hr⟩

end IntMul.Kappa.R8.Bit.Oppbank.CentBound3


