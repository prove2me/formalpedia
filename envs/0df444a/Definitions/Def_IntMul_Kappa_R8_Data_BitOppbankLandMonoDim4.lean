-- Prove2me | Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankLandMonoDim4
-- name    : IntMul_Kappa_R8_Data_BitOppbankLandMonoDim4
-- status  : Definition
-- author  : @Ethan Cheung Wang
-- created : 2026-10-28T21:09:40.427669+00:00
-- url     : https://prove2.me/theorems/5025dfad-c043-4284-a927-2412c7c1b805
-- title:
--   Dim-gated densSup land mono pack 4
-- statement:
--   # Dim-gated densSup land certificates, pack 4
--
--   For densified windows covering roughly $[10000,12500)$,
--   $$
--   \dim F(\mathrm{arg}_i n)<\dim F(n)
--   \Rightarrow
--   \mathrm{densSupG}(\mathrm{arg}_i n)\mathbin{\&}\mathrm{densSupG}(n)=\mathrm{densSupG}(\mathrm{arg}_i n).
--   $$
--   `decide` on Fin 50 (no `native_decide`).
-- source:
--   R8 BitOppbank densSup_land_mono

-- LandMonoDim pack 4: dim-gated densSupG child-land on windows starting in offsets list
-- Proves (dimF(arg_i n) < dimF n) → land(densSupG(arg_i n), densSupG n)=densSupG(arg_i n)

import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankPnd
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankSupG
import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 1000000
set_option exponentiation.threshold 2000

open IntMul.Kappa.R8.Bit.Oppbank.Pnd
open IntMul.Kappa.R8.Bit.Oppbank.SupG

namespace IntMul.Kappa.R8.Bit.Oppbank.LandMonoDim4

private def arg0 (n : ℕ) : ℕ := Nat.land (argF n) 65535
private def arg1 (n : ℕ) : ℕ := Nat.shiftRight (argF n) 16

private theorem m0_w0 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 10000))) (dimF (n.val + 10000)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 10000))) (densSupG (n.val + 10000))) (densSupG (arg0 (n.val + 10000)))) = true := by decide
private theorem m1_w0 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 10000))) (dimF (n.val + 10000)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 10000))) (densSupG (n.val + 10000))) (densSupG (arg1 (n.val + 10000)))) = true := by decide
private theorem m0_w1 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 10050))) (dimF (n.val + 10050)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 10050))) (densSupG (n.val + 10050))) (densSupG (arg0 (n.val + 10050)))) = true := by decide
private theorem m1_w1 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 10050))) (dimF (n.val + 10050)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 10050))) (densSupG (n.val + 10050))) (densSupG (arg1 (n.val + 10050)))) = true := by decide
private theorem m0_w2 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 10100))) (dimF (n.val + 10100)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 10100))) (densSupG (n.val + 10100))) (densSupG (arg0 (n.val + 10100)))) = true := by decide
private theorem m1_w2 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 10100))) (dimF (n.val + 10100)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 10100))) (densSupG (n.val + 10100))) (densSupG (arg1 (n.val + 10100)))) = true := by decide
private theorem m0_w3 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 10150))) (dimF (n.val + 10150)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 10150))) (densSupG (n.val + 10150))) (densSupG (arg0 (n.val + 10150)))) = true := by decide
private theorem m1_w3 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 10150))) (dimF (n.val + 10150)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 10150))) (densSupG (n.val + 10150))) (densSupG (arg1 (n.val + 10150)))) = true := by decide
private theorem m0_w4 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 10200))) (dimF (n.val + 10200)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 10200))) (densSupG (n.val + 10200))) (densSupG (arg0 (n.val + 10200)))) = true := by decide
private theorem m1_w4 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 10200))) (dimF (n.val + 10200)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 10200))) (densSupG (n.val + 10200))) (densSupG (arg1 (n.val + 10200)))) = true := by decide
private theorem m0_w5 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 10250))) (dimF (n.val + 10250)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 10250))) (densSupG (n.val + 10250))) (densSupG (arg0 (n.val + 10250)))) = true := by decide
private theorem m1_w5 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 10250))) (dimF (n.val + 10250)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 10250))) (densSupG (n.val + 10250))) (densSupG (arg1 (n.val + 10250)))) = true := by decide
private theorem m0_w6 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 10300))) (dimF (n.val + 10300)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 10300))) (densSupG (n.val + 10300))) (densSupG (arg0 (n.val + 10300)))) = true := by decide
private theorem m1_w6 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 10300))) (dimF (n.val + 10300)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 10300))) (densSupG (n.val + 10300))) (densSupG (arg1 (n.val + 10300)))) = true := by decide
private theorem m0_w7 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 10350))) (dimF (n.val + 10350)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 10350))) (densSupG (n.val + 10350))) (densSupG (arg0 (n.val + 10350)))) = true := by decide
private theorem m1_w7 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 10350))) (dimF (n.val + 10350)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 10350))) (densSupG (n.val + 10350))) (densSupG (arg1 (n.val + 10350)))) = true := by decide
private theorem m0_w8 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 10400))) (dimF (n.val + 10400)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 10400))) (densSupG (n.val + 10400))) (densSupG (arg0 (n.val + 10400)))) = true := by decide
private theorem m1_w8 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 10400))) (dimF (n.val + 10400)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 10400))) (densSupG (n.val + 10400))) (densSupG (arg1 (n.val + 10400)))) = true := by decide
private theorem m0_w9 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 10450))) (dimF (n.val + 10450)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 10450))) (densSupG (n.val + 10450))) (densSupG (arg0 (n.val + 10450)))) = true := by decide
private theorem m1_w9 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 10450))) (dimF (n.val + 10450)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 10450))) (densSupG (n.val + 10450))) (densSupG (arg1 (n.val + 10450)))) = true := by decide
private theorem m0_w10 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 10500))) (dimF (n.val + 10500)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 10500))) (densSupG (n.val + 10500))) (densSupG (arg0 (n.val + 10500)))) = true := by decide
private theorem m1_w10 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 10500))) (dimF (n.val + 10500)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 10500))) (densSupG (n.val + 10500))) (densSupG (arg1 (n.val + 10500)))) = true := by decide
private theorem m0_w11 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 10550))) (dimF (n.val + 10550)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 10550))) (densSupG (n.val + 10550))) (densSupG (arg0 (n.val + 10550)))) = true := by decide
private theorem m1_w11 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 10550))) (dimF (n.val + 10550)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 10550))) (densSupG (n.val + 10550))) (densSupG (arg1 (n.val + 10550)))) = true := by decide
private theorem m0_w12 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 10600))) (dimF (n.val + 10600)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 10600))) (densSupG (n.val + 10600))) (densSupG (arg0 (n.val + 10600)))) = true := by decide
private theorem m1_w12 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 10600))) (dimF (n.val + 10600)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 10600))) (densSupG (n.val + 10600))) (densSupG (arg1 (n.val + 10600)))) = true := by decide
private theorem m0_w13 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 10650))) (dimF (n.val + 10650)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 10650))) (densSupG (n.val + 10650))) (densSupG (arg0 (n.val + 10650)))) = true := by decide
private theorem m1_w13 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 10650))) (dimF (n.val + 10650)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 10650))) (densSupG (n.val + 10650))) (densSupG (arg1 (n.val + 10650)))) = true := by decide
private theorem m0_w14 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 10700))) (dimF (n.val + 10700)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 10700))) (densSupG (n.val + 10700))) (densSupG (arg0 (n.val + 10700)))) = true := by decide
private theorem m1_w14 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 10700))) (dimF (n.val + 10700)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 10700))) (densSupG (n.val + 10700))) (densSupG (arg1 (n.val + 10700)))) = true := by decide
private theorem m0_w15 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 10750))) (dimF (n.val + 10750)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 10750))) (densSupG (n.val + 10750))) (densSupG (arg0 (n.val + 10750)))) = true := by decide
private theorem m1_w15 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 10750))) (dimF (n.val + 10750)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 10750))) (densSupG (n.val + 10750))) (densSupG (arg1 (n.val + 10750)))) = true := by decide
private theorem m0_w16 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 10800))) (dimF (n.val + 10800)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 10800))) (densSupG (n.val + 10800))) (densSupG (arg0 (n.val + 10800)))) = true := by decide
private theorem m1_w16 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 10800))) (dimF (n.val + 10800)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 10800))) (densSupG (n.val + 10800))) (densSupG (arg1 (n.val + 10800)))) = true := by decide
private theorem m0_w17 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 10850))) (dimF (n.val + 10850)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 10850))) (densSupG (n.val + 10850))) (densSupG (arg0 (n.val + 10850)))) = true := by decide
private theorem m1_w17 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 10850))) (dimF (n.val + 10850)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 10850))) (densSupG (n.val + 10850))) (densSupG (arg1 (n.val + 10850)))) = true := by decide
private theorem m0_w18 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 10900))) (dimF (n.val + 10900)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 10900))) (densSupG (n.val + 10900))) (densSupG (arg0 (n.val + 10900)))) = true := by decide
private theorem m1_w18 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 10900))) (dimF (n.val + 10900)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 10900))) (densSupG (n.val + 10900))) (densSupG (arg1 (n.val + 10900)))) = true := by decide
private theorem m0_w19 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 10950))) (dimF (n.val + 10950)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 10950))) (densSupG (n.val + 10950))) (densSupG (arg0 (n.val + 10950)))) = true := by decide
private theorem m1_w19 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 10950))) (dimF (n.val + 10950)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 10950))) (densSupG (n.val + 10950))) (densSupG (arg1 (n.val + 10950)))) = true := by decide
private theorem m0_w20 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 11000))) (dimF (n.val + 11000)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 11000))) (densSupG (n.val + 11000))) (densSupG (arg0 (n.val + 11000)))) = true := by decide
private theorem m1_w20 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 11000))) (dimF (n.val + 11000)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 11000))) (densSupG (n.val + 11000))) (densSupG (arg1 (n.val + 11000)))) = true := by decide
private theorem m0_w21 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 11050))) (dimF (n.val + 11050)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 11050))) (densSupG (n.val + 11050))) (densSupG (arg0 (n.val + 11050)))) = true := by decide
private theorem m1_w21 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 11050))) (dimF (n.val + 11050)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 11050))) (densSupG (n.val + 11050))) (densSupG (arg1 (n.val + 11050)))) = true := by decide
private theorem m0_w22 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 11100))) (dimF (n.val + 11100)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 11100))) (densSupG (n.val + 11100))) (densSupG (arg0 (n.val + 11100)))) = true := by decide
private theorem m1_w22 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 11100))) (dimF (n.val + 11100)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 11100))) (densSupG (n.val + 11100))) (densSupG (arg1 (n.val + 11100)))) = true := by decide
private theorem m0_w23 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 11150))) (dimF (n.val + 11150)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 11150))) (densSupG (n.val + 11150))) (densSupG (arg0 (n.val + 11150)))) = true := by decide
private theorem m1_w23 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 11150))) (dimF (n.val + 11150)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 11150))) (densSupG (n.val + 11150))) (densSupG (arg1 (n.val + 11150)))) = true := by decide
private theorem m0_w24 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 11200))) (dimF (n.val + 11200)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 11200))) (densSupG (n.val + 11200))) (densSupG (arg0 (n.val + 11200)))) = true := by decide
private theorem m1_w24 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 11200))) (dimF (n.val + 11200)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 11200))) (densSupG (n.val + 11200))) (densSupG (arg1 (n.val + 11200)))) = true := by decide
private theorem m0_w25 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 11250))) (dimF (n.val + 11250)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 11250))) (densSupG (n.val + 11250))) (densSupG (arg0 (n.val + 11250)))) = true := by decide
private theorem m1_w25 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 11250))) (dimF (n.val + 11250)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 11250))) (densSupG (n.val + 11250))) (densSupG (arg1 (n.val + 11250)))) = true := by decide
private theorem m0_w26 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 11300))) (dimF (n.val + 11300)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 11300))) (densSupG (n.val + 11300))) (densSupG (arg0 (n.val + 11300)))) = true := by decide
private theorem m1_w26 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 11300))) (dimF (n.val + 11300)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 11300))) (densSupG (n.val + 11300))) (densSupG (arg1 (n.val + 11300)))) = true := by decide
private theorem m0_w27 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 11350))) (dimF (n.val + 11350)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 11350))) (densSupG (n.val + 11350))) (densSupG (arg0 (n.val + 11350)))) = true := by decide
private theorem m1_w27 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 11350))) (dimF (n.val + 11350)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 11350))) (densSupG (n.val + 11350))) (densSupG (arg1 (n.val + 11350)))) = true := by decide
private theorem m0_w28 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 11400))) (dimF (n.val + 11400)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 11400))) (densSupG (n.val + 11400))) (densSupG (arg0 (n.val + 11400)))) = true := by decide
private theorem m1_w28 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 11400))) (dimF (n.val + 11400)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 11400))) (densSupG (n.val + 11400))) (densSupG (arg1 (n.val + 11400)))) = true := by decide
private theorem m0_w29 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 11450))) (dimF (n.val + 11450)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 11450))) (densSupG (n.val + 11450))) (densSupG (arg0 (n.val + 11450)))) = true := by decide
private theorem m1_w29 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 11450))) (dimF (n.val + 11450)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 11450))) (densSupG (n.val + 11450))) (densSupG (arg1 (n.val + 11450)))) = true := by decide
private theorem m0_w30 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 11500))) (dimF (n.val + 11500)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 11500))) (densSupG (n.val + 11500))) (densSupG (arg0 (n.val + 11500)))) = true := by decide
private theorem m1_w30 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 11500))) (dimF (n.val + 11500)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 11500))) (densSupG (n.val + 11500))) (densSupG (arg1 (n.val + 11500)))) = true := by decide
private theorem m0_w31 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 11550))) (dimF (n.val + 11550)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 11550))) (densSupG (n.val + 11550))) (densSupG (arg0 (n.val + 11550)))) = true := by decide
private theorem m1_w31 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 11550))) (dimF (n.val + 11550)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 11550))) (densSupG (n.val + 11550))) (densSupG (arg1 (n.val + 11550)))) = true := by decide
private theorem m0_w32 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 11600))) (dimF (n.val + 11600)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 11600))) (densSupG (n.val + 11600))) (densSupG (arg0 (n.val + 11600)))) = true := by decide
private theorem m1_w32 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 11600))) (dimF (n.val + 11600)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 11600))) (densSupG (n.val + 11600))) (densSupG (arg1 (n.val + 11600)))) = true := by decide
private theorem m0_w33 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 11650))) (dimF (n.val + 11650)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 11650))) (densSupG (n.val + 11650))) (densSupG (arg0 (n.val + 11650)))) = true := by decide
private theorem m1_w33 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 11650))) (dimF (n.val + 11650)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 11650))) (densSupG (n.val + 11650))) (densSupG (arg1 (n.val + 11650)))) = true := by decide
private theorem m0_w34 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 11700))) (dimF (n.val + 11700)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 11700))) (densSupG (n.val + 11700))) (densSupG (arg0 (n.val + 11700)))) = true := by decide
private theorem m1_w34 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 11700))) (dimF (n.val + 11700)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 11700))) (densSupG (n.val + 11700))) (densSupG (arg1 (n.val + 11700)))) = true := by decide
private theorem m0_w35 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 11750))) (dimF (n.val + 11750)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 11750))) (densSupG (n.val + 11750))) (densSupG (arg0 (n.val + 11750)))) = true := by decide
private theorem m1_w35 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 11750))) (dimF (n.val + 11750)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 11750))) (densSupG (n.val + 11750))) (densSupG (arg1 (n.val + 11750)))) = true := by decide
private theorem m0_w36 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 11800))) (dimF (n.val + 11800)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 11800))) (densSupG (n.val + 11800))) (densSupG (arg0 (n.val + 11800)))) = true := by decide
private theorem m1_w36 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 11800))) (dimF (n.val + 11800)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 11800))) (densSupG (n.val + 11800))) (densSupG (arg1 (n.val + 11800)))) = true := by decide
private theorem m0_w37 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 11850))) (dimF (n.val + 11850)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 11850))) (densSupG (n.val + 11850))) (densSupG (arg0 (n.val + 11850)))) = true := by decide
private theorem m1_w37 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 11850))) (dimF (n.val + 11850)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 11850))) (densSupG (n.val + 11850))) (densSupG (arg1 (n.val + 11850)))) = true := by decide
private theorem m0_w38 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 11900))) (dimF (n.val + 11900)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 11900))) (densSupG (n.val + 11900))) (densSupG (arg0 (n.val + 11900)))) = true := by decide
private theorem m1_w38 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 11900))) (dimF (n.val + 11900)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 11900))) (densSupG (n.val + 11900))) (densSupG (arg1 (n.val + 11900)))) = true := by decide
private theorem m0_w39 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 11950))) (dimF (n.val + 11950)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 11950))) (densSupG (n.val + 11950))) (densSupG (arg0 (n.val + 11950)))) = true := by decide
private theorem m1_w39 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 11950))) (dimF (n.val + 11950)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 11950))) (densSupG (n.val + 11950))) (densSupG (arg1 (n.val + 11950)))) = true := by decide
private theorem m0_w40 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 12000))) (dimF (n.val + 12000)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 12000))) (densSupG (n.val + 12000))) (densSupG (arg0 (n.val + 12000)))) = true := by decide
private theorem m1_w40 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 12000))) (dimF (n.val + 12000)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 12000))) (densSupG (n.val + 12000))) (densSupG (arg1 (n.val + 12000)))) = true := by decide
private theorem m0_w41 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 12050))) (dimF (n.val + 12050)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 12050))) (densSupG (n.val + 12050))) (densSupG (arg0 (n.val + 12050)))) = true := by decide
private theorem m1_w41 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 12050))) (dimF (n.val + 12050)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 12050))) (densSupG (n.val + 12050))) (densSupG (arg1 (n.val + 12050)))) = true := by decide
private theorem m0_w42 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 12100))) (dimF (n.val + 12100)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 12100))) (densSupG (n.val + 12100))) (densSupG (arg0 (n.val + 12100)))) = true := by decide
private theorem m1_w42 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 12100))) (dimF (n.val + 12100)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 12100))) (densSupG (n.val + 12100))) (densSupG (arg1 (n.val + 12100)))) = true := by decide
private theorem m0_w43 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 12150))) (dimF (n.val + 12150)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 12150))) (densSupG (n.val + 12150))) (densSupG (arg0 (n.val + 12150)))) = true := by decide
private theorem m1_w43 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 12150))) (dimF (n.val + 12150)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 12150))) (densSupG (n.val + 12150))) (densSupG (arg1 (n.val + 12150)))) = true := by decide
private theorem m0_w44 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 12200))) (dimF (n.val + 12200)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 12200))) (densSupG (n.val + 12200))) (densSupG (arg0 (n.val + 12200)))) = true := by decide
private theorem m1_w44 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 12200))) (dimF (n.val + 12200)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 12200))) (densSupG (n.val + 12200))) (densSupG (arg1 (n.val + 12200)))) = true := by decide
private theorem m0_w45 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 12250))) (dimF (n.val + 12250)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 12250))) (densSupG (n.val + 12250))) (densSupG (arg0 (n.val + 12250)))) = true := by decide
private theorem m1_w45 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 12250))) (dimF (n.val + 12250)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 12250))) (densSupG (n.val + 12250))) (densSupG (arg1 (n.val + 12250)))) = true := by decide
private theorem m0_w46 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 12300))) (dimF (n.val + 12300)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 12300))) (densSupG (n.val + 12300))) (densSupG (arg0 (n.val + 12300)))) = true := by decide
private theorem m1_w46 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 12300))) (dimF (n.val + 12300)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 12300))) (densSupG (n.val + 12300))) (densSupG (arg1 (n.val + 12300)))) = true := by decide
private theorem m0_w47 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 12350))) (dimF (n.val + 12350)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 12350))) (densSupG (n.val + 12350))) (densSupG (arg0 (n.val + 12350)))) = true := by decide
private theorem m1_w47 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 12350))) (dimF (n.val + 12350)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 12350))) (densSupG (n.val + 12350))) (densSupG (arg1 (n.val + 12350)))) = true := by decide
private theorem m0_w48 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 12400))) (dimF (n.val + 12400)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 12400))) (densSupG (n.val + 12400))) (densSupG (arg0 (n.val + 12400)))) = true := by decide
private theorem m1_w48 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 12400))) (dimF (n.val + 12400)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 12400))) (densSupG (n.val + 12400))) (densSupG (arg1 (n.val + 12400)))) = true := by decide
private theorem m0_w49 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 12450))) (dimF (n.val + 12450)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 12450))) (densSupG (n.val + 12450))) (densSupG (arg0 (n.val + 12450)))) = true := by decide
private theorem m1_w49 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 12450))) (dimF (n.val + 12450)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 12450))) (densSupG (n.val + 12450))) (densSupG (arg1 (n.val + 12450)))) = true := by decide

end IntMul.Kappa.R8.Bit.Oppbank.LandMonoDim4


