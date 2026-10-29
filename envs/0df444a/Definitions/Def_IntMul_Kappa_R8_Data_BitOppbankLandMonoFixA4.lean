-- Prove2me | Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankLandMonoFixA4
-- name    : IntMul_Kappa_R8_Data_BitOppbankLandMonoFixA4
-- status  : Definition
-- author  : @Ethan Cheung Wang
-- created : 2026-10-28T21:13:22.266204+00:00
-- url     : https://prove2.me/theorems/223e8f3f-beb0-4cee-a221-1d8e23ff306b
-- title:
--   Dim-gated densSup land mono FixA pack 4
-- statement:
--   # Dim-gated densSup land (PndFix), pack A4
--
--   Range consolidators for $n\in[10000,12500)$.
-- source:
--   R8 BitOppbank PndFix

-- LandMonoFixA4: PUBLIC dim-gated land + range consolidators (PndFix)
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankPndFix
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankSupG
import Mathlib
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 12000000
set_option maxRecDepth 1000000
set_option exponentiation.threshold 2000
open IntMul.Kappa.R8.Bit.Oppbank.Pnd
open IntMul.Kappa.R8.Bit.Oppbank.SupG
namespace IntMul.Kappa.R8.Bit.Oppbank.LandMonoFixA4
def arg0 (n : ℕ) : ℕ := Nat.land (argF n) 65535
def arg1 (n : ℕ) : ℕ := Nat.shiftRight (argF n) 16
theorem m0_w0 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 10000))) (dimF (n.val + 10000)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 10000))) (densSupG (n.val + 10000))) (densSupG (arg0 (n.val + 10000)))) = true := by decide
theorem m1_w0 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 10000))) (dimF (n.val + 10000)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 10000))) (densSupG (n.val + 10000))) (densSupG (arg1 (n.val + 10000)))) = true := by decide
theorem m0_w1 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 10050))) (dimF (n.val + 10050)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 10050))) (densSupG (n.val + 10050))) (densSupG (arg0 (n.val + 10050)))) = true := by decide
theorem m1_w1 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 10050))) (dimF (n.val + 10050)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 10050))) (densSupG (n.val + 10050))) (densSupG (arg1 (n.val + 10050)))) = true := by decide
theorem m0_w2 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 10100))) (dimF (n.val + 10100)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 10100))) (densSupG (n.val + 10100))) (densSupG (arg0 (n.val + 10100)))) = true := by decide
theorem m1_w2 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 10100))) (dimF (n.val + 10100)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 10100))) (densSupG (n.val + 10100))) (densSupG (arg1 (n.val + 10100)))) = true := by decide
theorem m0_w3 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 10150))) (dimF (n.val + 10150)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 10150))) (densSupG (n.val + 10150))) (densSupG (arg0 (n.val + 10150)))) = true := by decide
theorem m1_w3 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 10150))) (dimF (n.val + 10150)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 10150))) (densSupG (n.val + 10150))) (densSupG (arg1 (n.val + 10150)))) = true := by decide
theorem m0_w4 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 10200))) (dimF (n.val + 10200)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 10200))) (densSupG (n.val + 10200))) (densSupG (arg0 (n.val + 10200)))) = true := by decide
theorem m1_w4 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 10200))) (dimF (n.val + 10200)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 10200))) (densSupG (n.val + 10200))) (densSupG (arg1 (n.val + 10200)))) = true := by decide
theorem m0_w5 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 10250))) (dimF (n.val + 10250)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 10250))) (densSupG (n.val + 10250))) (densSupG (arg0 (n.val + 10250)))) = true := by decide
theorem m1_w5 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 10250))) (dimF (n.val + 10250)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 10250))) (densSupG (n.val + 10250))) (densSupG (arg1 (n.val + 10250)))) = true := by decide
theorem m0_w6 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 10300))) (dimF (n.val + 10300)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 10300))) (densSupG (n.val + 10300))) (densSupG (arg0 (n.val + 10300)))) = true := by decide
theorem m1_w6 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 10300))) (dimF (n.val + 10300)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 10300))) (densSupG (n.val + 10300))) (densSupG (arg1 (n.val + 10300)))) = true := by decide
theorem m0_w7 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 10350))) (dimF (n.val + 10350)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 10350))) (densSupG (n.val + 10350))) (densSupG (arg0 (n.val + 10350)))) = true := by decide
theorem m1_w7 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 10350))) (dimF (n.val + 10350)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 10350))) (densSupG (n.val + 10350))) (densSupG (arg1 (n.val + 10350)))) = true := by decide
theorem m0_w8 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 10400))) (dimF (n.val + 10400)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 10400))) (densSupG (n.val + 10400))) (densSupG (arg0 (n.val + 10400)))) = true := by decide
theorem m1_w8 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 10400))) (dimF (n.val + 10400)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 10400))) (densSupG (n.val + 10400))) (densSupG (arg1 (n.val + 10400)))) = true := by decide
theorem m0_w9 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 10450))) (dimF (n.val + 10450)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 10450))) (densSupG (n.val + 10450))) (densSupG (arg0 (n.val + 10450)))) = true := by decide
theorem m1_w9 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 10450))) (dimF (n.val + 10450)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 10450))) (densSupG (n.val + 10450))) (densSupG (arg1 (n.val + 10450)))) = true := by decide
theorem m0_w10 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 10500))) (dimF (n.val + 10500)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 10500))) (densSupG (n.val + 10500))) (densSupG (arg0 (n.val + 10500)))) = true := by decide
theorem m1_w10 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 10500))) (dimF (n.val + 10500)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 10500))) (densSupG (n.val + 10500))) (densSupG (arg1 (n.val + 10500)))) = true := by decide
theorem m0_w11 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 10550))) (dimF (n.val + 10550)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 10550))) (densSupG (n.val + 10550))) (densSupG (arg0 (n.val + 10550)))) = true := by decide
theorem m1_w11 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 10550))) (dimF (n.val + 10550)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 10550))) (densSupG (n.val + 10550))) (densSupG (arg1 (n.val + 10550)))) = true := by decide
theorem m0_w12 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 10600))) (dimF (n.val + 10600)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 10600))) (densSupG (n.val + 10600))) (densSupG (arg0 (n.val + 10600)))) = true := by decide
theorem m1_w12 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 10600))) (dimF (n.val + 10600)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 10600))) (densSupG (n.val + 10600))) (densSupG (arg1 (n.val + 10600)))) = true := by decide
theorem m0_w13 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 10650))) (dimF (n.val + 10650)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 10650))) (densSupG (n.val + 10650))) (densSupG (arg0 (n.val + 10650)))) = true := by decide
theorem m1_w13 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 10650))) (dimF (n.val + 10650)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 10650))) (densSupG (n.val + 10650))) (densSupG (arg1 (n.val + 10650)))) = true := by decide
theorem m0_w14 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 10700))) (dimF (n.val + 10700)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 10700))) (densSupG (n.val + 10700))) (densSupG (arg0 (n.val + 10700)))) = true := by decide
theorem m1_w14 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 10700))) (dimF (n.val + 10700)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 10700))) (densSupG (n.val + 10700))) (densSupG (arg1 (n.val + 10700)))) = true := by decide
theorem m0_w15 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 10750))) (dimF (n.val + 10750)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 10750))) (densSupG (n.val + 10750))) (densSupG (arg0 (n.val + 10750)))) = true := by decide
theorem m1_w15 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 10750))) (dimF (n.val + 10750)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 10750))) (densSupG (n.val + 10750))) (densSupG (arg1 (n.val + 10750)))) = true := by decide
theorem m0_w16 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 10800))) (dimF (n.val + 10800)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 10800))) (densSupG (n.val + 10800))) (densSupG (arg0 (n.val + 10800)))) = true := by decide
theorem m1_w16 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 10800))) (dimF (n.val + 10800)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 10800))) (densSupG (n.val + 10800))) (densSupG (arg1 (n.val + 10800)))) = true := by decide
theorem m0_w17 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 10850))) (dimF (n.val + 10850)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 10850))) (densSupG (n.val + 10850))) (densSupG (arg0 (n.val + 10850)))) = true := by decide
theorem m1_w17 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 10850))) (dimF (n.val + 10850)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 10850))) (densSupG (n.val + 10850))) (densSupG (arg1 (n.val + 10850)))) = true := by decide
theorem m0_w18 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 10900))) (dimF (n.val + 10900)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 10900))) (densSupG (n.val + 10900))) (densSupG (arg0 (n.val + 10900)))) = true := by decide
theorem m1_w18 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 10900))) (dimF (n.val + 10900)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 10900))) (densSupG (n.val + 10900))) (densSupG (arg1 (n.val + 10900)))) = true := by decide
theorem m0_w19 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 10950))) (dimF (n.val + 10950)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 10950))) (densSupG (n.val + 10950))) (densSupG (arg0 (n.val + 10950)))) = true := by decide
theorem m1_w19 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 10950))) (dimF (n.val + 10950)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 10950))) (densSupG (n.val + 10950))) (densSupG (arg1 (n.val + 10950)))) = true := by decide
theorem m0_w20 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 11000))) (dimF (n.val + 11000)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 11000))) (densSupG (n.val + 11000))) (densSupG (arg0 (n.val + 11000)))) = true := by decide
theorem m1_w20 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 11000))) (dimF (n.val + 11000)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 11000))) (densSupG (n.val + 11000))) (densSupG (arg1 (n.val + 11000)))) = true := by decide
theorem m0_w21 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 11050))) (dimF (n.val + 11050)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 11050))) (densSupG (n.val + 11050))) (densSupG (arg0 (n.val + 11050)))) = true := by decide
theorem m1_w21 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 11050))) (dimF (n.val + 11050)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 11050))) (densSupG (n.val + 11050))) (densSupG (arg1 (n.val + 11050)))) = true := by decide
theorem m0_w22 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 11100))) (dimF (n.val + 11100)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 11100))) (densSupG (n.val + 11100))) (densSupG (arg0 (n.val + 11100)))) = true := by decide
theorem m1_w22 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 11100))) (dimF (n.val + 11100)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 11100))) (densSupG (n.val + 11100))) (densSupG (arg1 (n.val + 11100)))) = true := by decide
theorem m0_w23 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 11150))) (dimF (n.val + 11150)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 11150))) (densSupG (n.val + 11150))) (densSupG (arg0 (n.val + 11150)))) = true := by decide
theorem m1_w23 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 11150))) (dimF (n.val + 11150)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 11150))) (densSupG (n.val + 11150))) (densSupG (arg1 (n.val + 11150)))) = true := by decide
theorem m0_w24 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 11200))) (dimF (n.val + 11200)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 11200))) (densSupG (n.val + 11200))) (densSupG (arg0 (n.val + 11200)))) = true := by decide
theorem m1_w24 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 11200))) (dimF (n.val + 11200)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 11200))) (densSupG (n.val + 11200))) (densSupG (arg1 (n.val + 11200)))) = true := by decide
theorem m0_w25 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 11250))) (dimF (n.val + 11250)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 11250))) (densSupG (n.val + 11250))) (densSupG (arg0 (n.val + 11250)))) = true := by decide
theorem m1_w25 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 11250))) (dimF (n.val + 11250)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 11250))) (densSupG (n.val + 11250))) (densSupG (arg1 (n.val + 11250)))) = true := by decide
theorem m0_w26 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 11300))) (dimF (n.val + 11300)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 11300))) (densSupG (n.val + 11300))) (densSupG (arg0 (n.val + 11300)))) = true := by decide
theorem m1_w26 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 11300))) (dimF (n.val + 11300)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 11300))) (densSupG (n.val + 11300))) (densSupG (arg1 (n.val + 11300)))) = true := by decide
theorem m0_w27 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 11350))) (dimF (n.val + 11350)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 11350))) (densSupG (n.val + 11350))) (densSupG (arg0 (n.val + 11350)))) = true := by decide
theorem m1_w27 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 11350))) (dimF (n.val + 11350)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 11350))) (densSupG (n.val + 11350))) (densSupG (arg1 (n.val + 11350)))) = true := by decide
theorem m0_w28 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 11400))) (dimF (n.val + 11400)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 11400))) (densSupG (n.val + 11400))) (densSupG (arg0 (n.val + 11400)))) = true := by decide
theorem m1_w28 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 11400))) (dimF (n.val + 11400)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 11400))) (densSupG (n.val + 11400))) (densSupG (arg1 (n.val + 11400)))) = true := by decide
theorem m0_w29 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 11450))) (dimF (n.val + 11450)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 11450))) (densSupG (n.val + 11450))) (densSupG (arg0 (n.val + 11450)))) = true := by decide
theorem m1_w29 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 11450))) (dimF (n.val + 11450)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 11450))) (densSupG (n.val + 11450))) (densSupG (arg1 (n.val + 11450)))) = true := by decide
theorem m0_w30 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 11500))) (dimF (n.val + 11500)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 11500))) (densSupG (n.val + 11500))) (densSupG (arg0 (n.val + 11500)))) = true := by decide
theorem m1_w30 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 11500))) (dimF (n.val + 11500)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 11500))) (densSupG (n.val + 11500))) (densSupG (arg1 (n.val + 11500)))) = true := by decide
theorem m0_w31 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 11550))) (dimF (n.val + 11550)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 11550))) (densSupG (n.val + 11550))) (densSupG (arg0 (n.val + 11550)))) = true := by decide
theorem m1_w31 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 11550))) (dimF (n.val + 11550)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 11550))) (densSupG (n.val + 11550))) (densSupG (arg1 (n.val + 11550)))) = true := by decide
theorem m0_w32 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 11600))) (dimF (n.val + 11600)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 11600))) (densSupG (n.val + 11600))) (densSupG (arg0 (n.val + 11600)))) = true := by decide
theorem m1_w32 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 11600))) (dimF (n.val + 11600)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 11600))) (densSupG (n.val + 11600))) (densSupG (arg1 (n.val + 11600)))) = true := by decide
theorem m0_w33 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 11650))) (dimF (n.val + 11650)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 11650))) (densSupG (n.val + 11650))) (densSupG (arg0 (n.val + 11650)))) = true := by decide
theorem m1_w33 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 11650))) (dimF (n.val + 11650)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 11650))) (densSupG (n.val + 11650))) (densSupG (arg1 (n.val + 11650)))) = true := by decide
theorem m0_w34 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 11700))) (dimF (n.val + 11700)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 11700))) (densSupG (n.val + 11700))) (densSupG (arg0 (n.val + 11700)))) = true := by decide
theorem m1_w34 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 11700))) (dimF (n.val + 11700)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 11700))) (densSupG (n.val + 11700))) (densSupG (arg1 (n.val + 11700)))) = true := by decide
theorem m0_w35 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 11750))) (dimF (n.val + 11750)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 11750))) (densSupG (n.val + 11750))) (densSupG (arg0 (n.val + 11750)))) = true := by decide
theorem m1_w35 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 11750))) (dimF (n.val + 11750)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 11750))) (densSupG (n.val + 11750))) (densSupG (arg1 (n.val + 11750)))) = true := by decide
theorem m0_w36 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 11800))) (dimF (n.val + 11800)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 11800))) (densSupG (n.val + 11800))) (densSupG (arg0 (n.val + 11800)))) = true := by decide
theorem m1_w36 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 11800))) (dimF (n.val + 11800)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 11800))) (densSupG (n.val + 11800))) (densSupG (arg1 (n.val + 11800)))) = true := by decide
theorem m0_w37 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 11850))) (dimF (n.val + 11850)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 11850))) (densSupG (n.val + 11850))) (densSupG (arg0 (n.val + 11850)))) = true := by decide
theorem m1_w37 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 11850))) (dimF (n.val + 11850)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 11850))) (densSupG (n.val + 11850))) (densSupG (arg1 (n.val + 11850)))) = true := by decide
theorem m0_w38 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 11900))) (dimF (n.val + 11900)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 11900))) (densSupG (n.val + 11900))) (densSupG (arg0 (n.val + 11900)))) = true := by decide
theorem m1_w38 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 11900))) (dimF (n.val + 11900)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 11900))) (densSupG (n.val + 11900))) (densSupG (arg1 (n.val + 11900)))) = true := by decide
theorem m0_w39 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 11950))) (dimF (n.val + 11950)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 11950))) (densSupG (n.val + 11950))) (densSupG (arg0 (n.val + 11950)))) = true := by decide
theorem m1_w39 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 11950))) (dimF (n.val + 11950)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 11950))) (densSupG (n.val + 11950))) (densSupG (arg1 (n.val + 11950)))) = true := by decide
theorem m0_w40 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 12000))) (dimF (n.val + 12000)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 12000))) (densSupG (n.val + 12000))) (densSupG (arg0 (n.val + 12000)))) = true := by decide
theorem m1_w40 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 12000))) (dimF (n.val + 12000)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 12000))) (densSupG (n.val + 12000))) (densSupG (arg1 (n.val + 12000)))) = true := by decide
theorem m0_w41 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 12050))) (dimF (n.val + 12050)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 12050))) (densSupG (n.val + 12050))) (densSupG (arg0 (n.val + 12050)))) = true := by decide
theorem m1_w41 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 12050))) (dimF (n.val + 12050)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 12050))) (densSupG (n.val + 12050))) (densSupG (arg1 (n.val + 12050)))) = true := by decide
theorem m0_w42 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 12100))) (dimF (n.val + 12100)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 12100))) (densSupG (n.val + 12100))) (densSupG (arg0 (n.val + 12100)))) = true := by decide
theorem m1_w42 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 12100))) (dimF (n.val + 12100)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 12100))) (densSupG (n.val + 12100))) (densSupG (arg1 (n.val + 12100)))) = true := by decide
theorem m0_w43 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 12150))) (dimF (n.val + 12150)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 12150))) (densSupG (n.val + 12150))) (densSupG (arg0 (n.val + 12150)))) = true := by decide
theorem m1_w43 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 12150))) (dimF (n.val + 12150)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 12150))) (densSupG (n.val + 12150))) (densSupG (arg1 (n.val + 12150)))) = true := by decide
theorem m0_w44 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 12200))) (dimF (n.val + 12200)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 12200))) (densSupG (n.val + 12200))) (densSupG (arg0 (n.val + 12200)))) = true := by decide
theorem m1_w44 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 12200))) (dimF (n.val + 12200)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 12200))) (densSupG (n.val + 12200))) (densSupG (arg1 (n.val + 12200)))) = true := by decide
theorem m0_w45 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 12250))) (dimF (n.val + 12250)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 12250))) (densSupG (n.val + 12250))) (densSupG (arg0 (n.val + 12250)))) = true := by decide
theorem m1_w45 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 12250))) (dimF (n.val + 12250)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 12250))) (densSupG (n.val + 12250))) (densSupG (arg1 (n.val + 12250)))) = true := by decide
theorem m0_w46 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 12300))) (dimF (n.val + 12300)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 12300))) (densSupG (n.val + 12300))) (densSupG (arg0 (n.val + 12300)))) = true := by decide
theorem m1_w46 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 12300))) (dimF (n.val + 12300)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 12300))) (densSupG (n.val + 12300))) (densSupG (arg1 (n.val + 12300)))) = true := by decide
theorem m0_w47 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 12350))) (dimF (n.val + 12350)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 12350))) (densSupG (n.val + 12350))) (densSupG (arg0 (n.val + 12350)))) = true := by decide
theorem m1_w47 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 12350))) (dimF (n.val + 12350)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 12350))) (densSupG (n.val + 12350))) (densSupG (arg1 (n.val + 12350)))) = true := by decide
theorem m0_w48 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 12400))) (dimF (n.val + 12400)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 12400))) (densSupG (n.val + 12400))) (densSupG (arg0 (n.val + 12400)))) = true := by decide
theorem m1_w48 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 12400))) (dimF (n.val + 12400)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 12400))) (densSupG (n.val + 12400))) (densSupG (arg1 (n.val + 12400)))) = true := by decide
theorem m0_w49 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 12450))) (dimF (n.val + 12450)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 12450))) (densSupG (n.val + 12450))) (densSupG (arg0 (n.val + 12450)))) = true := by decide
theorem m1_w49 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 12450))) (dimF (n.val + 12450)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 12450))) (densSupG (n.val + 12450))) (densSupG (arg1 (n.val + 12450)))) = true := by decide
theorem land0_range (n : ℕ) (hn0 : 10000 ≤ n) (hn1 : n < 12500) :
    (!Nat.blt (dimF (arg0 n)) (dimF n) ||
      Nat.beq (Nat.land (densSupG (arg0 n)) (densSupG n)) (densSupG (arg0 n))) = true := by
  by_cases h0 : n < 10050
  · have hoff : 10000 ≤ n := by omega
    have hnfin : n - 10000 < 50 := by omega
    simpa [Nat.sub_add_cancel hoff] using m0_w0 ⟨n - 10000, hnfin⟩
  ·
    by_cases h1 : n < 10100
    · have hoff : 10050 ≤ n := by omega
      have hnfin : n - 10050 < 50 := by omega
      simpa [Nat.sub_add_cancel hoff] using m0_w1 ⟨n - 10050, hnfin⟩
    ·
      by_cases h2 : n < 10150
      · have hoff : 10100 ≤ n := by omega
        have hnfin : n - 10100 < 50 := by omega
        simpa [Nat.sub_add_cancel hoff] using m0_w2 ⟨n - 10100, hnfin⟩
      ·
        by_cases h3 : n < 10200
        · have hoff : 10150 ≤ n := by omega
          have hnfin : n - 10150 < 50 := by omega
          simpa [Nat.sub_add_cancel hoff] using m0_w3 ⟨n - 10150, hnfin⟩
        ·
          by_cases h4 : n < 10250
          · have hoff : 10200 ≤ n := by omega
            have hnfin : n - 10200 < 50 := by omega
            simpa [Nat.sub_add_cancel hoff] using m0_w4 ⟨n - 10200, hnfin⟩
          ·
            by_cases h5 : n < 10300
            · have hoff : 10250 ≤ n := by omega
              have hnfin : n - 10250 < 50 := by omega
              simpa [Nat.sub_add_cancel hoff] using m0_w5 ⟨n - 10250, hnfin⟩
            ·
              by_cases h6 : n < 10350
              · have hoff : 10300 ≤ n := by omega
                have hnfin : n - 10300 < 50 := by omega
                simpa [Nat.sub_add_cancel hoff] using m0_w6 ⟨n - 10300, hnfin⟩
              ·
                by_cases h7 : n < 10400
                · have hoff : 10350 ≤ n := by omega
                  have hnfin : n - 10350 < 50 := by omega
                  simpa [Nat.sub_add_cancel hoff] using m0_w7 ⟨n - 10350, hnfin⟩
                ·
                  by_cases h8 : n < 10450
                  · have hoff : 10400 ≤ n := by omega
                    have hnfin : n - 10400 < 50 := by omega
                    simpa [Nat.sub_add_cancel hoff] using m0_w8 ⟨n - 10400, hnfin⟩
                  ·
                    by_cases h9 : n < 10500
                    · have hoff : 10450 ≤ n := by omega
                      have hnfin : n - 10450 < 50 := by omega
                      simpa [Nat.sub_add_cancel hoff] using m0_w9 ⟨n - 10450, hnfin⟩
                    ·
                      by_cases h10 : n < 10550
                      · have hoff : 10500 ≤ n := by omega
                        have hnfin : n - 10500 < 50 := by omega
                        simpa [Nat.sub_add_cancel hoff] using m0_w10 ⟨n - 10500, hnfin⟩
                      ·
                        by_cases h11 : n < 10600
                        · have hoff : 10550 ≤ n := by omega
                          have hnfin : n - 10550 < 50 := by omega
                          simpa [Nat.sub_add_cancel hoff] using m0_w11 ⟨n - 10550, hnfin⟩
                        ·
                          by_cases h12 : n < 10650
                          · have hoff : 10600 ≤ n := by omega
                            have hnfin : n - 10600 < 50 := by omega
                            simpa [Nat.sub_add_cancel hoff] using m0_w12 ⟨n - 10600, hnfin⟩
                          ·
                            by_cases h13 : n < 10700
                            · have hoff : 10650 ≤ n := by omega
                              have hnfin : n - 10650 < 50 := by omega
                              simpa [Nat.sub_add_cancel hoff] using m0_w13 ⟨n - 10650, hnfin⟩
                            ·
                              by_cases h14 : n < 10750
                              · have hoff : 10700 ≤ n := by omega
                                have hnfin : n - 10700 < 50 := by omega
                                simpa [Nat.sub_add_cancel hoff] using m0_w14 ⟨n - 10700, hnfin⟩
                              ·
                                by_cases h15 : n < 10800
                                · have hoff : 10750 ≤ n := by omega
                                  have hnfin : n - 10750 < 50 := by omega
                                  simpa [Nat.sub_add_cancel hoff] using m0_w15 ⟨n - 10750, hnfin⟩
                                ·
                                  by_cases h16 : n < 10850
                                  · have hoff : 10800 ≤ n := by omega
                                    have hnfin : n - 10800 < 50 := by omega
                                    simpa [Nat.sub_add_cancel hoff] using m0_w16 ⟨n - 10800, hnfin⟩
                                  ·
                                    by_cases h17 : n < 10900
                                    · have hoff : 10850 ≤ n := by omega
                                      have hnfin : n - 10850 < 50 := by omega
                                      simpa [Nat.sub_add_cancel hoff] using m0_w17 ⟨n - 10850, hnfin⟩
                                    ·
                                      by_cases h18 : n < 10950
                                      · have hoff : 10900 ≤ n := by omega
                                        have hnfin : n - 10900 < 50 := by omega
                                        simpa [Nat.sub_add_cancel hoff] using m0_w18 ⟨n - 10900, hnfin⟩
                                      ·
                                        by_cases h19 : n < 11000
                                        · have hoff : 10950 ≤ n := by omega
                                          have hnfin : n - 10950 < 50 := by omega
                                          simpa [Nat.sub_add_cancel hoff] using m0_w19 ⟨n - 10950, hnfin⟩
                                        ·
                                          by_cases h20 : n < 11050
                                          · have hoff : 11000 ≤ n := by omega
                                            have hnfin : n - 11000 < 50 := by omega
                                            simpa [Nat.sub_add_cancel hoff] using m0_w20 ⟨n - 11000, hnfin⟩
                                          ·
                                            by_cases h21 : n < 11100
                                            · have hoff : 11050 ≤ n := by omega
                                              have hnfin : n - 11050 < 50 := by omega
                                              simpa [Nat.sub_add_cancel hoff] using m0_w21 ⟨n - 11050, hnfin⟩
                                            ·
                                              by_cases h22 : n < 11150
                                              · have hoff : 11100 ≤ n := by omega
                                                have hnfin : n - 11100 < 50 := by omega
                                                simpa [Nat.sub_add_cancel hoff] using m0_w22 ⟨n - 11100, hnfin⟩
                                              ·
                                                by_cases h23 : n < 11200
                                                · have hoff : 11150 ≤ n := by omega
                                                  have hnfin : n - 11150 < 50 := by omega
                                                  simpa [Nat.sub_add_cancel hoff] using m0_w23 ⟨n - 11150, hnfin⟩
                                                ·
                                                  by_cases h24 : n < 11250
                                                  · have hoff : 11200 ≤ n := by omega
                                                    have hnfin : n - 11200 < 50 := by omega
                                                    simpa [Nat.sub_add_cancel hoff] using m0_w24 ⟨n - 11200, hnfin⟩
                                                  ·
                                                    by_cases h25 : n < 11300
                                                    · have hoff : 11250 ≤ n := by omega
                                                      have hnfin : n - 11250 < 50 := by omega
                                                      simpa [Nat.sub_add_cancel hoff] using m0_w25 ⟨n - 11250, hnfin⟩
                                                    ·
                                                      by_cases h26 : n < 11350
                                                      · have hoff : 11300 ≤ n := by omega
                                                        have hnfin : n - 11300 < 50 := by omega
                                                        simpa [Nat.sub_add_cancel hoff] using m0_w26 ⟨n - 11300, hnfin⟩
                                                      ·
                                                        by_cases h27 : n < 11400
                                                        · have hoff : 11350 ≤ n := by omega
                                                          have hnfin : n - 11350 < 50 := by omega
                                                          simpa [Nat.sub_add_cancel hoff] using m0_w27 ⟨n - 11350, hnfin⟩
                                                        ·
                                                          by_cases h28 : n < 11450
                                                          · have hoff : 11400 ≤ n := by omega
                                                            have hnfin : n - 11400 < 50 := by omega
                                                            simpa [Nat.sub_add_cancel hoff] using m0_w28 ⟨n - 11400, hnfin⟩
                                                          ·
                                                            by_cases h29 : n < 11500
                                                            · have hoff : 11450 ≤ n := by omega
                                                              have hnfin : n - 11450 < 50 := by omega
                                                              simpa [Nat.sub_add_cancel hoff] using m0_w29 ⟨n - 11450, hnfin⟩
                                                            ·
                                                              by_cases h30 : n < 11550
                                                              · have hoff : 11500 ≤ n := by omega
                                                                have hnfin : n - 11500 < 50 := by omega
                                                                simpa [Nat.sub_add_cancel hoff] using m0_w30 ⟨n - 11500, hnfin⟩
                                                              ·
                                                                by_cases h31 : n < 11600
                                                                · have hoff : 11550 ≤ n := by omega
                                                                  have hnfin : n - 11550 < 50 := by omega
                                                                  simpa [Nat.sub_add_cancel hoff] using m0_w31 ⟨n - 11550, hnfin⟩
                                                                ·
                                                                  by_cases h32 : n < 11650
                                                                  · have hoff : 11600 ≤ n := by omega
                                                                    have hnfin : n - 11600 < 50 := by omega
                                                                    simpa [Nat.sub_add_cancel hoff] using m0_w32 ⟨n - 11600, hnfin⟩
                                                                  ·
                                                                    by_cases h33 : n < 11700
                                                                    · have hoff : 11650 ≤ n := by omega
                                                                      have hnfin : n - 11650 < 50 := by omega
                                                                      simpa [Nat.sub_add_cancel hoff] using m0_w33 ⟨n - 11650, hnfin⟩
                                                                    ·
                                                                      by_cases h34 : n < 11750
                                                                      · have hoff : 11700 ≤ n := by omega
                                                                        have hnfin : n - 11700 < 50 := by omega
                                                                        simpa [Nat.sub_add_cancel hoff] using m0_w34 ⟨n - 11700, hnfin⟩
                                                                      ·
                                                                        by_cases h35 : n < 11800
                                                                        · have hoff : 11750 ≤ n := by omega
                                                                          have hnfin : n - 11750 < 50 := by omega
                                                                          simpa [Nat.sub_add_cancel hoff] using m0_w35 ⟨n - 11750, hnfin⟩
                                                                        ·
                                                                          by_cases h36 : n < 11850
                                                                          · have hoff : 11800 ≤ n := by omega
                                                                            have hnfin : n - 11800 < 50 := by omega
                                                                            simpa [Nat.sub_add_cancel hoff] using m0_w36 ⟨n - 11800, hnfin⟩
                                                                          ·
                                                                            by_cases h37 : n < 11900
                                                                            · have hoff : 11850 ≤ n := by omega
                                                                              have hnfin : n - 11850 < 50 := by omega
                                                                              simpa [Nat.sub_add_cancel hoff] using m0_w37 ⟨n - 11850, hnfin⟩
                                                                            ·
                                                                              by_cases h38 : n < 11950
                                                                              · have hoff : 11900 ≤ n := by omega
                                                                                have hnfin : n - 11900 < 50 := by omega
                                                                                simpa [Nat.sub_add_cancel hoff] using m0_w38 ⟨n - 11900, hnfin⟩
                                                                              ·
                                                                                by_cases h39 : n < 12000
                                                                                · have hoff : 11950 ≤ n := by omega
                                                                                  have hnfin : n - 11950 < 50 := by omega
                                                                                  simpa [Nat.sub_add_cancel hoff] using m0_w39 ⟨n - 11950, hnfin⟩
                                                                                ·
                                                                                  by_cases h40 : n < 12050
                                                                                  · have hoff : 12000 ≤ n := by omega
                                                                                    have hnfin : n - 12000 < 50 := by omega
                                                                                    simpa [Nat.sub_add_cancel hoff] using m0_w40 ⟨n - 12000, hnfin⟩
                                                                                  ·
                                                                                    by_cases h41 : n < 12100
                                                                                    · have hoff : 12050 ≤ n := by omega
                                                                                      have hnfin : n - 12050 < 50 := by omega
                                                                                      simpa [Nat.sub_add_cancel hoff] using m0_w41 ⟨n - 12050, hnfin⟩
                                                                                    ·
                                                                                      by_cases h42 : n < 12150
                                                                                      · have hoff : 12100 ≤ n := by omega
                                                                                        have hnfin : n - 12100 < 50 := by omega
                                                                                        simpa [Nat.sub_add_cancel hoff] using m0_w42 ⟨n - 12100, hnfin⟩
                                                                                      ·
                                                                                        by_cases h43 : n < 12200
                                                                                        · have hoff : 12150 ≤ n := by omega
                                                                                          have hnfin : n - 12150 < 50 := by omega
                                                                                          simpa [Nat.sub_add_cancel hoff] using m0_w43 ⟨n - 12150, hnfin⟩
                                                                                        ·
                                                                                          by_cases h44 : n < 12250
                                                                                          · have hoff : 12200 ≤ n := by omega
                                                                                            have hnfin : n - 12200 < 50 := by omega
                                                                                            simpa [Nat.sub_add_cancel hoff] using m0_w44 ⟨n - 12200, hnfin⟩
                                                                                          ·
                                                                                            by_cases h45 : n < 12300
                                                                                            · have hoff : 12250 ≤ n := by omega
                                                                                              have hnfin : n - 12250 < 50 := by omega
                                                                                              simpa [Nat.sub_add_cancel hoff] using m0_w45 ⟨n - 12250, hnfin⟩
                                                                                            ·
                                                                                              by_cases h46 : n < 12350
                                                                                              · have hoff : 12300 ≤ n := by omega
                                                                                                have hnfin : n - 12300 < 50 := by omega
                                                                                                simpa [Nat.sub_add_cancel hoff] using m0_w46 ⟨n - 12300, hnfin⟩
                                                                                              ·
                                                                                                by_cases h47 : n < 12400
                                                                                                · have hoff : 12350 ≤ n := by omega
                                                                                                  have hnfin : n - 12350 < 50 := by omega
                                                                                                  simpa [Nat.sub_add_cancel hoff] using m0_w47 ⟨n - 12350, hnfin⟩
                                                                                                ·
                                                                                                  by_cases h48 : n < 12450
                                                                                                  · have hoff : 12400 ≤ n := by omega
                                                                                                    have hnfin : n - 12400 < 50 := by omega
                                                                                                    simpa [Nat.sub_add_cancel hoff] using m0_w48 ⟨n - 12400, hnfin⟩
                                                                                                  ·
                                                                                                    by_cases h49 : n < 12500
                                                                                                    · have hoff : 12450 ≤ n := by omega
                                                                                                      have hnfin : n - 12450 < 50 := by omega
                                                                                                      simpa [Nat.sub_add_cancel hoff] using m0_w49 ⟨n - 12450, hnfin⟩
                                                                                                    ·
                                                                                                      omega
theorem land1_range (n : ℕ) (hn0 : 10000 ≤ n) (hn1 : n < 12500) :
    (!Nat.blt (dimF (arg1 n)) (dimF n) ||
      Nat.beq (Nat.land (densSupG (arg1 n)) (densSupG n)) (densSupG (arg1 n))) = true := by
  by_cases h0 : n < 10050
  · have hoff : 10000 ≤ n := by omega
    have hnfin : n - 10000 < 50 := by omega
    simpa [Nat.sub_add_cancel hoff] using m1_w0 ⟨n - 10000, hnfin⟩
  ·
    by_cases h1 : n < 10100
    · have hoff : 10050 ≤ n := by omega
      have hnfin : n - 10050 < 50 := by omega
      simpa [Nat.sub_add_cancel hoff] using m1_w1 ⟨n - 10050, hnfin⟩
    ·
      by_cases h2 : n < 10150
      · have hoff : 10100 ≤ n := by omega
        have hnfin : n - 10100 < 50 := by omega
        simpa [Nat.sub_add_cancel hoff] using m1_w2 ⟨n - 10100, hnfin⟩
      ·
        by_cases h3 : n < 10200
        · have hoff : 10150 ≤ n := by omega
          have hnfin : n - 10150 < 50 := by omega
          simpa [Nat.sub_add_cancel hoff] using m1_w3 ⟨n - 10150, hnfin⟩
        ·
          by_cases h4 : n < 10250
          · have hoff : 10200 ≤ n := by omega
            have hnfin : n - 10200 < 50 := by omega
            simpa [Nat.sub_add_cancel hoff] using m1_w4 ⟨n - 10200, hnfin⟩
          ·
            by_cases h5 : n < 10300
            · have hoff : 10250 ≤ n := by omega
              have hnfin : n - 10250 < 50 := by omega
              simpa [Nat.sub_add_cancel hoff] using m1_w5 ⟨n - 10250, hnfin⟩
            ·
              by_cases h6 : n < 10350
              · have hoff : 10300 ≤ n := by omega
                have hnfin : n - 10300 < 50 := by omega
                simpa [Nat.sub_add_cancel hoff] using m1_w6 ⟨n - 10300, hnfin⟩
              ·
                by_cases h7 : n < 10400
                · have hoff : 10350 ≤ n := by omega
                  have hnfin : n - 10350 < 50 := by omega
                  simpa [Nat.sub_add_cancel hoff] using m1_w7 ⟨n - 10350, hnfin⟩
                ·
                  by_cases h8 : n < 10450
                  · have hoff : 10400 ≤ n := by omega
                    have hnfin : n - 10400 < 50 := by omega
                    simpa [Nat.sub_add_cancel hoff] using m1_w8 ⟨n - 10400, hnfin⟩
                  ·
                    by_cases h9 : n < 10500
                    · have hoff : 10450 ≤ n := by omega
                      have hnfin : n - 10450 < 50 := by omega
                      simpa [Nat.sub_add_cancel hoff] using m1_w9 ⟨n - 10450, hnfin⟩
                    ·
                      by_cases h10 : n < 10550
                      · have hoff : 10500 ≤ n := by omega
                        have hnfin : n - 10500 < 50 := by omega
                        simpa [Nat.sub_add_cancel hoff] using m1_w10 ⟨n - 10500, hnfin⟩
                      ·
                        by_cases h11 : n < 10600
                        · have hoff : 10550 ≤ n := by omega
                          have hnfin : n - 10550 < 50 := by omega
                          simpa [Nat.sub_add_cancel hoff] using m1_w11 ⟨n - 10550, hnfin⟩
                        ·
                          by_cases h12 : n < 10650
                          · have hoff : 10600 ≤ n := by omega
                            have hnfin : n - 10600 < 50 := by omega
                            simpa [Nat.sub_add_cancel hoff] using m1_w12 ⟨n - 10600, hnfin⟩
                          ·
                            by_cases h13 : n < 10700
                            · have hoff : 10650 ≤ n := by omega
                              have hnfin : n - 10650 < 50 := by omega
                              simpa [Nat.sub_add_cancel hoff] using m1_w13 ⟨n - 10650, hnfin⟩
                            ·
                              by_cases h14 : n < 10750
                              · have hoff : 10700 ≤ n := by omega
                                have hnfin : n - 10700 < 50 := by omega
                                simpa [Nat.sub_add_cancel hoff] using m1_w14 ⟨n - 10700, hnfin⟩
                              ·
                                by_cases h15 : n < 10800
                                · have hoff : 10750 ≤ n := by omega
                                  have hnfin : n - 10750 < 50 := by omega
                                  simpa [Nat.sub_add_cancel hoff] using m1_w15 ⟨n - 10750, hnfin⟩
                                ·
                                  by_cases h16 : n < 10850
                                  · have hoff : 10800 ≤ n := by omega
                                    have hnfin : n - 10800 < 50 := by omega
                                    simpa [Nat.sub_add_cancel hoff] using m1_w16 ⟨n - 10800, hnfin⟩
                                  ·
                                    by_cases h17 : n < 10900
                                    · have hoff : 10850 ≤ n := by omega
                                      have hnfin : n - 10850 < 50 := by omega
                                      simpa [Nat.sub_add_cancel hoff] using m1_w17 ⟨n - 10850, hnfin⟩
                                    ·
                                      by_cases h18 : n < 10950
                                      · have hoff : 10900 ≤ n := by omega
                                        have hnfin : n - 10900 < 50 := by omega
                                        simpa [Nat.sub_add_cancel hoff] using m1_w18 ⟨n - 10900, hnfin⟩
                                      ·
                                        by_cases h19 : n < 11000
                                        · have hoff : 10950 ≤ n := by omega
                                          have hnfin : n - 10950 < 50 := by omega
                                          simpa [Nat.sub_add_cancel hoff] using m1_w19 ⟨n - 10950, hnfin⟩
                                        ·
                                          by_cases h20 : n < 11050
                                          · have hoff : 11000 ≤ n := by omega
                                            have hnfin : n - 11000 < 50 := by omega
                                            simpa [Nat.sub_add_cancel hoff] using m1_w20 ⟨n - 11000, hnfin⟩
                                          ·
                                            by_cases h21 : n < 11100
                                            · have hoff : 11050 ≤ n := by omega
                                              have hnfin : n - 11050 < 50 := by omega
                                              simpa [Nat.sub_add_cancel hoff] using m1_w21 ⟨n - 11050, hnfin⟩
                                            ·
                                              by_cases h22 : n < 11150
                                              · have hoff : 11100 ≤ n := by omega
                                                have hnfin : n - 11100 < 50 := by omega
                                                simpa [Nat.sub_add_cancel hoff] using m1_w22 ⟨n - 11100, hnfin⟩
                                              ·
                                                by_cases h23 : n < 11200
                                                · have hoff : 11150 ≤ n := by omega
                                                  have hnfin : n - 11150 < 50 := by omega
                                                  simpa [Nat.sub_add_cancel hoff] using m1_w23 ⟨n - 11150, hnfin⟩
                                                ·
                                                  by_cases h24 : n < 11250
                                                  · have hoff : 11200 ≤ n := by omega
                                                    have hnfin : n - 11200 < 50 := by omega
                                                    simpa [Nat.sub_add_cancel hoff] using m1_w24 ⟨n - 11200, hnfin⟩
                                                  ·
                                                    by_cases h25 : n < 11300
                                                    · have hoff : 11250 ≤ n := by omega
                                                      have hnfin : n - 11250 < 50 := by omega
                                                      simpa [Nat.sub_add_cancel hoff] using m1_w25 ⟨n - 11250, hnfin⟩
                                                    ·
                                                      by_cases h26 : n < 11350
                                                      · have hoff : 11300 ≤ n := by omega
                                                        have hnfin : n - 11300 < 50 := by omega
                                                        simpa [Nat.sub_add_cancel hoff] using m1_w26 ⟨n - 11300, hnfin⟩
                                                      ·
                                                        by_cases h27 : n < 11400
                                                        · have hoff : 11350 ≤ n := by omega
                                                          have hnfin : n - 11350 < 50 := by omega
                                                          simpa [Nat.sub_add_cancel hoff] using m1_w27 ⟨n - 11350, hnfin⟩
                                                        ·
                                                          by_cases h28 : n < 11450
                                                          · have hoff : 11400 ≤ n := by omega
                                                            have hnfin : n - 11400 < 50 := by omega
                                                            simpa [Nat.sub_add_cancel hoff] using m1_w28 ⟨n - 11400, hnfin⟩
                                                          ·
                                                            by_cases h29 : n < 11500
                                                            · have hoff : 11450 ≤ n := by omega
                                                              have hnfin : n - 11450 < 50 := by omega
                                                              simpa [Nat.sub_add_cancel hoff] using m1_w29 ⟨n - 11450, hnfin⟩
                                                            ·
                                                              by_cases h30 : n < 11550
                                                              · have hoff : 11500 ≤ n := by omega
                                                                have hnfin : n - 11500 < 50 := by omega
                                                                simpa [Nat.sub_add_cancel hoff] using m1_w30 ⟨n - 11500, hnfin⟩
                                                              ·
                                                                by_cases h31 : n < 11600
                                                                · have hoff : 11550 ≤ n := by omega
                                                                  have hnfin : n - 11550 < 50 := by omega
                                                                  simpa [Nat.sub_add_cancel hoff] using m1_w31 ⟨n - 11550, hnfin⟩
                                                                ·
                                                                  by_cases h32 : n < 11650
                                                                  · have hoff : 11600 ≤ n := by omega
                                                                    have hnfin : n - 11600 < 50 := by omega
                                                                    simpa [Nat.sub_add_cancel hoff] using m1_w32 ⟨n - 11600, hnfin⟩
                                                                  ·
                                                                    by_cases h33 : n < 11700
                                                                    · have hoff : 11650 ≤ n := by omega
                                                                      have hnfin : n - 11650 < 50 := by omega
                                                                      simpa [Nat.sub_add_cancel hoff] using m1_w33 ⟨n - 11650, hnfin⟩
                                                                    ·
                                                                      by_cases h34 : n < 11750
                                                                      · have hoff : 11700 ≤ n := by omega
                                                                        have hnfin : n - 11700 < 50 := by omega
                                                                        simpa [Nat.sub_add_cancel hoff] using m1_w34 ⟨n - 11700, hnfin⟩
                                                                      ·
                                                                        by_cases h35 : n < 11800
                                                                        · have hoff : 11750 ≤ n := by omega
                                                                          have hnfin : n - 11750 < 50 := by omega
                                                                          simpa [Nat.sub_add_cancel hoff] using m1_w35 ⟨n - 11750, hnfin⟩
                                                                        ·
                                                                          by_cases h36 : n < 11850
                                                                          · have hoff : 11800 ≤ n := by omega
                                                                            have hnfin : n - 11800 < 50 := by omega
                                                                            simpa [Nat.sub_add_cancel hoff] using m1_w36 ⟨n - 11800, hnfin⟩
                                                                          ·
                                                                            by_cases h37 : n < 11900
                                                                            · have hoff : 11850 ≤ n := by omega
                                                                              have hnfin : n - 11850 < 50 := by omega
                                                                              simpa [Nat.sub_add_cancel hoff] using m1_w37 ⟨n - 11850, hnfin⟩
                                                                            ·
                                                                              by_cases h38 : n < 11950
                                                                              · have hoff : 11900 ≤ n := by omega
                                                                                have hnfin : n - 11900 < 50 := by omega
                                                                                simpa [Nat.sub_add_cancel hoff] using m1_w38 ⟨n - 11900, hnfin⟩
                                                                              ·
                                                                                by_cases h39 : n < 12000
                                                                                · have hoff : 11950 ≤ n := by omega
                                                                                  have hnfin : n - 11950 < 50 := by omega
                                                                                  simpa [Nat.sub_add_cancel hoff] using m1_w39 ⟨n - 11950, hnfin⟩
                                                                                ·
                                                                                  by_cases h40 : n < 12050
                                                                                  · have hoff : 12000 ≤ n := by omega
                                                                                    have hnfin : n - 12000 < 50 := by omega
                                                                                    simpa [Nat.sub_add_cancel hoff] using m1_w40 ⟨n - 12000, hnfin⟩
                                                                                  ·
                                                                                    by_cases h41 : n < 12100
                                                                                    · have hoff : 12050 ≤ n := by omega
                                                                                      have hnfin : n - 12050 < 50 := by omega
                                                                                      simpa [Nat.sub_add_cancel hoff] using m1_w41 ⟨n - 12050, hnfin⟩
                                                                                    ·
                                                                                      by_cases h42 : n < 12150
                                                                                      · have hoff : 12100 ≤ n := by omega
                                                                                        have hnfin : n - 12100 < 50 := by omega
                                                                                        simpa [Nat.sub_add_cancel hoff] using m1_w42 ⟨n - 12100, hnfin⟩
                                                                                      ·
                                                                                        by_cases h43 : n < 12200
                                                                                        · have hoff : 12150 ≤ n := by omega
                                                                                          have hnfin : n - 12150 < 50 := by omega
                                                                                          simpa [Nat.sub_add_cancel hoff] using m1_w43 ⟨n - 12150, hnfin⟩
                                                                                        ·
                                                                                          by_cases h44 : n < 12250
                                                                                          · have hoff : 12200 ≤ n := by omega
                                                                                            have hnfin : n - 12200 < 50 := by omega
                                                                                            simpa [Nat.sub_add_cancel hoff] using m1_w44 ⟨n - 12200, hnfin⟩
                                                                                          ·
                                                                                            by_cases h45 : n < 12300
                                                                                            · have hoff : 12250 ≤ n := by omega
                                                                                              have hnfin : n - 12250 < 50 := by omega
                                                                                              simpa [Nat.sub_add_cancel hoff] using m1_w45 ⟨n - 12250, hnfin⟩
                                                                                            ·
                                                                                              by_cases h46 : n < 12350
                                                                                              · have hoff : 12300 ≤ n := by omega
                                                                                                have hnfin : n - 12300 < 50 := by omega
                                                                                                simpa [Nat.sub_add_cancel hoff] using m1_w46 ⟨n - 12300, hnfin⟩
                                                                                              ·
                                                                                                by_cases h47 : n < 12400
                                                                                                · have hoff : 12350 ≤ n := by omega
                                                                                                  have hnfin : n - 12350 < 50 := by omega
                                                                                                  simpa [Nat.sub_add_cancel hoff] using m1_w47 ⟨n - 12350, hnfin⟩
                                                                                                ·
                                                                                                  by_cases h48 : n < 12450
                                                                                                  · have hoff : 12400 ≤ n := by omega
                                                                                                    have hnfin : n - 12400 < 50 := by omega
                                                                                                    simpa [Nat.sub_add_cancel hoff] using m1_w48 ⟨n - 12400, hnfin⟩
                                                                                                  ·
                                                                                                    by_cases h49 : n < 12500
                                                                                                    · have hoff : 12450 ≤ n := by omega
                                                                                                      have hnfin : n - 12450 < 50 := by omega
                                                                                                      simpa [Nat.sub_add_cancel hoff] using m1_w49 ⟨n - 12450, hnfin⟩
                                                                                                    ·
                                                                                                      omega
end IntMul.Kappa.R8.Bit.Oppbank.LandMonoFixA4


