-- Prove2me | Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankLandMonoFixA14
-- name    : IntMul_Kappa_R8_Data_BitOppbankLandMonoFixA14
-- status  : Definition
-- author  : @Ethan Cheung Wang
-- created : 2026-10-28T21:16:13.02881+00:00
-- url     : https://prove2.me/theorems/816e442e-c1d6-4f5f-8217-fcbe72d0cb02
-- title:
--   Dim-gated densSup land mono FixA pack 14
-- statement:
--   # Dim-gated densSup land (PndFix), pack A14
--
--   Range consolidators for $n\in[35000,37500)$.
-- source:
--   R8 BitOppbank PndFix

-- LandMonoFixA14: PUBLIC dim-gated land + range consolidators (PndFix)
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
namespace IntMul.Kappa.R8.Bit.Oppbank.LandMonoFixA14
def arg0 (n : ℕ) : ℕ := Nat.land (argF n) 65535
def arg1 (n : ℕ) : ℕ := Nat.shiftRight (argF n) 16
theorem m0_w0 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 35000))) (dimF (n.val + 35000)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 35000))) (densSupG (n.val + 35000))) (densSupG (arg0 (n.val + 35000)))) = true := by decide
theorem m1_w0 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 35000))) (dimF (n.val + 35000)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 35000))) (densSupG (n.val + 35000))) (densSupG (arg1 (n.val + 35000)))) = true := by decide
theorem m0_w1 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 35050))) (dimF (n.val + 35050)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 35050))) (densSupG (n.val + 35050))) (densSupG (arg0 (n.val + 35050)))) = true := by decide
theorem m1_w1 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 35050))) (dimF (n.val + 35050)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 35050))) (densSupG (n.val + 35050))) (densSupG (arg1 (n.val + 35050)))) = true := by decide
theorem m0_w2 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 35100))) (dimF (n.val + 35100)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 35100))) (densSupG (n.val + 35100))) (densSupG (arg0 (n.val + 35100)))) = true := by decide
theorem m1_w2 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 35100))) (dimF (n.val + 35100)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 35100))) (densSupG (n.val + 35100))) (densSupG (arg1 (n.val + 35100)))) = true := by decide
theorem m0_w3 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 35150))) (dimF (n.val + 35150)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 35150))) (densSupG (n.val + 35150))) (densSupG (arg0 (n.val + 35150)))) = true := by decide
theorem m1_w3 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 35150))) (dimF (n.val + 35150)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 35150))) (densSupG (n.val + 35150))) (densSupG (arg1 (n.val + 35150)))) = true := by decide
theorem m0_w4 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 35200))) (dimF (n.val + 35200)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 35200))) (densSupG (n.val + 35200))) (densSupG (arg0 (n.val + 35200)))) = true := by decide
theorem m1_w4 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 35200))) (dimF (n.val + 35200)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 35200))) (densSupG (n.val + 35200))) (densSupG (arg1 (n.val + 35200)))) = true := by decide
theorem m0_w5 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 35250))) (dimF (n.val + 35250)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 35250))) (densSupG (n.val + 35250))) (densSupG (arg0 (n.val + 35250)))) = true := by decide
theorem m1_w5 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 35250))) (dimF (n.val + 35250)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 35250))) (densSupG (n.val + 35250))) (densSupG (arg1 (n.val + 35250)))) = true := by decide
theorem m0_w6 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 35300))) (dimF (n.val + 35300)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 35300))) (densSupG (n.val + 35300))) (densSupG (arg0 (n.val + 35300)))) = true := by decide
theorem m1_w6 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 35300))) (dimF (n.val + 35300)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 35300))) (densSupG (n.val + 35300))) (densSupG (arg1 (n.val + 35300)))) = true := by decide
theorem m0_w7 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 35350))) (dimF (n.val + 35350)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 35350))) (densSupG (n.val + 35350))) (densSupG (arg0 (n.val + 35350)))) = true := by decide
theorem m1_w7 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 35350))) (dimF (n.val + 35350)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 35350))) (densSupG (n.val + 35350))) (densSupG (arg1 (n.val + 35350)))) = true := by decide
theorem m0_w8 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 35400))) (dimF (n.val + 35400)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 35400))) (densSupG (n.val + 35400))) (densSupG (arg0 (n.val + 35400)))) = true := by decide
theorem m1_w8 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 35400))) (dimF (n.val + 35400)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 35400))) (densSupG (n.val + 35400))) (densSupG (arg1 (n.val + 35400)))) = true := by decide
theorem m0_w9 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 35450))) (dimF (n.val + 35450)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 35450))) (densSupG (n.val + 35450))) (densSupG (arg0 (n.val + 35450)))) = true := by decide
theorem m1_w9 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 35450))) (dimF (n.val + 35450)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 35450))) (densSupG (n.val + 35450))) (densSupG (arg1 (n.val + 35450)))) = true := by decide
theorem m0_w10 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 35500))) (dimF (n.val + 35500)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 35500))) (densSupG (n.val + 35500))) (densSupG (arg0 (n.val + 35500)))) = true := by decide
theorem m1_w10 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 35500))) (dimF (n.val + 35500)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 35500))) (densSupG (n.val + 35500))) (densSupG (arg1 (n.val + 35500)))) = true := by decide
theorem m0_w11 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 35550))) (dimF (n.val + 35550)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 35550))) (densSupG (n.val + 35550))) (densSupG (arg0 (n.val + 35550)))) = true := by decide
theorem m1_w11 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 35550))) (dimF (n.val + 35550)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 35550))) (densSupG (n.val + 35550))) (densSupG (arg1 (n.val + 35550)))) = true := by decide
theorem m0_w12 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 35600))) (dimF (n.val + 35600)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 35600))) (densSupG (n.val + 35600))) (densSupG (arg0 (n.val + 35600)))) = true := by decide
theorem m1_w12 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 35600))) (dimF (n.val + 35600)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 35600))) (densSupG (n.val + 35600))) (densSupG (arg1 (n.val + 35600)))) = true := by decide
theorem m0_w13 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 35650))) (dimF (n.val + 35650)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 35650))) (densSupG (n.val + 35650))) (densSupG (arg0 (n.val + 35650)))) = true := by decide
theorem m1_w13 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 35650))) (dimF (n.val + 35650)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 35650))) (densSupG (n.val + 35650))) (densSupG (arg1 (n.val + 35650)))) = true := by decide
theorem m0_w14 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 35700))) (dimF (n.val + 35700)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 35700))) (densSupG (n.val + 35700))) (densSupG (arg0 (n.val + 35700)))) = true := by decide
theorem m1_w14 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 35700))) (dimF (n.val + 35700)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 35700))) (densSupG (n.val + 35700))) (densSupG (arg1 (n.val + 35700)))) = true := by decide
theorem m0_w15 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 35750))) (dimF (n.val + 35750)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 35750))) (densSupG (n.val + 35750))) (densSupG (arg0 (n.val + 35750)))) = true := by decide
theorem m1_w15 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 35750))) (dimF (n.val + 35750)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 35750))) (densSupG (n.val + 35750))) (densSupG (arg1 (n.val + 35750)))) = true := by decide
theorem m0_w16 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 35800))) (dimF (n.val + 35800)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 35800))) (densSupG (n.val + 35800))) (densSupG (arg0 (n.val + 35800)))) = true := by decide
theorem m1_w16 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 35800))) (dimF (n.val + 35800)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 35800))) (densSupG (n.val + 35800))) (densSupG (arg1 (n.val + 35800)))) = true := by decide
theorem m0_w17 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 35850))) (dimF (n.val + 35850)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 35850))) (densSupG (n.val + 35850))) (densSupG (arg0 (n.val + 35850)))) = true := by decide
theorem m1_w17 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 35850))) (dimF (n.val + 35850)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 35850))) (densSupG (n.val + 35850))) (densSupG (arg1 (n.val + 35850)))) = true := by decide
theorem m0_w18 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 35900))) (dimF (n.val + 35900)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 35900))) (densSupG (n.val + 35900))) (densSupG (arg0 (n.val + 35900)))) = true := by decide
theorem m1_w18 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 35900))) (dimF (n.val + 35900)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 35900))) (densSupG (n.val + 35900))) (densSupG (arg1 (n.val + 35900)))) = true := by decide
theorem m0_w19 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 35950))) (dimF (n.val + 35950)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 35950))) (densSupG (n.val + 35950))) (densSupG (arg0 (n.val + 35950)))) = true := by decide
theorem m1_w19 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 35950))) (dimF (n.val + 35950)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 35950))) (densSupG (n.val + 35950))) (densSupG (arg1 (n.val + 35950)))) = true := by decide
theorem m0_w20 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 36000))) (dimF (n.val + 36000)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 36000))) (densSupG (n.val + 36000))) (densSupG (arg0 (n.val + 36000)))) = true := by decide
theorem m1_w20 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 36000))) (dimF (n.val + 36000)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 36000))) (densSupG (n.val + 36000))) (densSupG (arg1 (n.val + 36000)))) = true := by decide
theorem m0_w21 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 36050))) (dimF (n.val + 36050)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 36050))) (densSupG (n.val + 36050))) (densSupG (arg0 (n.val + 36050)))) = true := by decide
theorem m1_w21 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 36050))) (dimF (n.val + 36050)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 36050))) (densSupG (n.val + 36050))) (densSupG (arg1 (n.val + 36050)))) = true := by decide
theorem m0_w22 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 36100))) (dimF (n.val + 36100)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 36100))) (densSupG (n.val + 36100))) (densSupG (arg0 (n.val + 36100)))) = true := by decide
theorem m1_w22 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 36100))) (dimF (n.val + 36100)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 36100))) (densSupG (n.val + 36100))) (densSupG (arg1 (n.val + 36100)))) = true := by decide
theorem m0_w23 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 36150))) (dimF (n.val + 36150)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 36150))) (densSupG (n.val + 36150))) (densSupG (arg0 (n.val + 36150)))) = true := by decide
theorem m1_w23 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 36150))) (dimF (n.val + 36150)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 36150))) (densSupG (n.val + 36150))) (densSupG (arg1 (n.val + 36150)))) = true := by decide
theorem m0_w24 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 36200))) (dimF (n.val + 36200)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 36200))) (densSupG (n.val + 36200))) (densSupG (arg0 (n.val + 36200)))) = true := by decide
theorem m1_w24 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 36200))) (dimF (n.val + 36200)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 36200))) (densSupG (n.val + 36200))) (densSupG (arg1 (n.val + 36200)))) = true := by decide
theorem m0_w25 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 36250))) (dimF (n.val + 36250)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 36250))) (densSupG (n.val + 36250))) (densSupG (arg0 (n.val + 36250)))) = true := by decide
theorem m1_w25 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 36250))) (dimF (n.val + 36250)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 36250))) (densSupG (n.val + 36250))) (densSupG (arg1 (n.val + 36250)))) = true := by decide
theorem m0_w26 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 36300))) (dimF (n.val + 36300)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 36300))) (densSupG (n.val + 36300))) (densSupG (arg0 (n.val + 36300)))) = true := by decide
theorem m1_w26 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 36300))) (dimF (n.val + 36300)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 36300))) (densSupG (n.val + 36300))) (densSupG (arg1 (n.val + 36300)))) = true := by decide
theorem m0_w27 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 36350))) (dimF (n.val + 36350)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 36350))) (densSupG (n.val + 36350))) (densSupG (arg0 (n.val + 36350)))) = true := by decide
theorem m1_w27 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 36350))) (dimF (n.val + 36350)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 36350))) (densSupG (n.val + 36350))) (densSupG (arg1 (n.val + 36350)))) = true := by decide
theorem m0_w28 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 36400))) (dimF (n.val + 36400)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 36400))) (densSupG (n.val + 36400))) (densSupG (arg0 (n.val + 36400)))) = true := by decide
theorem m1_w28 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 36400))) (dimF (n.val + 36400)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 36400))) (densSupG (n.val + 36400))) (densSupG (arg1 (n.val + 36400)))) = true := by decide
theorem m0_w29 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 36450))) (dimF (n.val + 36450)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 36450))) (densSupG (n.val + 36450))) (densSupG (arg0 (n.val + 36450)))) = true := by decide
theorem m1_w29 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 36450))) (dimF (n.val + 36450)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 36450))) (densSupG (n.val + 36450))) (densSupG (arg1 (n.val + 36450)))) = true := by decide
theorem m0_w30 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 36500))) (dimF (n.val + 36500)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 36500))) (densSupG (n.val + 36500))) (densSupG (arg0 (n.val + 36500)))) = true := by decide
theorem m1_w30 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 36500))) (dimF (n.val + 36500)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 36500))) (densSupG (n.val + 36500))) (densSupG (arg1 (n.val + 36500)))) = true := by decide
theorem m0_w31 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 36550))) (dimF (n.val + 36550)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 36550))) (densSupG (n.val + 36550))) (densSupG (arg0 (n.val + 36550)))) = true := by decide
theorem m1_w31 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 36550))) (dimF (n.val + 36550)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 36550))) (densSupG (n.val + 36550))) (densSupG (arg1 (n.val + 36550)))) = true := by decide
theorem m0_w32 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 36600))) (dimF (n.val + 36600)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 36600))) (densSupG (n.val + 36600))) (densSupG (arg0 (n.val + 36600)))) = true := by decide
theorem m1_w32 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 36600))) (dimF (n.val + 36600)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 36600))) (densSupG (n.val + 36600))) (densSupG (arg1 (n.val + 36600)))) = true := by decide
theorem m0_w33 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 36650))) (dimF (n.val + 36650)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 36650))) (densSupG (n.val + 36650))) (densSupG (arg0 (n.val + 36650)))) = true := by decide
theorem m1_w33 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 36650))) (dimF (n.val + 36650)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 36650))) (densSupG (n.val + 36650))) (densSupG (arg1 (n.val + 36650)))) = true := by decide
theorem m0_w34 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 36700))) (dimF (n.val + 36700)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 36700))) (densSupG (n.val + 36700))) (densSupG (arg0 (n.val + 36700)))) = true := by decide
theorem m1_w34 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 36700))) (dimF (n.val + 36700)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 36700))) (densSupG (n.val + 36700))) (densSupG (arg1 (n.val + 36700)))) = true := by decide
theorem m0_w35 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 36750))) (dimF (n.val + 36750)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 36750))) (densSupG (n.val + 36750))) (densSupG (arg0 (n.val + 36750)))) = true := by decide
theorem m1_w35 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 36750))) (dimF (n.val + 36750)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 36750))) (densSupG (n.val + 36750))) (densSupG (arg1 (n.val + 36750)))) = true := by decide
theorem m0_w36 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 36800))) (dimF (n.val + 36800)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 36800))) (densSupG (n.val + 36800))) (densSupG (arg0 (n.val + 36800)))) = true := by decide
theorem m1_w36 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 36800))) (dimF (n.val + 36800)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 36800))) (densSupG (n.val + 36800))) (densSupG (arg1 (n.val + 36800)))) = true := by decide
theorem m0_w37 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 36850))) (dimF (n.val + 36850)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 36850))) (densSupG (n.val + 36850))) (densSupG (arg0 (n.val + 36850)))) = true := by decide
theorem m1_w37 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 36850))) (dimF (n.val + 36850)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 36850))) (densSupG (n.val + 36850))) (densSupG (arg1 (n.val + 36850)))) = true := by decide
theorem m0_w38 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 36900))) (dimF (n.val + 36900)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 36900))) (densSupG (n.val + 36900))) (densSupG (arg0 (n.val + 36900)))) = true := by decide
theorem m1_w38 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 36900))) (dimF (n.val + 36900)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 36900))) (densSupG (n.val + 36900))) (densSupG (arg1 (n.val + 36900)))) = true := by decide
theorem m0_w39 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 36950))) (dimF (n.val + 36950)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 36950))) (densSupG (n.val + 36950))) (densSupG (arg0 (n.val + 36950)))) = true := by decide
theorem m1_w39 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 36950))) (dimF (n.val + 36950)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 36950))) (densSupG (n.val + 36950))) (densSupG (arg1 (n.val + 36950)))) = true := by decide
theorem m0_w40 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 37000))) (dimF (n.val + 37000)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 37000))) (densSupG (n.val + 37000))) (densSupG (arg0 (n.val + 37000)))) = true := by decide
theorem m1_w40 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 37000))) (dimF (n.val + 37000)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 37000))) (densSupG (n.val + 37000))) (densSupG (arg1 (n.val + 37000)))) = true := by decide
theorem m0_w41 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 37050))) (dimF (n.val + 37050)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 37050))) (densSupG (n.val + 37050))) (densSupG (arg0 (n.val + 37050)))) = true := by decide
theorem m1_w41 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 37050))) (dimF (n.val + 37050)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 37050))) (densSupG (n.val + 37050))) (densSupG (arg1 (n.val + 37050)))) = true := by decide
theorem m0_w42 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 37100))) (dimF (n.val + 37100)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 37100))) (densSupG (n.val + 37100))) (densSupG (arg0 (n.val + 37100)))) = true := by decide
theorem m1_w42 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 37100))) (dimF (n.val + 37100)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 37100))) (densSupG (n.val + 37100))) (densSupG (arg1 (n.val + 37100)))) = true := by decide
theorem m0_w43 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 37150))) (dimF (n.val + 37150)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 37150))) (densSupG (n.val + 37150))) (densSupG (arg0 (n.val + 37150)))) = true := by decide
theorem m1_w43 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 37150))) (dimF (n.val + 37150)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 37150))) (densSupG (n.val + 37150))) (densSupG (arg1 (n.val + 37150)))) = true := by decide
theorem m0_w44 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 37200))) (dimF (n.val + 37200)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 37200))) (densSupG (n.val + 37200))) (densSupG (arg0 (n.val + 37200)))) = true := by decide
theorem m1_w44 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 37200))) (dimF (n.val + 37200)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 37200))) (densSupG (n.val + 37200))) (densSupG (arg1 (n.val + 37200)))) = true := by decide
theorem m0_w45 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 37250))) (dimF (n.val + 37250)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 37250))) (densSupG (n.val + 37250))) (densSupG (arg0 (n.val + 37250)))) = true := by decide
theorem m1_w45 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 37250))) (dimF (n.val + 37250)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 37250))) (densSupG (n.val + 37250))) (densSupG (arg1 (n.val + 37250)))) = true := by decide
theorem m0_w46 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 37300))) (dimF (n.val + 37300)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 37300))) (densSupG (n.val + 37300))) (densSupG (arg0 (n.val + 37300)))) = true := by decide
theorem m1_w46 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 37300))) (dimF (n.val + 37300)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 37300))) (densSupG (n.val + 37300))) (densSupG (arg1 (n.val + 37300)))) = true := by decide
theorem m0_w47 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 37350))) (dimF (n.val + 37350)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 37350))) (densSupG (n.val + 37350))) (densSupG (arg0 (n.val + 37350)))) = true := by decide
theorem m1_w47 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 37350))) (dimF (n.val + 37350)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 37350))) (densSupG (n.val + 37350))) (densSupG (arg1 (n.val + 37350)))) = true := by decide
theorem m0_w48 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 37400))) (dimF (n.val + 37400)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 37400))) (densSupG (n.val + 37400))) (densSupG (arg0 (n.val + 37400)))) = true := by decide
theorem m1_w48 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 37400))) (dimF (n.val + 37400)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 37400))) (densSupG (n.val + 37400))) (densSupG (arg1 (n.val + 37400)))) = true := by decide
theorem m0_w49 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 37450))) (dimF (n.val + 37450)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 37450))) (densSupG (n.val + 37450))) (densSupG (arg0 (n.val + 37450)))) = true := by decide
theorem m1_w49 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 37450))) (dimF (n.val + 37450)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 37450))) (densSupG (n.val + 37450))) (densSupG (arg1 (n.val + 37450)))) = true := by decide
theorem land0_range (n : ℕ) (hn0 : 35000 ≤ n) (hn1 : n < 37500) :
    (!Nat.blt (dimF (arg0 n)) (dimF n) ||
      Nat.beq (Nat.land (densSupG (arg0 n)) (densSupG n)) (densSupG (arg0 n))) = true := by
  by_cases h0 : n < 35050
  · have hoff : 35000 ≤ n := by omega
    have hnfin : n - 35000 < 50 := by omega
    simpa [Nat.sub_add_cancel hoff] using m0_w0 ⟨n - 35000, hnfin⟩
  ·
    by_cases h1 : n < 35100
    · have hoff : 35050 ≤ n := by omega
      have hnfin : n - 35050 < 50 := by omega
      simpa [Nat.sub_add_cancel hoff] using m0_w1 ⟨n - 35050, hnfin⟩
    ·
      by_cases h2 : n < 35150
      · have hoff : 35100 ≤ n := by omega
        have hnfin : n - 35100 < 50 := by omega
        simpa [Nat.sub_add_cancel hoff] using m0_w2 ⟨n - 35100, hnfin⟩
      ·
        by_cases h3 : n < 35200
        · have hoff : 35150 ≤ n := by omega
          have hnfin : n - 35150 < 50 := by omega
          simpa [Nat.sub_add_cancel hoff] using m0_w3 ⟨n - 35150, hnfin⟩
        ·
          by_cases h4 : n < 35250
          · have hoff : 35200 ≤ n := by omega
            have hnfin : n - 35200 < 50 := by omega
            simpa [Nat.sub_add_cancel hoff] using m0_w4 ⟨n - 35200, hnfin⟩
          ·
            by_cases h5 : n < 35300
            · have hoff : 35250 ≤ n := by omega
              have hnfin : n - 35250 < 50 := by omega
              simpa [Nat.sub_add_cancel hoff] using m0_w5 ⟨n - 35250, hnfin⟩
            ·
              by_cases h6 : n < 35350
              · have hoff : 35300 ≤ n := by omega
                have hnfin : n - 35300 < 50 := by omega
                simpa [Nat.sub_add_cancel hoff] using m0_w6 ⟨n - 35300, hnfin⟩
              ·
                by_cases h7 : n < 35400
                · have hoff : 35350 ≤ n := by omega
                  have hnfin : n - 35350 < 50 := by omega
                  simpa [Nat.sub_add_cancel hoff] using m0_w7 ⟨n - 35350, hnfin⟩
                ·
                  by_cases h8 : n < 35450
                  · have hoff : 35400 ≤ n := by omega
                    have hnfin : n - 35400 < 50 := by omega
                    simpa [Nat.sub_add_cancel hoff] using m0_w8 ⟨n - 35400, hnfin⟩
                  ·
                    by_cases h9 : n < 35500
                    · have hoff : 35450 ≤ n := by omega
                      have hnfin : n - 35450 < 50 := by omega
                      simpa [Nat.sub_add_cancel hoff] using m0_w9 ⟨n - 35450, hnfin⟩
                    ·
                      by_cases h10 : n < 35550
                      · have hoff : 35500 ≤ n := by omega
                        have hnfin : n - 35500 < 50 := by omega
                        simpa [Nat.sub_add_cancel hoff] using m0_w10 ⟨n - 35500, hnfin⟩
                      ·
                        by_cases h11 : n < 35600
                        · have hoff : 35550 ≤ n := by omega
                          have hnfin : n - 35550 < 50 := by omega
                          simpa [Nat.sub_add_cancel hoff] using m0_w11 ⟨n - 35550, hnfin⟩
                        ·
                          by_cases h12 : n < 35650
                          · have hoff : 35600 ≤ n := by omega
                            have hnfin : n - 35600 < 50 := by omega
                            simpa [Nat.sub_add_cancel hoff] using m0_w12 ⟨n - 35600, hnfin⟩
                          ·
                            by_cases h13 : n < 35700
                            · have hoff : 35650 ≤ n := by omega
                              have hnfin : n - 35650 < 50 := by omega
                              simpa [Nat.sub_add_cancel hoff] using m0_w13 ⟨n - 35650, hnfin⟩
                            ·
                              by_cases h14 : n < 35750
                              · have hoff : 35700 ≤ n := by omega
                                have hnfin : n - 35700 < 50 := by omega
                                simpa [Nat.sub_add_cancel hoff] using m0_w14 ⟨n - 35700, hnfin⟩
                              ·
                                by_cases h15 : n < 35800
                                · have hoff : 35750 ≤ n := by omega
                                  have hnfin : n - 35750 < 50 := by omega
                                  simpa [Nat.sub_add_cancel hoff] using m0_w15 ⟨n - 35750, hnfin⟩
                                ·
                                  by_cases h16 : n < 35850
                                  · have hoff : 35800 ≤ n := by omega
                                    have hnfin : n - 35800 < 50 := by omega
                                    simpa [Nat.sub_add_cancel hoff] using m0_w16 ⟨n - 35800, hnfin⟩
                                  ·
                                    by_cases h17 : n < 35900
                                    · have hoff : 35850 ≤ n := by omega
                                      have hnfin : n - 35850 < 50 := by omega
                                      simpa [Nat.sub_add_cancel hoff] using m0_w17 ⟨n - 35850, hnfin⟩
                                    ·
                                      by_cases h18 : n < 35950
                                      · have hoff : 35900 ≤ n := by omega
                                        have hnfin : n - 35900 < 50 := by omega
                                        simpa [Nat.sub_add_cancel hoff] using m0_w18 ⟨n - 35900, hnfin⟩
                                      ·
                                        by_cases h19 : n < 36000
                                        · have hoff : 35950 ≤ n := by omega
                                          have hnfin : n - 35950 < 50 := by omega
                                          simpa [Nat.sub_add_cancel hoff] using m0_w19 ⟨n - 35950, hnfin⟩
                                        ·
                                          by_cases h20 : n < 36050
                                          · have hoff : 36000 ≤ n := by omega
                                            have hnfin : n - 36000 < 50 := by omega
                                            simpa [Nat.sub_add_cancel hoff] using m0_w20 ⟨n - 36000, hnfin⟩
                                          ·
                                            by_cases h21 : n < 36100
                                            · have hoff : 36050 ≤ n := by omega
                                              have hnfin : n - 36050 < 50 := by omega
                                              simpa [Nat.sub_add_cancel hoff] using m0_w21 ⟨n - 36050, hnfin⟩
                                            ·
                                              by_cases h22 : n < 36150
                                              · have hoff : 36100 ≤ n := by omega
                                                have hnfin : n - 36100 < 50 := by omega
                                                simpa [Nat.sub_add_cancel hoff] using m0_w22 ⟨n - 36100, hnfin⟩
                                              ·
                                                by_cases h23 : n < 36200
                                                · have hoff : 36150 ≤ n := by omega
                                                  have hnfin : n - 36150 < 50 := by omega
                                                  simpa [Nat.sub_add_cancel hoff] using m0_w23 ⟨n - 36150, hnfin⟩
                                                ·
                                                  by_cases h24 : n < 36250
                                                  · have hoff : 36200 ≤ n := by omega
                                                    have hnfin : n - 36200 < 50 := by omega
                                                    simpa [Nat.sub_add_cancel hoff] using m0_w24 ⟨n - 36200, hnfin⟩
                                                  ·
                                                    by_cases h25 : n < 36300
                                                    · have hoff : 36250 ≤ n := by omega
                                                      have hnfin : n - 36250 < 50 := by omega
                                                      simpa [Nat.sub_add_cancel hoff] using m0_w25 ⟨n - 36250, hnfin⟩
                                                    ·
                                                      by_cases h26 : n < 36350
                                                      · have hoff : 36300 ≤ n := by omega
                                                        have hnfin : n - 36300 < 50 := by omega
                                                        simpa [Nat.sub_add_cancel hoff] using m0_w26 ⟨n - 36300, hnfin⟩
                                                      ·
                                                        by_cases h27 : n < 36400
                                                        · have hoff : 36350 ≤ n := by omega
                                                          have hnfin : n - 36350 < 50 := by omega
                                                          simpa [Nat.sub_add_cancel hoff] using m0_w27 ⟨n - 36350, hnfin⟩
                                                        ·
                                                          by_cases h28 : n < 36450
                                                          · have hoff : 36400 ≤ n := by omega
                                                            have hnfin : n - 36400 < 50 := by omega
                                                            simpa [Nat.sub_add_cancel hoff] using m0_w28 ⟨n - 36400, hnfin⟩
                                                          ·
                                                            by_cases h29 : n < 36500
                                                            · have hoff : 36450 ≤ n := by omega
                                                              have hnfin : n - 36450 < 50 := by omega
                                                              simpa [Nat.sub_add_cancel hoff] using m0_w29 ⟨n - 36450, hnfin⟩
                                                            ·
                                                              by_cases h30 : n < 36550
                                                              · have hoff : 36500 ≤ n := by omega
                                                                have hnfin : n - 36500 < 50 := by omega
                                                                simpa [Nat.sub_add_cancel hoff] using m0_w30 ⟨n - 36500, hnfin⟩
                                                              ·
                                                                by_cases h31 : n < 36600
                                                                · have hoff : 36550 ≤ n := by omega
                                                                  have hnfin : n - 36550 < 50 := by omega
                                                                  simpa [Nat.sub_add_cancel hoff] using m0_w31 ⟨n - 36550, hnfin⟩
                                                                ·
                                                                  by_cases h32 : n < 36650
                                                                  · have hoff : 36600 ≤ n := by omega
                                                                    have hnfin : n - 36600 < 50 := by omega
                                                                    simpa [Nat.sub_add_cancel hoff] using m0_w32 ⟨n - 36600, hnfin⟩
                                                                  ·
                                                                    by_cases h33 : n < 36700
                                                                    · have hoff : 36650 ≤ n := by omega
                                                                      have hnfin : n - 36650 < 50 := by omega
                                                                      simpa [Nat.sub_add_cancel hoff] using m0_w33 ⟨n - 36650, hnfin⟩
                                                                    ·
                                                                      by_cases h34 : n < 36750
                                                                      · have hoff : 36700 ≤ n := by omega
                                                                        have hnfin : n - 36700 < 50 := by omega
                                                                        simpa [Nat.sub_add_cancel hoff] using m0_w34 ⟨n - 36700, hnfin⟩
                                                                      ·
                                                                        by_cases h35 : n < 36800
                                                                        · have hoff : 36750 ≤ n := by omega
                                                                          have hnfin : n - 36750 < 50 := by omega
                                                                          simpa [Nat.sub_add_cancel hoff] using m0_w35 ⟨n - 36750, hnfin⟩
                                                                        ·
                                                                          by_cases h36 : n < 36850
                                                                          · have hoff : 36800 ≤ n := by omega
                                                                            have hnfin : n - 36800 < 50 := by omega
                                                                            simpa [Nat.sub_add_cancel hoff] using m0_w36 ⟨n - 36800, hnfin⟩
                                                                          ·
                                                                            by_cases h37 : n < 36900
                                                                            · have hoff : 36850 ≤ n := by omega
                                                                              have hnfin : n - 36850 < 50 := by omega
                                                                              simpa [Nat.sub_add_cancel hoff] using m0_w37 ⟨n - 36850, hnfin⟩
                                                                            ·
                                                                              by_cases h38 : n < 36950
                                                                              · have hoff : 36900 ≤ n := by omega
                                                                                have hnfin : n - 36900 < 50 := by omega
                                                                                simpa [Nat.sub_add_cancel hoff] using m0_w38 ⟨n - 36900, hnfin⟩
                                                                              ·
                                                                                by_cases h39 : n < 37000
                                                                                · have hoff : 36950 ≤ n := by omega
                                                                                  have hnfin : n - 36950 < 50 := by omega
                                                                                  simpa [Nat.sub_add_cancel hoff] using m0_w39 ⟨n - 36950, hnfin⟩
                                                                                ·
                                                                                  by_cases h40 : n < 37050
                                                                                  · have hoff : 37000 ≤ n := by omega
                                                                                    have hnfin : n - 37000 < 50 := by omega
                                                                                    simpa [Nat.sub_add_cancel hoff] using m0_w40 ⟨n - 37000, hnfin⟩
                                                                                  ·
                                                                                    by_cases h41 : n < 37100
                                                                                    · have hoff : 37050 ≤ n := by omega
                                                                                      have hnfin : n - 37050 < 50 := by omega
                                                                                      simpa [Nat.sub_add_cancel hoff] using m0_w41 ⟨n - 37050, hnfin⟩
                                                                                    ·
                                                                                      by_cases h42 : n < 37150
                                                                                      · have hoff : 37100 ≤ n := by omega
                                                                                        have hnfin : n - 37100 < 50 := by omega
                                                                                        simpa [Nat.sub_add_cancel hoff] using m0_w42 ⟨n - 37100, hnfin⟩
                                                                                      ·
                                                                                        by_cases h43 : n < 37200
                                                                                        · have hoff : 37150 ≤ n := by omega
                                                                                          have hnfin : n - 37150 < 50 := by omega
                                                                                          simpa [Nat.sub_add_cancel hoff] using m0_w43 ⟨n - 37150, hnfin⟩
                                                                                        ·
                                                                                          by_cases h44 : n < 37250
                                                                                          · have hoff : 37200 ≤ n := by omega
                                                                                            have hnfin : n - 37200 < 50 := by omega
                                                                                            simpa [Nat.sub_add_cancel hoff] using m0_w44 ⟨n - 37200, hnfin⟩
                                                                                          ·
                                                                                            by_cases h45 : n < 37300
                                                                                            · have hoff : 37250 ≤ n := by omega
                                                                                              have hnfin : n - 37250 < 50 := by omega
                                                                                              simpa [Nat.sub_add_cancel hoff] using m0_w45 ⟨n - 37250, hnfin⟩
                                                                                            ·
                                                                                              by_cases h46 : n < 37350
                                                                                              · have hoff : 37300 ≤ n := by omega
                                                                                                have hnfin : n - 37300 < 50 := by omega
                                                                                                simpa [Nat.sub_add_cancel hoff] using m0_w46 ⟨n - 37300, hnfin⟩
                                                                                              ·
                                                                                                by_cases h47 : n < 37400
                                                                                                · have hoff : 37350 ≤ n := by omega
                                                                                                  have hnfin : n - 37350 < 50 := by omega
                                                                                                  simpa [Nat.sub_add_cancel hoff] using m0_w47 ⟨n - 37350, hnfin⟩
                                                                                                ·
                                                                                                  by_cases h48 : n < 37450
                                                                                                  · have hoff : 37400 ≤ n := by omega
                                                                                                    have hnfin : n - 37400 < 50 := by omega
                                                                                                    simpa [Nat.sub_add_cancel hoff] using m0_w48 ⟨n - 37400, hnfin⟩
                                                                                                  ·
                                                                                                    by_cases h49 : n < 37500
                                                                                                    · have hoff : 37450 ≤ n := by omega
                                                                                                      have hnfin : n - 37450 < 50 := by omega
                                                                                                      simpa [Nat.sub_add_cancel hoff] using m0_w49 ⟨n - 37450, hnfin⟩
                                                                                                    ·
                                                                                                      omega
theorem land1_range (n : ℕ) (hn0 : 35000 ≤ n) (hn1 : n < 37500) :
    (!Nat.blt (dimF (arg1 n)) (dimF n) ||
      Nat.beq (Nat.land (densSupG (arg1 n)) (densSupG n)) (densSupG (arg1 n))) = true := by
  by_cases h0 : n < 35050
  · have hoff : 35000 ≤ n := by omega
    have hnfin : n - 35000 < 50 := by omega
    simpa [Nat.sub_add_cancel hoff] using m1_w0 ⟨n - 35000, hnfin⟩
  ·
    by_cases h1 : n < 35100
    · have hoff : 35050 ≤ n := by omega
      have hnfin : n - 35050 < 50 := by omega
      simpa [Nat.sub_add_cancel hoff] using m1_w1 ⟨n - 35050, hnfin⟩
    ·
      by_cases h2 : n < 35150
      · have hoff : 35100 ≤ n := by omega
        have hnfin : n - 35100 < 50 := by omega
        simpa [Nat.sub_add_cancel hoff] using m1_w2 ⟨n - 35100, hnfin⟩
      ·
        by_cases h3 : n < 35200
        · have hoff : 35150 ≤ n := by omega
          have hnfin : n - 35150 < 50 := by omega
          simpa [Nat.sub_add_cancel hoff] using m1_w3 ⟨n - 35150, hnfin⟩
        ·
          by_cases h4 : n < 35250
          · have hoff : 35200 ≤ n := by omega
            have hnfin : n - 35200 < 50 := by omega
            simpa [Nat.sub_add_cancel hoff] using m1_w4 ⟨n - 35200, hnfin⟩
          ·
            by_cases h5 : n < 35300
            · have hoff : 35250 ≤ n := by omega
              have hnfin : n - 35250 < 50 := by omega
              simpa [Nat.sub_add_cancel hoff] using m1_w5 ⟨n - 35250, hnfin⟩
            ·
              by_cases h6 : n < 35350
              · have hoff : 35300 ≤ n := by omega
                have hnfin : n - 35300 < 50 := by omega
                simpa [Nat.sub_add_cancel hoff] using m1_w6 ⟨n - 35300, hnfin⟩
              ·
                by_cases h7 : n < 35400
                · have hoff : 35350 ≤ n := by omega
                  have hnfin : n - 35350 < 50 := by omega
                  simpa [Nat.sub_add_cancel hoff] using m1_w7 ⟨n - 35350, hnfin⟩
                ·
                  by_cases h8 : n < 35450
                  · have hoff : 35400 ≤ n := by omega
                    have hnfin : n - 35400 < 50 := by omega
                    simpa [Nat.sub_add_cancel hoff] using m1_w8 ⟨n - 35400, hnfin⟩
                  ·
                    by_cases h9 : n < 35500
                    · have hoff : 35450 ≤ n := by omega
                      have hnfin : n - 35450 < 50 := by omega
                      simpa [Nat.sub_add_cancel hoff] using m1_w9 ⟨n - 35450, hnfin⟩
                    ·
                      by_cases h10 : n < 35550
                      · have hoff : 35500 ≤ n := by omega
                        have hnfin : n - 35500 < 50 := by omega
                        simpa [Nat.sub_add_cancel hoff] using m1_w10 ⟨n - 35500, hnfin⟩
                      ·
                        by_cases h11 : n < 35600
                        · have hoff : 35550 ≤ n := by omega
                          have hnfin : n - 35550 < 50 := by omega
                          simpa [Nat.sub_add_cancel hoff] using m1_w11 ⟨n - 35550, hnfin⟩
                        ·
                          by_cases h12 : n < 35650
                          · have hoff : 35600 ≤ n := by omega
                            have hnfin : n - 35600 < 50 := by omega
                            simpa [Nat.sub_add_cancel hoff] using m1_w12 ⟨n - 35600, hnfin⟩
                          ·
                            by_cases h13 : n < 35700
                            · have hoff : 35650 ≤ n := by omega
                              have hnfin : n - 35650 < 50 := by omega
                              simpa [Nat.sub_add_cancel hoff] using m1_w13 ⟨n - 35650, hnfin⟩
                            ·
                              by_cases h14 : n < 35750
                              · have hoff : 35700 ≤ n := by omega
                                have hnfin : n - 35700 < 50 := by omega
                                simpa [Nat.sub_add_cancel hoff] using m1_w14 ⟨n - 35700, hnfin⟩
                              ·
                                by_cases h15 : n < 35800
                                · have hoff : 35750 ≤ n := by omega
                                  have hnfin : n - 35750 < 50 := by omega
                                  simpa [Nat.sub_add_cancel hoff] using m1_w15 ⟨n - 35750, hnfin⟩
                                ·
                                  by_cases h16 : n < 35850
                                  · have hoff : 35800 ≤ n := by omega
                                    have hnfin : n - 35800 < 50 := by omega
                                    simpa [Nat.sub_add_cancel hoff] using m1_w16 ⟨n - 35800, hnfin⟩
                                  ·
                                    by_cases h17 : n < 35900
                                    · have hoff : 35850 ≤ n := by omega
                                      have hnfin : n - 35850 < 50 := by omega
                                      simpa [Nat.sub_add_cancel hoff] using m1_w17 ⟨n - 35850, hnfin⟩
                                    ·
                                      by_cases h18 : n < 35950
                                      · have hoff : 35900 ≤ n := by omega
                                        have hnfin : n - 35900 < 50 := by omega
                                        simpa [Nat.sub_add_cancel hoff] using m1_w18 ⟨n - 35900, hnfin⟩
                                      ·
                                        by_cases h19 : n < 36000
                                        · have hoff : 35950 ≤ n := by omega
                                          have hnfin : n - 35950 < 50 := by omega
                                          simpa [Nat.sub_add_cancel hoff] using m1_w19 ⟨n - 35950, hnfin⟩
                                        ·
                                          by_cases h20 : n < 36050
                                          · have hoff : 36000 ≤ n := by omega
                                            have hnfin : n - 36000 < 50 := by omega
                                            simpa [Nat.sub_add_cancel hoff] using m1_w20 ⟨n - 36000, hnfin⟩
                                          ·
                                            by_cases h21 : n < 36100
                                            · have hoff : 36050 ≤ n := by omega
                                              have hnfin : n - 36050 < 50 := by omega
                                              simpa [Nat.sub_add_cancel hoff] using m1_w21 ⟨n - 36050, hnfin⟩
                                            ·
                                              by_cases h22 : n < 36150
                                              · have hoff : 36100 ≤ n := by omega
                                                have hnfin : n - 36100 < 50 := by omega
                                                simpa [Nat.sub_add_cancel hoff] using m1_w22 ⟨n - 36100, hnfin⟩
                                              ·
                                                by_cases h23 : n < 36200
                                                · have hoff : 36150 ≤ n := by omega
                                                  have hnfin : n - 36150 < 50 := by omega
                                                  simpa [Nat.sub_add_cancel hoff] using m1_w23 ⟨n - 36150, hnfin⟩
                                                ·
                                                  by_cases h24 : n < 36250
                                                  · have hoff : 36200 ≤ n := by omega
                                                    have hnfin : n - 36200 < 50 := by omega
                                                    simpa [Nat.sub_add_cancel hoff] using m1_w24 ⟨n - 36200, hnfin⟩
                                                  ·
                                                    by_cases h25 : n < 36300
                                                    · have hoff : 36250 ≤ n := by omega
                                                      have hnfin : n - 36250 < 50 := by omega
                                                      simpa [Nat.sub_add_cancel hoff] using m1_w25 ⟨n - 36250, hnfin⟩
                                                    ·
                                                      by_cases h26 : n < 36350
                                                      · have hoff : 36300 ≤ n := by omega
                                                        have hnfin : n - 36300 < 50 := by omega
                                                        simpa [Nat.sub_add_cancel hoff] using m1_w26 ⟨n - 36300, hnfin⟩
                                                      ·
                                                        by_cases h27 : n < 36400
                                                        · have hoff : 36350 ≤ n := by omega
                                                          have hnfin : n - 36350 < 50 := by omega
                                                          simpa [Nat.sub_add_cancel hoff] using m1_w27 ⟨n - 36350, hnfin⟩
                                                        ·
                                                          by_cases h28 : n < 36450
                                                          · have hoff : 36400 ≤ n := by omega
                                                            have hnfin : n - 36400 < 50 := by omega
                                                            simpa [Nat.sub_add_cancel hoff] using m1_w28 ⟨n - 36400, hnfin⟩
                                                          ·
                                                            by_cases h29 : n < 36500
                                                            · have hoff : 36450 ≤ n := by omega
                                                              have hnfin : n - 36450 < 50 := by omega
                                                              simpa [Nat.sub_add_cancel hoff] using m1_w29 ⟨n - 36450, hnfin⟩
                                                            ·
                                                              by_cases h30 : n < 36550
                                                              · have hoff : 36500 ≤ n := by omega
                                                                have hnfin : n - 36500 < 50 := by omega
                                                                simpa [Nat.sub_add_cancel hoff] using m1_w30 ⟨n - 36500, hnfin⟩
                                                              ·
                                                                by_cases h31 : n < 36600
                                                                · have hoff : 36550 ≤ n := by omega
                                                                  have hnfin : n - 36550 < 50 := by omega
                                                                  simpa [Nat.sub_add_cancel hoff] using m1_w31 ⟨n - 36550, hnfin⟩
                                                                ·
                                                                  by_cases h32 : n < 36650
                                                                  · have hoff : 36600 ≤ n := by omega
                                                                    have hnfin : n - 36600 < 50 := by omega
                                                                    simpa [Nat.sub_add_cancel hoff] using m1_w32 ⟨n - 36600, hnfin⟩
                                                                  ·
                                                                    by_cases h33 : n < 36700
                                                                    · have hoff : 36650 ≤ n := by omega
                                                                      have hnfin : n - 36650 < 50 := by omega
                                                                      simpa [Nat.sub_add_cancel hoff] using m1_w33 ⟨n - 36650, hnfin⟩
                                                                    ·
                                                                      by_cases h34 : n < 36750
                                                                      · have hoff : 36700 ≤ n := by omega
                                                                        have hnfin : n - 36700 < 50 := by omega
                                                                        simpa [Nat.sub_add_cancel hoff] using m1_w34 ⟨n - 36700, hnfin⟩
                                                                      ·
                                                                        by_cases h35 : n < 36800
                                                                        · have hoff : 36750 ≤ n := by omega
                                                                          have hnfin : n - 36750 < 50 := by omega
                                                                          simpa [Nat.sub_add_cancel hoff] using m1_w35 ⟨n - 36750, hnfin⟩
                                                                        ·
                                                                          by_cases h36 : n < 36850
                                                                          · have hoff : 36800 ≤ n := by omega
                                                                            have hnfin : n - 36800 < 50 := by omega
                                                                            simpa [Nat.sub_add_cancel hoff] using m1_w36 ⟨n - 36800, hnfin⟩
                                                                          ·
                                                                            by_cases h37 : n < 36900
                                                                            · have hoff : 36850 ≤ n := by omega
                                                                              have hnfin : n - 36850 < 50 := by omega
                                                                              simpa [Nat.sub_add_cancel hoff] using m1_w37 ⟨n - 36850, hnfin⟩
                                                                            ·
                                                                              by_cases h38 : n < 36950
                                                                              · have hoff : 36900 ≤ n := by omega
                                                                                have hnfin : n - 36900 < 50 := by omega
                                                                                simpa [Nat.sub_add_cancel hoff] using m1_w38 ⟨n - 36900, hnfin⟩
                                                                              ·
                                                                                by_cases h39 : n < 37000
                                                                                · have hoff : 36950 ≤ n := by omega
                                                                                  have hnfin : n - 36950 < 50 := by omega
                                                                                  simpa [Nat.sub_add_cancel hoff] using m1_w39 ⟨n - 36950, hnfin⟩
                                                                                ·
                                                                                  by_cases h40 : n < 37050
                                                                                  · have hoff : 37000 ≤ n := by omega
                                                                                    have hnfin : n - 37000 < 50 := by omega
                                                                                    simpa [Nat.sub_add_cancel hoff] using m1_w40 ⟨n - 37000, hnfin⟩
                                                                                  ·
                                                                                    by_cases h41 : n < 37100
                                                                                    · have hoff : 37050 ≤ n := by omega
                                                                                      have hnfin : n - 37050 < 50 := by omega
                                                                                      simpa [Nat.sub_add_cancel hoff] using m1_w41 ⟨n - 37050, hnfin⟩
                                                                                    ·
                                                                                      by_cases h42 : n < 37150
                                                                                      · have hoff : 37100 ≤ n := by omega
                                                                                        have hnfin : n - 37100 < 50 := by omega
                                                                                        simpa [Nat.sub_add_cancel hoff] using m1_w42 ⟨n - 37100, hnfin⟩
                                                                                      ·
                                                                                        by_cases h43 : n < 37200
                                                                                        · have hoff : 37150 ≤ n := by omega
                                                                                          have hnfin : n - 37150 < 50 := by omega
                                                                                          simpa [Nat.sub_add_cancel hoff] using m1_w43 ⟨n - 37150, hnfin⟩
                                                                                        ·
                                                                                          by_cases h44 : n < 37250
                                                                                          · have hoff : 37200 ≤ n := by omega
                                                                                            have hnfin : n - 37200 < 50 := by omega
                                                                                            simpa [Nat.sub_add_cancel hoff] using m1_w44 ⟨n - 37200, hnfin⟩
                                                                                          ·
                                                                                            by_cases h45 : n < 37300
                                                                                            · have hoff : 37250 ≤ n := by omega
                                                                                              have hnfin : n - 37250 < 50 := by omega
                                                                                              simpa [Nat.sub_add_cancel hoff] using m1_w45 ⟨n - 37250, hnfin⟩
                                                                                            ·
                                                                                              by_cases h46 : n < 37350
                                                                                              · have hoff : 37300 ≤ n := by omega
                                                                                                have hnfin : n - 37300 < 50 := by omega
                                                                                                simpa [Nat.sub_add_cancel hoff] using m1_w46 ⟨n - 37300, hnfin⟩
                                                                                              ·
                                                                                                by_cases h47 : n < 37400
                                                                                                · have hoff : 37350 ≤ n := by omega
                                                                                                  have hnfin : n - 37350 < 50 := by omega
                                                                                                  simpa [Nat.sub_add_cancel hoff] using m1_w47 ⟨n - 37350, hnfin⟩
                                                                                                ·
                                                                                                  by_cases h48 : n < 37450
                                                                                                  · have hoff : 37400 ≤ n := by omega
                                                                                                    have hnfin : n - 37400 < 50 := by omega
                                                                                                    simpa [Nat.sub_add_cancel hoff] using m1_w48 ⟨n - 37400, hnfin⟩
                                                                                                  ·
                                                                                                    by_cases h49 : n < 37500
                                                                                                    · have hoff : 37450 ≤ n := by omega
                                                                                                      have hnfin : n - 37450 < 50 := by omega
                                                                                                      simpa [Nat.sub_add_cancel hoff] using m1_w49 ⟨n - 37450, hnfin⟩
                                                                                                    ·
                                                                                                      omega
end IntMul.Kappa.R8.Bit.Oppbank.LandMonoFixA14


