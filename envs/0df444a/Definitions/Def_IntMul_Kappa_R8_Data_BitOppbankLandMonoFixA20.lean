-- Prove2me | Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankLandMonoFixA20
-- name    : IntMul_Kappa_R8_Data_BitOppbankLandMonoFixA20
-- status  : Definition
-- author  : @Ethan Cheung Wang
-- created : 2026-10-28T21:17:57.05418+00:00
-- url     : https://prove2.me/theorems/c4ea7604-4932-491f-8cb7-54187cc1b2ab
-- title:
--   Dim-gated densSup land mono FixA pack 20
-- statement:
--   # Dim-gated densSup land (PndFix), pack A20
--
--   Range consolidators for $n\in[50000,52500)$.
-- source:
--   R8 BitOppbank PndFix

-- LandMonoFixA20: PUBLIC dim-gated land + range consolidators (PndFix)
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
namespace IntMul.Kappa.R8.Bit.Oppbank.LandMonoFixA20
def arg0 (n : ℕ) : ℕ := Nat.land (argF n) 65535
def arg1 (n : ℕ) : ℕ := Nat.shiftRight (argF n) 16
theorem m0_w0 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 50000))) (dimF (n.val + 50000)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 50000))) (densSupG (n.val + 50000))) (densSupG (arg0 (n.val + 50000)))) = true := by decide
theorem m1_w0 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 50000))) (dimF (n.val + 50000)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 50000))) (densSupG (n.val + 50000))) (densSupG (arg1 (n.val + 50000)))) = true := by decide
theorem m0_w1 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 50050))) (dimF (n.val + 50050)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 50050))) (densSupG (n.val + 50050))) (densSupG (arg0 (n.val + 50050)))) = true := by decide
theorem m1_w1 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 50050))) (dimF (n.val + 50050)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 50050))) (densSupG (n.val + 50050))) (densSupG (arg1 (n.val + 50050)))) = true := by decide
theorem m0_w2 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 50100))) (dimF (n.val + 50100)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 50100))) (densSupG (n.val + 50100))) (densSupG (arg0 (n.val + 50100)))) = true := by decide
theorem m1_w2 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 50100))) (dimF (n.val + 50100)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 50100))) (densSupG (n.val + 50100))) (densSupG (arg1 (n.val + 50100)))) = true := by decide
theorem m0_w3 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 50150))) (dimF (n.val + 50150)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 50150))) (densSupG (n.val + 50150))) (densSupG (arg0 (n.val + 50150)))) = true := by decide
theorem m1_w3 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 50150))) (dimF (n.val + 50150)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 50150))) (densSupG (n.val + 50150))) (densSupG (arg1 (n.val + 50150)))) = true := by decide
theorem m0_w4 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 50200))) (dimF (n.val + 50200)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 50200))) (densSupG (n.val + 50200))) (densSupG (arg0 (n.val + 50200)))) = true := by decide
theorem m1_w4 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 50200))) (dimF (n.val + 50200)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 50200))) (densSupG (n.val + 50200))) (densSupG (arg1 (n.val + 50200)))) = true := by decide
theorem m0_w5 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 50250))) (dimF (n.val + 50250)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 50250))) (densSupG (n.val + 50250))) (densSupG (arg0 (n.val + 50250)))) = true := by decide
theorem m1_w5 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 50250))) (dimF (n.val + 50250)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 50250))) (densSupG (n.val + 50250))) (densSupG (arg1 (n.val + 50250)))) = true := by decide
theorem m0_w6 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 50300))) (dimF (n.val + 50300)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 50300))) (densSupG (n.val + 50300))) (densSupG (arg0 (n.val + 50300)))) = true := by decide
theorem m1_w6 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 50300))) (dimF (n.val + 50300)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 50300))) (densSupG (n.val + 50300))) (densSupG (arg1 (n.val + 50300)))) = true := by decide
theorem m0_w7 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 50350))) (dimF (n.val + 50350)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 50350))) (densSupG (n.val + 50350))) (densSupG (arg0 (n.val + 50350)))) = true := by decide
theorem m1_w7 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 50350))) (dimF (n.val + 50350)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 50350))) (densSupG (n.val + 50350))) (densSupG (arg1 (n.val + 50350)))) = true := by decide
theorem m0_w8 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 50400))) (dimF (n.val + 50400)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 50400))) (densSupG (n.val + 50400))) (densSupG (arg0 (n.val + 50400)))) = true := by decide
theorem m1_w8 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 50400))) (dimF (n.val + 50400)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 50400))) (densSupG (n.val + 50400))) (densSupG (arg1 (n.val + 50400)))) = true := by decide
theorem m0_w9 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 50450))) (dimF (n.val + 50450)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 50450))) (densSupG (n.val + 50450))) (densSupG (arg0 (n.val + 50450)))) = true := by decide
theorem m1_w9 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 50450))) (dimF (n.val + 50450)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 50450))) (densSupG (n.val + 50450))) (densSupG (arg1 (n.val + 50450)))) = true := by decide
theorem m0_w10 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 50500))) (dimF (n.val + 50500)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 50500))) (densSupG (n.val + 50500))) (densSupG (arg0 (n.val + 50500)))) = true := by decide
theorem m1_w10 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 50500))) (dimF (n.val + 50500)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 50500))) (densSupG (n.val + 50500))) (densSupG (arg1 (n.val + 50500)))) = true := by decide
theorem m0_w11 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 50550))) (dimF (n.val + 50550)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 50550))) (densSupG (n.val + 50550))) (densSupG (arg0 (n.val + 50550)))) = true := by decide
theorem m1_w11 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 50550))) (dimF (n.val + 50550)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 50550))) (densSupG (n.val + 50550))) (densSupG (arg1 (n.val + 50550)))) = true := by decide
theorem m0_w12 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 50600))) (dimF (n.val + 50600)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 50600))) (densSupG (n.val + 50600))) (densSupG (arg0 (n.val + 50600)))) = true := by decide
theorem m1_w12 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 50600))) (dimF (n.val + 50600)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 50600))) (densSupG (n.val + 50600))) (densSupG (arg1 (n.val + 50600)))) = true := by decide
theorem m0_w13 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 50650))) (dimF (n.val + 50650)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 50650))) (densSupG (n.val + 50650))) (densSupG (arg0 (n.val + 50650)))) = true := by decide
theorem m1_w13 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 50650))) (dimF (n.val + 50650)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 50650))) (densSupG (n.val + 50650))) (densSupG (arg1 (n.val + 50650)))) = true := by decide
theorem m0_w14 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 50700))) (dimF (n.val + 50700)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 50700))) (densSupG (n.val + 50700))) (densSupG (arg0 (n.val + 50700)))) = true := by decide
theorem m1_w14 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 50700))) (dimF (n.val + 50700)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 50700))) (densSupG (n.val + 50700))) (densSupG (arg1 (n.val + 50700)))) = true := by decide
theorem m0_w15 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 50750))) (dimF (n.val + 50750)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 50750))) (densSupG (n.val + 50750))) (densSupG (arg0 (n.val + 50750)))) = true := by decide
theorem m1_w15 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 50750))) (dimF (n.val + 50750)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 50750))) (densSupG (n.val + 50750))) (densSupG (arg1 (n.val + 50750)))) = true := by decide
theorem m0_w16 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 50800))) (dimF (n.val + 50800)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 50800))) (densSupG (n.val + 50800))) (densSupG (arg0 (n.val + 50800)))) = true := by decide
theorem m1_w16 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 50800))) (dimF (n.val + 50800)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 50800))) (densSupG (n.val + 50800))) (densSupG (arg1 (n.val + 50800)))) = true := by decide
theorem m0_w17 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 50850))) (dimF (n.val + 50850)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 50850))) (densSupG (n.val + 50850))) (densSupG (arg0 (n.val + 50850)))) = true := by decide
theorem m1_w17 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 50850))) (dimF (n.val + 50850)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 50850))) (densSupG (n.val + 50850))) (densSupG (arg1 (n.val + 50850)))) = true := by decide
theorem m0_w18 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 50900))) (dimF (n.val + 50900)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 50900))) (densSupG (n.val + 50900))) (densSupG (arg0 (n.val + 50900)))) = true := by decide
theorem m1_w18 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 50900))) (dimF (n.val + 50900)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 50900))) (densSupG (n.val + 50900))) (densSupG (arg1 (n.val + 50900)))) = true := by decide
theorem m0_w19 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 50950))) (dimF (n.val + 50950)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 50950))) (densSupG (n.val + 50950))) (densSupG (arg0 (n.val + 50950)))) = true := by decide
theorem m1_w19 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 50950))) (dimF (n.val + 50950)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 50950))) (densSupG (n.val + 50950))) (densSupG (arg1 (n.val + 50950)))) = true := by decide
theorem m0_w20 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 51000))) (dimF (n.val + 51000)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 51000))) (densSupG (n.val + 51000))) (densSupG (arg0 (n.val + 51000)))) = true := by decide
theorem m1_w20 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 51000))) (dimF (n.val + 51000)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 51000))) (densSupG (n.val + 51000))) (densSupG (arg1 (n.val + 51000)))) = true := by decide
theorem m0_w21 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 51050))) (dimF (n.val + 51050)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 51050))) (densSupG (n.val + 51050))) (densSupG (arg0 (n.val + 51050)))) = true := by decide
theorem m1_w21 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 51050))) (dimF (n.val + 51050)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 51050))) (densSupG (n.val + 51050))) (densSupG (arg1 (n.val + 51050)))) = true := by decide
theorem m0_w22 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 51100))) (dimF (n.val + 51100)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 51100))) (densSupG (n.val + 51100))) (densSupG (arg0 (n.val + 51100)))) = true := by decide
theorem m1_w22 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 51100))) (dimF (n.val + 51100)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 51100))) (densSupG (n.val + 51100))) (densSupG (arg1 (n.val + 51100)))) = true := by decide
theorem m0_w23 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 51150))) (dimF (n.val + 51150)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 51150))) (densSupG (n.val + 51150))) (densSupG (arg0 (n.val + 51150)))) = true := by decide
theorem m1_w23 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 51150))) (dimF (n.val + 51150)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 51150))) (densSupG (n.val + 51150))) (densSupG (arg1 (n.val + 51150)))) = true := by decide
theorem m0_w24 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 51200))) (dimF (n.val + 51200)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 51200))) (densSupG (n.val + 51200))) (densSupG (arg0 (n.val + 51200)))) = true := by decide
theorem m1_w24 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 51200))) (dimF (n.val + 51200)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 51200))) (densSupG (n.val + 51200))) (densSupG (arg1 (n.val + 51200)))) = true := by decide
theorem m0_w25 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 51250))) (dimF (n.val + 51250)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 51250))) (densSupG (n.val + 51250))) (densSupG (arg0 (n.val + 51250)))) = true := by decide
theorem m1_w25 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 51250))) (dimF (n.val + 51250)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 51250))) (densSupG (n.val + 51250))) (densSupG (arg1 (n.val + 51250)))) = true := by decide
theorem m0_w26 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 51300))) (dimF (n.val + 51300)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 51300))) (densSupG (n.val + 51300))) (densSupG (arg0 (n.val + 51300)))) = true := by decide
theorem m1_w26 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 51300))) (dimF (n.val + 51300)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 51300))) (densSupG (n.val + 51300))) (densSupG (arg1 (n.val + 51300)))) = true := by decide
theorem m0_w27 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 51350))) (dimF (n.val + 51350)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 51350))) (densSupG (n.val + 51350))) (densSupG (arg0 (n.val + 51350)))) = true := by decide
theorem m1_w27 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 51350))) (dimF (n.val + 51350)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 51350))) (densSupG (n.val + 51350))) (densSupG (arg1 (n.val + 51350)))) = true := by decide
theorem m0_w28 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 51400))) (dimF (n.val + 51400)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 51400))) (densSupG (n.val + 51400))) (densSupG (arg0 (n.val + 51400)))) = true := by decide
theorem m1_w28 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 51400))) (dimF (n.val + 51400)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 51400))) (densSupG (n.val + 51400))) (densSupG (arg1 (n.val + 51400)))) = true := by decide
theorem m0_w29 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 51450))) (dimF (n.val + 51450)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 51450))) (densSupG (n.val + 51450))) (densSupG (arg0 (n.val + 51450)))) = true := by decide
theorem m1_w29 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 51450))) (dimF (n.val + 51450)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 51450))) (densSupG (n.val + 51450))) (densSupG (arg1 (n.val + 51450)))) = true := by decide
theorem m0_w30 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 51500))) (dimF (n.val + 51500)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 51500))) (densSupG (n.val + 51500))) (densSupG (arg0 (n.val + 51500)))) = true := by decide
theorem m1_w30 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 51500))) (dimF (n.val + 51500)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 51500))) (densSupG (n.val + 51500))) (densSupG (arg1 (n.val + 51500)))) = true := by decide
theorem m0_w31 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 51550))) (dimF (n.val + 51550)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 51550))) (densSupG (n.val + 51550))) (densSupG (arg0 (n.val + 51550)))) = true := by decide
theorem m1_w31 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 51550))) (dimF (n.val + 51550)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 51550))) (densSupG (n.val + 51550))) (densSupG (arg1 (n.val + 51550)))) = true := by decide
theorem m0_w32 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 51600))) (dimF (n.val + 51600)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 51600))) (densSupG (n.val + 51600))) (densSupG (arg0 (n.val + 51600)))) = true := by decide
theorem m1_w32 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 51600))) (dimF (n.val + 51600)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 51600))) (densSupG (n.val + 51600))) (densSupG (arg1 (n.val + 51600)))) = true := by decide
theorem m0_w33 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 51650))) (dimF (n.val + 51650)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 51650))) (densSupG (n.val + 51650))) (densSupG (arg0 (n.val + 51650)))) = true := by decide
theorem m1_w33 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 51650))) (dimF (n.val + 51650)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 51650))) (densSupG (n.val + 51650))) (densSupG (arg1 (n.val + 51650)))) = true := by decide
theorem m0_w34 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 51700))) (dimF (n.val + 51700)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 51700))) (densSupG (n.val + 51700))) (densSupG (arg0 (n.val + 51700)))) = true := by decide
theorem m1_w34 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 51700))) (dimF (n.val + 51700)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 51700))) (densSupG (n.val + 51700))) (densSupG (arg1 (n.val + 51700)))) = true := by decide
theorem m0_w35 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 51750))) (dimF (n.val + 51750)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 51750))) (densSupG (n.val + 51750))) (densSupG (arg0 (n.val + 51750)))) = true := by decide
theorem m1_w35 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 51750))) (dimF (n.val + 51750)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 51750))) (densSupG (n.val + 51750))) (densSupG (arg1 (n.val + 51750)))) = true := by decide
theorem m0_w36 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 51800))) (dimF (n.val + 51800)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 51800))) (densSupG (n.val + 51800))) (densSupG (arg0 (n.val + 51800)))) = true := by decide
theorem m1_w36 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 51800))) (dimF (n.val + 51800)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 51800))) (densSupG (n.val + 51800))) (densSupG (arg1 (n.val + 51800)))) = true := by decide
theorem m0_w37 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 51850))) (dimF (n.val + 51850)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 51850))) (densSupG (n.val + 51850))) (densSupG (arg0 (n.val + 51850)))) = true := by decide
theorem m1_w37 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 51850))) (dimF (n.val + 51850)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 51850))) (densSupG (n.val + 51850))) (densSupG (arg1 (n.val + 51850)))) = true := by decide
theorem m0_w38 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 51900))) (dimF (n.val + 51900)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 51900))) (densSupG (n.val + 51900))) (densSupG (arg0 (n.val + 51900)))) = true := by decide
theorem m1_w38 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 51900))) (dimF (n.val + 51900)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 51900))) (densSupG (n.val + 51900))) (densSupG (arg1 (n.val + 51900)))) = true := by decide
theorem m0_w39 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 51950))) (dimF (n.val + 51950)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 51950))) (densSupG (n.val + 51950))) (densSupG (arg0 (n.val + 51950)))) = true := by decide
theorem m1_w39 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 51950))) (dimF (n.val + 51950)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 51950))) (densSupG (n.val + 51950))) (densSupG (arg1 (n.val + 51950)))) = true := by decide
theorem m0_w40 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 52000))) (dimF (n.val + 52000)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 52000))) (densSupG (n.val + 52000))) (densSupG (arg0 (n.val + 52000)))) = true := by decide
theorem m1_w40 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 52000))) (dimF (n.val + 52000)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 52000))) (densSupG (n.val + 52000))) (densSupG (arg1 (n.val + 52000)))) = true := by decide
theorem m0_w41 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 52050))) (dimF (n.val + 52050)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 52050))) (densSupG (n.val + 52050))) (densSupG (arg0 (n.val + 52050)))) = true := by decide
theorem m1_w41 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 52050))) (dimF (n.val + 52050)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 52050))) (densSupG (n.val + 52050))) (densSupG (arg1 (n.val + 52050)))) = true := by decide
theorem m0_w42 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 52100))) (dimF (n.val + 52100)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 52100))) (densSupG (n.val + 52100))) (densSupG (arg0 (n.val + 52100)))) = true := by decide
theorem m1_w42 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 52100))) (dimF (n.val + 52100)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 52100))) (densSupG (n.val + 52100))) (densSupG (arg1 (n.val + 52100)))) = true := by decide
theorem m0_w43 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 52150))) (dimF (n.val + 52150)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 52150))) (densSupG (n.val + 52150))) (densSupG (arg0 (n.val + 52150)))) = true := by decide
theorem m1_w43 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 52150))) (dimF (n.val + 52150)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 52150))) (densSupG (n.val + 52150))) (densSupG (arg1 (n.val + 52150)))) = true := by decide
theorem m0_w44 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 52200))) (dimF (n.val + 52200)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 52200))) (densSupG (n.val + 52200))) (densSupG (arg0 (n.val + 52200)))) = true := by decide
theorem m1_w44 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 52200))) (dimF (n.val + 52200)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 52200))) (densSupG (n.val + 52200))) (densSupG (arg1 (n.val + 52200)))) = true := by decide
theorem m0_w45 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 52250))) (dimF (n.val + 52250)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 52250))) (densSupG (n.val + 52250))) (densSupG (arg0 (n.val + 52250)))) = true := by decide
theorem m1_w45 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 52250))) (dimF (n.val + 52250)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 52250))) (densSupG (n.val + 52250))) (densSupG (arg1 (n.val + 52250)))) = true := by decide
theorem m0_w46 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 52300))) (dimF (n.val + 52300)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 52300))) (densSupG (n.val + 52300))) (densSupG (arg0 (n.val + 52300)))) = true := by decide
theorem m1_w46 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 52300))) (dimF (n.val + 52300)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 52300))) (densSupG (n.val + 52300))) (densSupG (arg1 (n.val + 52300)))) = true := by decide
theorem m0_w47 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 52350))) (dimF (n.val + 52350)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 52350))) (densSupG (n.val + 52350))) (densSupG (arg0 (n.val + 52350)))) = true := by decide
theorem m1_w47 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 52350))) (dimF (n.val + 52350)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 52350))) (densSupG (n.val + 52350))) (densSupG (arg1 (n.val + 52350)))) = true := by decide
theorem m0_w48 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 52400))) (dimF (n.val + 52400)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 52400))) (densSupG (n.val + 52400))) (densSupG (arg0 (n.val + 52400)))) = true := by decide
theorem m1_w48 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 52400))) (dimF (n.val + 52400)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 52400))) (densSupG (n.val + 52400))) (densSupG (arg1 (n.val + 52400)))) = true := by decide
theorem m0_w49 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 52450))) (dimF (n.val + 52450)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 52450))) (densSupG (n.val + 52450))) (densSupG (arg0 (n.val + 52450)))) = true := by decide
theorem m1_w49 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 52450))) (dimF (n.val + 52450)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 52450))) (densSupG (n.val + 52450))) (densSupG (arg1 (n.val + 52450)))) = true := by decide
theorem land0_range (n : ℕ) (hn0 : 50000 ≤ n) (hn1 : n < 52500) :
    (!Nat.blt (dimF (arg0 n)) (dimF n) ||
      Nat.beq (Nat.land (densSupG (arg0 n)) (densSupG n)) (densSupG (arg0 n))) = true := by
  by_cases h0 : n < 50050
  · have hoff : 50000 ≤ n := by omega
    have hnfin : n - 50000 < 50 := by omega
    simpa [Nat.sub_add_cancel hoff] using m0_w0 ⟨n - 50000, hnfin⟩
  ·
    by_cases h1 : n < 50100
    · have hoff : 50050 ≤ n := by omega
      have hnfin : n - 50050 < 50 := by omega
      simpa [Nat.sub_add_cancel hoff] using m0_w1 ⟨n - 50050, hnfin⟩
    ·
      by_cases h2 : n < 50150
      · have hoff : 50100 ≤ n := by omega
        have hnfin : n - 50100 < 50 := by omega
        simpa [Nat.sub_add_cancel hoff] using m0_w2 ⟨n - 50100, hnfin⟩
      ·
        by_cases h3 : n < 50200
        · have hoff : 50150 ≤ n := by omega
          have hnfin : n - 50150 < 50 := by omega
          simpa [Nat.sub_add_cancel hoff] using m0_w3 ⟨n - 50150, hnfin⟩
        ·
          by_cases h4 : n < 50250
          · have hoff : 50200 ≤ n := by omega
            have hnfin : n - 50200 < 50 := by omega
            simpa [Nat.sub_add_cancel hoff] using m0_w4 ⟨n - 50200, hnfin⟩
          ·
            by_cases h5 : n < 50300
            · have hoff : 50250 ≤ n := by omega
              have hnfin : n - 50250 < 50 := by omega
              simpa [Nat.sub_add_cancel hoff] using m0_w5 ⟨n - 50250, hnfin⟩
            ·
              by_cases h6 : n < 50350
              · have hoff : 50300 ≤ n := by omega
                have hnfin : n - 50300 < 50 := by omega
                simpa [Nat.sub_add_cancel hoff] using m0_w6 ⟨n - 50300, hnfin⟩
              ·
                by_cases h7 : n < 50400
                · have hoff : 50350 ≤ n := by omega
                  have hnfin : n - 50350 < 50 := by omega
                  simpa [Nat.sub_add_cancel hoff] using m0_w7 ⟨n - 50350, hnfin⟩
                ·
                  by_cases h8 : n < 50450
                  · have hoff : 50400 ≤ n := by omega
                    have hnfin : n - 50400 < 50 := by omega
                    simpa [Nat.sub_add_cancel hoff] using m0_w8 ⟨n - 50400, hnfin⟩
                  ·
                    by_cases h9 : n < 50500
                    · have hoff : 50450 ≤ n := by omega
                      have hnfin : n - 50450 < 50 := by omega
                      simpa [Nat.sub_add_cancel hoff] using m0_w9 ⟨n - 50450, hnfin⟩
                    ·
                      by_cases h10 : n < 50550
                      · have hoff : 50500 ≤ n := by omega
                        have hnfin : n - 50500 < 50 := by omega
                        simpa [Nat.sub_add_cancel hoff] using m0_w10 ⟨n - 50500, hnfin⟩
                      ·
                        by_cases h11 : n < 50600
                        · have hoff : 50550 ≤ n := by omega
                          have hnfin : n - 50550 < 50 := by omega
                          simpa [Nat.sub_add_cancel hoff] using m0_w11 ⟨n - 50550, hnfin⟩
                        ·
                          by_cases h12 : n < 50650
                          · have hoff : 50600 ≤ n := by omega
                            have hnfin : n - 50600 < 50 := by omega
                            simpa [Nat.sub_add_cancel hoff] using m0_w12 ⟨n - 50600, hnfin⟩
                          ·
                            by_cases h13 : n < 50700
                            · have hoff : 50650 ≤ n := by omega
                              have hnfin : n - 50650 < 50 := by omega
                              simpa [Nat.sub_add_cancel hoff] using m0_w13 ⟨n - 50650, hnfin⟩
                            ·
                              by_cases h14 : n < 50750
                              · have hoff : 50700 ≤ n := by omega
                                have hnfin : n - 50700 < 50 := by omega
                                simpa [Nat.sub_add_cancel hoff] using m0_w14 ⟨n - 50700, hnfin⟩
                              ·
                                by_cases h15 : n < 50800
                                · have hoff : 50750 ≤ n := by omega
                                  have hnfin : n - 50750 < 50 := by omega
                                  simpa [Nat.sub_add_cancel hoff] using m0_w15 ⟨n - 50750, hnfin⟩
                                ·
                                  by_cases h16 : n < 50850
                                  · have hoff : 50800 ≤ n := by omega
                                    have hnfin : n - 50800 < 50 := by omega
                                    simpa [Nat.sub_add_cancel hoff] using m0_w16 ⟨n - 50800, hnfin⟩
                                  ·
                                    by_cases h17 : n < 50900
                                    · have hoff : 50850 ≤ n := by omega
                                      have hnfin : n - 50850 < 50 := by omega
                                      simpa [Nat.sub_add_cancel hoff] using m0_w17 ⟨n - 50850, hnfin⟩
                                    ·
                                      by_cases h18 : n < 50950
                                      · have hoff : 50900 ≤ n := by omega
                                        have hnfin : n - 50900 < 50 := by omega
                                        simpa [Nat.sub_add_cancel hoff] using m0_w18 ⟨n - 50900, hnfin⟩
                                      ·
                                        by_cases h19 : n < 51000
                                        · have hoff : 50950 ≤ n := by omega
                                          have hnfin : n - 50950 < 50 := by omega
                                          simpa [Nat.sub_add_cancel hoff] using m0_w19 ⟨n - 50950, hnfin⟩
                                        ·
                                          by_cases h20 : n < 51050
                                          · have hoff : 51000 ≤ n := by omega
                                            have hnfin : n - 51000 < 50 := by omega
                                            simpa [Nat.sub_add_cancel hoff] using m0_w20 ⟨n - 51000, hnfin⟩
                                          ·
                                            by_cases h21 : n < 51100
                                            · have hoff : 51050 ≤ n := by omega
                                              have hnfin : n - 51050 < 50 := by omega
                                              simpa [Nat.sub_add_cancel hoff] using m0_w21 ⟨n - 51050, hnfin⟩
                                            ·
                                              by_cases h22 : n < 51150
                                              · have hoff : 51100 ≤ n := by omega
                                                have hnfin : n - 51100 < 50 := by omega
                                                simpa [Nat.sub_add_cancel hoff] using m0_w22 ⟨n - 51100, hnfin⟩
                                              ·
                                                by_cases h23 : n < 51200
                                                · have hoff : 51150 ≤ n := by omega
                                                  have hnfin : n - 51150 < 50 := by omega
                                                  simpa [Nat.sub_add_cancel hoff] using m0_w23 ⟨n - 51150, hnfin⟩
                                                ·
                                                  by_cases h24 : n < 51250
                                                  · have hoff : 51200 ≤ n := by omega
                                                    have hnfin : n - 51200 < 50 := by omega
                                                    simpa [Nat.sub_add_cancel hoff] using m0_w24 ⟨n - 51200, hnfin⟩
                                                  ·
                                                    by_cases h25 : n < 51300
                                                    · have hoff : 51250 ≤ n := by omega
                                                      have hnfin : n - 51250 < 50 := by omega
                                                      simpa [Nat.sub_add_cancel hoff] using m0_w25 ⟨n - 51250, hnfin⟩
                                                    ·
                                                      by_cases h26 : n < 51350
                                                      · have hoff : 51300 ≤ n := by omega
                                                        have hnfin : n - 51300 < 50 := by omega
                                                        simpa [Nat.sub_add_cancel hoff] using m0_w26 ⟨n - 51300, hnfin⟩
                                                      ·
                                                        by_cases h27 : n < 51400
                                                        · have hoff : 51350 ≤ n := by omega
                                                          have hnfin : n - 51350 < 50 := by omega
                                                          simpa [Nat.sub_add_cancel hoff] using m0_w27 ⟨n - 51350, hnfin⟩
                                                        ·
                                                          by_cases h28 : n < 51450
                                                          · have hoff : 51400 ≤ n := by omega
                                                            have hnfin : n - 51400 < 50 := by omega
                                                            simpa [Nat.sub_add_cancel hoff] using m0_w28 ⟨n - 51400, hnfin⟩
                                                          ·
                                                            by_cases h29 : n < 51500
                                                            · have hoff : 51450 ≤ n := by omega
                                                              have hnfin : n - 51450 < 50 := by omega
                                                              simpa [Nat.sub_add_cancel hoff] using m0_w29 ⟨n - 51450, hnfin⟩
                                                            ·
                                                              by_cases h30 : n < 51550
                                                              · have hoff : 51500 ≤ n := by omega
                                                                have hnfin : n - 51500 < 50 := by omega
                                                                simpa [Nat.sub_add_cancel hoff] using m0_w30 ⟨n - 51500, hnfin⟩
                                                              ·
                                                                by_cases h31 : n < 51600
                                                                · have hoff : 51550 ≤ n := by omega
                                                                  have hnfin : n - 51550 < 50 := by omega
                                                                  simpa [Nat.sub_add_cancel hoff] using m0_w31 ⟨n - 51550, hnfin⟩
                                                                ·
                                                                  by_cases h32 : n < 51650
                                                                  · have hoff : 51600 ≤ n := by omega
                                                                    have hnfin : n - 51600 < 50 := by omega
                                                                    simpa [Nat.sub_add_cancel hoff] using m0_w32 ⟨n - 51600, hnfin⟩
                                                                  ·
                                                                    by_cases h33 : n < 51700
                                                                    · have hoff : 51650 ≤ n := by omega
                                                                      have hnfin : n - 51650 < 50 := by omega
                                                                      simpa [Nat.sub_add_cancel hoff] using m0_w33 ⟨n - 51650, hnfin⟩
                                                                    ·
                                                                      by_cases h34 : n < 51750
                                                                      · have hoff : 51700 ≤ n := by omega
                                                                        have hnfin : n - 51700 < 50 := by omega
                                                                        simpa [Nat.sub_add_cancel hoff] using m0_w34 ⟨n - 51700, hnfin⟩
                                                                      ·
                                                                        by_cases h35 : n < 51800
                                                                        · have hoff : 51750 ≤ n := by omega
                                                                          have hnfin : n - 51750 < 50 := by omega
                                                                          simpa [Nat.sub_add_cancel hoff] using m0_w35 ⟨n - 51750, hnfin⟩
                                                                        ·
                                                                          by_cases h36 : n < 51850
                                                                          · have hoff : 51800 ≤ n := by omega
                                                                            have hnfin : n - 51800 < 50 := by omega
                                                                            simpa [Nat.sub_add_cancel hoff] using m0_w36 ⟨n - 51800, hnfin⟩
                                                                          ·
                                                                            by_cases h37 : n < 51900
                                                                            · have hoff : 51850 ≤ n := by omega
                                                                              have hnfin : n - 51850 < 50 := by omega
                                                                              simpa [Nat.sub_add_cancel hoff] using m0_w37 ⟨n - 51850, hnfin⟩
                                                                            ·
                                                                              by_cases h38 : n < 51950
                                                                              · have hoff : 51900 ≤ n := by omega
                                                                                have hnfin : n - 51900 < 50 := by omega
                                                                                simpa [Nat.sub_add_cancel hoff] using m0_w38 ⟨n - 51900, hnfin⟩
                                                                              ·
                                                                                by_cases h39 : n < 52000
                                                                                · have hoff : 51950 ≤ n := by omega
                                                                                  have hnfin : n - 51950 < 50 := by omega
                                                                                  simpa [Nat.sub_add_cancel hoff] using m0_w39 ⟨n - 51950, hnfin⟩
                                                                                ·
                                                                                  by_cases h40 : n < 52050
                                                                                  · have hoff : 52000 ≤ n := by omega
                                                                                    have hnfin : n - 52000 < 50 := by omega
                                                                                    simpa [Nat.sub_add_cancel hoff] using m0_w40 ⟨n - 52000, hnfin⟩
                                                                                  ·
                                                                                    by_cases h41 : n < 52100
                                                                                    · have hoff : 52050 ≤ n := by omega
                                                                                      have hnfin : n - 52050 < 50 := by omega
                                                                                      simpa [Nat.sub_add_cancel hoff] using m0_w41 ⟨n - 52050, hnfin⟩
                                                                                    ·
                                                                                      by_cases h42 : n < 52150
                                                                                      · have hoff : 52100 ≤ n := by omega
                                                                                        have hnfin : n - 52100 < 50 := by omega
                                                                                        simpa [Nat.sub_add_cancel hoff] using m0_w42 ⟨n - 52100, hnfin⟩
                                                                                      ·
                                                                                        by_cases h43 : n < 52200
                                                                                        · have hoff : 52150 ≤ n := by omega
                                                                                          have hnfin : n - 52150 < 50 := by omega
                                                                                          simpa [Nat.sub_add_cancel hoff] using m0_w43 ⟨n - 52150, hnfin⟩
                                                                                        ·
                                                                                          by_cases h44 : n < 52250
                                                                                          · have hoff : 52200 ≤ n := by omega
                                                                                            have hnfin : n - 52200 < 50 := by omega
                                                                                            simpa [Nat.sub_add_cancel hoff] using m0_w44 ⟨n - 52200, hnfin⟩
                                                                                          ·
                                                                                            by_cases h45 : n < 52300
                                                                                            · have hoff : 52250 ≤ n := by omega
                                                                                              have hnfin : n - 52250 < 50 := by omega
                                                                                              simpa [Nat.sub_add_cancel hoff] using m0_w45 ⟨n - 52250, hnfin⟩
                                                                                            ·
                                                                                              by_cases h46 : n < 52350
                                                                                              · have hoff : 52300 ≤ n := by omega
                                                                                                have hnfin : n - 52300 < 50 := by omega
                                                                                                simpa [Nat.sub_add_cancel hoff] using m0_w46 ⟨n - 52300, hnfin⟩
                                                                                              ·
                                                                                                by_cases h47 : n < 52400
                                                                                                · have hoff : 52350 ≤ n := by omega
                                                                                                  have hnfin : n - 52350 < 50 := by omega
                                                                                                  simpa [Nat.sub_add_cancel hoff] using m0_w47 ⟨n - 52350, hnfin⟩
                                                                                                ·
                                                                                                  by_cases h48 : n < 52450
                                                                                                  · have hoff : 52400 ≤ n := by omega
                                                                                                    have hnfin : n - 52400 < 50 := by omega
                                                                                                    simpa [Nat.sub_add_cancel hoff] using m0_w48 ⟨n - 52400, hnfin⟩
                                                                                                  ·
                                                                                                    by_cases h49 : n < 52500
                                                                                                    · have hoff : 52450 ≤ n := by omega
                                                                                                      have hnfin : n - 52450 < 50 := by omega
                                                                                                      simpa [Nat.sub_add_cancel hoff] using m0_w49 ⟨n - 52450, hnfin⟩
                                                                                                    ·
                                                                                                      omega
theorem land1_range (n : ℕ) (hn0 : 50000 ≤ n) (hn1 : n < 52500) :
    (!Nat.blt (dimF (arg1 n)) (dimF n) ||
      Nat.beq (Nat.land (densSupG (arg1 n)) (densSupG n)) (densSupG (arg1 n))) = true := by
  by_cases h0 : n < 50050
  · have hoff : 50000 ≤ n := by omega
    have hnfin : n - 50000 < 50 := by omega
    simpa [Nat.sub_add_cancel hoff] using m1_w0 ⟨n - 50000, hnfin⟩
  ·
    by_cases h1 : n < 50100
    · have hoff : 50050 ≤ n := by omega
      have hnfin : n - 50050 < 50 := by omega
      simpa [Nat.sub_add_cancel hoff] using m1_w1 ⟨n - 50050, hnfin⟩
    ·
      by_cases h2 : n < 50150
      · have hoff : 50100 ≤ n := by omega
        have hnfin : n - 50100 < 50 := by omega
        simpa [Nat.sub_add_cancel hoff] using m1_w2 ⟨n - 50100, hnfin⟩
      ·
        by_cases h3 : n < 50200
        · have hoff : 50150 ≤ n := by omega
          have hnfin : n - 50150 < 50 := by omega
          simpa [Nat.sub_add_cancel hoff] using m1_w3 ⟨n - 50150, hnfin⟩
        ·
          by_cases h4 : n < 50250
          · have hoff : 50200 ≤ n := by omega
            have hnfin : n - 50200 < 50 := by omega
            simpa [Nat.sub_add_cancel hoff] using m1_w4 ⟨n - 50200, hnfin⟩
          ·
            by_cases h5 : n < 50300
            · have hoff : 50250 ≤ n := by omega
              have hnfin : n - 50250 < 50 := by omega
              simpa [Nat.sub_add_cancel hoff] using m1_w5 ⟨n - 50250, hnfin⟩
            ·
              by_cases h6 : n < 50350
              · have hoff : 50300 ≤ n := by omega
                have hnfin : n - 50300 < 50 := by omega
                simpa [Nat.sub_add_cancel hoff] using m1_w6 ⟨n - 50300, hnfin⟩
              ·
                by_cases h7 : n < 50400
                · have hoff : 50350 ≤ n := by omega
                  have hnfin : n - 50350 < 50 := by omega
                  simpa [Nat.sub_add_cancel hoff] using m1_w7 ⟨n - 50350, hnfin⟩
                ·
                  by_cases h8 : n < 50450
                  · have hoff : 50400 ≤ n := by omega
                    have hnfin : n - 50400 < 50 := by omega
                    simpa [Nat.sub_add_cancel hoff] using m1_w8 ⟨n - 50400, hnfin⟩
                  ·
                    by_cases h9 : n < 50500
                    · have hoff : 50450 ≤ n := by omega
                      have hnfin : n - 50450 < 50 := by omega
                      simpa [Nat.sub_add_cancel hoff] using m1_w9 ⟨n - 50450, hnfin⟩
                    ·
                      by_cases h10 : n < 50550
                      · have hoff : 50500 ≤ n := by omega
                        have hnfin : n - 50500 < 50 := by omega
                        simpa [Nat.sub_add_cancel hoff] using m1_w10 ⟨n - 50500, hnfin⟩
                      ·
                        by_cases h11 : n < 50600
                        · have hoff : 50550 ≤ n := by omega
                          have hnfin : n - 50550 < 50 := by omega
                          simpa [Nat.sub_add_cancel hoff] using m1_w11 ⟨n - 50550, hnfin⟩
                        ·
                          by_cases h12 : n < 50650
                          · have hoff : 50600 ≤ n := by omega
                            have hnfin : n - 50600 < 50 := by omega
                            simpa [Nat.sub_add_cancel hoff] using m1_w12 ⟨n - 50600, hnfin⟩
                          ·
                            by_cases h13 : n < 50700
                            · have hoff : 50650 ≤ n := by omega
                              have hnfin : n - 50650 < 50 := by omega
                              simpa [Nat.sub_add_cancel hoff] using m1_w13 ⟨n - 50650, hnfin⟩
                            ·
                              by_cases h14 : n < 50750
                              · have hoff : 50700 ≤ n := by omega
                                have hnfin : n - 50700 < 50 := by omega
                                simpa [Nat.sub_add_cancel hoff] using m1_w14 ⟨n - 50700, hnfin⟩
                              ·
                                by_cases h15 : n < 50800
                                · have hoff : 50750 ≤ n := by omega
                                  have hnfin : n - 50750 < 50 := by omega
                                  simpa [Nat.sub_add_cancel hoff] using m1_w15 ⟨n - 50750, hnfin⟩
                                ·
                                  by_cases h16 : n < 50850
                                  · have hoff : 50800 ≤ n := by omega
                                    have hnfin : n - 50800 < 50 := by omega
                                    simpa [Nat.sub_add_cancel hoff] using m1_w16 ⟨n - 50800, hnfin⟩
                                  ·
                                    by_cases h17 : n < 50900
                                    · have hoff : 50850 ≤ n := by omega
                                      have hnfin : n - 50850 < 50 := by omega
                                      simpa [Nat.sub_add_cancel hoff] using m1_w17 ⟨n - 50850, hnfin⟩
                                    ·
                                      by_cases h18 : n < 50950
                                      · have hoff : 50900 ≤ n := by omega
                                        have hnfin : n - 50900 < 50 := by omega
                                        simpa [Nat.sub_add_cancel hoff] using m1_w18 ⟨n - 50900, hnfin⟩
                                      ·
                                        by_cases h19 : n < 51000
                                        · have hoff : 50950 ≤ n := by omega
                                          have hnfin : n - 50950 < 50 := by omega
                                          simpa [Nat.sub_add_cancel hoff] using m1_w19 ⟨n - 50950, hnfin⟩
                                        ·
                                          by_cases h20 : n < 51050
                                          · have hoff : 51000 ≤ n := by omega
                                            have hnfin : n - 51000 < 50 := by omega
                                            simpa [Nat.sub_add_cancel hoff] using m1_w20 ⟨n - 51000, hnfin⟩
                                          ·
                                            by_cases h21 : n < 51100
                                            · have hoff : 51050 ≤ n := by omega
                                              have hnfin : n - 51050 < 50 := by omega
                                              simpa [Nat.sub_add_cancel hoff] using m1_w21 ⟨n - 51050, hnfin⟩
                                            ·
                                              by_cases h22 : n < 51150
                                              · have hoff : 51100 ≤ n := by omega
                                                have hnfin : n - 51100 < 50 := by omega
                                                simpa [Nat.sub_add_cancel hoff] using m1_w22 ⟨n - 51100, hnfin⟩
                                              ·
                                                by_cases h23 : n < 51200
                                                · have hoff : 51150 ≤ n := by omega
                                                  have hnfin : n - 51150 < 50 := by omega
                                                  simpa [Nat.sub_add_cancel hoff] using m1_w23 ⟨n - 51150, hnfin⟩
                                                ·
                                                  by_cases h24 : n < 51250
                                                  · have hoff : 51200 ≤ n := by omega
                                                    have hnfin : n - 51200 < 50 := by omega
                                                    simpa [Nat.sub_add_cancel hoff] using m1_w24 ⟨n - 51200, hnfin⟩
                                                  ·
                                                    by_cases h25 : n < 51300
                                                    · have hoff : 51250 ≤ n := by omega
                                                      have hnfin : n - 51250 < 50 := by omega
                                                      simpa [Nat.sub_add_cancel hoff] using m1_w25 ⟨n - 51250, hnfin⟩
                                                    ·
                                                      by_cases h26 : n < 51350
                                                      · have hoff : 51300 ≤ n := by omega
                                                        have hnfin : n - 51300 < 50 := by omega
                                                        simpa [Nat.sub_add_cancel hoff] using m1_w26 ⟨n - 51300, hnfin⟩
                                                      ·
                                                        by_cases h27 : n < 51400
                                                        · have hoff : 51350 ≤ n := by omega
                                                          have hnfin : n - 51350 < 50 := by omega
                                                          simpa [Nat.sub_add_cancel hoff] using m1_w27 ⟨n - 51350, hnfin⟩
                                                        ·
                                                          by_cases h28 : n < 51450
                                                          · have hoff : 51400 ≤ n := by omega
                                                            have hnfin : n - 51400 < 50 := by omega
                                                            simpa [Nat.sub_add_cancel hoff] using m1_w28 ⟨n - 51400, hnfin⟩
                                                          ·
                                                            by_cases h29 : n < 51500
                                                            · have hoff : 51450 ≤ n := by omega
                                                              have hnfin : n - 51450 < 50 := by omega
                                                              simpa [Nat.sub_add_cancel hoff] using m1_w29 ⟨n - 51450, hnfin⟩
                                                            ·
                                                              by_cases h30 : n < 51550
                                                              · have hoff : 51500 ≤ n := by omega
                                                                have hnfin : n - 51500 < 50 := by omega
                                                                simpa [Nat.sub_add_cancel hoff] using m1_w30 ⟨n - 51500, hnfin⟩
                                                              ·
                                                                by_cases h31 : n < 51600
                                                                · have hoff : 51550 ≤ n := by omega
                                                                  have hnfin : n - 51550 < 50 := by omega
                                                                  simpa [Nat.sub_add_cancel hoff] using m1_w31 ⟨n - 51550, hnfin⟩
                                                                ·
                                                                  by_cases h32 : n < 51650
                                                                  · have hoff : 51600 ≤ n := by omega
                                                                    have hnfin : n - 51600 < 50 := by omega
                                                                    simpa [Nat.sub_add_cancel hoff] using m1_w32 ⟨n - 51600, hnfin⟩
                                                                  ·
                                                                    by_cases h33 : n < 51700
                                                                    · have hoff : 51650 ≤ n := by omega
                                                                      have hnfin : n - 51650 < 50 := by omega
                                                                      simpa [Nat.sub_add_cancel hoff] using m1_w33 ⟨n - 51650, hnfin⟩
                                                                    ·
                                                                      by_cases h34 : n < 51750
                                                                      · have hoff : 51700 ≤ n := by omega
                                                                        have hnfin : n - 51700 < 50 := by omega
                                                                        simpa [Nat.sub_add_cancel hoff] using m1_w34 ⟨n - 51700, hnfin⟩
                                                                      ·
                                                                        by_cases h35 : n < 51800
                                                                        · have hoff : 51750 ≤ n := by omega
                                                                          have hnfin : n - 51750 < 50 := by omega
                                                                          simpa [Nat.sub_add_cancel hoff] using m1_w35 ⟨n - 51750, hnfin⟩
                                                                        ·
                                                                          by_cases h36 : n < 51850
                                                                          · have hoff : 51800 ≤ n := by omega
                                                                            have hnfin : n - 51800 < 50 := by omega
                                                                            simpa [Nat.sub_add_cancel hoff] using m1_w36 ⟨n - 51800, hnfin⟩
                                                                          ·
                                                                            by_cases h37 : n < 51900
                                                                            · have hoff : 51850 ≤ n := by omega
                                                                              have hnfin : n - 51850 < 50 := by omega
                                                                              simpa [Nat.sub_add_cancel hoff] using m1_w37 ⟨n - 51850, hnfin⟩
                                                                            ·
                                                                              by_cases h38 : n < 51950
                                                                              · have hoff : 51900 ≤ n := by omega
                                                                                have hnfin : n - 51900 < 50 := by omega
                                                                                simpa [Nat.sub_add_cancel hoff] using m1_w38 ⟨n - 51900, hnfin⟩
                                                                              ·
                                                                                by_cases h39 : n < 52000
                                                                                · have hoff : 51950 ≤ n := by omega
                                                                                  have hnfin : n - 51950 < 50 := by omega
                                                                                  simpa [Nat.sub_add_cancel hoff] using m1_w39 ⟨n - 51950, hnfin⟩
                                                                                ·
                                                                                  by_cases h40 : n < 52050
                                                                                  · have hoff : 52000 ≤ n := by omega
                                                                                    have hnfin : n - 52000 < 50 := by omega
                                                                                    simpa [Nat.sub_add_cancel hoff] using m1_w40 ⟨n - 52000, hnfin⟩
                                                                                  ·
                                                                                    by_cases h41 : n < 52100
                                                                                    · have hoff : 52050 ≤ n := by omega
                                                                                      have hnfin : n - 52050 < 50 := by omega
                                                                                      simpa [Nat.sub_add_cancel hoff] using m1_w41 ⟨n - 52050, hnfin⟩
                                                                                    ·
                                                                                      by_cases h42 : n < 52150
                                                                                      · have hoff : 52100 ≤ n := by omega
                                                                                        have hnfin : n - 52100 < 50 := by omega
                                                                                        simpa [Nat.sub_add_cancel hoff] using m1_w42 ⟨n - 52100, hnfin⟩
                                                                                      ·
                                                                                        by_cases h43 : n < 52200
                                                                                        · have hoff : 52150 ≤ n := by omega
                                                                                          have hnfin : n - 52150 < 50 := by omega
                                                                                          simpa [Nat.sub_add_cancel hoff] using m1_w43 ⟨n - 52150, hnfin⟩
                                                                                        ·
                                                                                          by_cases h44 : n < 52250
                                                                                          · have hoff : 52200 ≤ n := by omega
                                                                                            have hnfin : n - 52200 < 50 := by omega
                                                                                            simpa [Nat.sub_add_cancel hoff] using m1_w44 ⟨n - 52200, hnfin⟩
                                                                                          ·
                                                                                            by_cases h45 : n < 52300
                                                                                            · have hoff : 52250 ≤ n := by omega
                                                                                              have hnfin : n - 52250 < 50 := by omega
                                                                                              simpa [Nat.sub_add_cancel hoff] using m1_w45 ⟨n - 52250, hnfin⟩
                                                                                            ·
                                                                                              by_cases h46 : n < 52350
                                                                                              · have hoff : 52300 ≤ n := by omega
                                                                                                have hnfin : n - 52300 < 50 := by omega
                                                                                                simpa [Nat.sub_add_cancel hoff] using m1_w46 ⟨n - 52300, hnfin⟩
                                                                                              ·
                                                                                                by_cases h47 : n < 52400
                                                                                                · have hoff : 52350 ≤ n := by omega
                                                                                                  have hnfin : n - 52350 < 50 := by omega
                                                                                                  simpa [Nat.sub_add_cancel hoff] using m1_w47 ⟨n - 52350, hnfin⟩
                                                                                                ·
                                                                                                  by_cases h48 : n < 52450
                                                                                                  · have hoff : 52400 ≤ n := by omega
                                                                                                    have hnfin : n - 52400 < 50 := by omega
                                                                                                    simpa [Nat.sub_add_cancel hoff] using m1_w48 ⟨n - 52400, hnfin⟩
                                                                                                  ·
                                                                                                    by_cases h49 : n < 52500
                                                                                                    · have hoff : 52450 ≤ n := by omega
                                                                                                      have hnfin : n - 52450 < 50 := by omega
                                                                                                      simpa [Nat.sub_add_cancel hoff] using m1_w49 ⟨n - 52450, hnfin⟩
                                                                                                    ·
                                                                                                      omega
end IntMul.Kappa.R8.Bit.Oppbank.LandMonoFixA20


