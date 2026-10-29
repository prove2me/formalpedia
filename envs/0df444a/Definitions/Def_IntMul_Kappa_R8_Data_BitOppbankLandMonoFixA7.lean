-- Prove2me | Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankLandMonoFixA7
-- name    : IntMul_Kappa_R8_Data_BitOppbankLandMonoFixA7
-- status  : Definition
-- author  : @Ethan Cheung Wang
-- created : 2026-10-28T21:14:20.860591+00:00
-- url     : https://prove2.me/theorems/c0edb4b3-9d91-49de-b390-c8f8b5c5782e
-- title:
--   Dim-gated densSup land mono FixA pack 7
-- statement:
--   # Dim-gated densSup land (PndFix), pack A7
--
--   Range consolidators for $n\in[17500,20000)$.
-- source:
--   R8 BitOppbank PndFix

-- LandMonoFixA7: PUBLIC dim-gated land + range consolidators (PndFix)
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
namespace IntMul.Kappa.R8.Bit.Oppbank.LandMonoFixA7
def arg0 (n : ℕ) : ℕ := Nat.land (argF n) 65535
def arg1 (n : ℕ) : ℕ := Nat.shiftRight (argF n) 16
theorem m0_w0 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 17500))) (dimF (n.val + 17500)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 17500))) (densSupG (n.val + 17500))) (densSupG (arg0 (n.val + 17500)))) = true := by decide
theorem m1_w0 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 17500))) (dimF (n.val + 17500)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 17500))) (densSupG (n.val + 17500))) (densSupG (arg1 (n.val + 17500)))) = true := by decide
theorem m0_w1 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 17550))) (dimF (n.val + 17550)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 17550))) (densSupG (n.val + 17550))) (densSupG (arg0 (n.val + 17550)))) = true := by decide
theorem m1_w1 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 17550))) (dimF (n.val + 17550)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 17550))) (densSupG (n.val + 17550))) (densSupG (arg1 (n.val + 17550)))) = true := by decide
theorem m0_w2 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 17600))) (dimF (n.val + 17600)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 17600))) (densSupG (n.val + 17600))) (densSupG (arg0 (n.val + 17600)))) = true := by decide
theorem m1_w2 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 17600))) (dimF (n.val + 17600)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 17600))) (densSupG (n.val + 17600))) (densSupG (arg1 (n.val + 17600)))) = true := by decide
theorem m0_w3 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 17650))) (dimF (n.val + 17650)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 17650))) (densSupG (n.val + 17650))) (densSupG (arg0 (n.val + 17650)))) = true := by decide
theorem m1_w3 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 17650))) (dimF (n.val + 17650)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 17650))) (densSupG (n.val + 17650))) (densSupG (arg1 (n.val + 17650)))) = true := by decide
theorem m0_w4 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 17700))) (dimF (n.val + 17700)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 17700))) (densSupG (n.val + 17700))) (densSupG (arg0 (n.val + 17700)))) = true := by decide
theorem m1_w4 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 17700))) (dimF (n.val + 17700)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 17700))) (densSupG (n.val + 17700))) (densSupG (arg1 (n.val + 17700)))) = true := by decide
theorem m0_w5 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 17750))) (dimF (n.val + 17750)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 17750))) (densSupG (n.val + 17750))) (densSupG (arg0 (n.val + 17750)))) = true := by decide
theorem m1_w5 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 17750))) (dimF (n.val + 17750)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 17750))) (densSupG (n.val + 17750))) (densSupG (arg1 (n.val + 17750)))) = true := by decide
theorem m0_w6 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 17800))) (dimF (n.val + 17800)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 17800))) (densSupG (n.val + 17800))) (densSupG (arg0 (n.val + 17800)))) = true := by decide
theorem m1_w6 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 17800))) (dimF (n.val + 17800)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 17800))) (densSupG (n.val + 17800))) (densSupG (arg1 (n.val + 17800)))) = true := by decide
theorem m0_w7 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 17850))) (dimF (n.val + 17850)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 17850))) (densSupG (n.val + 17850))) (densSupG (arg0 (n.val + 17850)))) = true := by decide
theorem m1_w7 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 17850))) (dimF (n.val + 17850)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 17850))) (densSupG (n.val + 17850))) (densSupG (arg1 (n.val + 17850)))) = true := by decide
theorem m0_w8 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 17900))) (dimF (n.val + 17900)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 17900))) (densSupG (n.val + 17900))) (densSupG (arg0 (n.val + 17900)))) = true := by decide
theorem m1_w8 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 17900))) (dimF (n.val + 17900)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 17900))) (densSupG (n.val + 17900))) (densSupG (arg1 (n.val + 17900)))) = true := by decide
theorem m0_w9 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 17950))) (dimF (n.val + 17950)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 17950))) (densSupG (n.val + 17950))) (densSupG (arg0 (n.val + 17950)))) = true := by decide
theorem m1_w9 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 17950))) (dimF (n.val + 17950)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 17950))) (densSupG (n.val + 17950))) (densSupG (arg1 (n.val + 17950)))) = true := by decide
theorem m0_w10 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 18000))) (dimF (n.val + 18000)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 18000))) (densSupG (n.val + 18000))) (densSupG (arg0 (n.val + 18000)))) = true := by decide
theorem m1_w10 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 18000))) (dimF (n.val + 18000)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 18000))) (densSupG (n.val + 18000))) (densSupG (arg1 (n.val + 18000)))) = true := by decide
theorem m0_w11 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 18050))) (dimF (n.val + 18050)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 18050))) (densSupG (n.val + 18050))) (densSupG (arg0 (n.val + 18050)))) = true := by decide
theorem m1_w11 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 18050))) (dimF (n.val + 18050)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 18050))) (densSupG (n.val + 18050))) (densSupG (arg1 (n.val + 18050)))) = true := by decide
theorem m0_w12 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 18100))) (dimF (n.val + 18100)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 18100))) (densSupG (n.val + 18100))) (densSupG (arg0 (n.val + 18100)))) = true := by decide
theorem m1_w12 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 18100))) (dimF (n.val + 18100)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 18100))) (densSupG (n.val + 18100))) (densSupG (arg1 (n.val + 18100)))) = true := by decide
theorem m0_w13 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 18150))) (dimF (n.val + 18150)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 18150))) (densSupG (n.val + 18150))) (densSupG (arg0 (n.val + 18150)))) = true := by decide
theorem m1_w13 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 18150))) (dimF (n.val + 18150)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 18150))) (densSupG (n.val + 18150))) (densSupG (arg1 (n.val + 18150)))) = true := by decide
theorem m0_w14 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 18200))) (dimF (n.val + 18200)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 18200))) (densSupG (n.val + 18200))) (densSupG (arg0 (n.val + 18200)))) = true := by decide
theorem m1_w14 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 18200))) (dimF (n.val + 18200)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 18200))) (densSupG (n.val + 18200))) (densSupG (arg1 (n.val + 18200)))) = true := by decide
theorem m0_w15 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 18250))) (dimF (n.val + 18250)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 18250))) (densSupG (n.val + 18250))) (densSupG (arg0 (n.val + 18250)))) = true := by decide
theorem m1_w15 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 18250))) (dimF (n.val + 18250)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 18250))) (densSupG (n.val + 18250))) (densSupG (arg1 (n.val + 18250)))) = true := by decide
theorem m0_w16 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 18300))) (dimF (n.val + 18300)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 18300))) (densSupG (n.val + 18300))) (densSupG (arg0 (n.val + 18300)))) = true := by decide
theorem m1_w16 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 18300))) (dimF (n.val + 18300)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 18300))) (densSupG (n.val + 18300))) (densSupG (arg1 (n.val + 18300)))) = true := by decide
theorem m0_w17 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 18350))) (dimF (n.val + 18350)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 18350))) (densSupG (n.val + 18350))) (densSupG (arg0 (n.val + 18350)))) = true := by decide
theorem m1_w17 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 18350))) (dimF (n.val + 18350)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 18350))) (densSupG (n.val + 18350))) (densSupG (arg1 (n.val + 18350)))) = true := by decide
theorem m0_w18 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 18400))) (dimF (n.val + 18400)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 18400))) (densSupG (n.val + 18400))) (densSupG (arg0 (n.val + 18400)))) = true := by decide
theorem m1_w18 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 18400))) (dimF (n.val + 18400)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 18400))) (densSupG (n.val + 18400))) (densSupG (arg1 (n.val + 18400)))) = true := by decide
theorem m0_w19 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 18450))) (dimF (n.val + 18450)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 18450))) (densSupG (n.val + 18450))) (densSupG (arg0 (n.val + 18450)))) = true := by decide
theorem m1_w19 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 18450))) (dimF (n.val + 18450)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 18450))) (densSupG (n.val + 18450))) (densSupG (arg1 (n.val + 18450)))) = true := by decide
theorem m0_w20 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 18500))) (dimF (n.val + 18500)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 18500))) (densSupG (n.val + 18500))) (densSupG (arg0 (n.val + 18500)))) = true := by decide
theorem m1_w20 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 18500))) (dimF (n.val + 18500)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 18500))) (densSupG (n.val + 18500))) (densSupG (arg1 (n.val + 18500)))) = true := by decide
theorem m0_w21 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 18550))) (dimF (n.val + 18550)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 18550))) (densSupG (n.val + 18550))) (densSupG (arg0 (n.val + 18550)))) = true := by decide
theorem m1_w21 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 18550))) (dimF (n.val + 18550)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 18550))) (densSupG (n.val + 18550))) (densSupG (arg1 (n.val + 18550)))) = true := by decide
theorem m0_w22 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 18600))) (dimF (n.val + 18600)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 18600))) (densSupG (n.val + 18600))) (densSupG (arg0 (n.val + 18600)))) = true := by decide
theorem m1_w22 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 18600))) (dimF (n.val + 18600)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 18600))) (densSupG (n.val + 18600))) (densSupG (arg1 (n.val + 18600)))) = true := by decide
theorem m0_w23 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 18650))) (dimF (n.val + 18650)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 18650))) (densSupG (n.val + 18650))) (densSupG (arg0 (n.val + 18650)))) = true := by decide
theorem m1_w23 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 18650))) (dimF (n.val + 18650)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 18650))) (densSupG (n.val + 18650))) (densSupG (arg1 (n.val + 18650)))) = true := by decide
theorem m0_w24 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 18700))) (dimF (n.val + 18700)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 18700))) (densSupG (n.val + 18700))) (densSupG (arg0 (n.val + 18700)))) = true := by decide
theorem m1_w24 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 18700))) (dimF (n.val + 18700)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 18700))) (densSupG (n.val + 18700))) (densSupG (arg1 (n.val + 18700)))) = true := by decide
theorem m0_w25 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 18750))) (dimF (n.val + 18750)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 18750))) (densSupG (n.val + 18750))) (densSupG (arg0 (n.val + 18750)))) = true := by decide
theorem m1_w25 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 18750))) (dimF (n.val + 18750)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 18750))) (densSupG (n.val + 18750))) (densSupG (arg1 (n.val + 18750)))) = true := by decide
theorem m0_w26 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 18800))) (dimF (n.val + 18800)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 18800))) (densSupG (n.val + 18800))) (densSupG (arg0 (n.val + 18800)))) = true := by decide
theorem m1_w26 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 18800))) (dimF (n.val + 18800)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 18800))) (densSupG (n.val + 18800))) (densSupG (arg1 (n.val + 18800)))) = true := by decide
theorem m0_w27 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 18850))) (dimF (n.val + 18850)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 18850))) (densSupG (n.val + 18850))) (densSupG (arg0 (n.val + 18850)))) = true := by decide
theorem m1_w27 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 18850))) (dimF (n.val + 18850)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 18850))) (densSupG (n.val + 18850))) (densSupG (arg1 (n.val + 18850)))) = true := by decide
theorem m0_w28 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 18900))) (dimF (n.val + 18900)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 18900))) (densSupG (n.val + 18900))) (densSupG (arg0 (n.val + 18900)))) = true := by decide
theorem m1_w28 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 18900))) (dimF (n.val + 18900)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 18900))) (densSupG (n.val + 18900))) (densSupG (arg1 (n.val + 18900)))) = true := by decide
theorem m0_w29 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 18950))) (dimF (n.val + 18950)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 18950))) (densSupG (n.val + 18950))) (densSupG (arg0 (n.val + 18950)))) = true := by decide
theorem m1_w29 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 18950))) (dimF (n.val + 18950)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 18950))) (densSupG (n.val + 18950))) (densSupG (arg1 (n.val + 18950)))) = true := by decide
theorem m0_w30 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 19000))) (dimF (n.val + 19000)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 19000))) (densSupG (n.val + 19000))) (densSupG (arg0 (n.val + 19000)))) = true := by decide
theorem m1_w30 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 19000))) (dimF (n.val + 19000)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 19000))) (densSupG (n.val + 19000))) (densSupG (arg1 (n.val + 19000)))) = true := by decide
theorem m0_w31 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 19050))) (dimF (n.val + 19050)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 19050))) (densSupG (n.val + 19050))) (densSupG (arg0 (n.val + 19050)))) = true := by decide
theorem m1_w31 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 19050))) (dimF (n.val + 19050)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 19050))) (densSupG (n.val + 19050))) (densSupG (arg1 (n.val + 19050)))) = true := by decide
theorem m0_w32 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 19100))) (dimF (n.val + 19100)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 19100))) (densSupG (n.val + 19100))) (densSupG (arg0 (n.val + 19100)))) = true := by decide
theorem m1_w32 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 19100))) (dimF (n.val + 19100)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 19100))) (densSupG (n.val + 19100))) (densSupG (arg1 (n.val + 19100)))) = true := by decide
theorem m0_w33 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 19150))) (dimF (n.val + 19150)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 19150))) (densSupG (n.val + 19150))) (densSupG (arg0 (n.val + 19150)))) = true := by decide
theorem m1_w33 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 19150))) (dimF (n.val + 19150)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 19150))) (densSupG (n.val + 19150))) (densSupG (arg1 (n.val + 19150)))) = true := by decide
theorem m0_w34 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 19200))) (dimF (n.val + 19200)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 19200))) (densSupG (n.val + 19200))) (densSupG (arg0 (n.val + 19200)))) = true := by decide
theorem m1_w34 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 19200))) (dimF (n.val + 19200)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 19200))) (densSupG (n.val + 19200))) (densSupG (arg1 (n.val + 19200)))) = true := by decide
theorem m0_w35 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 19250))) (dimF (n.val + 19250)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 19250))) (densSupG (n.val + 19250))) (densSupG (arg0 (n.val + 19250)))) = true := by decide
theorem m1_w35 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 19250))) (dimF (n.val + 19250)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 19250))) (densSupG (n.val + 19250))) (densSupG (arg1 (n.val + 19250)))) = true := by decide
theorem m0_w36 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 19300))) (dimF (n.val + 19300)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 19300))) (densSupG (n.val + 19300))) (densSupG (arg0 (n.val + 19300)))) = true := by decide
theorem m1_w36 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 19300))) (dimF (n.val + 19300)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 19300))) (densSupG (n.val + 19300))) (densSupG (arg1 (n.val + 19300)))) = true := by decide
theorem m0_w37 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 19350))) (dimF (n.val + 19350)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 19350))) (densSupG (n.val + 19350))) (densSupG (arg0 (n.val + 19350)))) = true := by decide
theorem m1_w37 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 19350))) (dimF (n.val + 19350)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 19350))) (densSupG (n.val + 19350))) (densSupG (arg1 (n.val + 19350)))) = true := by decide
theorem m0_w38 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 19400))) (dimF (n.val + 19400)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 19400))) (densSupG (n.val + 19400))) (densSupG (arg0 (n.val + 19400)))) = true := by decide
theorem m1_w38 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 19400))) (dimF (n.val + 19400)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 19400))) (densSupG (n.val + 19400))) (densSupG (arg1 (n.val + 19400)))) = true := by decide
theorem m0_w39 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 19450))) (dimF (n.val + 19450)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 19450))) (densSupG (n.val + 19450))) (densSupG (arg0 (n.val + 19450)))) = true := by decide
theorem m1_w39 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 19450))) (dimF (n.val + 19450)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 19450))) (densSupG (n.val + 19450))) (densSupG (arg1 (n.val + 19450)))) = true := by decide
theorem m0_w40 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 19500))) (dimF (n.val + 19500)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 19500))) (densSupG (n.val + 19500))) (densSupG (arg0 (n.val + 19500)))) = true := by decide
theorem m1_w40 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 19500))) (dimF (n.val + 19500)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 19500))) (densSupG (n.val + 19500))) (densSupG (arg1 (n.val + 19500)))) = true := by decide
theorem m0_w41 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 19550))) (dimF (n.val + 19550)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 19550))) (densSupG (n.val + 19550))) (densSupG (arg0 (n.val + 19550)))) = true := by decide
theorem m1_w41 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 19550))) (dimF (n.val + 19550)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 19550))) (densSupG (n.val + 19550))) (densSupG (arg1 (n.val + 19550)))) = true := by decide
theorem m0_w42 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 19600))) (dimF (n.val + 19600)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 19600))) (densSupG (n.val + 19600))) (densSupG (arg0 (n.val + 19600)))) = true := by decide
theorem m1_w42 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 19600))) (dimF (n.val + 19600)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 19600))) (densSupG (n.val + 19600))) (densSupG (arg1 (n.val + 19600)))) = true := by decide
theorem m0_w43 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 19650))) (dimF (n.val + 19650)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 19650))) (densSupG (n.val + 19650))) (densSupG (arg0 (n.val + 19650)))) = true := by decide
theorem m1_w43 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 19650))) (dimF (n.val + 19650)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 19650))) (densSupG (n.val + 19650))) (densSupG (arg1 (n.val + 19650)))) = true := by decide
theorem m0_w44 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 19700))) (dimF (n.val + 19700)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 19700))) (densSupG (n.val + 19700))) (densSupG (arg0 (n.val + 19700)))) = true := by decide
theorem m1_w44 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 19700))) (dimF (n.val + 19700)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 19700))) (densSupG (n.val + 19700))) (densSupG (arg1 (n.val + 19700)))) = true := by decide
theorem m0_w45 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 19750))) (dimF (n.val + 19750)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 19750))) (densSupG (n.val + 19750))) (densSupG (arg0 (n.val + 19750)))) = true := by decide
theorem m1_w45 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 19750))) (dimF (n.val + 19750)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 19750))) (densSupG (n.val + 19750))) (densSupG (arg1 (n.val + 19750)))) = true := by decide
theorem m0_w46 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 19800))) (dimF (n.val + 19800)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 19800))) (densSupG (n.val + 19800))) (densSupG (arg0 (n.val + 19800)))) = true := by decide
theorem m1_w46 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 19800))) (dimF (n.val + 19800)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 19800))) (densSupG (n.val + 19800))) (densSupG (arg1 (n.val + 19800)))) = true := by decide
theorem m0_w47 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 19850))) (dimF (n.val + 19850)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 19850))) (densSupG (n.val + 19850))) (densSupG (arg0 (n.val + 19850)))) = true := by decide
theorem m1_w47 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 19850))) (dimF (n.val + 19850)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 19850))) (densSupG (n.val + 19850))) (densSupG (arg1 (n.val + 19850)))) = true := by decide
theorem m0_w48 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 19900))) (dimF (n.val + 19900)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 19900))) (densSupG (n.val + 19900))) (densSupG (arg0 (n.val + 19900)))) = true := by decide
theorem m1_w48 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 19900))) (dimF (n.val + 19900)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 19900))) (densSupG (n.val + 19900))) (densSupG (arg1 (n.val + 19900)))) = true := by decide
theorem m0_w49 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 19950))) (dimF (n.val + 19950)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 19950))) (densSupG (n.val + 19950))) (densSupG (arg0 (n.val + 19950)))) = true := by decide
theorem m1_w49 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 19950))) (dimF (n.val + 19950)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 19950))) (densSupG (n.val + 19950))) (densSupG (arg1 (n.val + 19950)))) = true := by decide
theorem land0_range (n : ℕ) (hn0 : 17500 ≤ n) (hn1 : n < 20000) :
    (!Nat.blt (dimF (arg0 n)) (dimF n) ||
      Nat.beq (Nat.land (densSupG (arg0 n)) (densSupG n)) (densSupG (arg0 n))) = true := by
  by_cases h0 : n < 17550
  · have hoff : 17500 ≤ n := by omega
    have hnfin : n - 17500 < 50 := by omega
    simpa [Nat.sub_add_cancel hoff] using m0_w0 ⟨n - 17500, hnfin⟩
  ·
    by_cases h1 : n < 17600
    · have hoff : 17550 ≤ n := by omega
      have hnfin : n - 17550 < 50 := by omega
      simpa [Nat.sub_add_cancel hoff] using m0_w1 ⟨n - 17550, hnfin⟩
    ·
      by_cases h2 : n < 17650
      · have hoff : 17600 ≤ n := by omega
        have hnfin : n - 17600 < 50 := by omega
        simpa [Nat.sub_add_cancel hoff] using m0_w2 ⟨n - 17600, hnfin⟩
      ·
        by_cases h3 : n < 17700
        · have hoff : 17650 ≤ n := by omega
          have hnfin : n - 17650 < 50 := by omega
          simpa [Nat.sub_add_cancel hoff] using m0_w3 ⟨n - 17650, hnfin⟩
        ·
          by_cases h4 : n < 17750
          · have hoff : 17700 ≤ n := by omega
            have hnfin : n - 17700 < 50 := by omega
            simpa [Nat.sub_add_cancel hoff] using m0_w4 ⟨n - 17700, hnfin⟩
          ·
            by_cases h5 : n < 17800
            · have hoff : 17750 ≤ n := by omega
              have hnfin : n - 17750 < 50 := by omega
              simpa [Nat.sub_add_cancel hoff] using m0_w5 ⟨n - 17750, hnfin⟩
            ·
              by_cases h6 : n < 17850
              · have hoff : 17800 ≤ n := by omega
                have hnfin : n - 17800 < 50 := by omega
                simpa [Nat.sub_add_cancel hoff] using m0_w6 ⟨n - 17800, hnfin⟩
              ·
                by_cases h7 : n < 17900
                · have hoff : 17850 ≤ n := by omega
                  have hnfin : n - 17850 < 50 := by omega
                  simpa [Nat.sub_add_cancel hoff] using m0_w7 ⟨n - 17850, hnfin⟩
                ·
                  by_cases h8 : n < 17950
                  · have hoff : 17900 ≤ n := by omega
                    have hnfin : n - 17900 < 50 := by omega
                    simpa [Nat.sub_add_cancel hoff] using m0_w8 ⟨n - 17900, hnfin⟩
                  ·
                    by_cases h9 : n < 18000
                    · have hoff : 17950 ≤ n := by omega
                      have hnfin : n - 17950 < 50 := by omega
                      simpa [Nat.sub_add_cancel hoff] using m0_w9 ⟨n - 17950, hnfin⟩
                    ·
                      by_cases h10 : n < 18050
                      · have hoff : 18000 ≤ n := by omega
                        have hnfin : n - 18000 < 50 := by omega
                        simpa [Nat.sub_add_cancel hoff] using m0_w10 ⟨n - 18000, hnfin⟩
                      ·
                        by_cases h11 : n < 18100
                        · have hoff : 18050 ≤ n := by omega
                          have hnfin : n - 18050 < 50 := by omega
                          simpa [Nat.sub_add_cancel hoff] using m0_w11 ⟨n - 18050, hnfin⟩
                        ·
                          by_cases h12 : n < 18150
                          · have hoff : 18100 ≤ n := by omega
                            have hnfin : n - 18100 < 50 := by omega
                            simpa [Nat.sub_add_cancel hoff] using m0_w12 ⟨n - 18100, hnfin⟩
                          ·
                            by_cases h13 : n < 18200
                            · have hoff : 18150 ≤ n := by omega
                              have hnfin : n - 18150 < 50 := by omega
                              simpa [Nat.sub_add_cancel hoff] using m0_w13 ⟨n - 18150, hnfin⟩
                            ·
                              by_cases h14 : n < 18250
                              · have hoff : 18200 ≤ n := by omega
                                have hnfin : n - 18200 < 50 := by omega
                                simpa [Nat.sub_add_cancel hoff] using m0_w14 ⟨n - 18200, hnfin⟩
                              ·
                                by_cases h15 : n < 18300
                                · have hoff : 18250 ≤ n := by omega
                                  have hnfin : n - 18250 < 50 := by omega
                                  simpa [Nat.sub_add_cancel hoff] using m0_w15 ⟨n - 18250, hnfin⟩
                                ·
                                  by_cases h16 : n < 18350
                                  · have hoff : 18300 ≤ n := by omega
                                    have hnfin : n - 18300 < 50 := by omega
                                    simpa [Nat.sub_add_cancel hoff] using m0_w16 ⟨n - 18300, hnfin⟩
                                  ·
                                    by_cases h17 : n < 18400
                                    · have hoff : 18350 ≤ n := by omega
                                      have hnfin : n - 18350 < 50 := by omega
                                      simpa [Nat.sub_add_cancel hoff] using m0_w17 ⟨n - 18350, hnfin⟩
                                    ·
                                      by_cases h18 : n < 18450
                                      · have hoff : 18400 ≤ n := by omega
                                        have hnfin : n - 18400 < 50 := by omega
                                        simpa [Nat.sub_add_cancel hoff] using m0_w18 ⟨n - 18400, hnfin⟩
                                      ·
                                        by_cases h19 : n < 18500
                                        · have hoff : 18450 ≤ n := by omega
                                          have hnfin : n - 18450 < 50 := by omega
                                          simpa [Nat.sub_add_cancel hoff] using m0_w19 ⟨n - 18450, hnfin⟩
                                        ·
                                          by_cases h20 : n < 18550
                                          · have hoff : 18500 ≤ n := by omega
                                            have hnfin : n - 18500 < 50 := by omega
                                            simpa [Nat.sub_add_cancel hoff] using m0_w20 ⟨n - 18500, hnfin⟩
                                          ·
                                            by_cases h21 : n < 18600
                                            · have hoff : 18550 ≤ n := by omega
                                              have hnfin : n - 18550 < 50 := by omega
                                              simpa [Nat.sub_add_cancel hoff] using m0_w21 ⟨n - 18550, hnfin⟩
                                            ·
                                              by_cases h22 : n < 18650
                                              · have hoff : 18600 ≤ n := by omega
                                                have hnfin : n - 18600 < 50 := by omega
                                                simpa [Nat.sub_add_cancel hoff] using m0_w22 ⟨n - 18600, hnfin⟩
                                              ·
                                                by_cases h23 : n < 18700
                                                · have hoff : 18650 ≤ n := by omega
                                                  have hnfin : n - 18650 < 50 := by omega
                                                  simpa [Nat.sub_add_cancel hoff] using m0_w23 ⟨n - 18650, hnfin⟩
                                                ·
                                                  by_cases h24 : n < 18750
                                                  · have hoff : 18700 ≤ n := by omega
                                                    have hnfin : n - 18700 < 50 := by omega
                                                    simpa [Nat.sub_add_cancel hoff] using m0_w24 ⟨n - 18700, hnfin⟩
                                                  ·
                                                    by_cases h25 : n < 18800
                                                    · have hoff : 18750 ≤ n := by omega
                                                      have hnfin : n - 18750 < 50 := by omega
                                                      simpa [Nat.sub_add_cancel hoff] using m0_w25 ⟨n - 18750, hnfin⟩
                                                    ·
                                                      by_cases h26 : n < 18850
                                                      · have hoff : 18800 ≤ n := by omega
                                                        have hnfin : n - 18800 < 50 := by omega
                                                        simpa [Nat.sub_add_cancel hoff] using m0_w26 ⟨n - 18800, hnfin⟩
                                                      ·
                                                        by_cases h27 : n < 18900
                                                        · have hoff : 18850 ≤ n := by omega
                                                          have hnfin : n - 18850 < 50 := by omega
                                                          simpa [Nat.sub_add_cancel hoff] using m0_w27 ⟨n - 18850, hnfin⟩
                                                        ·
                                                          by_cases h28 : n < 18950
                                                          · have hoff : 18900 ≤ n := by omega
                                                            have hnfin : n - 18900 < 50 := by omega
                                                            simpa [Nat.sub_add_cancel hoff] using m0_w28 ⟨n - 18900, hnfin⟩
                                                          ·
                                                            by_cases h29 : n < 19000
                                                            · have hoff : 18950 ≤ n := by omega
                                                              have hnfin : n - 18950 < 50 := by omega
                                                              simpa [Nat.sub_add_cancel hoff] using m0_w29 ⟨n - 18950, hnfin⟩
                                                            ·
                                                              by_cases h30 : n < 19050
                                                              · have hoff : 19000 ≤ n := by omega
                                                                have hnfin : n - 19000 < 50 := by omega
                                                                simpa [Nat.sub_add_cancel hoff] using m0_w30 ⟨n - 19000, hnfin⟩
                                                              ·
                                                                by_cases h31 : n < 19100
                                                                · have hoff : 19050 ≤ n := by omega
                                                                  have hnfin : n - 19050 < 50 := by omega
                                                                  simpa [Nat.sub_add_cancel hoff] using m0_w31 ⟨n - 19050, hnfin⟩
                                                                ·
                                                                  by_cases h32 : n < 19150
                                                                  · have hoff : 19100 ≤ n := by omega
                                                                    have hnfin : n - 19100 < 50 := by omega
                                                                    simpa [Nat.sub_add_cancel hoff] using m0_w32 ⟨n - 19100, hnfin⟩
                                                                  ·
                                                                    by_cases h33 : n < 19200
                                                                    · have hoff : 19150 ≤ n := by omega
                                                                      have hnfin : n - 19150 < 50 := by omega
                                                                      simpa [Nat.sub_add_cancel hoff] using m0_w33 ⟨n - 19150, hnfin⟩
                                                                    ·
                                                                      by_cases h34 : n < 19250
                                                                      · have hoff : 19200 ≤ n := by omega
                                                                        have hnfin : n - 19200 < 50 := by omega
                                                                        simpa [Nat.sub_add_cancel hoff] using m0_w34 ⟨n - 19200, hnfin⟩
                                                                      ·
                                                                        by_cases h35 : n < 19300
                                                                        · have hoff : 19250 ≤ n := by omega
                                                                          have hnfin : n - 19250 < 50 := by omega
                                                                          simpa [Nat.sub_add_cancel hoff] using m0_w35 ⟨n - 19250, hnfin⟩
                                                                        ·
                                                                          by_cases h36 : n < 19350
                                                                          · have hoff : 19300 ≤ n := by omega
                                                                            have hnfin : n - 19300 < 50 := by omega
                                                                            simpa [Nat.sub_add_cancel hoff] using m0_w36 ⟨n - 19300, hnfin⟩
                                                                          ·
                                                                            by_cases h37 : n < 19400
                                                                            · have hoff : 19350 ≤ n := by omega
                                                                              have hnfin : n - 19350 < 50 := by omega
                                                                              simpa [Nat.sub_add_cancel hoff] using m0_w37 ⟨n - 19350, hnfin⟩
                                                                            ·
                                                                              by_cases h38 : n < 19450
                                                                              · have hoff : 19400 ≤ n := by omega
                                                                                have hnfin : n - 19400 < 50 := by omega
                                                                                simpa [Nat.sub_add_cancel hoff] using m0_w38 ⟨n - 19400, hnfin⟩
                                                                              ·
                                                                                by_cases h39 : n < 19500
                                                                                · have hoff : 19450 ≤ n := by omega
                                                                                  have hnfin : n - 19450 < 50 := by omega
                                                                                  simpa [Nat.sub_add_cancel hoff] using m0_w39 ⟨n - 19450, hnfin⟩
                                                                                ·
                                                                                  by_cases h40 : n < 19550
                                                                                  · have hoff : 19500 ≤ n := by omega
                                                                                    have hnfin : n - 19500 < 50 := by omega
                                                                                    simpa [Nat.sub_add_cancel hoff] using m0_w40 ⟨n - 19500, hnfin⟩
                                                                                  ·
                                                                                    by_cases h41 : n < 19600
                                                                                    · have hoff : 19550 ≤ n := by omega
                                                                                      have hnfin : n - 19550 < 50 := by omega
                                                                                      simpa [Nat.sub_add_cancel hoff] using m0_w41 ⟨n - 19550, hnfin⟩
                                                                                    ·
                                                                                      by_cases h42 : n < 19650
                                                                                      · have hoff : 19600 ≤ n := by omega
                                                                                        have hnfin : n - 19600 < 50 := by omega
                                                                                        simpa [Nat.sub_add_cancel hoff] using m0_w42 ⟨n - 19600, hnfin⟩
                                                                                      ·
                                                                                        by_cases h43 : n < 19700
                                                                                        · have hoff : 19650 ≤ n := by omega
                                                                                          have hnfin : n - 19650 < 50 := by omega
                                                                                          simpa [Nat.sub_add_cancel hoff] using m0_w43 ⟨n - 19650, hnfin⟩
                                                                                        ·
                                                                                          by_cases h44 : n < 19750
                                                                                          · have hoff : 19700 ≤ n := by omega
                                                                                            have hnfin : n - 19700 < 50 := by omega
                                                                                            simpa [Nat.sub_add_cancel hoff] using m0_w44 ⟨n - 19700, hnfin⟩
                                                                                          ·
                                                                                            by_cases h45 : n < 19800
                                                                                            · have hoff : 19750 ≤ n := by omega
                                                                                              have hnfin : n - 19750 < 50 := by omega
                                                                                              simpa [Nat.sub_add_cancel hoff] using m0_w45 ⟨n - 19750, hnfin⟩
                                                                                            ·
                                                                                              by_cases h46 : n < 19850
                                                                                              · have hoff : 19800 ≤ n := by omega
                                                                                                have hnfin : n - 19800 < 50 := by omega
                                                                                                simpa [Nat.sub_add_cancel hoff] using m0_w46 ⟨n - 19800, hnfin⟩
                                                                                              ·
                                                                                                by_cases h47 : n < 19900
                                                                                                · have hoff : 19850 ≤ n := by omega
                                                                                                  have hnfin : n - 19850 < 50 := by omega
                                                                                                  simpa [Nat.sub_add_cancel hoff] using m0_w47 ⟨n - 19850, hnfin⟩
                                                                                                ·
                                                                                                  by_cases h48 : n < 19950
                                                                                                  · have hoff : 19900 ≤ n := by omega
                                                                                                    have hnfin : n - 19900 < 50 := by omega
                                                                                                    simpa [Nat.sub_add_cancel hoff] using m0_w48 ⟨n - 19900, hnfin⟩
                                                                                                  ·
                                                                                                    by_cases h49 : n < 20000
                                                                                                    · have hoff : 19950 ≤ n := by omega
                                                                                                      have hnfin : n - 19950 < 50 := by omega
                                                                                                      simpa [Nat.sub_add_cancel hoff] using m0_w49 ⟨n - 19950, hnfin⟩
                                                                                                    ·
                                                                                                      omega
theorem land1_range (n : ℕ) (hn0 : 17500 ≤ n) (hn1 : n < 20000) :
    (!Nat.blt (dimF (arg1 n)) (dimF n) ||
      Nat.beq (Nat.land (densSupG (arg1 n)) (densSupG n)) (densSupG (arg1 n))) = true := by
  by_cases h0 : n < 17550
  · have hoff : 17500 ≤ n := by omega
    have hnfin : n - 17500 < 50 := by omega
    simpa [Nat.sub_add_cancel hoff] using m1_w0 ⟨n - 17500, hnfin⟩
  ·
    by_cases h1 : n < 17600
    · have hoff : 17550 ≤ n := by omega
      have hnfin : n - 17550 < 50 := by omega
      simpa [Nat.sub_add_cancel hoff] using m1_w1 ⟨n - 17550, hnfin⟩
    ·
      by_cases h2 : n < 17650
      · have hoff : 17600 ≤ n := by omega
        have hnfin : n - 17600 < 50 := by omega
        simpa [Nat.sub_add_cancel hoff] using m1_w2 ⟨n - 17600, hnfin⟩
      ·
        by_cases h3 : n < 17700
        · have hoff : 17650 ≤ n := by omega
          have hnfin : n - 17650 < 50 := by omega
          simpa [Nat.sub_add_cancel hoff] using m1_w3 ⟨n - 17650, hnfin⟩
        ·
          by_cases h4 : n < 17750
          · have hoff : 17700 ≤ n := by omega
            have hnfin : n - 17700 < 50 := by omega
            simpa [Nat.sub_add_cancel hoff] using m1_w4 ⟨n - 17700, hnfin⟩
          ·
            by_cases h5 : n < 17800
            · have hoff : 17750 ≤ n := by omega
              have hnfin : n - 17750 < 50 := by omega
              simpa [Nat.sub_add_cancel hoff] using m1_w5 ⟨n - 17750, hnfin⟩
            ·
              by_cases h6 : n < 17850
              · have hoff : 17800 ≤ n := by omega
                have hnfin : n - 17800 < 50 := by omega
                simpa [Nat.sub_add_cancel hoff] using m1_w6 ⟨n - 17800, hnfin⟩
              ·
                by_cases h7 : n < 17900
                · have hoff : 17850 ≤ n := by omega
                  have hnfin : n - 17850 < 50 := by omega
                  simpa [Nat.sub_add_cancel hoff] using m1_w7 ⟨n - 17850, hnfin⟩
                ·
                  by_cases h8 : n < 17950
                  · have hoff : 17900 ≤ n := by omega
                    have hnfin : n - 17900 < 50 := by omega
                    simpa [Nat.sub_add_cancel hoff] using m1_w8 ⟨n - 17900, hnfin⟩
                  ·
                    by_cases h9 : n < 18000
                    · have hoff : 17950 ≤ n := by omega
                      have hnfin : n - 17950 < 50 := by omega
                      simpa [Nat.sub_add_cancel hoff] using m1_w9 ⟨n - 17950, hnfin⟩
                    ·
                      by_cases h10 : n < 18050
                      · have hoff : 18000 ≤ n := by omega
                        have hnfin : n - 18000 < 50 := by omega
                        simpa [Nat.sub_add_cancel hoff] using m1_w10 ⟨n - 18000, hnfin⟩
                      ·
                        by_cases h11 : n < 18100
                        · have hoff : 18050 ≤ n := by omega
                          have hnfin : n - 18050 < 50 := by omega
                          simpa [Nat.sub_add_cancel hoff] using m1_w11 ⟨n - 18050, hnfin⟩
                        ·
                          by_cases h12 : n < 18150
                          · have hoff : 18100 ≤ n := by omega
                            have hnfin : n - 18100 < 50 := by omega
                            simpa [Nat.sub_add_cancel hoff] using m1_w12 ⟨n - 18100, hnfin⟩
                          ·
                            by_cases h13 : n < 18200
                            · have hoff : 18150 ≤ n := by omega
                              have hnfin : n - 18150 < 50 := by omega
                              simpa [Nat.sub_add_cancel hoff] using m1_w13 ⟨n - 18150, hnfin⟩
                            ·
                              by_cases h14 : n < 18250
                              · have hoff : 18200 ≤ n := by omega
                                have hnfin : n - 18200 < 50 := by omega
                                simpa [Nat.sub_add_cancel hoff] using m1_w14 ⟨n - 18200, hnfin⟩
                              ·
                                by_cases h15 : n < 18300
                                · have hoff : 18250 ≤ n := by omega
                                  have hnfin : n - 18250 < 50 := by omega
                                  simpa [Nat.sub_add_cancel hoff] using m1_w15 ⟨n - 18250, hnfin⟩
                                ·
                                  by_cases h16 : n < 18350
                                  · have hoff : 18300 ≤ n := by omega
                                    have hnfin : n - 18300 < 50 := by omega
                                    simpa [Nat.sub_add_cancel hoff] using m1_w16 ⟨n - 18300, hnfin⟩
                                  ·
                                    by_cases h17 : n < 18400
                                    · have hoff : 18350 ≤ n := by omega
                                      have hnfin : n - 18350 < 50 := by omega
                                      simpa [Nat.sub_add_cancel hoff] using m1_w17 ⟨n - 18350, hnfin⟩
                                    ·
                                      by_cases h18 : n < 18450
                                      · have hoff : 18400 ≤ n := by omega
                                        have hnfin : n - 18400 < 50 := by omega
                                        simpa [Nat.sub_add_cancel hoff] using m1_w18 ⟨n - 18400, hnfin⟩
                                      ·
                                        by_cases h19 : n < 18500
                                        · have hoff : 18450 ≤ n := by omega
                                          have hnfin : n - 18450 < 50 := by omega
                                          simpa [Nat.sub_add_cancel hoff] using m1_w19 ⟨n - 18450, hnfin⟩
                                        ·
                                          by_cases h20 : n < 18550
                                          · have hoff : 18500 ≤ n := by omega
                                            have hnfin : n - 18500 < 50 := by omega
                                            simpa [Nat.sub_add_cancel hoff] using m1_w20 ⟨n - 18500, hnfin⟩
                                          ·
                                            by_cases h21 : n < 18600
                                            · have hoff : 18550 ≤ n := by omega
                                              have hnfin : n - 18550 < 50 := by omega
                                              simpa [Nat.sub_add_cancel hoff] using m1_w21 ⟨n - 18550, hnfin⟩
                                            ·
                                              by_cases h22 : n < 18650
                                              · have hoff : 18600 ≤ n := by omega
                                                have hnfin : n - 18600 < 50 := by omega
                                                simpa [Nat.sub_add_cancel hoff] using m1_w22 ⟨n - 18600, hnfin⟩
                                              ·
                                                by_cases h23 : n < 18700
                                                · have hoff : 18650 ≤ n := by omega
                                                  have hnfin : n - 18650 < 50 := by omega
                                                  simpa [Nat.sub_add_cancel hoff] using m1_w23 ⟨n - 18650, hnfin⟩
                                                ·
                                                  by_cases h24 : n < 18750
                                                  · have hoff : 18700 ≤ n := by omega
                                                    have hnfin : n - 18700 < 50 := by omega
                                                    simpa [Nat.sub_add_cancel hoff] using m1_w24 ⟨n - 18700, hnfin⟩
                                                  ·
                                                    by_cases h25 : n < 18800
                                                    · have hoff : 18750 ≤ n := by omega
                                                      have hnfin : n - 18750 < 50 := by omega
                                                      simpa [Nat.sub_add_cancel hoff] using m1_w25 ⟨n - 18750, hnfin⟩
                                                    ·
                                                      by_cases h26 : n < 18850
                                                      · have hoff : 18800 ≤ n := by omega
                                                        have hnfin : n - 18800 < 50 := by omega
                                                        simpa [Nat.sub_add_cancel hoff] using m1_w26 ⟨n - 18800, hnfin⟩
                                                      ·
                                                        by_cases h27 : n < 18900
                                                        · have hoff : 18850 ≤ n := by omega
                                                          have hnfin : n - 18850 < 50 := by omega
                                                          simpa [Nat.sub_add_cancel hoff] using m1_w27 ⟨n - 18850, hnfin⟩
                                                        ·
                                                          by_cases h28 : n < 18950
                                                          · have hoff : 18900 ≤ n := by omega
                                                            have hnfin : n - 18900 < 50 := by omega
                                                            simpa [Nat.sub_add_cancel hoff] using m1_w28 ⟨n - 18900, hnfin⟩
                                                          ·
                                                            by_cases h29 : n < 19000
                                                            · have hoff : 18950 ≤ n := by omega
                                                              have hnfin : n - 18950 < 50 := by omega
                                                              simpa [Nat.sub_add_cancel hoff] using m1_w29 ⟨n - 18950, hnfin⟩
                                                            ·
                                                              by_cases h30 : n < 19050
                                                              · have hoff : 19000 ≤ n := by omega
                                                                have hnfin : n - 19000 < 50 := by omega
                                                                simpa [Nat.sub_add_cancel hoff] using m1_w30 ⟨n - 19000, hnfin⟩
                                                              ·
                                                                by_cases h31 : n < 19100
                                                                · have hoff : 19050 ≤ n := by omega
                                                                  have hnfin : n - 19050 < 50 := by omega
                                                                  simpa [Nat.sub_add_cancel hoff] using m1_w31 ⟨n - 19050, hnfin⟩
                                                                ·
                                                                  by_cases h32 : n < 19150
                                                                  · have hoff : 19100 ≤ n := by omega
                                                                    have hnfin : n - 19100 < 50 := by omega
                                                                    simpa [Nat.sub_add_cancel hoff] using m1_w32 ⟨n - 19100, hnfin⟩
                                                                  ·
                                                                    by_cases h33 : n < 19200
                                                                    · have hoff : 19150 ≤ n := by omega
                                                                      have hnfin : n - 19150 < 50 := by omega
                                                                      simpa [Nat.sub_add_cancel hoff] using m1_w33 ⟨n - 19150, hnfin⟩
                                                                    ·
                                                                      by_cases h34 : n < 19250
                                                                      · have hoff : 19200 ≤ n := by omega
                                                                        have hnfin : n - 19200 < 50 := by omega
                                                                        simpa [Nat.sub_add_cancel hoff] using m1_w34 ⟨n - 19200, hnfin⟩
                                                                      ·
                                                                        by_cases h35 : n < 19300
                                                                        · have hoff : 19250 ≤ n := by omega
                                                                          have hnfin : n - 19250 < 50 := by omega
                                                                          simpa [Nat.sub_add_cancel hoff] using m1_w35 ⟨n - 19250, hnfin⟩
                                                                        ·
                                                                          by_cases h36 : n < 19350
                                                                          · have hoff : 19300 ≤ n := by omega
                                                                            have hnfin : n - 19300 < 50 := by omega
                                                                            simpa [Nat.sub_add_cancel hoff] using m1_w36 ⟨n - 19300, hnfin⟩
                                                                          ·
                                                                            by_cases h37 : n < 19400
                                                                            · have hoff : 19350 ≤ n := by omega
                                                                              have hnfin : n - 19350 < 50 := by omega
                                                                              simpa [Nat.sub_add_cancel hoff] using m1_w37 ⟨n - 19350, hnfin⟩
                                                                            ·
                                                                              by_cases h38 : n < 19450
                                                                              · have hoff : 19400 ≤ n := by omega
                                                                                have hnfin : n - 19400 < 50 := by omega
                                                                                simpa [Nat.sub_add_cancel hoff] using m1_w38 ⟨n - 19400, hnfin⟩
                                                                              ·
                                                                                by_cases h39 : n < 19500
                                                                                · have hoff : 19450 ≤ n := by omega
                                                                                  have hnfin : n - 19450 < 50 := by omega
                                                                                  simpa [Nat.sub_add_cancel hoff] using m1_w39 ⟨n - 19450, hnfin⟩
                                                                                ·
                                                                                  by_cases h40 : n < 19550
                                                                                  · have hoff : 19500 ≤ n := by omega
                                                                                    have hnfin : n - 19500 < 50 := by omega
                                                                                    simpa [Nat.sub_add_cancel hoff] using m1_w40 ⟨n - 19500, hnfin⟩
                                                                                  ·
                                                                                    by_cases h41 : n < 19600
                                                                                    · have hoff : 19550 ≤ n := by omega
                                                                                      have hnfin : n - 19550 < 50 := by omega
                                                                                      simpa [Nat.sub_add_cancel hoff] using m1_w41 ⟨n - 19550, hnfin⟩
                                                                                    ·
                                                                                      by_cases h42 : n < 19650
                                                                                      · have hoff : 19600 ≤ n := by omega
                                                                                        have hnfin : n - 19600 < 50 := by omega
                                                                                        simpa [Nat.sub_add_cancel hoff] using m1_w42 ⟨n - 19600, hnfin⟩
                                                                                      ·
                                                                                        by_cases h43 : n < 19700
                                                                                        · have hoff : 19650 ≤ n := by omega
                                                                                          have hnfin : n - 19650 < 50 := by omega
                                                                                          simpa [Nat.sub_add_cancel hoff] using m1_w43 ⟨n - 19650, hnfin⟩
                                                                                        ·
                                                                                          by_cases h44 : n < 19750
                                                                                          · have hoff : 19700 ≤ n := by omega
                                                                                            have hnfin : n - 19700 < 50 := by omega
                                                                                            simpa [Nat.sub_add_cancel hoff] using m1_w44 ⟨n - 19700, hnfin⟩
                                                                                          ·
                                                                                            by_cases h45 : n < 19800
                                                                                            · have hoff : 19750 ≤ n := by omega
                                                                                              have hnfin : n - 19750 < 50 := by omega
                                                                                              simpa [Nat.sub_add_cancel hoff] using m1_w45 ⟨n - 19750, hnfin⟩
                                                                                            ·
                                                                                              by_cases h46 : n < 19850
                                                                                              · have hoff : 19800 ≤ n := by omega
                                                                                                have hnfin : n - 19800 < 50 := by omega
                                                                                                simpa [Nat.sub_add_cancel hoff] using m1_w46 ⟨n - 19800, hnfin⟩
                                                                                              ·
                                                                                                by_cases h47 : n < 19900
                                                                                                · have hoff : 19850 ≤ n := by omega
                                                                                                  have hnfin : n - 19850 < 50 := by omega
                                                                                                  simpa [Nat.sub_add_cancel hoff] using m1_w47 ⟨n - 19850, hnfin⟩
                                                                                                ·
                                                                                                  by_cases h48 : n < 19950
                                                                                                  · have hoff : 19900 ≤ n := by omega
                                                                                                    have hnfin : n - 19900 < 50 := by omega
                                                                                                    simpa [Nat.sub_add_cancel hoff] using m1_w48 ⟨n - 19900, hnfin⟩
                                                                                                  ·
                                                                                                    by_cases h49 : n < 20000
                                                                                                    · have hoff : 19950 ≤ n := by omega
                                                                                                      have hnfin : n - 19950 < 50 := by omega
                                                                                                      simpa [Nat.sub_add_cancel hoff] using m1_w49 ⟨n - 19950, hnfin⟩
                                                                                                    ·
                                                                                                      omega
end IntMul.Kappa.R8.Bit.Oppbank.LandMonoFixA7


