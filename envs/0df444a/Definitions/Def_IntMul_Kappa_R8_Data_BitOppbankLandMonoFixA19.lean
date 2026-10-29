-- Prove2me | Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankLandMonoFixA19
-- name    : IntMul_Kappa_R8_Data_BitOppbankLandMonoFixA19
-- status  : Definition
-- author  : @Ethan Cheung Wang
-- created : 2026-10-28T21:17:49.914505+00:00
-- url     : https://prove2.me/theorems/3901cc79-a2a3-4720-84e1-f9fe8d261934
-- title:
--   Dim-gated densSup land mono FixA pack 19
-- statement:
--   # Dim-gated densSup land (PndFix), pack A19
--
--   Range consolidators for $n\in[47500,50000)$.
-- source:
--   R8 BitOppbank PndFix

-- LandMonoFixA19: PUBLIC dim-gated land + range consolidators (PndFix)
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
namespace IntMul.Kappa.R8.Bit.Oppbank.LandMonoFixA19
def arg0 (n : ℕ) : ℕ := Nat.land (argF n) 65535
def arg1 (n : ℕ) : ℕ := Nat.shiftRight (argF n) 16
theorem m0_w0 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 47500))) (dimF (n.val + 47500)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 47500))) (densSupG (n.val + 47500))) (densSupG (arg0 (n.val + 47500)))) = true := by decide
theorem m1_w0 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 47500))) (dimF (n.val + 47500)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 47500))) (densSupG (n.val + 47500))) (densSupG (arg1 (n.val + 47500)))) = true := by decide
theorem m0_w1 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 47550))) (dimF (n.val + 47550)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 47550))) (densSupG (n.val + 47550))) (densSupG (arg0 (n.val + 47550)))) = true := by decide
theorem m1_w1 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 47550))) (dimF (n.val + 47550)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 47550))) (densSupG (n.val + 47550))) (densSupG (arg1 (n.val + 47550)))) = true := by decide
theorem m0_w2 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 47600))) (dimF (n.val + 47600)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 47600))) (densSupG (n.val + 47600))) (densSupG (arg0 (n.val + 47600)))) = true := by decide
theorem m1_w2 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 47600))) (dimF (n.val + 47600)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 47600))) (densSupG (n.val + 47600))) (densSupG (arg1 (n.val + 47600)))) = true := by decide
theorem m0_w3 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 47650))) (dimF (n.val + 47650)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 47650))) (densSupG (n.val + 47650))) (densSupG (arg0 (n.val + 47650)))) = true := by decide
theorem m1_w3 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 47650))) (dimF (n.val + 47650)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 47650))) (densSupG (n.val + 47650))) (densSupG (arg1 (n.val + 47650)))) = true := by decide
theorem m0_w4 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 47700))) (dimF (n.val + 47700)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 47700))) (densSupG (n.val + 47700))) (densSupG (arg0 (n.val + 47700)))) = true := by decide
theorem m1_w4 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 47700))) (dimF (n.val + 47700)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 47700))) (densSupG (n.val + 47700))) (densSupG (arg1 (n.val + 47700)))) = true := by decide
theorem m0_w5 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 47750))) (dimF (n.val + 47750)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 47750))) (densSupG (n.val + 47750))) (densSupG (arg0 (n.val + 47750)))) = true := by decide
theorem m1_w5 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 47750))) (dimF (n.val + 47750)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 47750))) (densSupG (n.val + 47750))) (densSupG (arg1 (n.val + 47750)))) = true := by decide
theorem m0_w6 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 47800))) (dimF (n.val + 47800)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 47800))) (densSupG (n.val + 47800))) (densSupG (arg0 (n.val + 47800)))) = true := by decide
theorem m1_w6 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 47800))) (dimF (n.val + 47800)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 47800))) (densSupG (n.val + 47800))) (densSupG (arg1 (n.val + 47800)))) = true := by decide
theorem m0_w7 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 47850))) (dimF (n.val + 47850)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 47850))) (densSupG (n.val + 47850))) (densSupG (arg0 (n.val + 47850)))) = true := by decide
theorem m1_w7 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 47850))) (dimF (n.val + 47850)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 47850))) (densSupG (n.val + 47850))) (densSupG (arg1 (n.val + 47850)))) = true := by decide
theorem m0_w8 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 47900))) (dimF (n.val + 47900)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 47900))) (densSupG (n.val + 47900))) (densSupG (arg0 (n.val + 47900)))) = true := by decide
theorem m1_w8 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 47900))) (dimF (n.val + 47900)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 47900))) (densSupG (n.val + 47900))) (densSupG (arg1 (n.val + 47900)))) = true := by decide
theorem m0_w9 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 47950))) (dimF (n.val + 47950)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 47950))) (densSupG (n.val + 47950))) (densSupG (arg0 (n.val + 47950)))) = true := by decide
theorem m1_w9 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 47950))) (dimF (n.val + 47950)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 47950))) (densSupG (n.val + 47950))) (densSupG (arg1 (n.val + 47950)))) = true := by decide
theorem m0_w10 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 48000))) (dimF (n.val + 48000)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 48000))) (densSupG (n.val + 48000))) (densSupG (arg0 (n.val + 48000)))) = true := by decide
theorem m1_w10 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 48000))) (dimF (n.val + 48000)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 48000))) (densSupG (n.val + 48000))) (densSupG (arg1 (n.val + 48000)))) = true := by decide
theorem m0_w11 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 48050))) (dimF (n.val + 48050)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 48050))) (densSupG (n.val + 48050))) (densSupG (arg0 (n.val + 48050)))) = true := by decide
theorem m1_w11 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 48050))) (dimF (n.val + 48050)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 48050))) (densSupG (n.val + 48050))) (densSupG (arg1 (n.val + 48050)))) = true := by decide
theorem m0_w12 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 48100))) (dimF (n.val + 48100)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 48100))) (densSupG (n.val + 48100))) (densSupG (arg0 (n.val + 48100)))) = true := by decide
theorem m1_w12 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 48100))) (dimF (n.val + 48100)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 48100))) (densSupG (n.val + 48100))) (densSupG (arg1 (n.val + 48100)))) = true := by decide
theorem m0_w13 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 48150))) (dimF (n.val + 48150)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 48150))) (densSupG (n.val + 48150))) (densSupG (arg0 (n.val + 48150)))) = true := by decide
theorem m1_w13 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 48150))) (dimF (n.val + 48150)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 48150))) (densSupG (n.val + 48150))) (densSupG (arg1 (n.val + 48150)))) = true := by decide
theorem m0_w14 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 48200))) (dimF (n.val + 48200)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 48200))) (densSupG (n.val + 48200))) (densSupG (arg0 (n.val + 48200)))) = true := by decide
theorem m1_w14 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 48200))) (dimF (n.val + 48200)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 48200))) (densSupG (n.val + 48200))) (densSupG (arg1 (n.val + 48200)))) = true := by decide
theorem m0_w15 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 48250))) (dimF (n.val + 48250)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 48250))) (densSupG (n.val + 48250))) (densSupG (arg0 (n.val + 48250)))) = true := by decide
theorem m1_w15 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 48250))) (dimF (n.val + 48250)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 48250))) (densSupG (n.val + 48250))) (densSupG (arg1 (n.val + 48250)))) = true := by decide
theorem m0_w16 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 48300))) (dimF (n.val + 48300)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 48300))) (densSupG (n.val + 48300))) (densSupG (arg0 (n.val + 48300)))) = true := by decide
theorem m1_w16 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 48300))) (dimF (n.val + 48300)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 48300))) (densSupG (n.val + 48300))) (densSupG (arg1 (n.val + 48300)))) = true := by decide
theorem m0_w17 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 48350))) (dimF (n.val + 48350)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 48350))) (densSupG (n.val + 48350))) (densSupG (arg0 (n.val + 48350)))) = true := by decide
theorem m1_w17 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 48350))) (dimF (n.val + 48350)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 48350))) (densSupG (n.val + 48350))) (densSupG (arg1 (n.val + 48350)))) = true := by decide
theorem m0_w18 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 48400))) (dimF (n.val + 48400)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 48400))) (densSupG (n.val + 48400))) (densSupG (arg0 (n.val + 48400)))) = true := by decide
theorem m1_w18 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 48400))) (dimF (n.val + 48400)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 48400))) (densSupG (n.val + 48400))) (densSupG (arg1 (n.val + 48400)))) = true := by decide
theorem m0_w19 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 48450))) (dimF (n.val + 48450)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 48450))) (densSupG (n.val + 48450))) (densSupG (arg0 (n.val + 48450)))) = true := by decide
theorem m1_w19 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 48450))) (dimF (n.val + 48450)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 48450))) (densSupG (n.val + 48450))) (densSupG (arg1 (n.val + 48450)))) = true := by decide
theorem m0_w20 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 48500))) (dimF (n.val + 48500)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 48500))) (densSupG (n.val + 48500))) (densSupG (arg0 (n.val + 48500)))) = true := by decide
theorem m1_w20 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 48500))) (dimF (n.val + 48500)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 48500))) (densSupG (n.val + 48500))) (densSupG (arg1 (n.val + 48500)))) = true := by decide
theorem m0_w21 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 48550))) (dimF (n.val + 48550)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 48550))) (densSupG (n.val + 48550))) (densSupG (arg0 (n.val + 48550)))) = true := by decide
theorem m1_w21 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 48550))) (dimF (n.val + 48550)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 48550))) (densSupG (n.val + 48550))) (densSupG (arg1 (n.val + 48550)))) = true := by decide
theorem m0_w22 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 48600))) (dimF (n.val + 48600)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 48600))) (densSupG (n.val + 48600))) (densSupG (arg0 (n.val + 48600)))) = true := by decide
theorem m1_w22 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 48600))) (dimF (n.val + 48600)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 48600))) (densSupG (n.val + 48600))) (densSupG (arg1 (n.val + 48600)))) = true := by decide
theorem m0_w23 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 48650))) (dimF (n.val + 48650)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 48650))) (densSupG (n.val + 48650))) (densSupG (arg0 (n.val + 48650)))) = true := by decide
theorem m1_w23 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 48650))) (dimF (n.val + 48650)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 48650))) (densSupG (n.val + 48650))) (densSupG (arg1 (n.val + 48650)))) = true := by decide
theorem m0_w24 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 48700))) (dimF (n.val + 48700)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 48700))) (densSupG (n.val + 48700))) (densSupG (arg0 (n.val + 48700)))) = true := by decide
theorem m1_w24 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 48700))) (dimF (n.val + 48700)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 48700))) (densSupG (n.val + 48700))) (densSupG (arg1 (n.val + 48700)))) = true := by decide
theorem m0_w25 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 48750))) (dimF (n.val + 48750)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 48750))) (densSupG (n.val + 48750))) (densSupG (arg0 (n.val + 48750)))) = true := by decide
theorem m1_w25 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 48750))) (dimF (n.val + 48750)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 48750))) (densSupG (n.val + 48750))) (densSupG (arg1 (n.val + 48750)))) = true := by decide
theorem m0_w26 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 48800))) (dimF (n.val + 48800)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 48800))) (densSupG (n.val + 48800))) (densSupG (arg0 (n.val + 48800)))) = true := by decide
theorem m1_w26 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 48800))) (dimF (n.val + 48800)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 48800))) (densSupG (n.val + 48800))) (densSupG (arg1 (n.val + 48800)))) = true := by decide
theorem m0_w27 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 48850))) (dimF (n.val + 48850)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 48850))) (densSupG (n.val + 48850))) (densSupG (arg0 (n.val + 48850)))) = true := by decide
theorem m1_w27 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 48850))) (dimF (n.val + 48850)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 48850))) (densSupG (n.val + 48850))) (densSupG (arg1 (n.val + 48850)))) = true := by decide
theorem m0_w28 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 48900))) (dimF (n.val + 48900)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 48900))) (densSupG (n.val + 48900))) (densSupG (arg0 (n.val + 48900)))) = true := by decide
theorem m1_w28 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 48900))) (dimF (n.val + 48900)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 48900))) (densSupG (n.val + 48900))) (densSupG (arg1 (n.val + 48900)))) = true := by decide
theorem m0_w29 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 48950))) (dimF (n.val + 48950)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 48950))) (densSupG (n.val + 48950))) (densSupG (arg0 (n.val + 48950)))) = true := by decide
theorem m1_w29 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 48950))) (dimF (n.val + 48950)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 48950))) (densSupG (n.val + 48950))) (densSupG (arg1 (n.val + 48950)))) = true := by decide
theorem m0_w30 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 49000))) (dimF (n.val + 49000)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 49000))) (densSupG (n.val + 49000))) (densSupG (arg0 (n.val + 49000)))) = true := by decide
theorem m1_w30 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 49000))) (dimF (n.val + 49000)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 49000))) (densSupG (n.val + 49000))) (densSupG (arg1 (n.val + 49000)))) = true := by decide
theorem m0_w31 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 49050))) (dimF (n.val + 49050)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 49050))) (densSupG (n.val + 49050))) (densSupG (arg0 (n.val + 49050)))) = true := by decide
theorem m1_w31 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 49050))) (dimF (n.val + 49050)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 49050))) (densSupG (n.val + 49050))) (densSupG (arg1 (n.val + 49050)))) = true := by decide
theorem m0_w32 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 49100))) (dimF (n.val + 49100)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 49100))) (densSupG (n.val + 49100))) (densSupG (arg0 (n.val + 49100)))) = true := by decide
theorem m1_w32 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 49100))) (dimF (n.val + 49100)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 49100))) (densSupG (n.val + 49100))) (densSupG (arg1 (n.val + 49100)))) = true := by decide
theorem m0_w33 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 49150))) (dimF (n.val + 49150)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 49150))) (densSupG (n.val + 49150))) (densSupG (arg0 (n.val + 49150)))) = true := by decide
theorem m1_w33 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 49150))) (dimF (n.val + 49150)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 49150))) (densSupG (n.val + 49150))) (densSupG (arg1 (n.val + 49150)))) = true := by decide
theorem m0_w34 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 49200))) (dimF (n.val + 49200)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 49200))) (densSupG (n.val + 49200))) (densSupG (arg0 (n.val + 49200)))) = true := by decide
theorem m1_w34 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 49200))) (dimF (n.val + 49200)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 49200))) (densSupG (n.val + 49200))) (densSupG (arg1 (n.val + 49200)))) = true := by decide
theorem m0_w35 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 49250))) (dimF (n.val + 49250)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 49250))) (densSupG (n.val + 49250))) (densSupG (arg0 (n.val + 49250)))) = true := by decide
theorem m1_w35 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 49250))) (dimF (n.val + 49250)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 49250))) (densSupG (n.val + 49250))) (densSupG (arg1 (n.val + 49250)))) = true := by decide
theorem m0_w36 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 49300))) (dimF (n.val + 49300)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 49300))) (densSupG (n.val + 49300))) (densSupG (arg0 (n.val + 49300)))) = true := by decide
theorem m1_w36 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 49300))) (dimF (n.val + 49300)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 49300))) (densSupG (n.val + 49300))) (densSupG (arg1 (n.val + 49300)))) = true := by decide
theorem m0_w37 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 49350))) (dimF (n.val + 49350)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 49350))) (densSupG (n.val + 49350))) (densSupG (arg0 (n.val + 49350)))) = true := by decide
theorem m1_w37 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 49350))) (dimF (n.val + 49350)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 49350))) (densSupG (n.val + 49350))) (densSupG (arg1 (n.val + 49350)))) = true := by decide
theorem m0_w38 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 49400))) (dimF (n.val + 49400)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 49400))) (densSupG (n.val + 49400))) (densSupG (arg0 (n.val + 49400)))) = true := by decide
theorem m1_w38 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 49400))) (dimF (n.val + 49400)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 49400))) (densSupG (n.val + 49400))) (densSupG (arg1 (n.val + 49400)))) = true := by decide
theorem m0_w39 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 49450))) (dimF (n.val + 49450)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 49450))) (densSupG (n.val + 49450))) (densSupG (arg0 (n.val + 49450)))) = true := by decide
theorem m1_w39 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 49450))) (dimF (n.val + 49450)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 49450))) (densSupG (n.val + 49450))) (densSupG (arg1 (n.val + 49450)))) = true := by decide
theorem m0_w40 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 49500))) (dimF (n.val + 49500)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 49500))) (densSupG (n.val + 49500))) (densSupG (arg0 (n.val + 49500)))) = true := by decide
theorem m1_w40 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 49500))) (dimF (n.val + 49500)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 49500))) (densSupG (n.val + 49500))) (densSupG (arg1 (n.val + 49500)))) = true := by decide
theorem m0_w41 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 49550))) (dimF (n.val + 49550)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 49550))) (densSupG (n.val + 49550))) (densSupG (arg0 (n.val + 49550)))) = true := by decide
theorem m1_w41 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 49550))) (dimF (n.val + 49550)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 49550))) (densSupG (n.val + 49550))) (densSupG (arg1 (n.val + 49550)))) = true := by decide
theorem m0_w42 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 49600))) (dimF (n.val + 49600)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 49600))) (densSupG (n.val + 49600))) (densSupG (arg0 (n.val + 49600)))) = true := by decide
theorem m1_w42 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 49600))) (dimF (n.val + 49600)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 49600))) (densSupG (n.val + 49600))) (densSupG (arg1 (n.val + 49600)))) = true := by decide
theorem m0_w43 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 49650))) (dimF (n.val + 49650)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 49650))) (densSupG (n.val + 49650))) (densSupG (arg0 (n.val + 49650)))) = true := by decide
theorem m1_w43 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 49650))) (dimF (n.val + 49650)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 49650))) (densSupG (n.val + 49650))) (densSupG (arg1 (n.val + 49650)))) = true := by decide
theorem m0_w44 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 49700))) (dimF (n.val + 49700)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 49700))) (densSupG (n.val + 49700))) (densSupG (arg0 (n.val + 49700)))) = true := by decide
theorem m1_w44 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 49700))) (dimF (n.val + 49700)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 49700))) (densSupG (n.val + 49700))) (densSupG (arg1 (n.val + 49700)))) = true := by decide
theorem m0_w45 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 49750))) (dimF (n.val + 49750)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 49750))) (densSupG (n.val + 49750))) (densSupG (arg0 (n.val + 49750)))) = true := by decide
theorem m1_w45 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 49750))) (dimF (n.val + 49750)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 49750))) (densSupG (n.val + 49750))) (densSupG (arg1 (n.val + 49750)))) = true := by decide
theorem m0_w46 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 49800))) (dimF (n.val + 49800)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 49800))) (densSupG (n.val + 49800))) (densSupG (arg0 (n.val + 49800)))) = true := by decide
theorem m1_w46 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 49800))) (dimF (n.val + 49800)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 49800))) (densSupG (n.val + 49800))) (densSupG (arg1 (n.val + 49800)))) = true := by decide
theorem m0_w47 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 49850))) (dimF (n.val + 49850)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 49850))) (densSupG (n.val + 49850))) (densSupG (arg0 (n.val + 49850)))) = true := by decide
theorem m1_w47 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 49850))) (dimF (n.val + 49850)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 49850))) (densSupG (n.val + 49850))) (densSupG (arg1 (n.val + 49850)))) = true := by decide
theorem m0_w48 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 49900))) (dimF (n.val + 49900)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 49900))) (densSupG (n.val + 49900))) (densSupG (arg0 (n.val + 49900)))) = true := by decide
theorem m1_w48 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 49900))) (dimF (n.val + 49900)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 49900))) (densSupG (n.val + 49900))) (densSupG (arg1 (n.val + 49900)))) = true := by decide
theorem m0_w49 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 49950))) (dimF (n.val + 49950)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 49950))) (densSupG (n.val + 49950))) (densSupG (arg0 (n.val + 49950)))) = true := by decide
theorem m1_w49 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 49950))) (dimF (n.val + 49950)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 49950))) (densSupG (n.val + 49950))) (densSupG (arg1 (n.val + 49950)))) = true := by decide
theorem land0_range (n : ℕ) (hn0 : 47500 ≤ n) (hn1 : n < 50000) :
    (!Nat.blt (dimF (arg0 n)) (dimF n) ||
      Nat.beq (Nat.land (densSupG (arg0 n)) (densSupG n)) (densSupG (arg0 n))) = true := by
  by_cases h0 : n < 47550
  · have hoff : 47500 ≤ n := by omega
    have hnfin : n - 47500 < 50 := by omega
    simpa [Nat.sub_add_cancel hoff] using m0_w0 ⟨n - 47500, hnfin⟩
  ·
    by_cases h1 : n < 47600
    · have hoff : 47550 ≤ n := by omega
      have hnfin : n - 47550 < 50 := by omega
      simpa [Nat.sub_add_cancel hoff] using m0_w1 ⟨n - 47550, hnfin⟩
    ·
      by_cases h2 : n < 47650
      · have hoff : 47600 ≤ n := by omega
        have hnfin : n - 47600 < 50 := by omega
        simpa [Nat.sub_add_cancel hoff] using m0_w2 ⟨n - 47600, hnfin⟩
      ·
        by_cases h3 : n < 47700
        · have hoff : 47650 ≤ n := by omega
          have hnfin : n - 47650 < 50 := by omega
          simpa [Nat.sub_add_cancel hoff] using m0_w3 ⟨n - 47650, hnfin⟩
        ·
          by_cases h4 : n < 47750
          · have hoff : 47700 ≤ n := by omega
            have hnfin : n - 47700 < 50 := by omega
            simpa [Nat.sub_add_cancel hoff] using m0_w4 ⟨n - 47700, hnfin⟩
          ·
            by_cases h5 : n < 47800
            · have hoff : 47750 ≤ n := by omega
              have hnfin : n - 47750 < 50 := by omega
              simpa [Nat.sub_add_cancel hoff] using m0_w5 ⟨n - 47750, hnfin⟩
            ·
              by_cases h6 : n < 47850
              · have hoff : 47800 ≤ n := by omega
                have hnfin : n - 47800 < 50 := by omega
                simpa [Nat.sub_add_cancel hoff] using m0_w6 ⟨n - 47800, hnfin⟩
              ·
                by_cases h7 : n < 47900
                · have hoff : 47850 ≤ n := by omega
                  have hnfin : n - 47850 < 50 := by omega
                  simpa [Nat.sub_add_cancel hoff] using m0_w7 ⟨n - 47850, hnfin⟩
                ·
                  by_cases h8 : n < 47950
                  · have hoff : 47900 ≤ n := by omega
                    have hnfin : n - 47900 < 50 := by omega
                    simpa [Nat.sub_add_cancel hoff] using m0_w8 ⟨n - 47900, hnfin⟩
                  ·
                    by_cases h9 : n < 48000
                    · have hoff : 47950 ≤ n := by omega
                      have hnfin : n - 47950 < 50 := by omega
                      simpa [Nat.sub_add_cancel hoff] using m0_w9 ⟨n - 47950, hnfin⟩
                    ·
                      by_cases h10 : n < 48050
                      · have hoff : 48000 ≤ n := by omega
                        have hnfin : n - 48000 < 50 := by omega
                        simpa [Nat.sub_add_cancel hoff] using m0_w10 ⟨n - 48000, hnfin⟩
                      ·
                        by_cases h11 : n < 48100
                        · have hoff : 48050 ≤ n := by omega
                          have hnfin : n - 48050 < 50 := by omega
                          simpa [Nat.sub_add_cancel hoff] using m0_w11 ⟨n - 48050, hnfin⟩
                        ·
                          by_cases h12 : n < 48150
                          · have hoff : 48100 ≤ n := by omega
                            have hnfin : n - 48100 < 50 := by omega
                            simpa [Nat.sub_add_cancel hoff] using m0_w12 ⟨n - 48100, hnfin⟩
                          ·
                            by_cases h13 : n < 48200
                            · have hoff : 48150 ≤ n := by omega
                              have hnfin : n - 48150 < 50 := by omega
                              simpa [Nat.sub_add_cancel hoff] using m0_w13 ⟨n - 48150, hnfin⟩
                            ·
                              by_cases h14 : n < 48250
                              · have hoff : 48200 ≤ n := by omega
                                have hnfin : n - 48200 < 50 := by omega
                                simpa [Nat.sub_add_cancel hoff] using m0_w14 ⟨n - 48200, hnfin⟩
                              ·
                                by_cases h15 : n < 48300
                                · have hoff : 48250 ≤ n := by omega
                                  have hnfin : n - 48250 < 50 := by omega
                                  simpa [Nat.sub_add_cancel hoff] using m0_w15 ⟨n - 48250, hnfin⟩
                                ·
                                  by_cases h16 : n < 48350
                                  · have hoff : 48300 ≤ n := by omega
                                    have hnfin : n - 48300 < 50 := by omega
                                    simpa [Nat.sub_add_cancel hoff] using m0_w16 ⟨n - 48300, hnfin⟩
                                  ·
                                    by_cases h17 : n < 48400
                                    · have hoff : 48350 ≤ n := by omega
                                      have hnfin : n - 48350 < 50 := by omega
                                      simpa [Nat.sub_add_cancel hoff] using m0_w17 ⟨n - 48350, hnfin⟩
                                    ·
                                      by_cases h18 : n < 48450
                                      · have hoff : 48400 ≤ n := by omega
                                        have hnfin : n - 48400 < 50 := by omega
                                        simpa [Nat.sub_add_cancel hoff] using m0_w18 ⟨n - 48400, hnfin⟩
                                      ·
                                        by_cases h19 : n < 48500
                                        · have hoff : 48450 ≤ n := by omega
                                          have hnfin : n - 48450 < 50 := by omega
                                          simpa [Nat.sub_add_cancel hoff] using m0_w19 ⟨n - 48450, hnfin⟩
                                        ·
                                          by_cases h20 : n < 48550
                                          · have hoff : 48500 ≤ n := by omega
                                            have hnfin : n - 48500 < 50 := by omega
                                            simpa [Nat.sub_add_cancel hoff] using m0_w20 ⟨n - 48500, hnfin⟩
                                          ·
                                            by_cases h21 : n < 48600
                                            · have hoff : 48550 ≤ n := by omega
                                              have hnfin : n - 48550 < 50 := by omega
                                              simpa [Nat.sub_add_cancel hoff] using m0_w21 ⟨n - 48550, hnfin⟩
                                            ·
                                              by_cases h22 : n < 48650
                                              · have hoff : 48600 ≤ n := by omega
                                                have hnfin : n - 48600 < 50 := by omega
                                                simpa [Nat.sub_add_cancel hoff] using m0_w22 ⟨n - 48600, hnfin⟩
                                              ·
                                                by_cases h23 : n < 48700
                                                · have hoff : 48650 ≤ n := by omega
                                                  have hnfin : n - 48650 < 50 := by omega
                                                  simpa [Nat.sub_add_cancel hoff] using m0_w23 ⟨n - 48650, hnfin⟩
                                                ·
                                                  by_cases h24 : n < 48750
                                                  · have hoff : 48700 ≤ n := by omega
                                                    have hnfin : n - 48700 < 50 := by omega
                                                    simpa [Nat.sub_add_cancel hoff] using m0_w24 ⟨n - 48700, hnfin⟩
                                                  ·
                                                    by_cases h25 : n < 48800
                                                    · have hoff : 48750 ≤ n := by omega
                                                      have hnfin : n - 48750 < 50 := by omega
                                                      simpa [Nat.sub_add_cancel hoff] using m0_w25 ⟨n - 48750, hnfin⟩
                                                    ·
                                                      by_cases h26 : n < 48850
                                                      · have hoff : 48800 ≤ n := by omega
                                                        have hnfin : n - 48800 < 50 := by omega
                                                        simpa [Nat.sub_add_cancel hoff] using m0_w26 ⟨n - 48800, hnfin⟩
                                                      ·
                                                        by_cases h27 : n < 48900
                                                        · have hoff : 48850 ≤ n := by omega
                                                          have hnfin : n - 48850 < 50 := by omega
                                                          simpa [Nat.sub_add_cancel hoff] using m0_w27 ⟨n - 48850, hnfin⟩
                                                        ·
                                                          by_cases h28 : n < 48950
                                                          · have hoff : 48900 ≤ n := by omega
                                                            have hnfin : n - 48900 < 50 := by omega
                                                            simpa [Nat.sub_add_cancel hoff] using m0_w28 ⟨n - 48900, hnfin⟩
                                                          ·
                                                            by_cases h29 : n < 49000
                                                            · have hoff : 48950 ≤ n := by omega
                                                              have hnfin : n - 48950 < 50 := by omega
                                                              simpa [Nat.sub_add_cancel hoff] using m0_w29 ⟨n - 48950, hnfin⟩
                                                            ·
                                                              by_cases h30 : n < 49050
                                                              · have hoff : 49000 ≤ n := by omega
                                                                have hnfin : n - 49000 < 50 := by omega
                                                                simpa [Nat.sub_add_cancel hoff] using m0_w30 ⟨n - 49000, hnfin⟩
                                                              ·
                                                                by_cases h31 : n < 49100
                                                                · have hoff : 49050 ≤ n := by omega
                                                                  have hnfin : n - 49050 < 50 := by omega
                                                                  simpa [Nat.sub_add_cancel hoff] using m0_w31 ⟨n - 49050, hnfin⟩
                                                                ·
                                                                  by_cases h32 : n < 49150
                                                                  · have hoff : 49100 ≤ n := by omega
                                                                    have hnfin : n - 49100 < 50 := by omega
                                                                    simpa [Nat.sub_add_cancel hoff] using m0_w32 ⟨n - 49100, hnfin⟩
                                                                  ·
                                                                    by_cases h33 : n < 49200
                                                                    · have hoff : 49150 ≤ n := by omega
                                                                      have hnfin : n - 49150 < 50 := by omega
                                                                      simpa [Nat.sub_add_cancel hoff] using m0_w33 ⟨n - 49150, hnfin⟩
                                                                    ·
                                                                      by_cases h34 : n < 49250
                                                                      · have hoff : 49200 ≤ n := by omega
                                                                        have hnfin : n - 49200 < 50 := by omega
                                                                        simpa [Nat.sub_add_cancel hoff] using m0_w34 ⟨n - 49200, hnfin⟩
                                                                      ·
                                                                        by_cases h35 : n < 49300
                                                                        · have hoff : 49250 ≤ n := by omega
                                                                          have hnfin : n - 49250 < 50 := by omega
                                                                          simpa [Nat.sub_add_cancel hoff] using m0_w35 ⟨n - 49250, hnfin⟩
                                                                        ·
                                                                          by_cases h36 : n < 49350
                                                                          · have hoff : 49300 ≤ n := by omega
                                                                            have hnfin : n - 49300 < 50 := by omega
                                                                            simpa [Nat.sub_add_cancel hoff] using m0_w36 ⟨n - 49300, hnfin⟩
                                                                          ·
                                                                            by_cases h37 : n < 49400
                                                                            · have hoff : 49350 ≤ n := by omega
                                                                              have hnfin : n - 49350 < 50 := by omega
                                                                              simpa [Nat.sub_add_cancel hoff] using m0_w37 ⟨n - 49350, hnfin⟩
                                                                            ·
                                                                              by_cases h38 : n < 49450
                                                                              · have hoff : 49400 ≤ n := by omega
                                                                                have hnfin : n - 49400 < 50 := by omega
                                                                                simpa [Nat.sub_add_cancel hoff] using m0_w38 ⟨n - 49400, hnfin⟩
                                                                              ·
                                                                                by_cases h39 : n < 49500
                                                                                · have hoff : 49450 ≤ n := by omega
                                                                                  have hnfin : n - 49450 < 50 := by omega
                                                                                  simpa [Nat.sub_add_cancel hoff] using m0_w39 ⟨n - 49450, hnfin⟩
                                                                                ·
                                                                                  by_cases h40 : n < 49550
                                                                                  · have hoff : 49500 ≤ n := by omega
                                                                                    have hnfin : n - 49500 < 50 := by omega
                                                                                    simpa [Nat.sub_add_cancel hoff] using m0_w40 ⟨n - 49500, hnfin⟩
                                                                                  ·
                                                                                    by_cases h41 : n < 49600
                                                                                    · have hoff : 49550 ≤ n := by omega
                                                                                      have hnfin : n - 49550 < 50 := by omega
                                                                                      simpa [Nat.sub_add_cancel hoff] using m0_w41 ⟨n - 49550, hnfin⟩
                                                                                    ·
                                                                                      by_cases h42 : n < 49650
                                                                                      · have hoff : 49600 ≤ n := by omega
                                                                                        have hnfin : n - 49600 < 50 := by omega
                                                                                        simpa [Nat.sub_add_cancel hoff] using m0_w42 ⟨n - 49600, hnfin⟩
                                                                                      ·
                                                                                        by_cases h43 : n < 49700
                                                                                        · have hoff : 49650 ≤ n := by omega
                                                                                          have hnfin : n - 49650 < 50 := by omega
                                                                                          simpa [Nat.sub_add_cancel hoff] using m0_w43 ⟨n - 49650, hnfin⟩
                                                                                        ·
                                                                                          by_cases h44 : n < 49750
                                                                                          · have hoff : 49700 ≤ n := by omega
                                                                                            have hnfin : n - 49700 < 50 := by omega
                                                                                            simpa [Nat.sub_add_cancel hoff] using m0_w44 ⟨n - 49700, hnfin⟩
                                                                                          ·
                                                                                            by_cases h45 : n < 49800
                                                                                            · have hoff : 49750 ≤ n := by omega
                                                                                              have hnfin : n - 49750 < 50 := by omega
                                                                                              simpa [Nat.sub_add_cancel hoff] using m0_w45 ⟨n - 49750, hnfin⟩
                                                                                            ·
                                                                                              by_cases h46 : n < 49850
                                                                                              · have hoff : 49800 ≤ n := by omega
                                                                                                have hnfin : n - 49800 < 50 := by omega
                                                                                                simpa [Nat.sub_add_cancel hoff] using m0_w46 ⟨n - 49800, hnfin⟩
                                                                                              ·
                                                                                                by_cases h47 : n < 49900
                                                                                                · have hoff : 49850 ≤ n := by omega
                                                                                                  have hnfin : n - 49850 < 50 := by omega
                                                                                                  simpa [Nat.sub_add_cancel hoff] using m0_w47 ⟨n - 49850, hnfin⟩
                                                                                                ·
                                                                                                  by_cases h48 : n < 49950
                                                                                                  · have hoff : 49900 ≤ n := by omega
                                                                                                    have hnfin : n - 49900 < 50 := by omega
                                                                                                    simpa [Nat.sub_add_cancel hoff] using m0_w48 ⟨n - 49900, hnfin⟩
                                                                                                  ·
                                                                                                    by_cases h49 : n < 50000
                                                                                                    · have hoff : 49950 ≤ n := by omega
                                                                                                      have hnfin : n - 49950 < 50 := by omega
                                                                                                      simpa [Nat.sub_add_cancel hoff] using m0_w49 ⟨n - 49950, hnfin⟩
                                                                                                    ·
                                                                                                      omega
theorem land1_range (n : ℕ) (hn0 : 47500 ≤ n) (hn1 : n < 50000) :
    (!Nat.blt (dimF (arg1 n)) (dimF n) ||
      Nat.beq (Nat.land (densSupG (arg1 n)) (densSupG n)) (densSupG (arg1 n))) = true := by
  by_cases h0 : n < 47550
  · have hoff : 47500 ≤ n := by omega
    have hnfin : n - 47500 < 50 := by omega
    simpa [Nat.sub_add_cancel hoff] using m1_w0 ⟨n - 47500, hnfin⟩
  ·
    by_cases h1 : n < 47600
    · have hoff : 47550 ≤ n := by omega
      have hnfin : n - 47550 < 50 := by omega
      simpa [Nat.sub_add_cancel hoff] using m1_w1 ⟨n - 47550, hnfin⟩
    ·
      by_cases h2 : n < 47650
      · have hoff : 47600 ≤ n := by omega
        have hnfin : n - 47600 < 50 := by omega
        simpa [Nat.sub_add_cancel hoff] using m1_w2 ⟨n - 47600, hnfin⟩
      ·
        by_cases h3 : n < 47700
        · have hoff : 47650 ≤ n := by omega
          have hnfin : n - 47650 < 50 := by omega
          simpa [Nat.sub_add_cancel hoff] using m1_w3 ⟨n - 47650, hnfin⟩
        ·
          by_cases h4 : n < 47750
          · have hoff : 47700 ≤ n := by omega
            have hnfin : n - 47700 < 50 := by omega
            simpa [Nat.sub_add_cancel hoff] using m1_w4 ⟨n - 47700, hnfin⟩
          ·
            by_cases h5 : n < 47800
            · have hoff : 47750 ≤ n := by omega
              have hnfin : n - 47750 < 50 := by omega
              simpa [Nat.sub_add_cancel hoff] using m1_w5 ⟨n - 47750, hnfin⟩
            ·
              by_cases h6 : n < 47850
              · have hoff : 47800 ≤ n := by omega
                have hnfin : n - 47800 < 50 := by omega
                simpa [Nat.sub_add_cancel hoff] using m1_w6 ⟨n - 47800, hnfin⟩
              ·
                by_cases h7 : n < 47900
                · have hoff : 47850 ≤ n := by omega
                  have hnfin : n - 47850 < 50 := by omega
                  simpa [Nat.sub_add_cancel hoff] using m1_w7 ⟨n - 47850, hnfin⟩
                ·
                  by_cases h8 : n < 47950
                  · have hoff : 47900 ≤ n := by omega
                    have hnfin : n - 47900 < 50 := by omega
                    simpa [Nat.sub_add_cancel hoff] using m1_w8 ⟨n - 47900, hnfin⟩
                  ·
                    by_cases h9 : n < 48000
                    · have hoff : 47950 ≤ n := by omega
                      have hnfin : n - 47950 < 50 := by omega
                      simpa [Nat.sub_add_cancel hoff] using m1_w9 ⟨n - 47950, hnfin⟩
                    ·
                      by_cases h10 : n < 48050
                      · have hoff : 48000 ≤ n := by omega
                        have hnfin : n - 48000 < 50 := by omega
                        simpa [Nat.sub_add_cancel hoff] using m1_w10 ⟨n - 48000, hnfin⟩
                      ·
                        by_cases h11 : n < 48100
                        · have hoff : 48050 ≤ n := by omega
                          have hnfin : n - 48050 < 50 := by omega
                          simpa [Nat.sub_add_cancel hoff] using m1_w11 ⟨n - 48050, hnfin⟩
                        ·
                          by_cases h12 : n < 48150
                          · have hoff : 48100 ≤ n := by omega
                            have hnfin : n - 48100 < 50 := by omega
                            simpa [Nat.sub_add_cancel hoff] using m1_w12 ⟨n - 48100, hnfin⟩
                          ·
                            by_cases h13 : n < 48200
                            · have hoff : 48150 ≤ n := by omega
                              have hnfin : n - 48150 < 50 := by omega
                              simpa [Nat.sub_add_cancel hoff] using m1_w13 ⟨n - 48150, hnfin⟩
                            ·
                              by_cases h14 : n < 48250
                              · have hoff : 48200 ≤ n := by omega
                                have hnfin : n - 48200 < 50 := by omega
                                simpa [Nat.sub_add_cancel hoff] using m1_w14 ⟨n - 48200, hnfin⟩
                              ·
                                by_cases h15 : n < 48300
                                · have hoff : 48250 ≤ n := by omega
                                  have hnfin : n - 48250 < 50 := by omega
                                  simpa [Nat.sub_add_cancel hoff] using m1_w15 ⟨n - 48250, hnfin⟩
                                ·
                                  by_cases h16 : n < 48350
                                  · have hoff : 48300 ≤ n := by omega
                                    have hnfin : n - 48300 < 50 := by omega
                                    simpa [Nat.sub_add_cancel hoff] using m1_w16 ⟨n - 48300, hnfin⟩
                                  ·
                                    by_cases h17 : n < 48400
                                    · have hoff : 48350 ≤ n := by omega
                                      have hnfin : n - 48350 < 50 := by omega
                                      simpa [Nat.sub_add_cancel hoff] using m1_w17 ⟨n - 48350, hnfin⟩
                                    ·
                                      by_cases h18 : n < 48450
                                      · have hoff : 48400 ≤ n := by omega
                                        have hnfin : n - 48400 < 50 := by omega
                                        simpa [Nat.sub_add_cancel hoff] using m1_w18 ⟨n - 48400, hnfin⟩
                                      ·
                                        by_cases h19 : n < 48500
                                        · have hoff : 48450 ≤ n := by omega
                                          have hnfin : n - 48450 < 50 := by omega
                                          simpa [Nat.sub_add_cancel hoff] using m1_w19 ⟨n - 48450, hnfin⟩
                                        ·
                                          by_cases h20 : n < 48550
                                          · have hoff : 48500 ≤ n := by omega
                                            have hnfin : n - 48500 < 50 := by omega
                                            simpa [Nat.sub_add_cancel hoff] using m1_w20 ⟨n - 48500, hnfin⟩
                                          ·
                                            by_cases h21 : n < 48600
                                            · have hoff : 48550 ≤ n := by omega
                                              have hnfin : n - 48550 < 50 := by omega
                                              simpa [Nat.sub_add_cancel hoff] using m1_w21 ⟨n - 48550, hnfin⟩
                                            ·
                                              by_cases h22 : n < 48650
                                              · have hoff : 48600 ≤ n := by omega
                                                have hnfin : n - 48600 < 50 := by omega
                                                simpa [Nat.sub_add_cancel hoff] using m1_w22 ⟨n - 48600, hnfin⟩
                                              ·
                                                by_cases h23 : n < 48700
                                                · have hoff : 48650 ≤ n := by omega
                                                  have hnfin : n - 48650 < 50 := by omega
                                                  simpa [Nat.sub_add_cancel hoff] using m1_w23 ⟨n - 48650, hnfin⟩
                                                ·
                                                  by_cases h24 : n < 48750
                                                  · have hoff : 48700 ≤ n := by omega
                                                    have hnfin : n - 48700 < 50 := by omega
                                                    simpa [Nat.sub_add_cancel hoff] using m1_w24 ⟨n - 48700, hnfin⟩
                                                  ·
                                                    by_cases h25 : n < 48800
                                                    · have hoff : 48750 ≤ n := by omega
                                                      have hnfin : n - 48750 < 50 := by omega
                                                      simpa [Nat.sub_add_cancel hoff] using m1_w25 ⟨n - 48750, hnfin⟩
                                                    ·
                                                      by_cases h26 : n < 48850
                                                      · have hoff : 48800 ≤ n := by omega
                                                        have hnfin : n - 48800 < 50 := by omega
                                                        simpa [Nat.sub_add_cancel hoff] using m1_w26 ⟨n - 48800, hnfin⟩
                                                      ·
                                                        by_cases h27 : n < 48900
                                                        · have hoff : 48850 ≤ n := by omega
                                                          have hnfin : n - 48850 < 50 := by omega
                                                          simpa [Nat.sub_add_cancel hoff] using m1_w27 ⟨n - 48850, hnfin⟩
                                                        ·
                                                          by_cases h28 : n < 48950
                                                          · have hoff : 48900 ≤ n := by omega
                                                            have hnfin : n - 48900 < 50 := by omega
                                                            simpa [Nat.sub_add_cancel hoff] using m1_w28 ⟨n - 48900, hnfin⟩
                                                          ·
                                                            by_cases h29 : n < 49000
                                                            · have hoff : 48950 ≤ n := by omega
                                                              have hnfin : n - 48950 < 50 := by omega
                                                              simpa [Nat.sub_add_cancel hoff] using m1_w29 ⟨n - 48950, hnfin⟩
                                                            ·
                                                              by_cases h30 : n < 49050
                                                              · have hoff : 49000 ≤ n := by omega
                                                                have hnfin : n - 49000 < 50 := by omega
                                                                simpa [Nat.sub_add_cancel hoff] using m1_w30 ⟨n - 49000, hnfin⟩
                                                              ·
                                                                by_cases h31 : n < 49100
                                                                · have hoff : 49050 ≤ n := by omega
                                                                  have hnfin : n - 49050 < 50 := by omega
                                                                  simpa [Nat.sub_add_cancel hoff] using m1_w31 ⟨n - 49050, hnfin⟩
                                                                ·
                                                                  by_cases h32 : n < 49150
                                                                  · have hoff : 49100 ≤ n := by omega
                                                                    have hnfin : n - 49100 < 50 := by omega
                                                                    simpa [Nat.sub_add_cancel hoff] using m1_w32 ⟨n - 49100, hnfin⟩
                                                                  ·
                                                                    by_cases h33 : n < 49200
                                                                    · have hoff : 49150 ≤ n := by omega
                                                                      have hnfin : n - 49150 < 50 := by omega
                                                                      simpa [Nat.sub_add_cancel hoff] using m1_w33 ⟨n - 49150, hnfin⟩
                                                                    ·
                                                                      by_cases h34 : n < 49250
                                                                      · have hoff : 49200 ≤ n := by omega
                                                                        have hnfin : n - 49200 < 50 := by omega
                                                                        simpa [Nat.sub_add_cancel hoff] using m1_w34 ⟨n - 49200, hnfin⟩
                                                                      ·
                                                                        by_cases h35 : n < 49300
                                                                        · have hoff : 49250 ≤ n := by omega
                                                                          have hnfin : n - 49250 < 50 := by omega
                                                                          simpa [Nat.sub_add_cancel hoff] using m1_w35 ⟨n - 49250, hnfin⟩
                                                                        ·
                                                                          by_cases h36 : n < 49350
                                                                          · have hoff : 49300 ≤ n := by omega
                                                                            have hnfin : n - 49300 < 50 := by omega
                                                                            simpa [Nat.sub_add_cancel hoff] using m1_w36 ⟨n - 49300, hnfin⟩
                                                                          ·
                                                                            by_cases h37 : n < 49400
                                                                            · have hoff : 49350 ≤ n := by omega
                                                                              have hnfin : n - 49350 < 50 := by omega
                                                                              simpa [Nat.sub_add_cancel hoff] using m1_w37 ⟨n - 49350, hnfin⟩
                                                                            ·
                                                                              by_cases h38 : n < 49450
                                                                              · have hoff : 49400 ≤ n := by omega
                                                                                have hnfin : n - 49400 < 50 := by omega
                                                                                simpa [Nat.sub_add_cancel hoff] using m1_w38 ⟨n - 49400, hnfin⟩
                                                                              ·
                                                                                by_cases h39 : n < 49500
                                                                                · have hoff : 49450 ≤ n := by omega
                                                                                  have hnfin : n - 49450 < 50 := by omega
                                                                                  simpa [Nat.sub_add_cancel hoff] using m1_w39 ⟨n - 49450, hnfin⟩
                                                                                ·
                                                                                  by_cases h40 : n < 49550
                                                                                  · have hoff : 49500 ≤ n := by omega
                                                                                    have hnfin : n - 49500 < 50 := by omega
                                                                                    simpa [Nat.sub_add_cancel hoff] using m1_w40 ⟨n - 49500, hnfin⟩
                                                                                  ·
                                                                                    by_cases h41 : n < 49600
                                                                                    · have hoff : 49550 ≤ n := by omega
                                                                                      have hnfin : n - 49550 < 50 := by omega
                                                                                      simpa [Nat.sub_add_cancel hoff] using m1_w41 ⟨n - 49550, hnfin⟩
                                                                                    ·
                                                                                      by_cases h42 : n < 49650
                                                                                      · have hoff : 49600 ≤ n := by omega
                                                                                        have hnfin : n - 49600 < 50 := by omega
                                                                                        simpa [Nat.sub_add_cancel hoff] using m1_w42 ⟨n - 49600, hnfin⟩
                                                                                      ·
                                                                                        by_cases h43 : n < 49700
                                                                                        · have hoff : 49650 ≤ n := by omega
                                                                                          have hnfin : n - 49650 < 50 := by omega
                                                                                          simpa [Nat.sub_add_cancel hoff] using m1_w43 ⟨n - 49650, hnfin⟩
                                                                                        ·
                                                                                          by_cases h44 : n < 49750
                                                                                          · have hoff : 49700 ≤ n := by omega
                                                                                            have hnfin : n - 49700 < 50 := by omega
                                                                                            simpa [Nat.sub_add_cancel hoff] using m1_w44 ⟨n - 49700, hnfin⟩
                                                                                          ·
                                                                                            by_cases h45 : n < 49800
                                                                                            · have hoff : 49750 ≤ n := by omega
                                                                                              have hnfin : n - 49750 < 50 := by omega
                                                                                              simpa [Nat.sub_add_cancel hoff] using m1_w45 ⟨n - 49750, hnfin⟩
                                                                                            ·
                                                                                              by_cases h46 : n < 49850
                                                                                              · have hoff : 49800 ≤ n := by omega
                                                                                                have hnfin : n - 49800 < 50 := by omega
                                                                                                simpa [Nat.sub_add_cancel hoff] using m1_w46 ⟨n - 49800, hnfin⟩
                                                                                              ·
                                                                                                by_cases h47 : n < 49900
                                                                                                · have hoff : 49850 ≤ n := by omega
                                                                                                  have hnfin : n - 49850 < 50 := by omega
                                                                                                  simpa [Nat.sub_add_cancel hoff] using m1_w47 ⟨n - 49850, hnfin⟩
                                                                                                ·
                                                                                                  by_cases h48 : n < 49950
                                                                                                  · have hoff : 49900 ≤ n := by omega
                                                                                                    have hnfin : n - 49900 < 50 := by omega
                                                                                                    simpa [Nat.sub_add_cancel hoff] using m1_w48 ⟨n - 49900, hnfin⟩
                                                                                                  ·
                                                                                                    by_cases h49 : n < 50000
                                                                                                    · have hoff : 49950 ≤ n := by omega
                                                                                                      have hnfin : n - 49950 < 50 := by omega
                                                                                                      simpa [Nat.sub_add_cancel hoff] using m1_w49 ⟨n - 49950, hnfin⟩
                                                                                                    ·
                                                                                                      omega
end IntMul.Kappa.R8.Bit.Oppbank.LandMonoFixA19


