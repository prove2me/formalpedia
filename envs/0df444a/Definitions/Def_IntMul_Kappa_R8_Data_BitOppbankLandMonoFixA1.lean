-- Prove2me | Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankLandMonoFixA1
-- name    : IntMul_Kappa_R8_Data_BitOppbankLandMonoFixA1
-- status  : Definition
-- author  : @Ethan Cheung Wang
-- created : 2026-10-28T21:12:29.694028+00:00
-- url     : https://prove2.me/theorems/532934a5-5cb3-46bd-844f-b73385459f3e
-- title:
--   Dim-gated densSup land mono FixA pack 1
-- statement:
--   # Dim-gated densSup land (PndFix), pack A1
--
--   Range consolidators for $n\in[2500,5000)$.
-- source:
--   R8 BitOppbank PndFix

-- LandMonoFixA1: PUBLIC dim-gated land + range consolidators (PndFix)
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
namespace IntMul.Kappa.R8.Bit.Oppbank.LandMonoFixA1
def arg0 (n : ℕ) : ℕ := Nat.land (argF n) 65535
def arg1 (n : ℕ) : ℕ := Nat.shiftRight (argF n) 16
theorem m0_w0 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 2500))) (dimF (n.val + 2500)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 2500))) (densSupG (n.val + 2500))) (densSupG (arg0 (n.val + 2500)))) = true := by decide
theorem m1_w0 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 2500))) (dimF (n.val + 2500)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 2500))) (densSupG (n.val + 2500))) (densSupG (arg1 (n.val + 2500)))) = true := by decide
theorem m0_w1 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 2550))) (dimF (n.val + 2550)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 2550))) (densSupG (n.val + 2550))) (densSupG (arg0 (n.val + 2550)))) = true := by decide
theorem m1_w1 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 2550))) (dimF (n.val + 2550)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 2550))) (densSupG (n.val + 2550))) (densSupG (arg1 (n.val + 2550)))) = true := by decide
theorem m0_w2 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 2600))) (dimF (n.val + 2600)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 2600))) (densSupG (n.val + 2600))) (densSupG (arg0 (n.val + 2600)))) = true := by decide
theorem m1_w2 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 2600))) (dimF (n.val + 2600)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 2600))) (densSupG (n.val + 2600))) (densSupG (arg1 (n.val + 2600)))) = true := by decide
theorem m0_w3 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 2650))) (dimF (n.val + 2650)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 2650))) (densSupG (n.val + 2650))) (densSupG (arg0 (n.val + 2650)))) = true := by decide
theorem m1_w3 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 2650))) (dimF (n.val + 2650)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 2650))) (densSupG (n.val + 2650))) (densSupG (arg1 (n.val + 2650)))) = true := by decide
theorem m0_w4 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 2700))) (dimF (n.val + 2700)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 2700))) (densSupG (n.val + 2700))) (densSupG (arg0 (n.val + 2700)))) = true := by decide
theorem m1_w4 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 2700))) (dimF (n.val + 2700)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 2700))) (densSupG (n.val + 2700))) (densSupG (arg1 (n.val + 2700)))) = true := by decide
theorem m0_w5 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 2750))) (dimF (n.val + 2750)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 2750))) (densSupG (n.val + 2750))) (densSupG (arg0 (n.val + 2750)))) = true := by decide
theorem m1_w5 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 2750))) (dimF (n.val + 2750)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 2750))) (densSupG (n.val + 2750))) (densSupG (arg1 (n.val + 2750)))) = true := by decide
theorem m0_w6 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 2800))) (dimF (n.val + 2800)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 2800))) (densSupG (n.val + 2800))) (densSupG (arg0 (n.val + 2800)))) = true := by decide
theorem m1_w6 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 2800))) (dimF (n.val + 2800)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 2800))) (densSupG (n.val + 2800))) (densSupG (arg1 (n.val + 2800)))) = true := by decide
theorem m0_w7 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 2850))) (dimF (n.val + 2850)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 2850))) (densSupG (n.val + 2850))) (densSupG (arg0 (n.val + 2850)))) = true := by decide
theorem m1_w7 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 2850))) (dimF (n.val + 2850)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 2850))) (densSupG (n.val + 2850))) (densSupG (arg1 (n.val + 2850)))) = true := by decide
theorem m0_w8 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 2900))) (dimF (n.val + 2900)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 2900))) (densSupG (n.val + 2900))) (densSupG (arg0 (n.val + 2900)))) = true := by decide
theorem m1_w8 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 2900))) (dimF (n.val + 2900)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 2900))) (densSupG (n.val + 2900))) (densSupG (arg1 (n.val + 2900)))) = true := by decide
theorem m0_w9 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 2950))) (dimF (n.val + 2950)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 2950))) (densSupG (n.val + 2950))) (densSupG (arg0 (n.val + 2950)))) = true := by decide
theorem m1_w9 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 2950))) (dimF (n.val + 2950)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 2950))) (densSupG (n.val + 2950))) (densSupG (arg1 (n.val + 2950)))) = true := by decide
theorem m0_w10 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 3000))) (dimF (n.val + 3000)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 3000))) (densSupG (n.val + 3000))) (densSupG (arg0 (n.val + 3000)))) = true := by decide
theorem m1_w10 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 3000))) (dimF (n.val + 3000)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 3000))) (densSupG (n.val + 3000))) (densSupG (arg1 (n.val + 3000)))) = true := by decide
theorem m0_w11 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 3050))) (dimF (n.val + 3050)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 3050))) (densSupG (n.val + 3050))) (densSupG (arg0 (n.val + 3050)))) = true := by decide
theorem m1_w11 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 3050))) (dimF (n.val + 3050)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 3050))) (densSupG (n.val + 3050))) (densSupG (arg1 (n.val + 3050)))) = true := by decide
theorem m0_w12 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 3100))) (dimF (n.val + 3100)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 3100))) (densSupG (n.val + 3100))) (densSupG (arg0 (n.val + 3100)))) = true := by decide
theorem m1_w12 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 3100))) (dimF (n.val + 3100)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 3100))) (densSupG (n.val + 3100))) (densSupG (arg1 (n.val + 3100)))) = true := by decide
theorem m0_w13 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 3150))) (dimF (n.val + 3150)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 3150))) (densSupG (n.val + 3150))) (densSupG (arg0 (n.val + 3150)))) = true := by decide
theorem m1_w13 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 3150))) (dimF (n.val + 3150)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 3150))) (densSupG (n.val + 3150))) (densSupG (arg1 (n.val + 3150)))) = true := by decide
theorem m0_w14 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 3200))) (dimF (n.val + 3200)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 3200))) (densSupG (n.val + 3200))) (densSupG (arg0 (n.val + 3200)))) = true := by decide
theorem m1_w14 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 3200))) (dimF (n.val + 3200)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 3200))) (densSupG (n.val + 3200))) (densSupG (arg1 (n.val + 3200)))) = true := by decide
theorem m0_w15 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 3250))) (dimF (n.val + 3250)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 3250))) (densSupG (n.val + 3250))) (densSupG (arg0 (n.val + 3250)))) = true := by decide
theorem m1_w15 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 3250))) (dimF (n.val + 3250)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 3250))) (densSupG (n.val + 3250))) (densSupG (arg1 (n.val + 3250)))) = true := by decide
theorem m0_w16 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 3300))) (dimF (n.val + 3300)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 3300))) (densSupG (n.val + 3300))) (densSupG (arg0 (n.val + 3300)))) = true := by decide
theorem m1_w16 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 3300))) (dimF (n.val + 3300)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 3300))) (densSupG (n.val + 3300))) (densSupG (arg1 (n.val + 3300)))) = true := by decide
theorem m0_w17 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 3350))) (dimF (n.val + 3350)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 3350))) (densSupG (n.val + 3350))) (densSupG (arg0 (n.val + 3350)))) = true := by decide
theorem m1_w17 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 3350))) (dimF (n.val + 3350)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 3350))) (densSupG (n.val + 3350))) (densSupG (arg1 (n.val + 3350)))) = true := by decide
theorem m0_w18 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 3400))) (dimF (n.val + 3400)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 3400))) (densSupG (n.val + 3400))) (densSupG (arg0 (n.val + 3400)))) = true := by decide
theorem m1_w18 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 3400))) (dimF (n.val + 3400)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 3400))) (densSupG (n.val + 3400))) (densSupG (arg1 (n.val + 3400)))) = true := by decide
theorem m0_w19 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 3450))) (dimF (n.val + 3450)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 3450))) (densSupG (n.val + 3450))) (densSupG (arg0 (n.val + 3450)))) = true := by decide
theorem m1_w19 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 3450))) (dimF (n.val + 3450)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 3450))) (densSupG (n.val + 3450))) (densSupG (arg1 (n.val + 3450)))) = true := by decide
theorem m0_w20 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 3500))) (dimF (n.val + 3500)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 3500))) (densSupG (n.val + 3500))) (densSupG (arg0 (n.val + 3500)))) = true := by decide
theorem m1_w20 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 3500))) (dimF (n.val + 3500)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 3500))) (densSupG (n.val + 3500))) (densSupG (arg1 (n.val + 3500)))) = true := by decide
theorem m0_w21 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 3550))) (dimF (n.val + 3550)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 3550))) (densSupG (n.val + 3550))) (densSupG (arg0 (n.val + 3550)))) = true := by decide
theorem m1_w21 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 3550))) (dimF (n.val + 3550)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 3550))) (densSupG (n.val + 3550))) (densSupG (arg1 (n.val + 3550)))) = true := by decide
theorem m0_w22 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 3600))) (dimF (n.val + 3600)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 3600))) (densSupG (n.val + 3600))) (densSupG (arg0 (n.val + 3600)))) = true := by decide
theorem m1_w22 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 3600))) (dimF (n.val + 3600)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 3600))) (densSupG (n.val + 3600))) (densSupG (arg1 (n.val + 3600)))) = true := by decide
theorem m0_w23 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 3650))) (dimF (n.val + 3650)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 3650))) (densSupG (n.val + 3650))) (densSupG (arg0 (n.val + 3650)))) = true := by decide
theorem m1_w23 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 3650))) (dimF (n.val + 3650)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 3650))) (densSupG (n.val + 3650))) (densSupG (arg1 (n.val + 3650)))) = true := by decide
theorem m0_w24 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 3700))) (dimF (n.val + 3700)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 3700))) (densSupG (n.val + 3700))) (densSupG (arg0 (n.val + 3700)))) = true := by decide
theorem m1_w24 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 3700))) (dimF (n.val + 3700)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 3700))) (densSupG (n.val + 3700))) (densSupG (arg1 (n.val + 3700)))) = true := by decide
theorem m0_w25 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 3750))) (dimF (n.val + 3750)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 3750))) (densSupG (n.val + 3750))) (densSupG (arg0 (n.val + 3750)))) = true := by decide
theorem m1_w25 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 3750))) (dimF (n.val + 3750)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 3750))) (densSupG (n.val + 3750))) (densSupG (arg1 (n.val + 3750)))) = true := by decide
theorem m0_w26 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 3800))) (dimF (n.val + 3800)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 3800))) (densSupG (n.val + 3800))) (densSupG (arg0 (n.val + 3800)))) = true := by decide
theorem m1_w26 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 3800))) (dimF (n.val + 3800)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 3800))) (densSupG (n.val + 3800))) (densSupG (arg1 (n.val + 3800)))) = true := by decide
theorem m0_w27 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 3850))) (dimF (n.val + 3850)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 3850))) (densSupG (n.val + 3850))) (densSupG (arg0 (n.val + 3850)))) = true := by decide
theorem m1_w27 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 3850))) (dimF (n.val + 3850)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 3850))) (densSupG (n.val + 3850))) (densSupG (arg1 (n.val + 3850)))) = true := by decide
theorem m0_w28 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 3900))) (dimF (n.val + 3900)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 3900))) (densSupG (n.val + 3900))) (densSupG (arg0 (n.val + 3900)))) = true := by decide
theorem m1_w28 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 3900))) (dimF (n.val + 3900)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 3900))) (densSupG (n.val + 3900))) (densSupG (arg1 (n.val + 3900)))) = true := by decide
theorem m0_w29 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 3950))) (dimF (n.val + 3950)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 3950))) (densSupG (n.val + 3950))) (densSupG (arg0 (n.val + 3950)))) = true := by decide
theorem m1_w29 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 3950))) (dimF (n.val + 3950)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 3950))) (densSupG (n.val + 3950))) (densSupG (arg1 (n.val + 3950)))) = true := by decide
theorem m0_w30 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 4000))) (dimF (n.val + 4000)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 4000))) (densSupG (n.val + 4000))) (densSupG (arg0 (n.val + 4000)))) = true := by decide
theorem m1_w30 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 4000))) (dimF (n.val + 4000)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 4000))) (densSupG (n.val + 4000))) (densSupG (arg1 (n.val + 4000)))) = true := by decide
theorem m0_w31 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 4050))) (dimF (n.val + 4050)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 4050))) (densSupG (n.val + 4050))) (densSupG (arg0 (n.val + 4050)))) = true := by decide
theorem m1_w31 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 4050))) (dimF (n.val + 4050)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 4050))) (densSupG (n.val + 4050))) (densSupG (arg1 (n.val + 4050)))) = true := by decide
theorem m0_w32 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 4100))) (dimF (n.val + 4100)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 4100))) (densSupG (n.val + 4100))) (densSupG (arg0 (n.val + 4100)))) = true := by decide
theorem m1_w32 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 4100))) (dimF (n.val + 4100)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 4100))) (densSupG (n.val + 4100))) (densSupG (arg1 (n.val + 4100)))) = true := by decide
theorem m0_w33 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 4150))) (dimF (n.val + 4150)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 4150))) (densSupG (n.val + 4150))) (densSupG (arg0 (n.val + 4150)))) = true := by decide
theorem m1_w33 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 4150))) (dimF (n.val + 4150)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 4150))) (densSupG (n.val + 4150))) (densSupG (arg1 (n.val + 4150)))) = true := by decide
theorem m0_w34 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 4200))) (dimF (n.val + 4200)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 4200))) (densSupG (n.val + 4200))) (densSupG (arg0 (n.val + 4200)))) = true := by decide
theorem m1_w34 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 4200))) (dimF (n.val + 4200)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 4200))) (densSupG (n.val + 4200))) (densSupG (arg1 (n.val + 4200)))) = true := by decide
theorem m0_w35 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 4250))) (dimF (n.val + 4250)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 4250))) (densSupG (n.val + 4250))) (densSupG (arg0 (n.val + 4250)))) = true := by decide
theorem m1_w35 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 4250))) (dimF (n.val + 4250)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 4250))) (densSupG (n.val + 4250))) (densSupG (arg1 (n.val + 4250)))) = true := by decide
theorem m0_w36 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 4300))) (dimF (n.val + 4300)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 4300))) (densSupG (n.val + 4300))) (densSupG (arg0 (n.val + 4300)))) = true := by decide
theorem m1_w36 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 4300))) (dimF (n.val + 4300)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 4300))) (densSupG (n.val + 4300))) (densSupG (arg1 (n.val + 4300)))) = true := by decide
theorem m0_w37 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 4350))) (dimF (n.val + 4350)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 4350))) (densSupG (n.val + 4350))) (densSupG (arg0 (n.val + 4350)))) = true := by decide
theorem m1_w37 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 4350))) (dimF (n.val + 4350)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 4350))) (densSupG (n.val + 4350))) (densSupG (arg1 (n.val + 4350)))) = true := by decide
theorem m0_w38 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 4400))) (dimF (n.val + 4400)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 4400))) (densSupG (n.val + 4400))) (densSupG (arg0 (n.val + 4400)))) = true := by decide
theorem m1_w38 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 4400))) (dimF (n.val + 4400)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 4400))) (densSupG (n.val + 4400))) (densSupG (arg1 (n.val + 4400)))) = true := by decide
theorem m0_w39 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 4450))) (dimF (n.val + 4450)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 4450))) (densSupG (n.val + 4450))) (densSupG (arg0 (n.val + 4450)))) = true := by decide
theorem m1_w39 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 4450))) (dimF (n.val + 4450)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 4450))) (densSupG (n.val + 4450))) (densSupG (arg1 (n.val + 4450)))) = true := by decide
theorem m0_w40 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 4500))) (dimF (n.val + 4500)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 4500))) (densSupG (n.val + 4500))) (densSupG (arg0 (n.val + 4500)))) = true := by decide
theorem m1_w40 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 4500))) (dimF (n.val + 4500)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 4500))) (densSupG (n.val + 4500))) (densSupG (arg1 (n.val + 4500)))) = true := by decide
theorem m0_w41 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 4550))) (dimF (n.val + 4550)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 4550))) (densSupG (n.val + 4550))) (densSupG (arg0 (n.val + 4550)))) = true := by decide
theorem m1_w41 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 4550))) (dimF (n.val + 4550)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 4550))) (densSupG (n.val + 4550))) (densSupG (arg1 (n.val + 4550)))) = true := by decide
theorem m0_w42 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 4600))) (dimF (n.val + 4600)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 4600))) (densSupG (n.val + 4600))) (densSupG (arg0 (n.val + 4600)))) = true := by decide
theorem m1_w42 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 4600))) (dimF (n.val + 4600)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 4600))) (densSupG (n.val + 4600))) (densSupG (arg1 (n.val + 4600)))) = true := by decide
theorem m0_w43 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 4650))) (dimF (n.val + 4650)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 4650))) (densSupG (n.val + 4650))) (densSupG (arg0 (n.val + 4650)))) = true := by decide
theorem m1_w43 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 4650))) (dimF (n.val + 4650)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 4650))) (densSupG (n.val + 4650))) (densSupG (arg1 (n.val + 4650)))) = true := by decide
theorem m0_w44 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 4700))) (dimF (n.val + 4700)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 4700))) (densSupG (n.val + 4700))) (densSupG (arg0 (n.val + 4700)))) = true := by decide
theorem m1_w44 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 4700))) (dimF (n.val + 4700)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 4700))) (densSupG (n.val + 4700))) (densSupG (arg1 (n.val + 4700)))) = true := by decide
theorem m0_w45 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 4750))) (dimF (n.val + 4750)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 4750))) (densSupG (n.val + 4750))) (densSupG (arg0 (n.val + 4750)))) = true := by decide
theorem m1_w45 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 4750))) (dimF (n.val + 4750)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 4750))) (densSupG (n.val + 4750))) (densSupG (arg1 (n.val + 4750)))) = true := by decide
theorem m0_w46 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 4800))) (dimF (n.val + 4800)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 4800))) (densSupG (n.val + 4800))) (densSupG (arg0 (n.val + 4800)))) = true := by decide
theorem m1_w46 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 4800))) (dimF (n.val + 4800)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 4800))) (densSupG (n.val + 4800))) (densSupG (arg1 (n.val + 4800)))) = true := by decide
theorem m0_w47 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 4850))) (dimF (n.val + 4850)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 4850))) (densSupG (n.val + 4850))) (densSupG (arg0 (n.val + 4850)))) = true := by decide
theorem m1_w47 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 4850))) (dimF (n.val + 4850)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 4850))) (densSupG (n.val + 4850))) (densSupG (arg1 (n.val + 4850)))) = true := by decide
theorem m0_w48 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 4900))) (dimF (n.val + 4900)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 4900))) (densSupG (n.val + 4900))) (densSupG (arg0 (n.val + 4900)))) = true := by decide
theorem m1_w48 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 4900))) (dimF (n.val + 4900)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 4900))) (densSupG (n.val + 4900))) (densSupG (arg1 (n.val + 4900)))) = true := by decide
theorem m0_w49 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 4950))) (dimF (n.val + 4950)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 4950))) (densSupG (n.val + 4950))) (densSupG (arg0 (n.val + 4950)))) = true := by decide
theorem m1_w49 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 4950))) (dimF (n.val + 4950)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 4950))) (densSupG (n.val + 4950))) (densSupG (arg1 (n.val + 4950)))) = true := by decide
theorem land0_range (n : ℕ) (hn0 : 2500 ≤ n) (hn1 : n < 5000) :
    (!Nat.blt (dimF (arg0 n)) (dimF n) ||
      Nat.beq (Nat.land (densSupG (arg0 n)) (densSupG n)) (densSupG (arg0 n))) = true := by
  by_cases h0 : n < 2550
  · have hoff : 2500 ≤ n := by omega
    have hnfin : n - 2500 < 50 := by omega
    simpa [Nat.sub_add_cancel hoff] using m0_w0 ⟨n - 2500, hnfin⟩
  ·
    by_cases h1 : n < 2600
    · have hoff : 2550 ≤ n := by omega
      have hnfin : n - 2550 < 50 := by omega
      simpa [Nat.sub_add_cancel hoff] using m0_w1 ⟨n - 2550, hnfin⟩
    ·
      by_cases h2 : n < 2650
      · have hoff : 2600 ≤ n := by omega
        have hnfin : n - 2600 < 50 := by omega
        simpa [Nat.sub_add_cancel hoff] using m0_w2 ⟨n - 2600, hnfin⟩
      ·
        by_cases h3 : n < 2700
        · have hoff : 2650 ≤ n := by omega
          have hnfin : n - 2650 < 50 := by omega
          simpa [Nat.sub_add_cancel hoff] using m0_w3 ⟨n - 2650, hnfin⟩
        ·
          by_cases h4 : n < 2750
          · have hoff : 2700 ≤ n := by omega
            have hnfin : n - 2700 < 50 := by omega
            simpa [Nat.sub_add_cancel hoff] using m0_w4 ⟨n - 2700, hnfin⟩
          ·
            by_cases h5 : n < 2800
            · have hoff : 2750 ≤ n := by omega
              have hnfin : n - 2750 < 50 := by omega
              simpa [Nat.sub_add_cancel hoff] using m0_w5 ⟨n - 2750, hnfin⟩
            ·
              by_cases h6 : n < 2850
              · have hoff : 2800 ≤ n := by omega
                have hnfin : n - 2800 < 50 := by omega
                simpa [Nat.sub_add_cancel hoff] using m0_w6 ⟨n - 2800, hnfin⟩
              ·
                by_cases h7 : n < 2900
                · have hoff : 2850 ≤ n := by omega
                  have hnfin : n - 2850 < 50 := by omega
                  simpa [Nat.sub_add_cancel hoff] using m0_w7 ⟨n - 2850, hnfin⟩
                ·
                  by_cases h8 : n < 2950
                  · have hoff : 2900 ≤ n := by omega
                    have hnfin : n - 2900 < 50 := by omega
                    simpa [Nat.sub_add_cancel hoff] using m0_w8 ⟨n - 2900, hnfin⟩
                  ·
                    by_cases h9 : n < 3000
                    · have hoff : 2950 ≤ n := by omega
                      have hnfin : n - 2950 < 50 := by omega
                      simpa [Nat.sub_add_cancel hoff] using m0_w9 ⟨n - 2950, hnfin⟩
                    ·
                      by_cases h10 : n < 3050
                      · have hoff : 3000 ≤ n := by omega
                        have hnfin : n - 3000 < 50 := by omega
                        simpa [Nat.sub_add_cancel hoff] using m0_w10 ⟨n - 3000, hnfin⟩
                      ·
                        by_cases h11 : n < 3100
                        · have hoff : 3050 ≤ n := by omega
                          have hnfin : n - 3050 < 50 := by omega
                          simpa [Nat.sub_add_cancel hoff] using m0_w11 ⟨n - 3050, hnfin⟩
                        ·
                          by_cases h12 : n < 3150
                          · have hoff : 3100 ≤ n := by omega
                            have hnfin : n - 3100 < 50 := by omega
                            simpa [Nat.sub_add_cancel hoff] using m0_w12 ⟨n - 3100, hnfin⟩
                          ·
                            by_cases h13 : n < 3200
                            · have hoff : 3150 ≤ n := by omega
                              have hnfin : n - 3150 < 50 := by omega
                              simpa [Nat.sub_add_cancel hoff] using m0_w13 ⟨n - 3150, hnfin⟩
                            ·
                              by_cases h14 : n < 3250
                              · have hoff : 3200 ≤ n := by omega
                                have hnfin : n - 3200 < 50 := by omega
                                simpa [Nat.sub_add_cancel hoff] using m0_w14 ⟨n - 3200, hnfin⟩
                              ·
                                by_cases h15 : n < 3300
                                · have hoff : 3250 ≤ n := by omega
                                  have hnfin : n - 3250 < 50 := by omega
                                  simpa [Nat.sub_add_cancel hoff] using m0_w15 ⟨n - 3250, hnfin⟩
                                ·
                                  by_cases h16 : n < 3350
                                  · have hoff : 3300 ≤ n := by omega
                                    have hnfin : n - 3300 < 50 := by omega
                                    simpa [Nat.sub_add_cancel hoff] using m0_w16 ⟨n - 3300, hnfin⟩
                                  ·
                                    by_cases h17 : n < 3400
                                    · have hoff : 3350 ≤ n := by omega
                                      have hnfin : n - 3350 < 50 := by omega
                                      simpa [Nat.sub_add_cancel hoff] using m0_w17 ⟨n - 3350, hnfin⟩
                                    ·
                                      by_cases h18 : n < 3450
                                      · have hoff : 3400 ≤ n := by omega
                                        have hnfin : n - 3400 < 50 := by omega
                                        simpa [Nat.sub_add_cancel hoff] using m0_w18 ⟨n - 3400, hnfin⟩
                                      ·
                                        by_cases h19 : n < 3500
                                        · have hoff : 3450 ≤ n := by omega
                                          have hnfin : n - 3450 < 50 := by omega
                                          simpa [Nat.sub_add_cancel hoff] using m0_w19 ⟨n - 3450, hnfin⟩
                                        ·
                                          by_cases h20 : n < 3550
                                          · have hoff : 3500 ≤ n := by omega
                                            have hnfin : n - 3500 < 50 := by omega
                                            simpa [Nat.sub_add_cancel hoff] using m0_w20 ⟨n - 3500, hnfin⟩
                                          ·
                                            by_cases h21 : n < 3600
                                            · have hoff : 3550 ≤ n := by omega
                                              have hnfin : n - 3550 < 50 := by omega
                                              simpa [Nat.sub_add_cancel hoff] using m0_w21 ⟨n - 3550, hnfin⟩
                                            ·
                                              by_cases h22 : n < 3650
                                              · have hoff : 3600 ≤ n := by omega
                                                have hnfin : n - 3600 < 50 := by omega
                                                simpa [Nat.sub_add_cancel hoff] using m0_w22 ⟨n - 3600, hnfin⟩
                                              ·
                                                by_cases h23 : n < 3700
                                                · have hoff : 3650 ≤ n := by omega
                                                  have hnfin : n - 3650 < 50 := by omega
                                                  simpa [Nat.sub_add_cancel hoff] using m0_w23 ⟨n - 3650, hnfin⟩
                                                ·
                                                  by_cases h24 : n < 3750
                                                  · have hoff : 3700 ≤ n := by omega
                                                    have hnfin : n - 3700 < 50 := by omega
                                                    simpa [Nat.sub_add_cancel hoff] using m0_w24 ⟨n - 3700, hnfin⟩
                                                  ·
                                                    by_cases h25 : n < 3800
                                                    · have hoff : 3750 ≤ n := by omega
                                                      have hnfin : n - 3750 < 50 := by omega
                                                      simpa [Nat.sub_add_cancel hoff] using m0_w25 ⟨n - 3750, hnfin⟩
                                                    ·
                                                      by_cases h26 : n < 3850
                                                      · have hoff : 3800 ≤ n := by omega
                                                        have hnfin : n - 3800 < 50 := by omega
                                                        simpa [Nat.sub_add_cancel hoff] using m0_w26 ⟨n - 3800, hnfin⟩
                                                      ·
                                                        by_cases h27 : n < 3900
                                                        · have hoff : 3850 ≤ n := by omega
                                                          have hnfin : n - 3850 < 50 := by omega
                                                          simpa [Nat.sub_add_cancel hoff] using m0_w27 ⟨n - 3850, hnfin⟩
                                                        ·
                                                          by_cases h28 : n < 3950
                                                          · have hoff : 3900 ≤ n := by omega
                                                            have hnfin : n - 3900 < 50 := by omega
                                                            simpa [Nat.sub_add_cancel hoff] using m0_w28 ⟨n - 3900, hnfin⟩
                                                          ·
                                                            by_cases h29 : n < 4000
                                                            · have hoff : 3950 ≤ n := by omega
                                                              have hnfin : n - 3950 < 50 := by omega
                                                              simpa [Nat.sub_add_cancel hoff] using m0_w29 ⟨n - 3950, hnfin⟩
                                                            ·
                                                              by_cases h30 : n < 4050
                                                              · have hoff : 4000 ≤ n := by omega
                                                                have hnfin : n - 4000 < 50 := by omega
                                                                simpa [Nat.sub_add_cancel hoff] using m0_w30 ⟨n - 4000, hnfin⟩
                                                              ·
                                                                by_cases h31 : n < 4100
                                                                · have hoff : 4050 ≤ n := by omega
                                                                  have hnfin : n - 4050 < 50 := by omega
                                                                  simpa [Nat.sub_add_cancel hoff] using m0_w31 ⟨n - 4050, hnfin⟩
                                                                ·
                                                                  by_cases h32 : n < 4150
                                                                  · have hoff : 4100 ≤ n := by omega
                                                                    have hnfin : n - 4100 < 50 := by omega
                                                                    simpa [Nat.sub_add_cancel hoff] using m0_w32 ⟨n - 4100, hnfin⟩
                                                                  ·
                                                                    by_cases h33 : n < 4200
                                                                    · have hoff : 4150 ≤ n := by omega
                                                                      have hnfin : n - 4150 < 50 := by omega
                                                                      simpa [Nat.sub_add_cancel hoff] using m0_w33 ⟨n - 4150, hnfin⟩
                                                                    ·
                                                                      by_cases h34 : n < 4250
                                                                      · have hoff : 4200 ≤ n := by omega
                                                                        have hnfin : n - 4200 < 50 := by omega
                                                                        simpa [Nat.sub_add_cancel hoff] using m0_w34 ⟨n - 4200, hnfin⟩
                                                                      ·
                                                                        by_cases h35 : n < 4300
                                                                        · have hoff : 4250 ≤ n := by omega
                                                                          have hnfin : n - 4250 < 50 := by omega
                                                                          simpa [Nat.sub_add_cancel hoff] using m0_w35 ⟨n - 4250, hnfin⟩
                                                                        ·
                                                                          by_cases h36 : n < 4350
                                                                          · have hoff : 4300 ≤ n := by omega
                                                                            have hnfin : n - 4300 < 50 := by omega
                                                                            simpa [Nat.sub_add_cancel hoff] using m0_w36 ⟨n - 4300, hnfin⟩
                                                                          ·
                                                                            by_cases h37 : n < 4400
                                                                            · have hoff : 4350 ≤ n := by omega
                                                                              have hnfin : n - 4350 < 50 := by omega
                                                                              simpa [Nat.sub_add_cancel hoff] using m0_w37 ⟨n - 4350, hnfin⟩
                                                                            ·
                                                                              by_cases h38 : n < 4450
                                                                              · have hoff : 4400 ≤ n := by omega
                                                                                have hnfin : n - 4400 < 50 := by omega
                                                                                simpa [Nat.sub_add_cancel hoff] using m0_w38 ⟨n - 4400, hnfin⟩
                                                                              ·
                                                                                by_cases h39 : n < 4500
                                                                                · have hoff : 4450 ≤ n := by omega
                                                                                  have hnfin : n - 4450 < 50 := by omega
                                                                                  simpa [Nat.sub_add_cancel hoff] using m0_w39 ⟨n - 4450, hnfin⟩
                                                                                ·
                                                                                  by_cases h40 : n < 4550
                                                                                  · have hoff : 4500 ≤ n := by omega
                                                                                    have hnfin : n - 4500 < 50 := by omega
                                                                                    simpa [Nat.sub_add_cancel hoff] using m0_w40 ⟨n - 4500, hnfin⟩
                                                                                  ·
                                                                                    by_cases h41 : n < 4600
                                                                                    · have hoff : 4550 ≤ n := by omega
                                                                                      have hnfin : n - 4550 < 50 := by omega
                                                                                      simpa [Nat.sub_add_cancel hoff] using m0_w41 ⟨n - 4550, hnfin⟩
                                                                                    ·
                                                                                      by_cases h42 : n < 4650
                                                                                      · have hoff : 4600 ≤ n := by omega
                                                                                        have hnfin : n - 4600 < 50 := by omega
                                                                                        simpa [Nat.sub_add_cancel hoff] using m0_w42 ⟨n - 4600, hnfin⟩
                                                                                      ·
                                                                                        by_cases h43 : n < 4700
                                                                                        · have hoff : 4650 ≤ n := by omega
                                                                                          have hnfin : n - 4650 < 50 := by omega
                                                                                          simpa [Nat.sub_add_cancel hoff] using m0_w43 ⟨n - 4650, hnfin⟩
                                                                                        ·
                                                                                          by_cases h44 : n < 4750
                                                                                          · have hoff : 4700 ≤ n := by omega
                                                                                            have hnfin : n - 4700 < 50 := by omega
                                                                                            simpa [Nat.sub_add_cancel hoff] using m0_w44 ⟨n - 4700, hnfin⟩
                                                                                          ·
                                                                                            by_cases h45 : n < 4800
                                                                                            · have hoff : 4750 ≤ n := by omega
                                                                                              have hnfin : n - 4750 < 50 := by omega
                                                                                              simpa [Nat.sub_add_cancel hoff] using m0_w45 ⟨n - 4750, hnfin⟩
                                                                                            ·
                                                                                              by_cases h46 : n < 4850
                                                                                              · have hoff : 4800 ≤ n := by omega
                                                                                                have hnfin : n - 4800 < 50 := by omega
                                                                                                simpa [Nat.sub_add_cancel hoff] using m0_w46 ⟨n - 4800, hnfin⟩
                                                                                              ·
                                                                                                by_cases h47 : n < 4900
                                                                                                · have hoff : 4850 ≤ n := by omega
                                                                                                  have hnfin : n - 4850 < 50 := by omega
                                                                                                  simpa [Nat.sub_add_cancel hoff] using m0_w47 ⟨n - 4850, hnfin⟩
                                                                                                ·
                                                                                                  by_cases h48 : n < 4950
                                                                                                  · have hoff : 4900 ≤ n := by omega
                                                                                                    have hnfin : n - 4900 < 50 := by omega
                                                                                                    simpa [Nat.sub_add_cancel hoff] using m0_w48 ⟨n - 4900, hnfin⟩
                                                                                                  ·
                                                                                                    by_cases h49 : n < 5000
                                                                                                    · have hoff : 4950 ≤ n := by omega
                                                                                                      have hnfin : n - 4950 < 50 := by omega
                                                                                                      simpa [Nat.sub_add_cancel hoff] using m0_w49 ⟨n - 4950, hnfin⟩
                                                                                                    ·
                                                                                                      omega
theorem land1_range (n : ℕ) (hn0 : 2500 ≤ n) (hn1 : n < 5000) :
    (!Nat.blt (dimF (arg1 n)) (dimF n) ||
      Nat.beq (Nat.land (densSupG (arg1 n)) (densSupG n)) (densSupG (arg1 n))) = true := by
  by_cases h0 : n < 2550
  · have hoff : 2500 ≤ n := by omega
    have hnfin : n - 2500 < 50 := by omega
    simpa [Nat.sub_add_cancel hoff] using m1_w0 ⟨n - 2500, hnfin⟩
  ·
    by_cases h1 : n < 2600
    · have hoff : 2550 ≤ n := by omega
      have hnfin : n - 2550 < 50 := by omega
      simpa [Nat.sub_add_cancel hoff] using m1_w1 ⟨n - 2550, hnfin⟩
    ·
      by_cases h2 : n < 2650
      · have hoff : 2600 ≤ n := by omega
        have hnfin : n - 2600 < 50 := by omega
        simpa [Nat.sub_add_cancel hoff] using m1_w2 ⟨n - 2600, hnfin⟩
      ·
        by_cases h3 : n < 2700
        · have hoff : 2650 ≤ n := by omega
          have hnfin : n - 2650 < 50 := by omega
          simpa [Nat.sub_add_cancel hoff] using m1_w3 ⟨n - 2650, hnfin⟩
        ·
          by_cases h4 : n < 2750
          · have hoff : 2700 ≤ n := by omega
            have hnfin : n - 2700 < 50 := by omega
            simpa [Nat.sub_add_cancel hoff] using m1_w4 ⟨n - 2700, hnfin⟩
          ·
            by_cases h5 : n < 2800
            · have hoff : 2750 ≤ n := by omega
              have hnfin : n - 2750 < 50 := by omega
              simpa [Nat.sub_add_cancel hoff] using m1_w5 ⟨n - 2750, hnfin⟩
            ·
              by_cases h6 : n < 2850
              · have hoff : 2800 ≤ n := by omega
                have hnfin : n - 2800 < 50 := by omega
                simpa [Nat.sub_add_cancel hoff] using m1_w6 ⟨n - 2800, hnfin⟩
              ·
                by_cases h7 : n < 2900
                · have hoff : 2850 ≤ n := by omega
                  have hnfin : n - 2850 < 50 := by omega
                  simpa [Nat.sub_add_cancel hoff] using m1_w7 ⟨n - 2850, hnfin⟩
                ·
                  by_cases h8 : n < 2950
                  · have hoff : 2900 ≤ n := by omega
                    have hnfin : n - 2900 < 50 := by omega
                    simpa [Nat.sub_add_cancel hoff] using m1_w8 ⟨n - 2900, hnfin⟩
                  ·
                    by_cases h9 : n < 3000
                    · have hoff : 2950 ≤ n := by omega
                      have hnfin : n - 2950 < 50 := by omega
                      simpa [Nat.sub_add_cancel hoff] using m1_w9 ⟨n - 2950, hnfin⟩
                    ·
                      by_cases h10 : n < 3050
                      · have hoff : 3000 ≤ n := by omega
                        have hnfin : n - 3000 < 50 := by omega
                        simpa [Nat.sub_add_cancel hoff] using m1_w10 ⟨n - 3000, hnfin⟩
                      ·
                        by_cases h11 : n < 3100
                        · have hoff : 3050 ≤ n := by omega
                          have hnfin : n - 3050 < 50 := by omega
                          simpa [Nat.sub_add_cancel hoff] using m1_w11 ⟨n - 3050, hnfin⟩
                        ·
                          by_cases h12 : n < 3150
                          · have hoff : 3100 ≤ n := by omega
                            have hnfin : n - 3100 < 50 := by omega
                            simpa [Nat.sub_add_cancel hoff] using m1_w12 ⟨n - 3100, hnfin⟩
                          ·
                            by_cases h13 : n < 3200
                            · have hoff : 3150 ≤ n := by omega
                              have hnfin : n - 3150 < 50 := by omega
                              simpa [Nat.sub_add_cancel hoff] using m1_w13 ⟨n - 3150, hnfin⟩
                            ·
                              by_cases h14 : n < 3250
                              · have hoff : 3200 ≤ n := by omega
                                have hnfin : n - 3200 < 50 := by omega
                                simpa [Nat.sub_add_cancel hoff] using m1_w14 ⟨n - 3200, hnfin⟩
                              ·
                                by_cases h15 : n < 3300
                                · have hoff : 3250 ≤ n := by omega
                                  have hnfin : n - 3250 < 50 := by omega
                                  simpa [Nat.sub_add_cancel hoff] using m1_w15 ⟨n - 3250, hnfin⟩
                                ·
                                  by_cases h16 : n < 3350
                                  · have hoff : 3300 ≤ n := by omega
                                    have hnfin : n - 3300 < 50 := by omega
                                    simpa [Nat.sub_add_cancel hoff] using m1_w16 ⟨n - 3300, hnfin⟩
                                  ·
                                    by_cases h17 : n < 3400
                                    · have hoff : 3350 ≤ n := by omega
                                      have hnfin : n - 3350 < 50 := by omega
                                      simpa [Nat.sub_add_cancel hoff] using m1_w17 ⟨n - 3350, hnfin⟩
                                    ·
                                      by_cases h18 : n < 3450
                                      · have hoff : 3400 ≤ n := by omega
                                        have hnfin : n - 3400 < 50 := by omega
                                        simpa [Nat.sub_add_cancel hoff] using m1_w18 ⟨n - 3400, hnfin⟩
                                      ·
                                        by_cases h19 : n < 3500
                                        · have hoff : 3450 ≤ n := by omega
                                          have hnfin : n - 3450 < 50 := by omega
                                          simpa [Nat.sub_add_cancel hoff] using m1_w19 ⟨n - 3450, hnfin⟩
                                        ·
                                          by_cases h20 : n < 3550
                                          · have hoff : 3500 ≤ n := by omega
                                            have hnfin : n - 3500 < 50 := by omega
                                            simpa [Nat.sub_add_cancel hoff] using m1_w20 ⟨n - 3500, hnfin⟩
                                          ·
                                            by_cases h21 : n < 3600
                                            · have hoff : 3550 ≤ n := by omega
                                              have hnfin : n - 3550 < 50 := by omega
                                              simpa [Nat.sub_add_cancel hoff] using m1_w21 ⟨n - 3550, hnfin⟩
                                            ·
                                              by_cases h22 : n < 3650
                                              · have hoff : 3600 ≤ n := by omega
                                                have hnfin : n - 3600 < 50 := by omega
                                                simpa [Nat.sub_add_cancel hoff] using m1_w22 ⟨n - 3600, hnfin⟩
                                              ·
                                                by_cases h23 : n < 3700
                                                · have hoff : 3650 ≤ n := by omega
                                                  have hnfin : n - 3650 < 50 := by omega
                                                  simpa [Nat.sub_add_cancel hoff] using m1_w23 ⟨n - 3650, hnfin⟩
                                                ·
                                                  by_cases h24 : n < 3750
                                                  · have hoff : 3700 ≤ n := by omega
                                                    have hnfin : n - 3700 < 50 := by omega
                                                    simpa [Nat.sub_add_cancel hoff] using m1_w24 ⟨n - 3700, hnfin⟩
                                                  ·
                                                    by_cases h25 : n < 3800
                                                    · have hoff : 3750 ≤ n := by omega
                                                      have hnfin : n - 3750 < 50 := by omega
                                                      simpa [Nat.sub_add_cancel hoff] using m1_w25 ⟨n - 3750, hnfin⟩
                                                    ·
                                                      by_cases h26 : n < 3850
                                                      · have hoff : 3800 ≤ n := by omega
                                                        have hnfin : n - 3800 < 50 := by omega
                                                        simpa [Nat.sub_add_cancel hoff] using m1_w26 ⟨n - 3800, hnfin⟩
                                                      ·
                                                        by_cases h27 : n < 3900
                                                        · have hoff : 3850 ≤ n := by omega
                                                          have hnfin : n - 3850 < 50 := by omega
                                                          simpa [Nat.sub_add_cancel hoff] using m1_w27 ⟨n - 3850, hnfin⟩
                                                        ·
                                                          by_cases h28 : n < 3950
                                                          · have hoff : 3900 ≤ n := by omega
                                                            have hnfin : n - 3900 < 50 := by omega
                                                            simpa [Nat.sub_add_cancel hoff] using m1_w28 ⟨n - 3900, hnfin⟩
                                                          ·
                                                            by_cases h29 : n < 4000
                                                            · have hoff : 3950 ≤ n := by omega
                                                              have hnfin : n - 3950 < 50 := by omega
                                                              simpa [Nat.sub_add_cancel hoff] using m1_w29 ⟨n - 3950, hnfin⟩
                                                            ·
                                                              by_cases h30 : n < 4050
                                                              · have hoff : 4000 ≤ n := by omega
                                                                have hnfin : n - 4000 < 50 := by omega
                                                                simpa [Nat.sub_add_cancel hoff] using m1_w30 ⟨n - 4000, hnfin⟩
                                                              ·
                                                                by_cases h31 : n < 4100
                                                                · have hoff : 4050 ≤ n := by omega
                                                                  have hnfin : n - 4050 < 50 := by omega
                                                                  simpa [Nat.sub_add_cancel hoff] using m1_w31 ⟨n - 4050, hnfin⟩
                                                                ·
                                                                  by_cases h32 : n < 4150
                                                                  · have hoff : 4100 ≤ n := by omega
                                                                    have hnfin : n - 4100 < 50 := by omega
                                                                    simpa [Nat.sub_add_cancel hoff] using m1_w32 ⟨n - 4100, hnfin⟩
                                                                  ·
                                                                    by_cases h33 : n < 4200
                                                                    · have hoff : 4150 ≤ n := by omega
                                                                      have hnfin : n - 4150 < 50 := by omega
                                                                      simpa [Nat.sub_add_cancel hoff] using m1_w33 ⟨n - 4150, hnfin⟩
                                                                    ·
                                                                      by_cases h34 : n < 4250
                                                                      · have hoff : 4200 ≤ n := by omega
                                                                        have hnfin : n - 4200 < 50 := by omega
                                                                        simpa [Nat.sub_add_cancel hoff] using m1_w34 ⟨n - 4200, hnfin⟩
                                                                      ·
                                                                        by_cases h35 : n < 4300
                                                                        · have hoff : 4250 ≤ n := by omega
                                                                          have hnfin : n - 4250 < 50 := by omega
                                                                          simpa [Nat.sub_add_cancel hoff] using m1_w35 ⟨n - 4250, hnfin⟩
                                                                        ·
                                                                          by_cases h36 : n < 4350
                                                                          · have hoff : 4300 ≤ n := by omega
                                                                            have hnfin : n - 4300 < 50 := by omega
                                                                            simpa [Nat.sub_add_cancel hoff] using m1_w36 ⟨n - 4300, hnfin⟩
                                                                          ·
                                                                            by_cases h37 : n < 4400
                                                                            · have hoff : 4350 ≤ n := by omega
                                                                              have hnfin : n - 4350 < 50 := by omega
                                                                              simpa [Nat.sub_add_cancel hoff] using m1_w37 ⟨n - 4350, hnfin⟩
                                                                            ·
                                                                              by_cases h38 : n < 4450
                                                                              · have hoff : 4400 ≤ n := by omega
                                                                                have hnfin : n - 4400 < 50 := by omega
                                                                                simpa [Nat.sub_add_cancel hoff] using m1_w38 ⟨n - 4400, hnfin⟩
                                                                              ·
                                                                                by_cases h39 : n < 4500
                                                                                · have hoff : 4450 ≤ n := by omega
                                                                                  have hnfin : n - 4450 < 50 := by omega
                                                                                  simpa [Nat.sub_add_cancel hoff] using m1_w39 ⟨n - 4450, hnfin⟩
                                                                                ·
                                                                                  by_cases h40 : n < 4550
                                                                                  · have hoff : 4500 ≤ n := by omega
                                                                                    have hnfin : n - 4500 < 50 := by omega
                                                                                    simpa [Nat.sub_add_cancel hoff] using m1_w40 ⟨n - 4500, hnfin⟩
                                                                                  ·
                                                                                    by_cases h41 : n < 4600
                                                                                    · have hoff : 4550 ≤ n := by omega
                                                                                      have hnfin : n - 4550 < 50 := by omega
                                                                                      simpa [Nat.sub_add_cancel hoff] using m1_w41 ⟨n - 4550, hnfin⟩
                                                                                    ·
                                                                                      by_cases h42 : n < 4650
                                                                                      · have hoff : 4600 ≤ n := by omega
                                                                                        have hnfin : n - 4600 < 50 := by omega
                                                                                        simpa [Nat.sub_add_cancel hoff] using m1_w42 ⟨n - 4600, hnfin⟩
                                                                                      ·
                                                                                        by_cases h43 : n < 4700
                                                                                        · have hoff : 4650 ≤ n := by omega
                                                                                          have hnfin : n - 4650 < 50 := by omega
                                                                                          simpa [Nat.sub_add_cancel hoff] using m1_w43 ⟨n - 4650, hnfin⟩
                                                                                        ·
                                                                                          by_cases h44 : n < 4750
                                                                                          · have hoff : 4700 ≤ n := by omega
                                                                                            have hnfin : n - 4700 < 50 := by omega
                                                                                            simpa [Nat.sub_add_cancel hoff] using m1_w44 ⟨n - 4700, hnfin⟩
                                                                                          ·
                                                                                            by_cases h45 : n < 4800
                                                                                            · have hoff : 4750 ≤ n := by omega
                                                                                              have hnfin : n - 4750 < 50 := by omega
                                                                                              simpa [Nat.sub_add_cancel hoff] using m1_w45 ⟨n - 4750, hnfin⟩
                                                                                            ·
                                                                                              by_cases h46 : n < 4850
                                                                                              · have hoff : 4800 ≤ n := by omega
                                                                                                have hnfin : n - 4800 < 50 := by omega
                                                                                                simpa [Nat.sub_add_cancel hoff] using m1_w46 ⟨n - 4800, hnfin⟩
                                                                                              ·
                                                                                                by_cases h47 : n < 4900
                                                                                                · have hoff : 4850 ≤ n := by omega
                                                                                                  have hnfin : n - 4850 < 50 := by omega
                                                                                                  simpa [Nat.sub_add_cancel hoff] using m1_w47 ⟨n - 4850, hnfin⟩
                                                                                                ·
                                                                                                  by_cases h48 : n < 4950
                                                                                                  · have hoff : 4900 ≤ n := by omega
                                                                                                    have hnfin : n - 4900 < 50 := by omega
                                                                                                    simpa [Nat.sub_add_cancel hoff] using m1_w48 ⟨n - 4900, hnfin⟩
                                                                                                  ·
                                                                                                    by_cases h49 : n < 5000
                                                                                                    · have hoff : 4950 ≤ n := by omega
                                                                                                      have hnfin : n - 4950 < 50 := by omega
                                                                                                      simpa [Nat.sub_add_cancel hoff] using m1_w49 ⟨n - 4950, hnfin⟩
                                                                                                    ·
                                                                                                      omega
end IntMul.Kappa.R8.Bit.Oppbank.LandMonoFixA1


