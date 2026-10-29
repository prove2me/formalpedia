-- Prove2me | Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankLandMonoFixA2
-- name    : IntMul_Kappa_R8_Data_BitOppbankLandMonoFixA2
-- status  : Definition
-- author  : @Ethan Cheung Wang
-- created : 2026-10-28T21:13:36.820991+00:00
-- url     : https://prove2.me/theorems/5e282f46-7681-40b9-b4e7-5090883a482d
-- title:
--   Dim-gated densSup land mono FixA pack 2
-- statement:
--   # Dim-gated densSup land (PndFix), pack A2
--
--   Range consolidators for $n\in[5000,7500)$.
-- source:
--   R8 BitOppbank PndFix

-- LandMonoFixA2: PUBLIC dim-gated land + range consolidators (PndFix)
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
namespace IntMul.Kappa.R8.Bit.Oppbank.LandMonoFixA2
def arg0 (n : ℕ) : ℕ := Nat.land (argF n) 65535
def arg1 (n : ℕ) : ℕ := Nat.shiftRight (argF n) 16
theorem m0_w0 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 5000))) (dimF (n.val + 5000)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 5000))) (densSupG (n.val + 5000))) (densSupG (arg0 (n.val + 5000)))) = true := by decide
theorem m1_w0 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 5000))) (dimF (n.val + 5000)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 5000))) (densSupG (n.val + 5000))) (densSupG (arg1 (n.val + 5000)))) = true := by decide
theorem m0_w1 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 5050))) (dimF (n.val + 5050)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 5050))) (densSupG (n.val + 5050))) (densSupG (arg0 (n.val + 5050)))) = true := by decide
theorem m1_w1 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 5050))) (dimF (n.val + 5050)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 5050))) (densSupG (n.val + 5050))) (densSupG (arg1 (n.val + 5050)))) = true := by decide
theorem m0_w2 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 5100))) (dimF (n.val + 5100)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 5100))) (densSupG (n.val + 5100))) (densSupG (arg0 (n.val + 5100)))) = true := by decide
theorem m1_w2 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 5100))) (dimF (n.val + 5100)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 5100))) (densSupG (n.val + 5100))) (densSupG (arg1 (n.val + 5100)))) = true := by decide
theorem m0_w3 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 5150))) (dimF (n.val + 5150)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 5150))) (densSupG (n.val + 5150))) (densSupG (arg0 (n.val + 5150)))) = true := by decide
theorem m1_w3 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 5150))) (dimF (n.val + 5150)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 5150))) (densSupG (n.val + 5150))) (densSupG (arg1 (n.val + 5150)))) = true := by decide
theorem m0_w4 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 5200))) (dimF (n.val + 5200)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 5200))) (densSupG (n.val + 5200))) (densSupG (arg0 (n.val + 5200)))) = true := by decide
theorem m1_w4 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 5200))) (dimF (n.val + 5200)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 5200))) (densSupG (n.val + 5200))) (densSupG (arg1 (n.val + 5200)))) = true := by decide
theorem m0_w5 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 5250))) (dimF (n.val + 5250)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 5250))) (densSupG (n.val + 5250))) (densSupG (arg0 (n.val + 5250)))) = true := by decide
theorem m1_w5 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 5250))) (dimF (n.val + 5250)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 5250))) (densSupG (n.val + 5250))) (densSupG (arg1 (n.val + 5250)))) = true := by decide
theorem m0_w6 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 5300))) (dimF (n.val + 5300)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 5300))) (densSupG (n.val + 5300))) (densSupG (arg0 (n.val + 5300)))) = true := by decide
theorem m1_w6 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 5300))) (dimF (n.val + 5300)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 5300))) (densSupG (n.val + 5300))) (densSupG (arg1 (n.val + 5300)))) = true := by decide
theorem m0_w7 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 5350))) (dimF (n.val + 5350)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 5350))) (densSupG (n.val + 5350))) (densSupG (arg0 (n.val + 5350)))) = true := by decide
theorem m1_w7 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 5350))) (dimF (n.val + 5350)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 5350))) (densSupG (n.val + 5350))) (densSupG (arg1 (n.val + 5350)))) = true := by decide
theorem m0_w8 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 5400))) (dimF (n.val + 5400)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 5400))) (densSupG (n.val + 5400))) (densSupG (arg0 (n.val + 5400)))) = true := by decide
theorem m1_w8 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 5400))) (dimF (n.val + 5400)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 5400))) (densSupG (n.val + 5400))) (densSupG (arg1 (n.val + 5400)))) = true := by decide
theorem m0_w9 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 5450))) (dimF (n.val + 5450)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 5450))) (densSupG (n.val + 5450))) (densSupG (arg0 (n.val + 5450)))) = true := by decide
theorem m1_w9 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 5450))) (dimF (n.val + 5450)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 5450))) (densSupG (n.val + 5450))) (densSupG (arg1 (n.val + 5450)))) = true := by decide
theorem m0_w10 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 5500))) (dimF (n.val + 5500)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 5500))) (densSupG (n.val + 5500))) (densSupG (arg0 (n.val + 5500)))) = true := by decide
theorem m1_w10 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 5500))) (dimF (n.val + 5500)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 5500))) (densSupG (n.val + 5500))) (densSupG (arg1 (n.val + 5500)))) = true := by decide
theorem m0_w11 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 5550))) (dimF (n.val + 5550)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 5550))) (densSupG (n.val + 5550))) (densSupG (arg0 (n.val + 5550)))) = true := by decide
theorem m1_w11 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 5550))) (dimF (n.val + 5550)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 5550))) (densSupG (n.val + 5550))) (densSupG (arg1 (n.val + 5550)))) = true := by decide
theorem m0_w12 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 5600))) (dimF (n.val + 5600)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 5600))) (densSupG (n.val + 5600))) (densSupG (arg0 (n.val + 5600)))) = true := by decide
theorem m1_w12 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 5600))) (dimF (n.val + 5600)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 5600))) (densSupG (n.val + 5600))) (densSupG (arg1 (n.val + 5600)))) = true := by decide
theorem m0_w13 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 5650))) (dimF (n.val + 5650)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 5650))) (densSupG (n.val + 5650))) (densSupG (arg0 (n.val + 5650)))) = true := by decide
theorem m1_w13 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 5650))) (dimF (n.val + 5650)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 5650))) (densSupG (n.val + 5650))) (densSupG (arg1 (n.val + 5650)))) = true := by decide
theorem m0_w14 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 5700))) (dimF (n.val + 5700)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 5700))) (densSupG (n.val + 5700))) (densSupG (arg0 (n.val + 5700)))) = true := by decide
theorem m1_w14 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 5700))) (dimF (n.val + 5700)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 5700))) (densSupG (n.val + 5700))) (densSupG (arg1 (n.val + 5700)))) = true := by decide
theorem m0_w15 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 5750))) (dimF (n.val + 5750)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 5750))) (densSupG (n.val + 5750))) (densSupG (arg0 (n.val + 5750)))) = true := by decide
theorem m1_w15 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 5750))) (dimF (n.val + 5750)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 5750))) (densSupG (n.val + 5750))) (densSupG (arg1 (n.val + 5750)))) = true := by decide
theorem m0_w16 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 5800))) (dimF (n.val + 5800)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 5800))) (densSupG (n.val + 5800))) (densSupG (arg0 (n.val + 5800)))) = true := by decide
theorem m1_w16 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 5800))) (dimF (n.val + 5800)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 5800))) (densSupG (n.val + 5800))) (densSupG (arg1 (n.val + 5800)))) = true := by decide
theorem m0_w17 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 5850))) (dimF (n.val + 5850)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 5850))) (densSupG (n.val + 5850))) (densSupG (arg0 (n.val + 5850)))) = true := by decide
theorem m1_w17 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 5850))) (dimF (n.val + 5850)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 5850))) (densSupG (n.val + 5850))) (densSupG (arg1 (n.val + 5850)))) = true := by decide
theorem m0_w18 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 5900))) (dimF (n.val + 5900)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 5900))) (densSupG (n.val + 5900))) (densSupG (arg0 (n.val + 5900)))) = true := by decide
theorem m1_w18 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 5900))) (dimF (n.val + 5900)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 5900))) (densSupG (n.val + 5900))) (densSupG (arg1 (n.val + 5900)))) = true := by decide
theorem m0_w19 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 5950))) (dimF (n.val + 5950)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 5950))) (densSupG (n.val + 5950))) (densSupG (arg0 (n.val + 5950)))) = true := by decide
theorem m1_w19 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 5950))) (dimF (n.val + 5950)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 5950))) (densSupG (n.val + 5950))) (densSupG (arg1 (n.val + 5950)))) = true := by decide
theorem m0_w20 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 6000))) (dimF (n.val + 6000)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 6000))) (densSupG (n.val + 6000))) (densSupG (arg0 (n.val + 6000)))) = true := by decide
theorem m1_w20 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 6000))) (dimF (n.val + 6000)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 6000))) (densSupG (n.val + 6000))) (densSupG (arg1 (n.val + 6000)))) = true := by decide
theorem m0_w21 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 6050))) (dimF (n.val + 6050)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 6050))) (densSupG (n.val + 6050))) (densSupG (arg0 (n.val + 6050)))) = true := by decide
theorem m1_w21 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 6050))) (dimF (n.val + 6050)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 6050))) (densSupG (n.val + 6050))) (densSupG (arg1 (n.val + 6050)))) = true := by decide
theorem m0_w22 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 6100))) (dimF (n.val + 6100)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 6100))) (densSupG (n.val + 6100))) (densSupG (arg0 (n.val + 6100)))) = true := by decide
theorem m1_w22 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 6100))) (dimF (n.val + 6100)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 6100))) (densSupG (n.val + 6100))) (densSupG (arg1 (n.val + 6100)))) = true := by decide
theorem m0_w23 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 6150))) (dimF (n.val + 6150)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 6150))) (densSupG (n.val + 6150))) (densSupG (arg0 (n.val + 6150)))) = true := by decide
theorem m1_w23 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 6150))) (dimF (n.val + 6150)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 6150))) (densSupG (n.val + 6150))) (densSupG (arg1 (n.val + 6150)))) = true := by decide
theorem m0_w24 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 6200))) (dimF (n.val + 6200)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 6200))) (densSupG (n.val + 6200))) (densSupG (arg0 (n.val + 6200)))) = true := by decide
theorem m1_w24 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 6200))) (dimF (n.val + 6200)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 6200))) (densSupG (n.val + 6200))) (densSupG (arg1 (n.val + 6200)))) = true := by decide
theorem m0_w25 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 6250))) (dimF (n.val + 6250)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 6250))) (densSupG (n.val + 6250))) (densSupG (arg0 (n.val + 6250)))) = true := by decide
theorem m1_w25 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 6250))) (dimF (n.val + 6250)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 6250))) (densSupG (n.val + 6250))) (densSupG (arg1 (n.val + 6250)))) = true := by decide
theorem m0_w26 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 6300))) (dimF (n.val + 6300)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 6300))) (densSupG (n.val + 6300))) (densSupG (arg0 (n.val + 6300)))) = true := by decide
theorem m1_w26 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 6300))) (dimF (n.val + 6300)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 6300))) (densSupG (n.val + 6300))) (densSupG (arg1 (n.val + 6300)))) = true := by decide
theorem m0_w27 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 6350))) (dimF (n.val + 6350)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 6350))) (densSupG (n.val + 6350))) (densSupG (arg0 (n.val + 6350)))) = true := by decide
theorem m1_w27 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 6350))) (dimF (n.val + 6350)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 6350))) (densSupG (n.val + 6350))) (densSupG (arg1 (n.val + 6350)))) = true := by decide
theorem m0_w28 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 6400))) (dimF (n.val + 6400)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 6400))) (densSupG (n.val + 6400))) (densSupG (arg0 (n.val + 6400)))) = true := by decide
theorem m1_w28 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 6400))) (dimF (n.val + 6400)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 6400))) (densSupG (n.val + 6400))) (densSupG (arg1 (n.val + 6400)))) = true := by decide
theorem m0_w29 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 6450))) (dimF (n.val + 6450)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 6450))) (densSupG (n.val + 6450))) (densSupG (arg0 (n.val + 6450)))) = true := by decide
theorem m1_w29 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 6450))) (dimF (n.val + 6450)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 6450))) (densSupG (n.val + 6450))) (densSupG (arg1 (n.val + 6450)))) = true := by decide
theorem m0_w30 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 6500))) (dimF (n.val + 6500)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 6500))) (densSupG (n.val + 6500))) (densSupG (arg0 (n.val + 6500)))) = true := by decide
theorem m1_w30 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 6500))) (dimF (n.val + 6500)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 6500))) (densSupG (n.val + 6500))) (densSupG (arg1 (n.val + 6500)))) = true := by decide
theorem m0_w31 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 6550))) (dimF (n.val + 6550)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 6550))) (densSupG (n.val + 6550))) (densSupG (arg0 (n.val + 6550)))) = true := by decide
theorem m1_w31 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 6550))) (dimF (n.val + 6550)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 6550))) (densSupG (n.val + 6550))) (densSupG (arg1 (n.val + 6550)))) = true := by decide
theorem m0_w32 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 6600))) (dimF (n.val + 6600)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 6600))) (densSupG (n.val + 6600))) (densSupG (arg0 (n.val + 6600)))) = true := by decide
theorem m1_w32 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 6600))) (dimF (n.val + 6600)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 6600))) (densSupG (n.val + 6600))) (densSupG (arg1 (n.val + 6600)))) = true := by decide
theorem m0_w33 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 6650))) (dimF (n.val + 6650)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 6650))) (densSupG (n.val + 6650))) (densSupG (arg0 (n.val + 6650)))) = true := by decide
theorem m1_w33 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 6650))) (dimF (n.val + 6650)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 6650))) (densSupG (n.val + 6650))) (densSupG (arg1 (n.val + 6650)))) = true := by decide
theorem m0_w34 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 6700))) (dimF (n.val + 6700)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 6700))) (densSupG (n.val + 6700))) (densSupG (arg0 (n.val + 6700)))) = true := by decide
theorem m1_w34 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 6700))) (dimF (n.val + 6700)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 6700))) (densSupG (n.val + 6700))) (densSupG (arg1 (n.val + 6700)))) = true := by decide
theorem m0_w35 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 6750))) (dimF (n.val + 6750)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 6750))) (densSupG (n.val + 6750))) (densSupG (arg0 (n.val + 6750)))) = true := by decide
theorem m1_w35 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 6750))) (dimF (n.val + 6750)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 6750))) (densSupG (n.val + 6750))) (densSupG (arg1 (n.val + 6750)))) = true := by decide
theorem m0_w36 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 6800))) (dimF (n.val + 6800)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 6800))) (densSupG (n.val + 6800))) (densSupG (arg0 (n.val + 6800)))) = true := by decide
theorem m1_w36 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 6800))) (dimF (n.val + 6800)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 6800))) (densSupG (n.val + 6800))) (densSupG (arg1 (n.val + 6800)))) = true := by decide
theorem m0_w37 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 6850))) (dimF (n.val + 6850)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 6850))) (densSupG (n.val + 6850))) (densSupG (arg0 (n.val + 6850)))) = true := by decide
theorem m1_w37 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 6850))) (dimF (n.val + 6850)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 6850))) (densSupG (n.val + 6850))) (densSupG (arg1 (n.val + 6850)))) = true := by decide
theorem m0_w38 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 6900))) (dimF (n.val + 6900)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 6900))) (densSupG (n.val + 6900))) (densSupG (arg0 (n.val + 6900)))) = true := by decide
theorem m1_w38 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 6900))) (dimF (n.val + 6900)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 6900))) (densSupG (n.val + 6900))) (densSupG (arg1 (n.val + 6900)))) = true := by decide
theorem m0_w39 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 6950))) (dimF (n.val + 6950)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 6950))) (densSupG (n.val + 6950))) (densSupG (arg0 (n.val + 6950)))) = true := by decide
theorem m1_w39 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 6950))) (dimF (n.val + 6950)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 6950))) (densSupG (n.val + 6950))) (densSupG (arg1 (n.val + 6950)))) = true := by decide
theorem m0_w40 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 7000))) (dimF (n.val + 7000)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 7000))) (densSupG (n.val + 7000))) (densSupG (arg0 (n.val + 7000)))) = true := by decide
theorem m1_w40 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 7000))) (dimF (n.val + 7000)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 7000))) (densSupG (n.val + 7000))) (densSupG (arg1 (n.val + 7000)))) = true := by decide
theorem m0_w41 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 7050))) (dimF (n.val + 7050)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 7050))) (densSupG (n.val + 7050))) (densSupG (arg0 (n.val + 7050)))) = true := by decide
theorem m1_w41 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 7050))) (dimF (n.val + 7050)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 7050))) (densSupG (n.val + 7050))) (densSupG (arg1 (n.val + 7050)))) = true := by decide
theorem m0_w42 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 7100))) (dimF (n.val + 7100)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 7100))) (densSupG (n.val + 7100))) (densSupG (arg0 (n.val + 7100)))) = true := by decide
theorem m1_w42 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 7100))) (dimF (n.val + 7100)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 7100))) (densSupG (n.val + 7100))) (densSupG (arg1 (n.val + 7100)))) = true := by decide
theorem m0_w43 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 7150))) (dimF (n.val + 7150)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 7150))) (densSupG (n.val + 7150))) (densSupG (arg0 (n.val + 7150)))) = true := by decide
theorem m1_w43 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 7150))) (dimF (n.val + 7150)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 7150))) (densSupG (n.val + 7150))) (densSupG (arg1 (n.val + 7150)))) = true := by decide
theorem m0_w44 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 7200))) (dimF (n.val + 7200)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 7200))) (densSupG (n.val + 7200))) (densSupG (arg0 (n.val + 7200)))) = true := by decide
theorem m1_w44 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 7200))) (dimF (n.val + 7200)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 7200))) (densSupG (n.val + 7200))) (densSupG (arg1 (n.val + 7200)))) = true := by decide
theorem m0_w45 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 7250))) (dimF (n.val + 7250)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 7250))) (densSupG (n.val + 7250))) (densSupG (arg0 (n.val + 7250)))) = true := by decide
theorem m1_w45 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 7250))) (dimF (n.val + 7250)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 7250))) (densSupG (n.val + 7250))) (densSupG (arg1 (n.val + 7250)))) = true := by decide
theorem m0_w46 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 7300))) (dimF (n.val + 7300)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 7300))) (densSupG (n.val + 7300))) (densSupG (arg0 (n.val + 7300)))) = true := by decide
theorem m1_w46 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 7300))) (dimF (n.val + 7300)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 7300))) (densSupG (n.val + 7300))) (densSupG (arg1 (n.val + 7300)))) = true := by decide
theorem m0_w47 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 7350))) (dimF (n.val + 7350)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 7350))) (densSupG (n.val + 7350))) (densSupG (arg0 (n.val + 7350)))) = true := by decide
theorem m1_w47 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 7350))) (dimF (n.val + 7350)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 7350))) (densSupG (n.val + 7350))) (densSupG (arg1 (n.val + 7350)))) = true := by decide
theorem m0_w48 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 7400))) (dimF (n.val + 7400)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 7400))) (densSupG (n.val + 7400))) (densSupG (arg0 (n.val + 7400)))) = true := by decide
theorem m1_w48 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 7400))) (dimF (n.val + 7400)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 7400))) (densSupG (n.val + 7400))) (densSupG (arg1 (n.val + 7400)))) = true := by decide
theorem m0_w49 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 7450))) (dimF (n.val + 7450)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 7450))) (densSupG (n.val + 7450))) (densSupG (arg0 (n.val + 7450)))) = true := by decide
theorem m1_w49 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 7450))) (dimF (n.val + 7450)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 7450))) (densSupG (n.val + 7450))) (densSupG (arg1 (n.val + 7450)))) = true := by decide
theorem land0_range (n : ℕ) (hn0 : 5000 ≤ n) (hn1 : n < 7500) :
    (!Nat.blt (dimF (arg0 n)) (dimF n) ||
      Nat.beq (Nat.land (densSupG (arg0 n)) (densSupG n)) (densSupG (arg0 n))) = true := by
  by_cases h0 : n < 5050
  · have hoff : 5000 ≤ n := by omega
    have hnfin : n - 5000 < 50 := by omega
    simpa [Nat.sub_add_cancel hoff] using m0_w0 ⟨n - 5000, hnfin⟩
  ·
    by_cases h1 : n < 5100
    · have hoff : 5050 ≤ n := by omega
      have hnfin : n - 5050 < 50 := by omega
      simpa [Nat.sub_add_cancel hoff] using m0_w1 ⟨n - 5050, hnfin⟩
    ·
      by_cases h2 : n < 5150
      · have hoff : 5100 ≤ n := by omega
        have hnfin : n - 5100 < 50 := by omega
        simpa [Nat.sub_add_cancel hoff] using m0_w2 ⟨n - 5100, hnfin⟩
      ·
        by_cases h3 : n < 5200
        · have hoff : 5150 ≤ n := by omega
          have hnfin : n - 5150 < 50 := by omega
          simpa [Nat.sub_add_cancel hoff] using m0_w3 ⟨n - 5150, hnfin⟩
        ·
          by_cases h4 : n < 5250
          · have hoff : 5200 ≤ n := by omega
            have hnfin : n - 5200 < 50 := by omega
            simpa [Nat.sub_add_cancel hoff] using m0_w4 ⟨n - 5200, hnfin⟩
          ·
            by_cases h5 : n < 5300
            · have hoff : 5250 ≤ n := by omega
              have hnfin : n - 5250 < 50 := by omega
              simpa [Nat.sub_add_cancel hoff] using m0_w5 ⟨n - 5250, hnfin⟩
            ·
              by_cases h6 : n < 5350
              · have hoff : 5300 ≤ n := by omega
                have hnfin : n - 5300 < 50 := by omega
                simpa [Nat.sub_add_cancel hoff] using m0_w6 ⟨n - 5300, hnfin⟩
              ·
                by_cases h7 : n < 5400
                · have hoff : 5350 ≤ n := by omega
                  have hnfin : n - 5350 < 50 := by omega
                  simpa [Nat.sub_add_cancel hoff] using m0_w7 ⟨n - 5350, hnfin⟩
                ·
                  by_cases h8 : n < 5450
                  · have hoff : 5400 ≤ n := by omega
                    have hnfin : n - 5400 < 50 := by omega
                    simpa [Nat.sub_add_cancel hoff] using m0_w8 ⟨n - 5400, hnfin⟩
                  ·
                    by_cases h9 : n < 5500
                    · have hoff : 5450 ≤ n := by omega
                      have hnfin : n - 5450 < 50 := by omega
                      simpa [Nat.sub_add_cancel hoff] using m0_w9 ⟨n - 5450, hnfin⟩
                    ·
                      by_cases h10 : n < 5550
                      · have hoff : 5500 ≤ n := by omega
                        have hnfin : n - 5500 < 50 := by omega
                        simpa [Nat.sub_add_cancel hoff] using m0_w10 ⟨n - 5500, hnfin⟩
                      ·
                        by_cases h11 : n < 5600
                        · have hoff : 5550 ≤ n := by omega
                          have hnfin : n - 5550 < 50 := by omega
                          simpa [Nat.sub_add_cancel hoff] using m0_w11 ⟨n - 5550, hnfin⟩
                        ·
                          by_cases h12 : n < 5650
                          · have hoff : 5600 ≤ n := by omega
                            have hnfin : n - 5600 < 50 := by omega
                            simpa [Nat.sub_add_cancel hoff] using m0_w12 ⟨n - 5600, hnfin⟩
                          ·
                            by_cases h13 : n < 5700
                            · have hoff : 5650 ≤ n := by omega
                              have hnfin : n - 5650 < 50 := by omega
                              simpa [Nat.sub_add_cancel hoff] using m0_w13 ⟨n - 5650, hnfin⟩
                            ·
                              by_cases h14 : n < 5750
                              · have hoff : 5700 ≤ n := by omega
                                have hnfin : n - 5700 < 50 := by omega
                                simpa [Nat.sub_add_cancel hoff] using m0_w14 ⟨n - 5700, hnfin⟩
                              ·
                                by_cases h15 : n < 5800
                                · have hoff : 5750 ≤ n := by omega
                                  have hnfin : n - 5750 < 50 := by omega
                                  simpa [Nat.sub_add_cancel hoff] using m0_w15 ⟨n - 5750, hnfin⟩
                                ·
                                  by_cases h16 : n < 5850
                                  · have hoff : 5800 ≤ n := by omega
                                    have hnfin : n - 5800 < 50 := by omega
                                    simpa [Nat.sub_add_cancel hoff] using m0_w16 ⟨n - 5800, hnfin⟩
                                  ·
                                    by_cases h17 : n < 5900
                                    · have hoff : 5850 ≤ n := by omega
                                      have hnfin : n - 5850 < 50 := by omega
                                      simpa [Nat.sub_add_cancel hoff] using m0_w17 ⟨n - 5850, hnfin⟩
                                    ·
                                      by_cases h18 : n < 5950
                                      · have hoff : 5900 ≤ n := by omega
                                        have hnfin : n - 5900 < 50 := by omega
                                        simpa [Nat.sub_add_cancel hoff] using m0_w18 ⟨n - 5900, hnfin⟩
                                      ·
                                        by_cases h19 : n < 6000
                                        · have hoff : 5950 ≤ n := by omega
                                          have hnfin : n - 5950 < 50 := by omega
                                          simpa [Nat.sub_add_cancel hoff] using m0_w19 ⟨n - 5950, hnfin⟩
                                        ·
                                          by_cases h20 : n < 6050
                                          · have hoff : 6000 ≤ n := by omega
                                            have hnfin : n - 6000 < 50 := by omega
                                            simpa [Nat.sub_add_cancel hoff] using m0_w20 ⟨n - 6000, hnfin⟩
                                          ·
                                            by_cases h21 : n < 6100
                                            · have hoff : 6050 ≤ n := by omega
                                              have hnfin : n - 6050 < 50 := by omega
                                              simpa [Nat.sub_add_cancel hoff] using m0_w21 ⟨n - 6050, hnfin⟩
                                            ·
                                              by_cases h22 : n < 6150
                                              · have hoff : 6100 ≤ n := by omega
                                                have hnfin : n - 6100 < 50 := by omega
                                                simpa [Nat.sub_add_cancel hoff] using m0_w22 ⟨n - 6100, hnfin⟩
                                              ·
                                                by_cases h23 : n < 6200
                                                · have hoff : 6150 ≤ n := by omega
                                                  have hnfin : n - 6150 < 50 := by omega
                                                  simpa [Nat.sub_add_cancel hoff] using m0_w23 ⟨n - 6150, hnfin⟩
                                                ·
                                                  by_cases h24 : n < 6250
                                                  · have hoff : 6200 ≤ n := by omega
                                                    have hnfin : n - 6200 < 50 := by omega
                                                    simpa [Nat.sub_add_cancel hoff] using m0_w24 ⟨n - 6200, hnfin⟩
                                                  ·
                                                    by_cases h25 : n < 6300
                                                    · have hoff : 6250 ≤ n := by omega
                                                      have hnfin : n - 6250 < 50 := by omega
                                                      simpa [Nat.sub_add_cancel hoff] using m0_w25 ⟨n - 6250, hnfin⟩
                                                    ·
                                                      by_cases h26 : n < 6350
                                                      · have hoff : 6300 ≤ n := by omega
                                                        have hnfin : n - 6300 < 50 := by omega
                                                        simpa [Nat.sub_add_cancel hoff] using m0_w26 ⟨n - 6300, hnfin⟩
                                                      ·
                                                        by_cases h27 : n < 6400
                                                        · have hoff : 6350 ≤ n := by omega
                                                          have hnfin : n - 6350 < 50 := by omega
                                                          simpa [Nat.sub_add_cancel hoff] using m0_w27 ⟨n - 6350, hnfin⟩
                                                        ·
                                                          by_cases h28 : n < 6450
                                                          · have hoff : 6400 ≤ n := by omega
                                                            have hnfin : n - 6400 < 50 := by omega
                                                            simpa [Nat.sub_add_cancel hoff] using m0_w28 ⟨n - 6400, hnfin⟩
                                                          ·
                                                            by_cases h29 : n < 6500
                                                            · have hoff : 6450 ≤ n := by omega
                                                              have hnfin : n - 6450 < 50 := by omega
                                                              simpa [Nat.sub_add_cancel hoff] using m0_w29 ⟨n - 6450, hnfin⟩
                                                            ·
                                                              by_cases h30 : n < 6550
                                                              · have hoff : 6500 ≤ n := by omega
                                                                have hnfin : n - 6500 < 50 := by omega
                                                                simpa [Nat.sub_add_cancel hoff] using m0_w30 ⟨n - 6500, hnfin⟩
                                                              ·
                                                                by_cases h31 : n < 6600
                                                                · have hoff : 6550 ≤ n := by omega
                                                                  have hnfin : n - 6550 < 50 := by omega
                                                                  simpa [Nat.sub_add_cancel hoff] using m0_w31 ⟨n - 6550, hnfin⟩
                                                                ·
                                                                  by_cases h32 : n < 6650
                                                                  · have hoff : 6600 ≤ n := by omega
                                                                    have hnfin : n - 6600 < 50 := by omega
                                                                    simpa [Nat.sub_add_cancel hoff] using m0_w32 ⟨n - 6600, hnfin⟩
                                                                  ·
                                                                    by_cases h33 : n < 6700
                                                                    · have hoff : 6650 ≤ n := by omega
                                                                      have hnfin : n - 6650 < 50 := by omega
                                                                      simpa [Nat.sub_add_cancel hoff] using m0_w33 ⟨n - 6650, hnfin⟩
                                                                    ·
                                                                      by_cases h34 : n < 6750
                                                                      · have hoff : 6700 ≤ n := by omega
                                                                        have hnfin : n - 6700 < 50 := by omega
                                                                        simpa [Nat.sub_add_cancel hoff] using m0_w34 ⟨n - 6700, hnfin⟩
                                                                      ·
                                                                        by_cases h35 : n < 6800
                                                                        · have hoff : 6750 ≤ n := by omega
                                                                          have hnfin : n - 6750 < 50 := by omega
                                                                          simpa [Nat.sub_add_cancel hoff] using m0_w35 ⟨n - 6750, hnfin⟩
                                                                        ·
                                                                          by_cases h36 : n < 6850
                                                                          · have hoff : 6800 ≤ n := by omega
                                                                            have hnfin : n - 6800 < 50 := by omega
                                                                            simpa [Nat.sub_add_cancel hoff] using m0_w36 ⟨n - 6800, hnfin⟩
                                                                          ·
                                                                            by_cases h37 : n < 6900
                                                                            · have hoff : 6850 ≤ n := by omega
                                                                              have hnfin : n - 6850 < 50 := by omega
                                                                              simpa [Nat.sub_add_cancel hoff] using m0_w37 ⟨n - 6850, hnfin⟩
                                                                            ·
                                                                              by_cases h38 : n < 6950
                                                                              · have hoff : 6900 ≤ n := by omega
                                                                                have hnfin : n - 6900 < 50 := by omega
                                                                                simpa [Nat.sub_add_cancel hoff] using m0_w38 ⟨n - 6900, hnfin⟩
                                                                              ·
                                                                                by_cases h39 : n < 7000
                                                                                · have hoff : 6950 ≤ n := by omega
                                                                                  have hnfin : n - 6950 < 50 := by omega
                                                                                  simpa [Nat.sub_add_cancel hoff] using m0_w39 ⟨n - 6950, hnfin⟩
                                                                                ·
                                                                                  by_cases h40 : n < 7050
                                                                                  · have hoff : 7000 ≤ n := by omega
                                                                                    have hnfin : n - 7000 < 50 := by omega
                                                                                    simpa [Nat.sub_add_cancel hoff] using m0_w40 ⟨n - 7000, hnfin⟩
                                                                                  ·
                                                                                    by_cases h41 : n < 7100
                                                                                    · have hoff : 7050 ≤ n := by omega
                                                                                      have hnfin : n - 7050 < 50 := by omega
                                                                                      simpa [Nat.sub_add_cancel hoff] using m0_w41 ⟨n - 7050, hnfin⟩
                                                                                    ·
                                                                                      by_cases h42 : n < 7150
                                                                                      · have hoff : 7100 ≤ n := by omega
                                                                                        have hnfin : n - 7100 < 50 := by omega
                                                                                        simpa [Nat.sub_add_cancel hoff] using m0_w42 ⟨n - 7100, hnfin⟩
                                                                                      ·
                                                                                        by_cases h43 : n < 7200
                                                                                        · have hoff : 7150 ≤ n := by omega
                                                                                          have hnfin : n - 7150 < 50 := by omega
                                                                                          simpa [Nat.sub_add_cancel hoff] using m0_w43 ⟨n - 7150, hnfin⟩
                                                                                        ·
                                                                                          by_cases h44 : n < 7250
                                                                                          · have hoff : 7200 ≤ n := by omega
                                                                                            have hnfin : n - 7200 < 50 := by omega
                                                                                            simpa [Nat.sub_add_cancel hoff] using m0_w44 ⟨n - 7200, hnfin⟩
                                                                                          ·
                                                                                            by_cases h45 : n < 7300
                                                                                            · have hoff : 7250 ≤ n := by omega
                                                                                              have hnfin : n - 7250 < 50 := by omega
                                                                                              simpa [Nat.sub_add_cancel hoff] using m0_w45 ⟨n - 7250, hnfin⟩
                                                                                            ·
                                                                                              by_cases h46 : n < 7350
                                                                                              · have hoff : 7300 ≤ n := by omega
                                                                                                have hnfin : n - 7300 < 50 := by omega
                                                                                                simpa [Nat.sub_add_cancel hoff] using m0_w46 ⟨n - 7300, hnfin⟩
                                                                                              ·
                                                                                                by_cases h47 : n < 7400
                                                                                                · have hoff : 7350 ≤ n := by omega
                                                                                                  have hnfin : n - 7350 < 50 := by omega
                                                                                                  simpa [Nat.sub_add_cancel hoff] using m0_w47 ⟨n - 7350, hnfin⟩
                                                                                                ·
                                                                                                  by_cases h48 : n < 7450
                                                                                                  · have hoff : 7400 ≤ n := by omega
                                                                                                    have hnfin : n - 7400 < 50 := by omega
                                                                                                    simpa [Nat.sub_add_cancel hoff] using m0_w48 ⟨n - 7400, hnfin⟩
                                                                                                  ·
                                                                                                    by_cases h49 : n < 7500
                                                                                                    · have hoff : 7450 ≤ n := by omega
                                                                                                      have hnfin : n - 7450 < 50 := by omega
                                                                                                      simpa [Nat.sub_add_cancel hoff] using m0_w49 ⟨n - 7450, hnfin⟩
                                                                                                    ·
                                                                                                      omega
theorem land1_range (n : ℕ) (hn0 : 5000 ≤ n) (hn1 : n < 7500) :
    (!Nat.blt (dimF (arg1 n)) (dimF n) ||
      Nat.beq (Nat.land (densSupG (arg1 n)) (densSupG n)) (densSupG (arg1 n))) = true := by
  by_cases h0 : n < 5050
  · have hoff : 5000 ≤ n := by omega
    have hnfin : n - 5000 < 50 := by omega
    simpa [Nat.sub_add_cancel hoff] using m1_w0 ⟨n - 5000, hnfin⟩
  ·
    by_cases h1 : n < 5100
    · have hoff : 5050 ≤ n := by omega
      have hnfin : n - 5050 < 50 := by omega
      simpa [Nat.sub_add_cancel hoff] using m1_w1 ⟨n - 5050, hnfin⟩
    ·
      by_cases h2 : n < 5150
      · have hoff : 5100 ≤ n := by omega
        have hnfin : n - 5100 < 50 := by omega
        simpa [Nat.sub_add_cancel hoff] using m1_w2 ⟨n - 5100, hnfin⟩
      ·
        by_cases h3 : n < 5200
        · have hoff : 5150 ≤ n := by omega
          have hnfin : n - 5150 < 50 := by omega
          simpa [Nat.sub_add_cancel hoff] using m1_w3 ⟨n - 5150, hnfin⟩
        ·
          by_cases h4 : n < 5250
          · have hoff : 5200 ≤ n := by omega
            have hnfin : n - 5200 < 50 := by omega
            simpa [Nat.sub_add_cancel hoff] using m1_w4 ⟨n - 5200, hnfin⟩
          ·
            by_cases h5 : n < 5300
            · have hoff : 5250 ≤ n := by omega
              have hnfin : n - 5250 < 50 := by omega
              simpa [Nat.sub_add_cancel hoff] using m1_w5 ⟨n - 5250, hnfin⟩
            ·
              by_cases h6 : n < 5350
              · have hoff : 5300 ≤ n := by omega
                have hnfin : n - 5300 < 50 := by omega
                simpa [Nat.sub_add_cancel hoff] using m1_w6 ⟨n - 5300, hnfin⟩
              ·
                by_cases h7 : n < 5400
                · have hoff : 5350 ≤ n := by omega
                  have hnfin : n - 5350 < 50 := by omega
                  simpa [Nat.sub_add_cancel hoff] using m1_w7 ⟨n - 5350, hnfin⟩
                ·
                  by_cases h8 : n < 5450
                  · have hoff : 5400 ≤ n := by omega
                    have hnfin : n - 5400 < 50 := by omega
                    simpa [Nat.sub_add_cancel hoff] using m1_w8 ⟨n - 5400, hnfin⟩
                  ·
                    by_cases h9 : n < 5500
                    · have hoff : 5450 ≤ n := by omega
                      have hnfin : n - 5450 < 50 := by omega
                      simpa [Nat.sub_add_cancel hoff] using m1_w9 ⟨n - 5450, hnfin⟩
                    ·
                      by_cases h10 : n < 5550
                      · have hoff : 5500 ≤ n := by omega
                        have hnfin : n - 5500 < 50 := by omega
                        simpa [Nat.sub_add_cancel hoff] using m1_w10 ⟨n - 5500, hnfin⟩
                      ·
                        by_cases h11 : n < 5600
                        · have hoff : 5550 ≤ n := by omega
                          have hnfin : n - 5550 < 50 := by omega
                          simpa [Nat.sub_add_cancel hoff] using m1_w11 ⟨n - 5550, hnfin⟩
                        ·
                          by_cases h12 : n < 5650
                          · have hoff : 5600 ≤ n := by omega
                            have hnfin : n - 5600 < 50 := by omega
                            simpa [Nat.sub_add_cancel hoff] using m1_w12 ⟨n - 5600, hnfin⟩
                          ·
                            by_cases h13 : n < 5700
                            · have hoff : 5650 ≤ n := by omega
                              have hnfin : n - 5650 < 50 := by omega
                              simpa [Nat.sub_add_cancel hoff] using m1_w13 ⟨n - 5650, hnfin⟩
                            ·
                              by_cases h14 : n < 5750
                              · have hoff : 5700 ≤ n := by omega
                                have hnfin : n - 5700 < 50 := by omega
                                simpa [Nat.sub_add_cancel hoff] using m1_w14 ⟨n - 5700, hnfin⟩
                              ·
                                by_cases h15 : n < 5800
                                · have hoff : 5750 ≤ n := by omega
                                  have hnfin : n - 5750 < 50 := by omega
                                  simpa [Nat.sub_add_cancel hoff] using m1_w15 ⟨n - 5750, hnfin⟩
                                ·
                                  by_cases h16 : n < 5850
                                  · have hoff : 5800 ≤ n := by omega
                                    have hnfin : n - 5800 < 50 := by omega
                                    simpa [Nat.sub_add_cancel hoff] using m1_w16 ⟨n - 5800, hnfin⟩
                                  ·
                                    by_cases h17 : n < 5900
                                    · have hoff : 5850 ≤ n := by omega
                                      have hnfin : n - 5850 < 50 := by omega
                                      simpa [Nat.sub_add_cancel hoff] using m1_w17 ⟨n - 5850, hnfin⟩
                                    ·
                                      by_cases h18 : n < 5950
                                      · have hoff : 5900 ≤ n := by omega
                                        have hnfin : n - 5900 < 50 := by omega
                                        simpa [Nat.sub_add_cancel hoff] using m1_w18 ⟨n - 5900, hnfin⟩
                                      ·
                                        by_cases h19 : n < 6000
                                        · have hoff : 5950 ≤ n := by omega
                                          have hnfin : n - 5950 < 50 := by omega
                                          simpa [Nat.sub_add_cancel hoff] using m1_w19 ⟨n - 5950, hnfin⟩
                                        ·
                                          by_cases h20 : n < 6050
                                          · have hoff : 6000 ≤ n := by omega
                                            have hnfin : n - 6000 < 50 := by omega
                                            simpa [Nat.sub_add_cancel hoff] using m1_w20 ⟨n - 6000, hnfin⟩
                                          ·
                                            by_cases h21 : n < 6100
                                            · have hoff : 6050 ≤ n := by omega
                                              have hnfin : n - 6050 < 50 := by omega
                                              simpa [Nat.sub_add_cancel hoff] using m1_w21 ⟨n - 6050, hnfin⟩
                                            ·
                                              by_cases h22 : n < 6150
                                              · have hoff : 6100 ≤ n := by omega
                                                have hnfin : n - 6100 < 50 := by omega
                                                simpa [Nat.sub_add_cancel hoff] using m1_w22 ⟨n - 6100, hnfin⟩
                                              ·
                                                by_cases h23 : n < 6200
                                                · have hoff : 6150 ≤ n := by omega
                                                  have hnfin : n - 6150 < 50 := by omega
                                                  simpa [Nat.sub_add_cancel hoff] using m1_w23 ⟨n - 6150, hnfin⟩
                                                ·
                                                  by_cases h24 : n < 6250
                                                  · have hoff : 6200 ≤ n := by omega
                                                    have hnfin : n - 6200 < 50 := by omega
                                                    simpa [Nat.sub_add_cancel hoff] using m1_w24 ⟨n - 6200, hnfin⟩
                                                  ·
                                                    by_cases h25 : n < 6300
                                                    · have hoff : 6250 ≤ n := by omega
                                                      have hnfin : n - 6250 < 50 := by omega
                                                      simpa [Nat.sub_add_cancel hoff] using m1_w25 ⟨n - 6250, hnfin⟩
                                                    ·
                                                      by_cases h26 : n < 6350
                                                      · have hoff : 6300 ≤ n := by omega
                                                        have hnfin : n - 6300 < 50 := by omega
                                                        simpa [Nat.sub_add_cancel hoff] using m1_w26 ⟨n - 6300, hnfin⟩
                                                      ·
                                                        by_cases h27 : n < 6400
                                                        · have hoff : 6350 ≤ n := by omega
                                                          have hnfin : n - 6350 < 50 := by omega
                                                          simpa [Nat.sub_add_cancel hoff] using m1_w27 ⟨n - 6350, hnfin⟩
                                                        ·
                                                          by_cases h28 : n < 6450
                                                          · have hoff : 6400 ≤ n := by omega
                                                            have hnfin : n - 6400 < 50 := by omega
                                                            simpa [Nat.sub_add_cancel hoff] using m1_w28 ⟨n - 6400, hnfin⟩
                                                          ·
                                                            by_cases h29 : n < 6500
                                                            · have hoff : 6450 ≤ n := by omega
                                                              have hnfin : n - 6450 < 50 := by omega
                                                              simpa [Nat.sub_add_cancel hoff] using m1_w29 ⟨n - 6450, hnfin⟩
                                                            ·
                                                              by_cases h30 : n < 6550
                                                              · have hoff : 6500 ≤ n := by omega
                                                                have hnfin : n - 6500 < 50 := by omega
                                                                simpa [Nat.sub_add_cancel hoff] using m1_w30 ⟨n - 6500, hnfin⟩
                                                              ·
                                                                by_cases h31 : n < 6600
                                                                · have hoff : 6550 ≤ n := by omega
                                                                  have hnfin : n - 6550 < 50 := by omega
                                                                  simpa [Nat.sub_add_cancel hoff] using m1_w31 ⟨n - 6550, hnfin⟩
                                                                ·
                                                                  by_cases h32 : n < 6650
                                                                  · have hoff : 6600 ≤ n := by omega
                                                                    have hnfin : n - 6600 < 50 := by omega
                                                                    simpa [Nat.sub_add_cancel hoff] using m1_w32 ⟨n - 6600, hnfin⟩
                                                                  ·
                                                                    by_cases h33 : n < 6700
                                                                    · have hoff : 6650 ≤ n := by omega
                                                                      have hnfin : n - 6650 < 50 := by omega
                                                                      simpa [Nat.sub_add_cancel hoff] using m1_w33 ⟨n - 6650, hnfin⟩
                                                                    ·
                                                                      by_cases h34 : n < 6750
                                                                      · have hoff : 6700 ≤ n := by omega
                                                                        have hnfin : n - 6700 < 50 := by omega
                                                                        simpa [Nat.sub_add_cancel hoff] using m1_w34 ⟨n - 6700, hnfin⟩
                                                                      ·
                                                                        by_cases h35 : n < 6800
                                                                        · have hoff : 6750 ≤ n := by omega
                                                                          have hnfin : n - 6750 < 50 := by omega
                                                                          simpa [Nat.sub_add_cancel hoff] using m1_w35 ⟨n - 6750, hnfin⟩
                                                                        ·
                                                                          by_cases h36 : n < 6850
                                                                          · have hoff : 6800 ≤ n := by omega
                                                                            have hnfin : n - 6800 < 50 := by omega
                                                                            simpa [Nat.sub_add_cancel hoff] using m1_w36 ⟨n - 6800, hnfin⟩
                                                                          ·
                                                                            by_cases h37 : n < 6900
                                                                            · have hoff : 6850 ≤ n := by omega
                                                                              have hnfin : n - 6850 < 50 := by omega
                                                                              simpa [Nat.sub_add_cancel hoff] using m1_w37 ⟨n - 6850, hnfin⟩
                                                                            ·
                                                                              by_cases h38 : n < 6950
                                                                              · have hoff : 6900 ≤ n := by omega
                                                                                have hnfin : n - 6900 < 50 := by omega
                                                                                simpa [Nat.sub_add_cancel hoff] using m1_w38 ⟨n - 6900, hnfin⟩
                                                                              ·
                                                                                by_cases h39 : n < 7000
                                                                                · have hoff : 6950 ≤ n := by omega
                                                                                  have hnfin : n - 6950 < 50 := by omega
                                                                                  simpa [Nat.sub_add_cancel hoff] using m1_w39 ⟨n - 6950, hnfin⟩
                                                                                ·
                                                                                  by_cases h40 : n < 7050
                                                                                  · have hoff : 7000 ≤ n := by omega
                                                                                    have hnfin : n - 7000 < 50 := by omega
                                                                                    simpa [Nat.sub_add_cancel hoff] using m1_w40 ⟨n - 7000, hnfin⟩
                                                                                  ·
                                                                                    by_cases h41 : n < 7100
                                                                                    · have hoff : 7050 ≤ n := by omega
                                                                                      have hnfin : n - 7050 < 50 := by omega
                                                                                      simpa [Nat.sub_add_cancel hoff] using m1_w41 ⟨n - 7050, hnfin⟩
                                                                                    ·
                                                                                      by_cases h42 : n < 7150
                                                                                      · have hoff : 7100 ≤ n := by omega
                                                                                        have hnfin : n - 7100 < 50 := by omega
                                                                                        simpa [Nat.sub_add_cancel hoff] using m1_w42 ⟨n - 7100, hnfin⟩
                                                                                      ·
                                                                                        by_cases h43 : n < 7200
                                                                                        · have hoff : 7150 ≤ n := by omega
                                                                                          have hnfin : n - 7150 < 50 := by omega
                                                                                          simpa [Nat.sub_add_cancel hoff] using m1_w43 ⟨n - 7150, hnfin⟩
                                                                                        ·
                                                                                          by_cases h44 : n < 7250
                                                                                          · have hoff : 7200 ≤ n := by omega
                                                                                            have hnfin : n - 7200 < 50 := by omega
                                                                                            simpa [Nat.sub_add_cancel hoff] using m1_w44 ⟨n - 7200, hnfin⟩
                                                                                          ·
                                                                                            by_cases h45 : n < 7300
                                                                                            · have hoff : 7250 ≤ n := by omega
                                                                                              have hnfin : n - 7250 < 50 := by omega
                                                                                              simpa [Nat.sub_add_cancel hoff] using m1_w45 ⟨n - 7250, hnfin⟩
                                                                                            ·
                                                                                              by_cases h46 : n < 7350
                                                                                              · have hoff : 7300 ≤ n := by omega
                                                                                                have hnfin : n - 7300 < 50 := by omega
                                                                                                simpa [Nat.sub_add_cancel hoff] using m1_w46 ⟨n - 7300, hnfin⟩
                                                                                              ·
                                                                                                by_cases h47 : n < 7400
                                                                                                · have hoff : 7350 ≤ n := by omega
                                                                                                  have hnfin : n - 7350 < 50 := by omega
                                                                                                  simpa [Nat.sub_add_cancel hoff] using m1_w47 ⟨n - 7350, hnfin⟩
                                                                                                ·
                                                                                                  by_cases h48 : n < 7450
                                                                                                  · have hoff : 7400 ≤ n := by omega
                                                                                                    have hnfin : n - 7400 < 50 := by omega
                                                                                                    simpa [Nat.sub_add_cancel hoff] using m1_w48 ⟨n - 7400, hnfin⟩
                                                                                                  ·
                                                                                                    by_cases h49 : n < 7500
                                                                                                    · have hoff : 7450 ≤ n := by omega
                                                                                                      have hnfin : n - 7450 < 50 := by omega
                                                                                                      simpa [Nat.sub_add_cancel hoff] using m1_w49 ⟨n - 7450, hnfin⟩
                                                                                                    ·
                                                                                                      omega
end IntMul.Kappa.R8.Bit.Oppbank.LandMonoFixA2


