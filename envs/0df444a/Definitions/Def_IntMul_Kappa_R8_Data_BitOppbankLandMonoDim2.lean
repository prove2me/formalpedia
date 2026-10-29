-- Prove2me | Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankLandMonoDim2
-- name    : IntMul_Kappa_R8_Data_BitOppbankLandMonoDim2
-- status  : Definition
-- author  : @Ethan Cheung Wang
-- created : 2026-10-28T21:08:54.643302+00:00
-- url     : https://prove2.me/theorems/886c515d-824e-4c8e-ada6-3506f195c262
-- title:
--   Dim-gated densSup land mono pack 2
-- statement:
--   # Dim-gated densSup land certificates, pack 2
--
--   For densified windows covering roughly $[5000,7500)$,
--   $$
--   \dim F(\mathrm{arg}_i n)<\dim F(n)
--   \Rightarrow
--   \mathrm{densSupG}(\mathrm{arg}_i n)\mathbin{\&}\mathrm{densSupG}(n)=\mathrm{densSupG}(\mathrm{arg}_i n).
--   $$
--   `decide` on Fin 50 (no `native_decide`).
-- source:
--   R8 BitOppbank densSup_land_mono

-- LandMonoDim pack 2: dim-gated densSupG child-land on windows starting in offsets list
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

namespace IntMul.Kappa.R8.Bit.Oppbank.LandMonoDim2

private def arg0 (n : ℕ) : ℕ := Nat.land (argF n) 65535
private def arg1 (n : ℕ) : ℕ := Nat.shiftRight (argF n) 16

private theorem m0_w0 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 5000))) (dimF (n.val + 5000)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 5000))) (densSupG (n.val + 5000))) (densSupG (arg0 (n.val + 5000)))) = true := by decide
private theorem m1_w0 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 5000))) (dimF (n.val + 5000)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 5000))) (densSupG (n.val + 5000))) (densSupG (arg1 (n.val + 5000)))) = true := by decide
private theorem m0_w1 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 5050))) (dimF (n.val + 5050)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 5050))) (densSupG (n.val + 5050))) (densSupG (arg0 (n.val + 5050)))) = true := by decide
private theorem m1_w1 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 5050))) (dimF (n.val + 5050)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 5050))) (densSupG (n.val + 5050))) (densSupG (arg1 (n.val + 5050)))) = true := by decide
private theorem m0_w2 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 5100))) (dimF (n.val + 5100)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 5100))) (densSupG (n.val + 5100))) (densSupG (arg0 (n.val + 5100)))) = true := by decide
private theorem m1_w2 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 5100))) (dimF (n.val + 5100)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 5100))) (densSupG (n.val + 5100))) (densSupG (arg1 (n.val + 5100)))) = true := by decide
private theorem m0_w3 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 5150))) (dimF (n.val + 5150)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 5150))) (densSupG (n.val + 5150))) (densSupG (arg0 (n.val + 5150)))) = true := by decide
private theorem m1_w3 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 5150))) (dimF (n.val + 5150)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 5150))) (densSupG (n.val + 5150))) (densSupG (arg1 (n.val + 5150)))) = true := by decide
private theorem m0_w4 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 5200))) (dimF (n.val + 5200)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 5200))) (densSupG (n.val + 5200))) (densSupG (arg0 (n.val + 5200)))) = true := by decide
private theorem m1_w4 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 5200))) (dimF (n.val + 5200)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 5200))) (densSupG (n.val + 5200))) (densSupG (arg1 (n.val + 5200)))) = true := by decide
private theorem m0_w5 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 5250))) (dimF (n.val + 5250)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 5250))) (densSupG (n.val + 5250))) (densSupG (arg0 (n.val + 5250)))) = true := by decide
private theorem m1_w5 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 5250))) (dimF (n.val + 5250)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 5250))) (densSupG (n.val + 5250))) (densSupG (arg1 (n.val + 5250)))) = true := by decide
private theorem m0_w6 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 5300))) (dimF (n.val + 5300)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 5300))) (densSupG (n.val + 5300))) (densSupG (arg0 (n.val + 5300)))) = true := by decide
private theorem m1_w6 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 5300))) (dimF (n.val + 5300)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 5300))) (densSupG (n.val + 5300))) (densSupG (arg1 (n.val + 5300)))) = true := by decide
private theorem m0_w7 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 5350))) (dimF (n.val + 5350)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 5350))) (densSupG (n.val + 5350))) (densSupG (arg0 (n.val + 5350)))) = true := by decide
private theorem m1_w7 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 5350))) (dimF (n.val + 5350)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 5350))) (densSupG (n.val + 5350))) (densSupG (arg1 (n.val + 5350)))) = true := by decide
private theorem m0_w8 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 5400))) (dimF (n.val + 5400)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 5400))) (densSupG (n.val + 5400))) (densSupG (arg0 (n.val + 5400)))) = true := by decide
private theorem m1_w8 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 5400))) (dimF (n.val + 5400)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 5400))) (densSupG (n.val + 5400))) (densSupG (arg1 (n.val + 5400)))) = true := by decide
private theorem m0_w9 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 5450))) (dimF (n.val + 5450)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 5450))) (densSupG (n.val + 5450))) (densSupG (arg0 (n.val + 5450)))) = true := by decide
private theorem m1_w9 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 5450))) (dimF (n.val + 5450)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 5450))) (densSupG (n.val + 5450))) (densSupG (arg1 (n.val + 5450)))) = true := by decide
private theorem m0_w10 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 5500))) (dimF (n.val + 5500)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 5500))) (densSupG (n.val + 5500))) (densSupG (arg0 (n.val + 5500)))) = true := by decide
private theorem m1_w10 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 5500))) (dimF (n.val + 5500)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 5500))) (densSupG (n.val + 5500))) (densSupG (arg1 (n.val + 5500)))) = true := by decide
private theorem m0_w11 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 5550))) (dimF (n.val + 5550)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 5550))) (densSupG (n.val + 5550))) (densSupG (arg0 (n.val + 5550)))) = true := by decide
private theorem m1_w11 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 5550))) (dimF (n.val + 5550)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 5550))) (densSupG (n.val + 5550))) (densSupG (arg1 (n.val + 5550)))) = true := by decide
private theorem m0_w12 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 5600))) (dimF (n.val + 5600)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 5600))) (densSupG (n.val + 5600))) (densSupG (arg0 (n.val + 5600)))) = true := by decide
private theorem m1_w12 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 5600))) (dimF (n.val + 5600)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 5600))) (densSupG (n.val + 5600))) (densSupG (arg1 (n.val + 5600)))) = true := by decide
private theorem m0_w13 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 5650))) (dimF (n.val + 5650)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 5650))) (densSupG (n.val + 5650))) (densSupG (arg0 (n.val + 5650)))) = true := by decide
private theorem m1_w13 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 5650))) (dimF (n.val + 5650)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 5650))) (densSupG (n.val + 5650))) (densSupG (arg1 (n.val + 5650)))) = true := by decide
private theorem m0_w14 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 5700))) (dimF (n.val + 5700)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 5700))) (densSupG (n.val + 5700))) (densSupG (arg0 (n.val + 5700)))) = true := by decide
private theorem m1_w14 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 5700))) (dimF (n.val + 5700)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 5700))) (densSupG (n.val + 5700))) (densSupG (arg1 (n.val + 5700)))) = true := by decide
private theorem m0_w15 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 5750))) (dimF (n.val + 5750)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 5750))) (densSupG (n.val + 5750))) (densSupG (arg0 (n.val + 5750)))) = true := by decide
private theorem m1_w15 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 5750))) (dimF (n.val + 5750)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 5750))) (densSupG (n.val + 5750))) (densSupG (arg1 (n.val + 5750)))) = true := by decide
private theorem m0_w16 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 5800))) (dimF (n.val + 5800)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 5800))) (densSupG (n.val + 5800))) (densSupG (arg0 (n.val + 5800)))) = true := by decide
private theorem m1_w16 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 5800))) (dimF (n.val + 5800)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 5800))) (densSupG (n.val + 5800))) (densSupG (arg1 (n.val + 5800)))) = true := by decide
private theorem m0_w17 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 5850))) (dimF (n.val + 5850)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 5850))) (densSupG (n.val + 5850))) (densSupG (arg0 (n.val + 5850)))) = true := by decide
private theorem m1_w17 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 5850))) (dimF (n.val + 5850)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 5850))) (densSupG (n.val + 5850))) (densSupG (arg1 (n.val + 5850)))) = true := by decide
private theorem m0_w18 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 5900))) (dimF (n.val + 5900)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 5900))) (densSupG (n.val + 5900))) (densSupG (arg0 (n.val + 5900)))) = true := by decide
private theorem m1_w18 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 5900))) (dimF (n.val + 5900)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 5900))) (densSupG (n.val + 5900))) (densSupG (arg1 (n.val + 5900)))) = true := by decide
private theorem m0_w19 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 5950))) (dimF (n.val + 5950)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 5950))) (densSupG (n.val + 5950))) (densSupG (arg0 (n.val + 5950)))) = true := by decide
private theorem m1_w19 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 5950))) (dimF (n.val + 5950)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 5950))) (densSupG (n.val + 5950))) (densSupG (arg1 (n.val + 5950)))) = true := by decide
private theorem m0_w20 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 6000))) (dimF (n.val + 6000)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 6000))) (densSupG (n.val + 6000))) (densSupG (arg0 (n.val + 6000)))) = true := by decide
private theorem m1_w20 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 6000))) (dimF (n.val + 6000)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 6000))) (densSupG (n.val + 6000))) (densSupG (arg1 (n.val + 6000)))) = true := by decide
private theorem m0_w21 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 6050))) (dimF (n.val + 6050)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 6050))) (densSupG (n.val + 6050))) (densSupG (arg0 (n.val + 6050)))) = true := by decide
private theorem m1_w21 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 6050))) (dimF (n.val + 6050)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 6050))) (densSupG (n.val + 6050))) (densSupG (arg1 (n.val + 6050)))) = true := by decide
private theorem m0_w22 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 6100))) (dimF (n.val + 6100)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 6100))) (densSupG (n.val + 6100))) (densSupG (arg0 (n.val + 6100)))) = true := by decide
private theorem m1_w22 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 6100))) (dimF (n.val + 6100)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 6100))) (densSupG (n.val + 6100))) (densSupG (arg1 (n.val + 6100)))) = true := by decide
private theorem m0_w23 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 6150))) (dimF (n.val + 6150)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 6150))) (densSupG (n.val + 6150))) (densSupG (arg0 (n.val + 6150)))) = true := by decide
private theorem m1_w23 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 6150))) (dimF (n.val + 6150)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 6150))) (densSupG (n.val + 6150))) (densSupG (arg1 (n.val + 6150)))) = true := by decide
private theorem m0_w24 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 6200))) (dimF (n.val + 6200)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 6200))) (densSupG (n.val + 6200))) (densSupG (arg0 (n.val + 6200)))) = true := by decide
private theorem m1_w24 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 6200))) (dimF (n.val + 6200)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 6200))) (densSupG (n.val + 6200))) (densSupG (arg1 (n.val + 6200)))) = true := by decide
private theorem m0_w25 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 6250))) (dimF (n.val + 6250)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 6250))) (densSupG (n.val + 6250))) (densSupG (arg0 (n.val + 6250)))) = true := by decide
private theorem m1_w25 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 6250))) (dimF (n.val + 6250)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 6250))) (densSupG (n.val + 6250))) (densSupG (arg1 (n.val + 6250)))) = true := by decide
private theorem m0_w26 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 6300))) (dimF (n.val + 6300)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 6300))) (densSupG (n.val + 6300))) (densSupG (arg0 (n.val + 6300)))) = true := by decide
private theorem m1_w26 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 6300))) (dimF (n.val + 6300)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 6300))) (densSupG (n.val + 6300))) (densSupG (arg1 (n.val + 6300)))) = true := by decide
private theorem m0_w27 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 6350))) (dimF (n.val + 6350)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 6350))) (densSupG (n.val + 6350))) (densSupG (arg0 (n.val + 6350)))) = true := by decide
private theorem m1_w27 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 6350))) (dimF (n.val + 6350)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 6350))) (densSupG (n.val + 6350))) (densSupG (arg1 (n.val + 6350)))) = true := by decide
private theorem m0_w28 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 6400))) (dimF (n.val + 6400)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 6400))) (densSupG (n.val + 6400))) (densSupG (arg0 (n.val + 6400)))) = true := by decide
private theorem m1_w28 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 6400))) (dimF (n.val + 6400)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 6400))) (densSupG (n.val + 6400))) (densSupG (arg1 (n.val + 6400)))) = true := by decide
private theorem m0_w29 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 6450))) (dimF (n.val + 6450)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 6450))) (densSupG (n.val + 6450))) (densSupG (arg0 (n.val + 6450)))) = true := by decide
private theorem m1_w29 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 6450))) (dimF (n.val + 6450)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 6450))) (densSupG (n.val + 6450))) (densSupG (arg1 (n.val + 6450)))) = true := by decide
private theorem m0_w30 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 6500))) (dimF (n.val + 6500)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 6500))) (densSupG (n.val + 6500))) (densSupG (arg0 (n.val + 6500)))) = true := by decide
private theorem m1_w30 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 6500))) (dimF (n.val + 6500)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 6500))) (densSupG (n.val + 6500))) (densSupG (arg1 (n.val + 6500)))) = true := by decide
private theorem m0_w31 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 6550))) (dimF (n.val + 6550)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 6550))) (densSupG (n.val + 6550))) (densSupG (arg0 (n.val + 6550)))) = true := by decide
private theorem m1_w31 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 6550))) (dimF (n.val + 6550)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 6550))) (densSupG (n.val + 6550))) (densSupG (arg1 (n.val + 6550)))) = true := by decide
private theorem m0_w32 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 6600))) (dimF (n.val + 6600)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 6600))) (densSupG (n.val + 6600))) (densSupG (arg0 (n.val + 6600)))) = true := by decide
private theorem m1_w32 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 6600))) (dimF (n.val + 6600)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 6600))) (densSupG (n.val + 6600))) (densSupG (arg1 (n.val + 6600)))) = true := by decide
private theorem m0_w33 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 6650))) (dimF (n.val + 6650)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 6650))) (densSupG (n.val + 6650))) (densSupG (arg0 (n.val + 6650)))) = true := by decide
private theorem m1_w33 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 6650))) (dimF (n.val + 6650)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 6650))) (densSupG (n.val + 6650))) (densSupG (arg1 (n.val + 6650)))) = true := by decide
private theorem m0_w34 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 6700))) (dimF (n.val + 6700)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 6700))) (densSupG (n.val + 6700))) (densSupG (arg0 (n.val + 6700)))) = true := by decide
private theorem m1_w34 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 6700))) (dimF (n.val + 6700)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 6700))) (densSupG (n.val + 6700))) (densSupG (arg1 (n.val + 6700)))) = true := by decide
private theorem m0_w35 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 6750))) (dimF (n.val + 6750)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 6750))) (densSupG (n.val + 6750))) (densSupG (arg0 (n.val + 6750)))) = true := by decide
private theorem m1_w35 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 6750))) (dimF (n.val + 6750)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 6750))) (densSupG (n.val + 6750))) (densSupG (arg1 (n.val + 6750)))) = true := by decide
private theorem m0_w36 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 6800))) (dimF (n.val + 6800)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 6800))) (densSupG (n.val + 6800))) (densSupG (arg0 (n.val + 6800)))) = true := by decide
private theorem m1_w36 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 6800))) (dimF (n.val + 6800)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 6800))) (densSupG (n.val + 6800))) (densSupG (arg1 (n.val + 6800)))) = true := by decide
private theorem m0_w37 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 6850))) (dimF (n.val + 6850)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 6850))) (densSupG (n.val + 6850))) (densSupG (arg0 (n.val + 6850)))) = true := by decide
private theorem m1_w37 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 6850))) (dimF (n.val + 6850)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 6850))) (densSupG (n.val + 6850))) (densSupG (arg1 (n.val + 6850)))) = true := by decide
private theorem m0_w38 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 6900))) (dimF (n.val + 6900)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 6900))) (densSupG (n.val + 6900))) (densSupG (arg0 (n.val + 6900)))) = true := by decide
private theorem m1_w38 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 6900))) (dimF (n.val + 6900)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 6900))) (densSupG (n.val + 6900))) (densSupG (arg1 (n.val + 6900)))) = true := by decide
private theorem m0_w39 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 6950))) (dimF (n.val + 6950)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 6950))) (densSupG (n.val + 6950))) (densSupG (arg0 (n.val + 6950)))) = true := by decide
private theorem m1_w39 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 6950))) (dimF (n.val + 6950)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 6950))) (densSupG (n.val + 6950))) (densSupG (arg1 (n.val + 6950)))) = true := by decide
private theorem m0_w40 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 7000))) (dimF (n.val + 7000)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 7000))) (densSupG (n.val + 7000))) (densSupG (arg0 (n.val + 7000)))) = true := by decide
private theorem m1_w40 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 7000))) (dimF (n.val + 7000)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 7000))) (densSupG (n.val + 7000))) (densSupG (arg1 (n.val + 7000)))) = true := by decide
private theorem m0_w41 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 7050))) (dimF (n.val + 7050)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 7050))) (densSupG (n.val + 7050))) (densSupG (arg0 (n.val + 7050)))) = true := by decide
private theorem m1_w41 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 7050))) (dimF (n.val + 7050)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 7050))) (densSupG (n.val + 7050))) (densSupG (arg1 (n.val + 7050)))) = true := by decide
private theorem m0_w42 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 7100))) (dimF (n.val + 7100)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 7100))) (densSupG (n.val + 7100))) (densSupG (arg0 (n.val + 7100)))) = true := by decide
private theorem m1_w42 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 7100))) (dimF (n.val + 7100)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 7100))) (densSupG (n.val + 7100))) (densSupG (arg1 (n.val + 7100)))) = true := by decide
private theorem m0_w43 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 7150))) (dimF (n.val + 7150)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 7150))) (densSupG (n.val + 7150))) (densSupG (arg0 (n.val + 7150)))) = true := by decide
private theorem m1_w43 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 7150))) (dimF (n.val + 7150)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 7150))) (densSupG (n.val + 7150))) (densSupG (arg1 (n.val + 7150)))) = true := by decide
private theorem m0_w44 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 7200))) (dimF (n.val + 7200)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 7200))) (densSupG (n.val + 7200))) (densSupG (arg0 (n.val + 7200)))) = true := by decide
private theorem m1_w44 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 7200))) (dimF (n.val + 7200)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 7200))) (densSupG (n.val + 7200))) (densSupG (arg1 (n.val + 7200)))) = true := by decide
private theorem m0_w45 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 7250))) (dimF (n.val + 7250)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 7250))) (densSupG (n.val + 7250))) (densSupG (arg0 (n.val + 7250)))) = true := by decide
private theorem m1_w45 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 7250))) (dimF (n.val + 7250)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 7250))) (densSupG (n.val + 7250))) (densSupG (arg1 (n.val + 7250)))) = true := by decide
private theorem m0_w46 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 7300))) (dimF (n.val + 7300)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 7300))) (densSupG (n.val + 7300))) (densSupG (arg0 (n.val + 7300)))) = true := by decide
private theorem m1_w46 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 7300))) (dimF (n.val + 7300)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 7300))) (densSupG (n.val + 7300))) (densSupG (arg1 (n.val + 7300)))) = true := by decide
private theorem m0_w47 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 7350))) (dimF (n.val + 7350)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 7350))) (densSupG (n.val + 7350))) (densSupG (arg0 (n.val + 7350)))) = true := by decide
private theorem m1_w47 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 7350))) (dimF (n.val + 7350)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 7350))) (densSupG (n.val + 7350))) (densSupG (arg1 (n.val + 7350)))) = true := by decide
private theorem m0_w48 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 7400))) (dimF (n.val + 7400)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 7400))) (densSupG (n.val + 7400))) (densSupG (arg0 (n.val + 7400)))) = true := by decide
private theorem m1_w48 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 7400))) (dimF (n.val + 7400)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 7400))) (densSupG (n.val + 7400))) (densSupG (arg1 (n.val + 7400)))) = true := by decide
private theorem m0_w49 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 7450))) (dimF (n.val + 7450)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 7450))) (densSupG (n.val + 7450))) (densSupG (arg0 (n.val + 7450)))) = true := by decide
private theorem m1_w49 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 7450))) (dimF (n.val + 7450)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 7450))) (densSupG (n.val + 7450))) (densSupG (arg1 (n.val + 7450)))) = true := by decide

end IntMul.Kappa.R8.Bit.Oppbank.LandMonoDim2


