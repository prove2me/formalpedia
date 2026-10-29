-- Prove2me | Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankLandMonoDim0
-- name    : IntMul_Kappa_R8_Data_BitOppbankLandMonoDim0
-- status  : Definition
-- author  : @Ethan Cheung Wang
-- created : 2026-10-28T21:06:21.515807+00:00
-- url     : https://prove2.me/theorems/6e727d5a-5154-46ec-92a6-b5c942a8f54a
-- title:
--   Dim-gated densSup land mono pack 0
-- statement:
--   # Dim-gated densSup land certificates, pack 0
--
--   For densified indices $n$ in the first 50-width windows of $[0,nNodes)$,
--   $$
--   \dim F(\mathrm{arg}_i n)<\dim F(n)
--   \;\Rightarrow\;
--   \mathrm{densSupG}(\mathrm{arg}_i n)\mathbin{\&}\mathrm{densSupG}(n)=\mathrm{densSupG}(\mathrm{arg}_i n)
--   $$
--   ($i\in\{0,1\}$). Proved by `decide` on `Fin 50` (no `native_decide`).
-- source:
--   R8 BitOppbank densSup_land_mono

-- LandMonoDim pack 0: dim-gated densSupG child-land on windows starting in offsets list
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

namespace IntMul.Kappa.R8.Bit.Oppbank.LandMonoDim0

private def arg0 (n : ℕ) : ℕ := Nat.land (argF n) 65535
private def arg1 (n : ℕ) : ℕ := Nat.shiftRight (argF n) 16

private theorem m0_w0 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 0))) (dimF (n.val + 0)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 0))) (densSupG (n.val + 0))) (densSupG (arg0 (n.val + 0)))) = true := by decide
private theorem m1_w0 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 0))) (dimF (n.val + 0)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 0))) (densSupG (n.val + 0))) (densSupG (arg1 (n.val + 0)))) = true := by decide
private theorem m0_w1 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 50))) (dimF (n.val + 50)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 50))) (densSupG (n.val + 50))) (densSupG (arg0 (n.val + 50)))) = true := by decide
private theorem m1_w1 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 50))) (dimF (n.val + 50)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 50))) (densSupG (n.val + 50))) (densSupG (arg1 (n.val + 50)))) = true := by decide
private theorem m0_w2 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 100))) (dimF (n.val + 100)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 100))) (densSupG (n.val + 100))) (densSupG (arg0 (n.val + 100)))) = true := by decide
private theorem m1_w2 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 100))) (dimF (n.val + 100)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 100))) (densSupG (n.val + 100))) (densSupG (arg1 (n.val + 100)))) = true := by decide
private theorem m0_w3 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 150))) (dimF (n.val + 150)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 150))) (densSupG (n.val + 150))) (densSupG (arg0 (n.val + 150)))) = true := by decide
private theorem m1_w3 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 150))) (dimF (n.val + 150)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 150))) (densSupG (n.val + 150))) (densSupG (arg1 (n.val + 150)))) = true := by decide
private theorem m0_w4 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 200))) (dimF (n.val + 200)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 200))) (densSupG (n.val + 200))) (densSupG (arg0 (n.val + 200)))) = true := by decide
private theorem m1_w4 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 200))) (dimF (n.val + 200)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 200))) (densSupG (n.val + 200))) (densSupG (arg1 (n.val + 200)))) = true := by decide
private theorem m0_w5 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 250))) (dimF (n.val + 250)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 250))) (densSupG (n.val + 250))) (densSupG (arg0 (n.val + 250)))) = true := by decide
private theorem m1_w5 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 250))) (dimF (n.val + 250)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 250))) (densSupG (n.val + 250))) (densSupG (arg1 (n.val + 250)))) = true := by decide
private theorem m0_w6 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 300))) (dimF (n.val + 300)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 300))) (densSupG (n.val + 300))) (densSupG (arg0 (n.val + 300)))) = true := by decide
private theorem m1_w6 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 300))) (dimF (n.val + 300)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 300))) (densSupG (n.val + 300))) (densSupG (arg1 (n.val + 300)))) = true := by decide
private theorem m0_w7 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 350))) (dimF (n.val + 350)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 350))) (densSupG (n.val + 350))) (densSupG (arg0 (n.val + 350)))) = true := by decide
private theorem m1_w7 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 350))) (dimF (n.val + 350)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 350))) (densSupG (n.val + 350))) (densSupG (arg1 (n.val + 350)))) = true := by decide
private theorem m0_w8 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 400))) (dimF (n.val + 400)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 400))) (densSupG (n.val + 400))) (densSupG (arg0 (n.val + 400)))) = true := by decide
private theorem m1_w8 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 400))) (dimF (n.val + 400)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 400))) (densSupG (n.val + 400))) (densSupG (arg1 (n.val + 400)))) = true := by decide
private theorem m0_w9 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 450))) (dimF (n.val + 450)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 450))) (densSupG (n.val + 450))) (densSupG (arg0 (n.val + 450)))) = true := by decide
private theorem m1_w9 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 450))) (dimF (n.val + 450)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 450))) (densSupG (n.val + 450))) (densSupG (arg1 (n.val + 450)))) = true := by decide
private theorem m0_w10 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 500))) (dimF (n.val + 500)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 500))) (densSupG (n.val + 500))) (densSupG (arg0 (n.val + 500)))) = true := by decide
private theorem m1_w10 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 500))) (dimF (n.val + 500)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 500))) (densSupG (n.val + 500))) (densSupG (arg1 (n.val + 500)))) = true := by decide
private theorem m0_w11 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 550))) (dimF (n.val + 550)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 550))) (densSupG (n.val + 550))) (densSupG (arg0 (n.val + 550)))) = true := by decide
private theorem m1_w11 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 550))) (dimF (n.val + 550)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 550))) (densSupG (n.val + 550))) (densSupG (arg1 (n.val + 550)))) = true := by decide
private theorem m0_w12 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 600))) (dimF (n.val + 600)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 600))) (densSupG (n.val + 600))) (densSupG (arg0 (n.val + 600)))) = true := by decide
private theorem m1_w12 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 600))) (dimF (n.val + 600)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 600))) (densSupG (n.val + 600))) (densSupG (arg1 (n.val + 600)))) = true := by decide
private theorem m0_w13 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 650))) (dimF (n.val + 650)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 650))) (densSupG (n.val + 650))) (densSupG (arg0 (n.val + 650)))) = true := by decide
private theorem m1_w13 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 650))) (dimF (n.val + 650)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 650))) (densSupG (n.val + 650))) (densSupG (arg1 (n.val + 650)))) = true := by decide
private theorem m0_w14 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 700))) (dimF (n.val + 700)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 700))) (densSupG (n.val + 700))) (densSupG (arg0 (n.val + 700)))) = true := by decide
private theorem m1_w14 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 700))) (dimF (n.val + 700)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 700))) (densSupG (n.val + 700))) (densSupG (arg1 (n.val + 700)))) = true := by decide
private theorem m0_w15 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 750))) (dimF (n.val + 750)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 750))) (densSupG (n.val + 750))) (densSupG (arg0 (n.val + 750)))) = true := by decide
private theorem m1_w15 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 750))) (dimF (n.val + 750)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 750))) (densSupG (n.val + 750))) (densSupG (arg1 (n.val + 750)))) = true := by decide
private theorem m0_w16 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 800))) (dimF (n.val + 800)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 800))) (densSupG (n.val + 800))) (densSupG (arg0 (n.val + 800)))) = true := by decide
private theorem m1_w16 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 800))) (dimF (n.val + 800)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 800))) (densSupG (n.val + 800))) (densSupG (arg1 (n.val + 800)))) = true := by decide
private theorem m0_w17 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 850))) (dimF (n.val + 850)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 850))) (densSupG (n.val + 850))) (densSupG (arg0 (n.val + 850)))) = true := by decide
private theorem m1_w17 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 850))) (dimF (n.val + 850)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 850))) (densSupG (n.val + 850))) (densSupG (arg1 (n.val + 850)))) = true := by decide
private theorem m0_w18 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 900))) (dimF (n.val + 900)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 900))) (densSupG (n.val + 900))) (densSupG (arg0 (n.val + 900)))) = true := by decide
private theorem m1_w18 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 900))) (dimF (n.val + 900)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 900))) (densSupG (n.val + 900))) (densSupG (arg1 (n.val + 900)))) = true := by decide
private theorem m0_w19 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 950))) (dimF (n.val + 950)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 950))) (densSupG (n.val + 950))) (densSupG (arg0 (n.val + 950)))) = true := by decide
private theorem m1_w19 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 950))) (dimF (n.val + 950)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 950))) (densSupG (n.val + 950))) (densSupG (arg1 (n.val + 950)))) = true := by decide
private theorem m0_w20 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 1000))) (dimF (n.val + 1000)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 1000))) (densSupG (n.val + 1000))) (densSupG (arg0 (n.val + 1000)))) = true := by decide
private theorem m1_w20 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 1000))) (dimF (n.val + 1000)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 1000))) (densSupG (n.val + 1000))) (densSupG (arg1 (n.val + 1000)))) = true := by decide
private theorem m0_w21 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 1050))) (dimF (n.val + 1050)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 1050))) (densSupG (n.val + 1050))) (densSupG (arg0 (n.val + 1050)))) = true := by decide
private theorem m1_w21 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 1050))) (dimF (n.val + 1050)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 1050))) (densSupG (n.val + 1050))) (densSupG (arg1 (n.val + 1050)))) = true := by decide
private theorem m0_w22 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 1100))) (dimF (n.val + 1100)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 1100))) (densSupG (n.val + 1100))) (densSupG (arg0 (n.val + 1100)))) = true := by decide
private theorem m1_w22 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 1100))) (dimF (n.val + 1100)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 1100))) (densSupG (n.val + 1100))) (densSupG (arg1 (n.val + 1100)))) = true := by decide
private theorem m0_w23 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 1150))) (dimF (n.val + 1150)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 1150))) (densSupG (n.val + 1150))) (densSupG (arg0 (n.val + 1150)))) = true := by decide
private theorem m1_w23 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 1150))) (dimF (n.val + 1150)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 1150))) (densSupG (n.val + 1150))) (densSupG (arg1 (n.val + 1150)))) = true := by decide
private theorem m0_w24 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 1200))) (dimF (n.val + 1200)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 1200))) (densSupG (n.val + 1200))) (densSupG (arg0 (n.val + 1200)))) = true := by decide
private theorem m1_w24 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 1200))) (dimF (n.val + 1200)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 1200))) (densSupG (n.val + 1200))) (densSupG (arg1 (n.val + 1200)))) = true := by decide
private theorem m0_w25 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 1250))) (dimF (n.val + 1250)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 1250))) (densSupG (n.val + 1250))) (densSupG (arg0 (n.val + 1250)))) = true := by decide
private theorem m1_w25 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 1250))) (dimF (n.val + 1250)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 1250))) (densSupG (n.val + 1250))) (densSupG (arg1 (n.val + 1250)))) = true := by decide
private theorem m0_w26 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 1300))) (dimF (n.val + 1300)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 1300))) (densSupG (n.val + 1300))) (densSupG (arg0 (n.val + 1300)))) = true := by decide
private theorem m1_w26 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 1300))) (dimF (n.val + 1300)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 1300))) (densSupG (n.val + 1300))) (densSupG (arg1 (n.val + 1300)))) = true := by decide
private theorem m0_w27 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 1350))) (dimF (n.val + 1350)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 1350))) (densSupG (n.val + 1350))) (densSupG (arg0 (n.val + 1350)))) = true := by decide
private theorem m1_w27 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 1350))) (dimF (n.val + 1350)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 1350))) (densSupG (n.val + 1350))) (densSupG (arg1 (n.val + 1350)))) = true := by decide
private theorem m0_w28 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 1400))) (dimF (n.val + 1400)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 1400))) (densSupG (n.val + 1400))) (densSupG (arg0 (n.val + 1400)))) = true := by decide
private theorem m1_w28 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 1400))) (dimF (n.val + 1400)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 1400))) (densSupG (n.val + 1400))) (densSupG (arg1 (n.val + 1400)))) = true := by decide
private theorem m0_w29 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 1450))) (dimF (n.val + 1450)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 1450))) (densSupG (n.val + 1450))) (densSupG (arg0 (n.val + 1450)))) = true := by decide
private theorem m1_w29 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 1450))) (dimF (n.val + 1450)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 1450))) (densSupG (n.val + 1450))) (densSupG (arg1 (n.val + 1450)))) = true := by decide
private theorem m0_w30 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 1500))) (dimF (n.val + 1500)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 1500))) (densSupG (n.val + 1500))) (densSupG (arg0 (n.val + 1500)))) = true := by decide
private theorem m1_w30 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 1500))) (dimF (n.val + 1500)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 1500))) (densSupG (n.val + 1500))) (densSupG (arg1 (n.val + 1500)))) = true := by decide
private theorem m0_w31 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 1550))) (dimF (n.val + 1550)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 1550))) (densSupG (n.val + 1550))) (densSupG (arg0 (n.val + 1550)))) = true := by decide
private theorem m1_w31 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 1550))) (dimF (n.val + 1550)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 1550))) (densSupG (n.val + 1550))) (densSupG (arg1 (n.val + 1550)))) = true := by decide
private theorem m0_w32 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 1600))) (dimF (n.val + 1600)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 1600))) (densSupG (n.val + 1600))) (densSupG (arg0 (n.val + 1600)))) = true := by decide
private theorem m1_w32 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 1600))) (dimF (n.val + 1600)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 1600))) (densSupG (n.val + 1600))) (densSupG (arg1 (n.val + 1600)))) = true := by decide
private theorem m0_w33 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 1650))) (dimF (n.val + 1650)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 1650))) (densSupG (n.val + 1650))) (densSupG (arg0 (n.val + 1650)))) = true := by decide
private theorem m1_w33 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 1650))) (dimF (n.val + 1650)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 1650))) (densSupG (n.val + 1650))) (densSupG (arg1 (n.val + 1650)))) = true := by decide
private theorem m0_w34 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 1700))) (dimF (n.val + 1700)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 1700))) (densSupG (n.val + 1700))) (densSupG (arg0 (n.val + 1700)))) = true := by decide
private theorem m1_w34 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 1700))) (dimF (n.val + 1700)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 1700))) (densSupG (n.val + 1700))) (densSupG (arg1 (n.val + 1700)))) = true := by decide
private theorem m0_w35 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 1750))) (dimF (n.val + 1750)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 1750))) (densSupG (n.val + 1750))) (densSupG (arg0 (n.val + 1750)))) = true := by decide
private theorem m1_w35 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 1750))) (dimF (n.val + 1750)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 1750))) (densSupG (n.val + 1750))) (densSupG (arg1 (n.val + 1750)))) = true := by decide
private theorem m0_w36 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 1800))) (dimF (n.val + 1800)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 1800))) (densSupG (n.val + 1800))) (densSupG (arg0 (n.val + 1800)))) = true := by decide
private theorem m1_w36 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 1800))) (dimF (n.val + 1800)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 1800))) (densSupG (n.val + 1800))) (densSupG (arg1 (n.val + 1800)))) = true := by decide
private theorem m0_w37 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 1850))) (dimF (n.val + 1850)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 1850))) (densSupG (n.val + 1850))) (densSupG (arg0 (n.val + 1850)))) = true := by decide
private theorem m1_w37 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 1850))) (dimF (n.val + 1850)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 1850))) (densSupG (n.val + 1850))) (densSupG (arg1 (n.val + 1850)))) = true := by decide
private theorem m0_w38 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 1900))) (dimF (n.val + 1900)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 1900))) (densSupG (n.val + 1900))) (densSupG (arg0 (n.val + 1900)))) = true := by decide
private theorem m1_w38 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 1900))) (dimF (n.val + 1900)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 1900))) (densSupG (n.val + 1900))) (densSupG (arg1 (n.val + 1900)))) = true := by decide
private theorem m0_w39 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 1950))) (dimF (n.val + 1950)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 1950))) (densSupG (n.val + 1950))) (densSupG (arg0 (n.val + 1950)))) = true := by decide
private theorem m1_w39 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 1950))) (dimF (n.val + 1950)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 1950))) (densSupG (n.val + 1950))) (densSupG (arg1 (n.val + 1950)))) = true := by decide
private theorem m0_w40 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 2000))) (dimF (n.val + 2000)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 2000))) (densSupG (n.val + 2000))) (densSupG (arg0 (n.val + 2000)))) = true := by decide
private theorem m1_w40 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 2000))) (dimF (n.val + 2000)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 2000))) (densSupG (n.val + 2000))) (densSupG (arg1 (n.val + 2000)))) = true := by decide
private theorem m0_w41 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 2050))) (dimF (n.val + 2050)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 2050))) (densSupG (n.val + 2050))) (densSupG (arg0 (n.val + 2050)))) = true := by decide
private theorem m1_w41 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 2050))) (dimF (n.val + 2050)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 2050))) (densSupG (n.val + 2050))) (densSupG (arg1 (n.val + 2050)))) = true := by decide
private theorem m0_w42 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 2100))) (dimF (n.val + 2100)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 2100))) (densSupG (n.val + 2100))) (densSupG (arg0 (n.val + 2100)))) = true := by decide
private theorem m1_w42 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 2100))) (dimF (n.val + 2100)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 2100))) (densSupG (n.val + 2100))) (densSupG (arg1 (n.val + 2100)))) = true := by decide
private theorem m0_w43 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 2150))) (dimF (n.val + 2150)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 2150))) (densSupG (n.val + 2150))) (densSupG (arg0 (n.val + 2150)))) = true := by decide
private theorem m1_w43 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 2150))) (dimF (n.val + 2150)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 2150))) (densSupG (n.val + 2150))) (densSupG (arg1 (n.val + 2150)))) = true := by decide
private theorem m0_w44 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 2200))) (dimF (n.val + 2200)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 2200))) (densSupG (n.val + 2200))) (densSupG (arg0 (n.val + 2200)))) = true := by decide
private theorem m1_w44 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 2200))) (dimF (n.val + 2200)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 2200))) (densSupG (n.val + 2200))) (densSupG (arg1 (n.val + 2200)))) = true := by decide
private theorem m0_w45 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 2250))) (dimF (n.val + 2250)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 2250))) (densSupG (n.val + 2250))) (densSupG (arg0 (n.val + 2250)))) = true := by decide
private theorem m1_w45 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 2250))) (dimF (n.val + 2250)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 2250))) (densSupG (n.val + 2250))) (densSupG (arg1 (n.val + 2250)))) = true := by decide
private theorem m0_w46 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 2300))) (dimF (n.val + 2300)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 2300))) (densSupG (n.val + 2300))) (densSupG (arg0 (n.val + 2300)))) = true := by decide
private theorem m1_w46 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 2300))) (dimF (n.val + 2300)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 2300))) (densSupG (n.val + 2300))) (densSupG (arg1 (n.val + 2300)))) = true := by decide
private theorem m0_w47 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 2350))) (dimF (n.val + 2350)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 2350))) (densSupG (n.val + 2350))) (densSupG (arg0 (n.val + 2350)))) = true := by decide
private theorem m1_w47 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 2350))) (dimF (n.val + 2350)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 2350))) (densSupG (n.val + 2350))) (densSupG (arg1 (n.val + 2350)))) = true := by decide
private theorem m0_w48 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 2400))) (dimF (n.val + 2400)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 2400))) (densSupG (n.val + 2400))) (densSupG (arg0 (n.val + 2400)))) = true := by decide
private theorem m1_w48 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 2400))) (dimF (n.val + 2400)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 2400))) (densSupG (n.val + 2400))) (densSupG (arg1 (n.val + 2400)))) = true := by decide
private theorem m0_w49 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 2450))) (dimF (n.val + 2450)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 2450))) (densSupG (n.val + 2450))) (densSupG (arg0 (n.val + 2450)))) = true := by decide
private theorem m1_w49 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 2450))) (dimF (n.val + 2450)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 2450))) (densSupG (n.val + 2450))) (densSupG (arg1 (n.val + 2450)))) = true := by decide

end IntMul.Kappa.R8.Bit.Oppbank.LandMonoDim0


