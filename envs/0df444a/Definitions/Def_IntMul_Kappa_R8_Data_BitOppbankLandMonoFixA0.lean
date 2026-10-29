-- Prove2me | Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankLandMonoFixA0
-- name    : IntMul_Kappa_R8_Data_BitOppbankLandMonoFixA0
-- status  : Definition
-- author  : @Ethan Cheung Wang
-- created : 2026-10-28T21:11:38.848898+00:00
-- url     : https://prove2.me/theorems/e4202fb4-9595-4c62-affa-a0c56d9f0f52
-- title:
--   Dim-gated densSup land mono FixA pack 0
-- statement:
--   # Dim-gated densSup land certificates (PndFix), pack A0
--
--   Range consolidators for $n\in[0,2500)$:
--   $$
--   \dim F(\mathrm{arg}_i n)<\dim F(n)
--   \Rightarrow
--   \mathrm{densSupG}(\mathrm{arg}_i n)\mathbin{\&}\mathrm{densSupG}(n)=\mathrm{densSupG}(\mathrm{arg}_i n).
--   $$
-- source:
--   R8 BitOppbank PndFix

-- LandMonoFixA0: PUBLIC dim-gated land + range consolidators (PndFix)
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
namespace IntMul.Kappa.R8.Bit.Oppbank.LandMonoFixA0
def arg0 (n : ℕ) : ℕ := Nat.land (argF n) 65535
def arg1 (n : ℕ) : ℕ := Nat.shiftRight (argF n) 16
theorem m0_w0 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 0))) (dimF (n.val + 0)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 0))) (densSupG (n.val + 0))) (densSupG (arg0 (n.val + 0)))) = true := by decide
theorem m1_w0 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 0))) (dimF (n.val + 0)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 0))) (densSupG (n.val + 0))) (densSupG (arg1 (n.val + 0)))) = true := by decide
theorem m0_w1 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 50))) (dimF (n.val + 50)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 50))) (densSupG (n.val + 50))) (densSupG (arg0 (n.val + 50)))) = true := by decide
theorem m1_w1 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 50))) (dimF (n.val + 50)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 50))) (densSupG (n.val + 50))) (densSupG (arg1 (n.val + 50)))) = true := by decide
theorem m0_w2 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 100))) (dimF (n.val + 100)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 100))) (densSupG (n.val + 100))) (densSupG (arg0 (n.val + 100)))) = true := by decide
theorem m1_w2 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 100))) (dimF (n.val + 100)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 100))) (densSupG (n.val + 100))) (densSupG (arg1 (n.val + 100)))) = true := by decide
theorem m0_w3 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 150))) (dimF (n.val + 150)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 150))) (densSupG (n.val + 150))) (densSupG (arg0 (n.val + 150)))) = true := by decide
theorem m1_w3 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 150))) (dimF (n.val + 150)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 150))) (densSupG (n.val + 150))) (densSupG (arg1 (n.val + 150)))) = true := by decide
theorem m0_w4 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 200))) (dimF (n.val + 200)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 200))) (densSupG (n.val + 200))) (densSupG (arg0 (n.val + 200)))) = true := by decide
theorem m1_w4 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 200))) (dimF (n.val + 200)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 200))) (densSupG (n.val + 200))) (densSupG (arg1 (n.val + 200)))) = true := by decide
theorem m0_w5 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 250))) (dimF (n.val + 250)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 250))) (densSupG (n.val + 250))) (densSupG (arg0 (n.val + 250)))) = true := by decide
theorem m1_w5 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 250))) (dimF (n.val + 250)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 250))) (densSupG (n.val + 250))) (densSupG (arg1 (n.val + 250)))) = true := by decide
theorem m0_w6 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 300))) (dimF (n.val + 300)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 300))) (densSupG (n.val + 300))) (densSupG (arg0 (n.val + 300)))) = true := by decide
theorem m1_w6 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 300))) (dimF (n.val + 300)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 300))) (densSupG (n.val + 300))) (densSupG (arg1 (n.val + 300)))) = true := by decide
theorem m0_w7 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 350))) (dimF (n.val + 350)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 350))) (densSupG (n.val + 350))) (densSupG (arg0 (n.val + 350)))) = true := by decide
theorem m1_w7 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 350))) (dimF (n.val + 350)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 350))) (densSupG (n.val + 350))) (densSupG (arg1 (n.val + 350)))) = true := by decide
theorem m0_w8 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 400))) (dimF (n.val + 400)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 400))) (densSupG (n.val + 400))) (densSupG (arg0 (n.val + 400)))) = true := by decide
theorem m1_w8 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 400))) (dimF (n.val + 400)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 400))) (densSupG (n.val + 400))) (densSupG (arg1 (n.val + 400)))) = true := by decide
theorem m0_w9 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 450))) (dimF (n.val + 450)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 450))) (densSupG (n.val + 450))) (densSupG (arg0 (n.val + 450)))) = true := by decide
theorem m1_w9 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 450))) (dimF (n.val + 450)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 450))) (densSupG (n.val + 450))) (densSupG (arg1 (n.val + 450)))) = true := by decide
theorem m0_w10 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 500))) (dimF (n.val + 500)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 500))) (densSupG (n.val + 500))) (densSupG (arg0 (n.val + 500)))) = true := by decide
theorem m1_w10 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 500))) (dimF (n.val + 500)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 500))) (densSupG (n.val + 500))) (densSupG (arg1 (n.val + 500)))) = true := by decide
theorem m0_w11 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 550))) (dimF (n.val + 550)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 550))) (densSupG (n.val + 550))) (densSupG (arg0 (n.val + 550)))) = true := by decide
theorem m1_w11 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 550))) (dimF (n.val + 550)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 550))) (densSupG (n.val + 550))) (densSupG (arg1 (n.val + 550)))) = true := by decide
theorem m0_w12 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 600))) (dimF (n.val + 600)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 600))) (densSupG (n.val + 600))) (densSupG (arg0 (n.val + 600)))) = true := by decide
theorem m1_w12 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 600))) (dimF (n.val + 600)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 600))) (densSupG (n.val + 600))) (densSupG (arg1 (n.val + 600)))) = true := by decide
theorem m0_w13 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 650))) (dimF (n.val + 650)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 650))) (densSupG (n.val + 650))) (densSupG (arg0 (n.val + 650)))) = true := by decide
theorem m1_w13 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 650))) (dimF (n.val + 650)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 650))) (densSupG (n.val + 650))) (densSupG (arg1 (n.val + 650)))) = true := by decide
theorem m0_w14 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 700))) (dimF (n.val + 700)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 700))) (densSupG (n.val + 700))) (densSupG (arg0 (n.val + 700)))) = true := by decide
theorem m1_w14 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 700))) (dimF (n.val + 700)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 700))) (densSupG (n.val + 700))) (densSupG (arg1 (n.val + 700)))) = true := by decide
theorem m0_w15 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 750))) (dimF (n.val + 750)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 750))) (densSupG (n.val + 750))) (densSupG (arg0 (n.val + 750)))) = true := by decide
theorem m1_w15 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 750))) (dimF (n.val + 750)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 750))) (densSupG (n.val + 750))) (densSupG (arg1 (n.val + 750)))) = true := by decide
theorem m0_w16 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 800))) (dimF (n.val + 800)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 800))) (densSupG (n.val + 800))) (densSupG (arg0 (n.val + 800)))) = true := by decide
theorem m1_w16 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 800))) (dimF (n.val + 800)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 800))) (densSupG (n.val + 800))) (densSupG (arg1 (n.val + 800)))) = true := by decide
theorem m0_w17 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 850))) (dimF (n.val + 850)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 850))) (densSupG (n.val + 850))) (densSupG (arg0 (n.val + 850)))) = true := by decide
theorem m1_w17 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 850))) (dimF (n.val + 850)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 850))) (densSupG (n.val + 850))) (densSupG (arg1 (n.val + 850)))) = true := by decide
theorem m0_w18 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 900))) (dimF (n.val + 900)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 900))) (densSupG (n.val + 900))) (densSupG (arg0 (n.val + 900)))) = true := by decide
theorem m1_w18 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 900))) (dimF (n.val + 900)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 900))) (densSupG (n.val + 900))) (densSupG (arg1 (n.val + 900)))) = true := by decide
theorem m0_w19 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 950))) (dimF (n.val + 950)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 950))) (densSupG (n.val + 950))) (densSupG (arg0 (n.val + 950)))) = true := by decide
theorem m1_w19 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 950))) (dimF (n.val + 950)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 950))) (densSupG (n.val + 950))) (densSupG (arg1 (n.val + 950)))) = true := by decide
theorem m0_w20 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 1000))) (dimF (n.val + 1000)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 1000))) (densSupG (n.val + 1000))) (densSupG (arg0 (n.val + 1000)))) = true := by decide
theorem m1_w20 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 1000))) (dimF (n.val + 1000)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 1000))) (densSupG (n.val + 1000))) (densSupG (arg1 (n.val + 1000)))) = true := by decide
theorem m0_w21 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 1050))) (dimF (n.val + 1050)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 1050))) (densSupG (n.val + 1050))) (densSupG (arg0 (n.val + 1050)))) = true := by decide
theorem m1_w21 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 1050))) (dimF (n.val + 1050)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 1050))) (densSupG (n.val + 1050))) (densSupG (arg1 (n.val + 1050)))) = true := by decide
theorem m0_w22 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 1100))) (dimF (n.val + 1100)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 1100))) (densSupG (n.val + 1100))) (densSupG (arg0 (n.val + 1100)))) = true := by decide
theorem m1_w22 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 1100))) (dimF (n.val + 1100)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 1100))) (densSupG (n.val + 1100))) (densSupG (arg1 (n.val + 1100)))) = true := by decide
theorem m0_w23 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 1150))) (dimF (n.val + 1150)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 1150))) (densSupG (n.val + 1150))) (densSupG (arg0 (n.val + 1150)))) = true := by decide
theorem m1_w23 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 1150))) (dimF (n.val + 1150)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 1150))) (densSupG (n.val + 1150))) (densSupG (arg1 (n.val + 1150)))) = true := by decide
theorem m0_w24 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 1200))) (dimF (n.val + 1200)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 1200))) (densSupG (n.val + 1200))) (densSupG (arg0 (n.val + 1200)))) = true := by decide
theorem m1_w24 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 1200))) (dimF (n.val + 1200)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 1200))) (densSupG (n.val + 1200))) (densSupG (arg1 (n.val + 1200)))) = true := by decide
theorem m0_w25 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 1250))) (dimF (n.val + 1250)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 1250))) (densSupG (n.val + 1250))) (densSupG (arg0 (n.val + 1250)))) = true := by decide
theorem m1_w25 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 1250))) (dimF (n.val + 1250)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 1250))) (densSupG (n.val + 1250))) (densSupG (arg1 (n.val + 1250)))) = true := by decide
theorem m0_w26 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 1300))) (dimF (n.val + 1300)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 1300))) (densSupG (n.val + 1300))) (densSupG (arg0 (n.val + 1300)))) = true := by decide
theorem m1_w26 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 1300))) (dimF (n.val + 1300)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 1300))) (densSupG (n.val + 1300))) (densSupG (arg1 (n.val + 1300)))) = true := by decide
theorem m0_w27 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 1350))) (dimF (n.val + 1350)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 1350))) (densSupG (n.val + 1350))) (densSupG (arg0 (n.val + 1350)))) = true := by decide
theorem m1_w27 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 1350))) (dimF (n.val + 1350)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 1350))) (densSupG (n.val + 1350))) (densSupG (arg1 (n.val + 1350)))) = true := by decide
theorem m0_w28 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 1400))) (dimF (n.val + 1400)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 1400))) (densSupG (n.val + 1400))) (densSupG (arg0 (n.val + 1400)))) = true := by decide
theorem m1_w28 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 1400))) (dimF (n.val + 1400)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 1400))) (densSupG (n.val + 1400))) (densSupG (arg1 (n.val + 1400)))) = true := by decide
theorem m0_w29 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 1450))) (dimF (n.val + 1450)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 1450))) (densSupG (n.val + 1450))) (densSupG (arg0 (n.val + 1450)))) = true := by decide
theorem m1_w29 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 1450))) (dimF (n.val + 1450)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 1450))) (densSupG (n.val + 1450))) (densSupG (arg1 (n.val + 1450)))) = true := by decide
theorem m0_w30 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 1500))) (dimF (n.val + 1500)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 1500))) (densSupG (n.val + 1500))) (densSupG (arg0 (n.val + 1500)))) = true := by decide
theorem m1_w30 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 1500))) (dimF (n.val + 1500)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 1500))) (densSupG (n.val + 1500))) (densSupG (arg1 (n.val + 1500)))) = true := by decide
theorem m0_w31 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 1550))) (dimF (n.val + 1550)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 1550))) (densSupG (n.val + 1550))) (densSupG (arg0 (n.val + 1550)))) = true := by decide
theorem m1_w31 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 1550))) (dimF (n.val + 1550)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 1550))) (densSupG (n.val + 1550))) (densSupG (arg1 (n.val + 1550)))) = true := by decide
theorem m0_w32 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 1600))) (dimF (n.val + 1600)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 1600))) (densSupG (n.val + 1600))) (densSupG (arg0 (n.val + 1600)))) = true := by decide
theorem m1_w32 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 1600))) (dimF (n.val + 1600)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 1600))) (densSupG (n.val + 1600))) (densSupG (arg1 (n.val + 1600)))) = true := by decide
theorem m0_w33 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 1650))) (dimF (n.val + 1650)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 1650))) (densSupG (n.val + 1650))) (densSupG (arg0 (n.val + 1650)))) = true := by decide
theorem m1_w33 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 1650))) (dimF (n.val + 1650)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 1650))) (densSupG (n.val + 1650))) (densSupG (arg1 (n.val + 1650)))) = true := by decide
theorem m0_w34 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 1700))) (dimF (n.val + 1700)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 1700))) (densSupG (n.val + 1700))) (densSupG (arg0 (n.val + 1700)))) = true := by decide
theorem m1_w34 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 1700))) (dimF (n.val + 1700)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 1700))) (densSupG (n.val + 1700))) (densSupG (arg1 (n.val + 1700)))) = true := by decide
theorem m0_w35 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 1750))) (dimF (n.val + 1750)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 1750))) (densSupG (n.val + 1750))) (densSupG (arg0 (n.val + 1750)))) = true := by decide
theorem m1_w35 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 1750))) (dimF (n.val + 1750)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 1750))) (densSupG (n.val + 1750))) (densSupG (arg1 (n.val + 1750)))) = true := by decide
theorem m0_w36 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 1800))) (dimF (n.val + 1800)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 1800))) (densSupG (n.val + 1800))) (densSupG (arg0 (n.val + 1800)))) = true := by decide
theorem m1_w36 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 1800))) (dimF (n.val + 1800)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 1800))) (densSupG (n.val + 1800))) (densSupG (arg1 (n.val + 1800)))) = true := by decide
theorem m0_w37 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 1850))) (dimF (n.val + 1850)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 1850))) (densSupG (n.val + 1850))) (densSupG (arg0 (n.val + 1850)))) = true := by decide
theorem m1_w37 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 1850))) (dimF (n.val + 1850)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 1850))) (densSupG (n.val + 1850))) (densSupG (arg1 (n.val + 1850)))) = true := by decide
theorem m0_w38 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 1900))) (dimF (n.val + 1900)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 1900))) (densSupG (n.val + 1900))) (densSupG (arg0 (n.val + 1900)))) = true := by decide
theorem m1_w38 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 1900))) (dimF (n.val + 1900)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 1900))) (densSupG (n.val + 1900))) (densSupG (arg1 (n.val + 1900)))) = true := by decide
theorem m0_w39 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 1950))) (dimF (n.val + 1950)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 1950))) (densSupG (n.val + 1950))) (densSupG (arg0 (n.val + 1950)))) = true := by decide
theorem m1_w39 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 1950))) (dimF (n.val + 1950)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 1950))) (densSupG (n.val + 1950))) (densSupG (arg1 (n.val + 1950)))) = true := by decide
theorem m0_w40 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 2000))) (dimF (n.val + 2000)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 2000))) (densSupG (n.val + 2000))) (densSupG (arg0 (n.val + 2000)))) = true := by decide
theorem m1_w40 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 2000))) (dimF (n.val + 2000)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 2000))) (densSupG (n.val + 2000))) (densSupG (arg1 (n.val + 2000)))) = true := by decide
theorem m0_w41 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 2050))) (dimF (n.val + 2050)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 2050))) (densSupG (n.val + 2050))) (densSupG (arg0 (n.val + 2050)))) = true := by decide
theorem m1_w41 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 2050))) (dimF (n.val + 2050)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 2050))) (densSupG (n.val + 2050))) (densSupG (arg1 (n.val + 2050)))) = true := by decide
theorem m0_w42 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 2100))) (dimF (n.val + 2100)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 2100))) (densSupG (n.val + 2100))) (densSupG (arg0 (n.val + 2100)))) = true := by decide
theorem m1_w42 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 2100))) (dimF (n.val + 2100)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 2100))) (densSupG (n.val + 2100))) (densSupG (arg1 (n.val + 2100)))) = true := by decide
theorem m0_w43 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 2150))) (dimF (n.val + 2150)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 2150))) (densSupG (n.val + 2150))) (densSupG (arg0 (n.val + 2150)))) = true := by decide
theorem m1_w43 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 2150))) (dimF (n.val + 2150)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 2150))) (densSupG (n.val + 2150))) (densSupG (arg1 (n.val + 2150)))) = true := by decide
theorem m0_w44 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 2200))) (dimF (n.val + 2200)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 2200))) (densSupG (n.val + 2200))) (densSupG (arg0 (n.val + 2200)))) = true := by decide
theorem m1_w44 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 2200))) (dimF (n.val + 2200)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 2200))) (densSupG (n.val + 2200))) (densSupG (arg1 (n.val + 2200)))) = true := by decide
theorem m0_w45 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 2250))) (dimF (n.val + 2250)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 2250))) (densSupG (n.val + 2250))) (densSupG (arg0 (n.val + 2250)))) = true := by decide
theorem m1_w45 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 2250))) (dimF (n.val + 2250)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 2250))) (densSupG (n.val + 2250))) (densSupG (arg1 (n.val + 2250)))) = true := by decide
theorem m0_w46 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 2300))) (dimF (n.val + 2300)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 2300))) (densSupG (n.val + 2300))) (densSupG (arg0 (n.val + 2300)))) = true := by decide
theorem m1_w46 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 2300))) (dimF (n.val + 2300)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 2300))) (densSupG (n.val + 2300))) (densSupG (arg1 (n.val + 2300)))) = true := by decide
theorem m0_w47 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 2350))) (dimF (n.val + 2350)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 2350))) (densSupG (n.val + 2350))) (densSupG (arg0 (n.val + 2350)))) = true := by decide
theorem m1_w47 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 2350))) (dimF (n.val + 2350)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 2350))) (densSupG (n.val + 2350))) (densSupG (arg1 (n.val + 2350)))) = true := by decide
theorem m0_w48 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 2400))) (dimF (n.val + 2400)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 2400))) (densSupG (n.val + 2400))) (densSupG (arg0 (n.val + 2400)))) = true := by decide
theorem m1_w48 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 2400))) (dimF (n.val + 2400)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 2400))) (densSupG (n.val + 2400))) (densSupG (arg1 (n.val + 2400)))) = true := by decide
theorem m0_w49 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 2450))) (dimF (n.val + 2450)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 2450))) (densSupG (n.val + 2450))) (densSupG (arg0 (n.val + 2450)))) = true := by decide
theorem m1_w49 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 2450))) (dimF (n.val + 2450)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 2450))) (densSupG (n.val + 2450))) (densSupG (arg1 (n.val + 2450)))) = true := by decide
theorem land0_range (n : ℕ) (hn0 : 0 ≤ n) (hn1 : n < 2500) :
    (!Nat.blt (dimF (arg0 n)) (dimF n) ||
      Nat.beq (Nat.land (densSupG (arg0 n)) (densSupG n)) (densSupG (arg0 n))) = true := by
  by_cases h0 : n < 50
  · have hoff : 0 ≤ n := by omega
    have hnfin : n - 0 < 50 := by omega
    simpa [Nat.sub_add_cancel hoff] using m0_w0 ⟨n - 0, hnfin⟩
  ·
    by_cases h1 : n < 100
    · have hoff : 50 ≤ n := by omega
      have hnfin : n - 50 < 50 := by omega
      simpa [Nat.sub_add_cancel hoff] using m0_w1 ⟨n - 50, hnfin⟩
    ·
      by_cases h2 : n < 150
      · have hoff : 100 ≤ n := by omega
        have hnfin : n - 100 < 50 := by omega
        simpa [Nat.sub_add_cancel hoff] using m0_w2 ⟨n - 100, hnfin⟩
      ·
        by_cases h3 : n < 200
        · have hoff : 150 ≤ n := by omega
          have hnfin : n - 150 < 50 := by omega
          simpa [Nat.sub_add_cancel hoff] using m0_w3 ⟨n - 150, hnfin⟩
        ·
          by_cases h4 : n < 250
          · have hoff : 200 ≤ n := by omega
            have hnfin : n - 200 < 50 := by omega
            simpa [Nat.sub_add_cancel hoff] using m0_w4 ⟨n - 200, hnfin⟩
          ·
            by_cases h5 : n < 300
            · have hoff : 250 ≤ n := by omega
              have hnfin : n - 250 < 50 := by omega
              simpa [Nat.sub_add_cancel hoff] using m0_w5 ⟨n - 250, hnfin⟩
            ·
              by_cases h6 : n < 350
              · have hoff : 300 ≤ n := by omega
                have hnfin : n - 300 < 50 := by omega
                simpa [Nat.sub_add_cancel hoff] using m0_w6 ⟨n - 300, hnfin⟩
              ·
                by_cases h7 : n < 400
                · have hoff : 350 ≤ n := by omega
                  have hnfin : n - 350 < 50 := by omega
                  simpa [Nat.sub_add_cancel hoff] using m0_w7 ⟨n - 350, hnfin⟩
                ·
                  by_cases h8 : n < 450
                  · have hoff : 400 ≤ n := by omega
                    have hnfin : n - 400 < 50 := by omega
                    simpa [Nat.sub_add_cancel hoff] using m0_w8 ⟨n - 400, hnfin⟩
                  ·
                    by_cases h9 : n < 500
                    · have hoff : 450 ≤ n := by omega
                      have hnfin : n - 450 < 50 := by omega
                      simpa [Nat.sub_add_cancel hoff] using m0_w9 ⟨n - 450, hnfin⟩
                    ·
                      by_cases h10 : n < 550
                      · have hoff : 500 ≤ n := by omega
                        have hnfin : n - 500 < 50 := by omega
                        simpa [Nat.sub_add_cancel hoff] using m0_w10 ⟨n - 500, hnfin⟩
                      ·
                        by_cases h11 : n < 600
                        · have hoff : 550 ≤ n := by omega
                          have hnfin : n - 550 < 50 := by omega
                          simpa [Nat.sub_add_cancel hoff] using m0_w11 ⟨n - 550, hnfin⟩
                        ·
                          by_cases h12 : n < 650
                          · have hoff : 600 ≤ n := by omega
                            have hnfin : n - 600 < 50 := by omega
                            simpa [Nat.sub_add_cancel hoff] using m0_w12 ⟨n - 600, hnfin⟩
                          ·
                            by_cases h13 : n < 700
                            · have hoff : 650 ≤ n := by omega
                              have hnfin : n - 650 < 50 := by omega
                              simpa [Nat.sub_add_cancel hoff] using m0_w13 ⟨n - 650, hnfin⟩
                            ·
                              by_cases h14 : n < 750
                              · have hoff : 700 ≤ n := by omega
                                have hnfin : n - 700 < 50 := by omega
                                simpa [Nat.sub_add_cancel hoff] using m0_w14 ⟨n - 700, hnfin⟩
                              ·
                                by_cases h15 : n < 800
                                · have hoff : 750 ≤ n := by omega
                                  have hnfin : n - 750 < 50 := by omega
                                  simpa [Nat.sub_add_cancel hoff] using m0_w15 ⟨n - 750, hnfin⟩
                                ·
                                  by_cases h16 : n < 850
                                  · have hoff : 800 ≤ n := by omega
                                    have hnfin : n - 800 < 50 := by omega
                                    simpa [Nat.sub_add_cancel hoff] using m0_w16 ⟨n - 800, hnfin⟩
                                  ·
                                    by_cases h17 : n < 900
                                    · have hoff : 850 ≤ n := by omega
                                      have hnfin : n - 850 < 50 := by omega
                                      simpa [Nat.sub_add_cancel hoff] using m0_w17 ⟨n - 850, hnfin⟩
                                    ·
                                      by_cases h18 : n < 950
                                      · have hoff : 900 ≤ n := by omega
                                        have hnfin : n - 900 < 50 := by omega
                                        simpa [Nat.sub_add_cancel hoff] using m0_w18 ⟨n - 900, hnfin⟩
                                      ·
                                        by_cases h19 : n < 1000
                                        · have hoff : 950 ≤ n := by omega
                                          have hnfin : n - 950 < 50 := by omega
                                          simpa [Nat.sub_add_cancel hoff] using m0_w19 ⟨n - 950, hnfin⟩
                                        ·
                                          by_cases h20 : n < 1050
                                          · have hoff : 1000 ≤ n := by omega
                                            have hnfin : n - 1000 < 50 := by omega
                                            simpa [Nat.sub_add_cancel hoff] using m0_w20 ⟨n - 1000, hnfin⟩
                                          ·
                                            by_cases h21 : n < 1100
                                            · have hoff : 1050 ≤ n := by omega
                                              have hnfin : n - 1050 < 50 := by omega
                                              simpa [Nat.sub_add_cancel hoff] using m0_w21 ⟨n - 1050, hnfin⟩
                                            ·
                                              by_cases h22 : n < 1150
                                              · have hoff : 1100 ≤ n := by omega
                                                have hnfin : n - 1100 < 50 := by omega
                                                simpa [Nat.sub_add_cancel hoff] using m0_w22 ⟨n - 1100, hnfin⟩
                                              ·
                                                by_cases h23 : n < 1200
                                                · have hoff : 1150 ≤ n := by omega
                                                  have hnfin : n - 1150 < 50 := by omega
                                                  simpa [Nat.sub_add_cancel hoff] using m0_w23 ⟨n - 1150, hnfin⟩
                                                ·
                                                  by_cases h24 : n < 1250
                                                  · have hoff : 1200 ≤ n := by omega
                                                    have hnfin : n - 1200 < 50 := by omega
                                                    simpa [Nat.sub_add_cancel hoff] using m0_w24 ⟨n - 1200, hnfin⟩
                                                  ·
                                                    by_cases h25 : n < 1300
                                                    · have hoff : 1250 ≤ n := by omega
                                                      have hnfin : n - 1250 < 50 := by omega
                                                      simpa [Nat.sub_add_cancel hoff] using m0_w25 ⟨n - 1250, hnfin⟩
                                                    ·
                                                      by_cases h26 : n < 1350
                                                      · have hoff : 1300 ≤ n := by omega
                                                        have hnfin : n - 1300 < 50 := by omega
                                                        simpa [Nat.sub_add_cancel hoff] using m0_w26 ⟨n - 1300, hnfin⟩
                                                      ·
                                                        by_cases h27 : n < 1400
                                                        · have hoff : 1350 ≤ n := by omega
                                                          have hnfin : n - 1350 < 50 := by omega
                                                          simpa [Nat.sub_add_cancel hoff] using m0_w27 ⟨n - 1350, hnfin⟩
                                                        ·
                                                          by_cases h28 : n < 1450
                                                          · have hoff : 1400 ≤ n := by omega
                                                            have hnfin : n - 1400 < 50 := by omega
                                                            simpa [Nat.sub_add_cancel hoff] using m0_w28 ⟨n - 1400, hnfin⟩
                                                          ·
                                                            by_cases h29 : n < 1500
                                                            · have hoff : 1450 ≤ n := by omega
                                                              have hnfin : n - 1450 < 50 := by omega
                                                              simpa [Nat.sub_add_cancel hoff] using m0_w29 ⟨n - 1450, hnfin⟩
                                                            ·
                                                              by_cases h30 : n < 1550
                                                              · have hoff : 1500 ≤ n := by omega
                                                                have hnfin : n - 1500 < 50 := by omega
                                                                simpa [Nat.sub_add_cancel hoff] using m0_w30 ⟨n - 1500, hnfin⟩
                                                              ·
                                                                by_cases h31 : n < 1600
                                                                · have hoff : 1550 ≤ n := by omega
                                                                  have hnfin : n - 1550 < 50 := by omega
                                                                  simpa [Nat.sub_add_cancel hoff] using m0_w31 ⟨n - 1550, hnfin⟩
                                                                ·
                                                                  by_cases h32 : n < 1650
                                                                  · have hoff : 1600 ≤ n := by omega
                                                                    have hnfin : n - 1600 < 50 := by omega
                                                                    simpa [Nat.sub_add_cancel hoff] using m0_w32 ⟨n - 1600, hnfin⟩
                                                                  ·
                                                                    by_cases h33 : n < 1700
                                                                    · have hoff : 1650 ≤ n := by omega
                                                                      have hnfin : n - 1650 < 50 := by omega
                                                                      simpa [Nat.sub_add_cancel hoff] using m0_w33 ⟨n - 1650, hnfin⟩
                                                                    ·
                                                                      by_cases h34 : n < 1750
                                                                      · have hoff : 1700 ≤ n := by omega
                                                                        have hnfin : n - 1700 < 50 := by omega
                                                                        simpa [Nat.sub_add_cancel hoff] using m0_w34 ⟨n - 1700, hnfin⟩
                                                                      ·
                                                                        by_cases h35 : n < 1800
                                                                        · have hoff : 1750 ≤ n := by omega
                                                                          have hnfin : n - 1750 < 50 := by omega
                                                                          simpa [Nat.sub_add_cancel hoff] using m0_w35 ⟨n - 1750, hnfin⟩
                                                                        ·
                                                                          by_cases h36 : n < 1850
                                                                          · have hoff : 1800 ≤ n := by omega
                                                                            have hnfin : n - 1800 < 50 := by omega
                                                                            simpa [Nat.sub_add_cancel hoff] using m0_w36 ⟨n - 1800, hnfin⟩
                                                                          ·
                                                                            by_cases h37 : n < 1900
                                                                            · have hoff : 1850 ≤ n := by omega
                                                                              have hnfin : n - 1850 < 50 := by omega
                                                                              simpa [Nat.sub_add_cancel hoff] using m0_w37 ⟨n - 1850, hnfin⟩
                                                                            ·
                                                                              by_cases h38 : n < 1950
                                                                              · have hoff : 1900 ≤ n := by omega
                                                                                have hnfin : n - 1900 < 50 := by omega
                                                                                simpa [Nat.sub_add_cancel hoff] using m0_w38 ⟨n - 1900, hnfin⟩
                                                                              ·
                                                                                by_cases h39 : n < 2000
                                                                                · have hoff : 1950 ≤ n := by omega
                                                                                  have hnfin : n - 1950 < 50 := by omega
                                                                                  simpa [Nat.sub_add_cancel hoff] using m0_w39 ⟨n - 1950, hnfin⟩
                                                                                ·
                                                                                  by_cases h40 : n < 2050
                                                                                  · have hoff : 2000 ≤ n := by omega
                                                                                    have hnfin : n - 2000 < 50 := by omega
                                                                                    simpa [Nat.sub_add_cancel hoff] using m0_w40 ⟨n - 2000, hnfin⟩
                                                                                  ·
                                                                                    by_cases h41 : n < 2100
                                                                                    · have hoff : 2050 ≤ n := by omega
                                                                                      have hnfin : n - 2050 < 50 := by omega
                                                                                      simpa [Nat.sub_add_cancel hoff] using m0_w41 ⟨n - 2050, hnfin⟩
                                                                                    ·
                                                                                      by_cases h42 : n < 2150
                                                                                      · have hoff : 2100 ≤ n := by omega
                                                                                        have hnfin : n - 2100 < 50 := by omega
                                                                                        simpa [Nat.sub_add_cancel hoff] using m0_w42 ⟨n - 2100, hnfin⟩
                                                                                      ·
                                                                                        by_cases h43 : n < 2200
                                                                                        · have hoff : 2150 ≤ n := by omega
                                                                                          have hnfin : n - 2150 < 50 := by omega
                                                                                          simpa [Nat.sub_add_cancel hoff] using m0_w43 ⟨n - 2150, hnfin⟩
                                                                                        ·
                                                                                          by_cases h44 : n < 2250
                                                                                          · have hoff : 2200 ≤ n := by omega
                                                                                            have hnfin : n - 2200 < 50 := by omega
                                                                                            simpa [Nat.sub_add_cancel hoff] using m0_w44 ⟨n - 2200, hnfin⟩
                                                                                          ·
                                                                                            by_cases h45 : n < 2300
                                                                                            · have hoff : 2250 ≤ n := by omega
                                                                                              have hnfin : n - 2250 < 50 := by omega
                                                                                              simpa [Nat.sub_add_cancel hoff] using m0_w45 ⟨n - 2250, hnfin⟩
                                                                                            ·
                                                                                              by_cases h46 : n < 2350
                                                                                              · have hoff : 2300 ≤ n := by omega
                                                                                                have hnfin : n - 2300 < 50 := by omega
                                                                                                simpa [Nat.sub_add_cancel hoff] using m0_w46 ⟨n - 2300, hnfin⟩
                                                                                              ·
                                                                                                by_cases h47 : n < 2400
                                                                                                · have hoff : 2350 ≤ n := by omega
                                                                                                  have hnfin : n - 2350 < 50 := by omega
                                                                                                  simpa [Nat.sub_add_cancel hoff] using m0_w47 ⟨n - 2350, hnfin⟩
                                                                                                ·
                                                                                                  by_cases h48 : n < 2450
                                                                                                  · have hoff : 2400 ≤ n := by omega
                                                                                                    have hnfin : n - 2400 < 50 := by omega
                                                                                                    simpa [Nat.sub_add_cancel hoff] using m0_w48 ⟨n - 2400, hnfin⟩
                                                                                                  ·
                                                                                                    by_cases h49 : n < 2500
                                                                                                    · have hoff : 2450 ≤ n := by omega
                                                                                                      have hnfin : n - 2450 < 50 := by omega
                                                                                                      simpa [Nat.sub_add_cancel hoff] using m0_w49 ⟨n - 2450, hnfin⟩
                                                                                                    ·
                                                                                                      omega
theorem land1_range (n : ℕ) (hn0 : 0 ≤ n) (hn1 : n < 2500) :
    (!Nat.blt (dimF (arg1 n)) (dimF n) ||
      Nat.beq (Nat.land (densSupG (arg1 n)) (densSupG n)) (densSupG (arg1 n))) = true := by
  by_cases h0 : n < 50
  · have hoff : 0 ≤ n := by omega
    have hnfin : n - 0 < 50 := by omega
    simpa [Nat.sub_add_cancel hoff] using m1_w0 ⟨n - 0, hnfin⟩
  ·
    by_cases h1 : n < 100
    · have hoff : 50 ≤ n := by omega
      have hnfin : n - 50 < 50 := by omega
      simpa [Nat.sub_add_cancel hoff] using m1_w1 ⟨n - 50, hnfin⟩
    ·
      by_cases h2 : n < 150
      · have hoff : 100 ≤ n := by omega
        have hnfin : n - 100 < 50 := by omega
        simpa [Nat.sub_add_cancel hoff] using m1_w2 ⟨n - 100, hnfin⟩
      ·
        by_cases h3 : n < 200
        · have hoff : 150 ≤ n := by omega
          have hnfin : n - 150 < 50 := by omega
          simpa [Nat.sub_add_cancel hoff] using m1_w3 ⟨n - 150, hnfin⟩
        ·
          by_cases h4 : n < 250
          · have hoff : 200 ≤ n := by omega
            have hnfin : n - 200 < 50 := by omega
            simpa [Nat.sub_add_cancel hoff] using m1_w4 ⟨n - 200, hnfin⟩
          ·
            by_cases h5 : n < 300
            · have hoff : 250 ≤ n := by omega
              have hnfin : n - 250 < 50 := by omega
              simpa [Nat.sub_add_cancel hoff] using m1_w5 ⟨n - 250, hnfin⟩
            ·
              by_cases h6 : n < 350
              · have hoff : 300 ≤ n := by omega
                have hnfin : n - 300 < 50 := by omega
                simpa [Nat.sub_add_cancel hoff] using m1_w6 ⟨n - 300, hnfin⟩
              ·
                by_cases h7 : n < 400
                · have hoff : 350 ≤ n := by omega
                  have hnfin : n - 350 < 50 := by omega
                  simpa [Nat.sub_add_cancel hoff] using m1_w7 ⟨n - 350, hnfin⟩
                ·
                  by_cases h8 : n < 450
                  · have hoff : 400 ≤ n := by omega
                    have hnfin : n - 400 < 50 := by omega
                    simpa [Nat.sub_add_cancel hoff] using m1_w8 ⟨n - 400, hnfin⟩
                  ·
                    by_cases h9 : n < 500
                    · have hoff : 450 ≤ n := by omega
                      have hnfin : n - 450 < 50 := by omega
                      simpa [Nat.sub_add_cancel hoff] using m1_w9 ⟨n - 450, hnfin⟩
                    ·
                      by_cases h10 : n < 550
                      · have hoff : 500 ≤ n := by omega
                        have hnfin : n - 500 < 50 := by omega
                        simpa [Nat.sub_add_cancel hoff] using m1_w10 ⟨n - 500, hnfin⟩
                      ·
                        by_cases h11 : n < 600
                        · have hoff : 550 ≤ n := by omega
                          have hnfin : n - 550 < 50 := by omega
                          simpa [Nat.sub_add_cancel hoff] using m1_w11 ⟨n - 550, hnfin⟩
                        ·
                          by_cases h12 : n < 650
                          · have hoff : 600 ≤ n := by omega
                            have hnfin : n - 600 < 50 := by omega
                            simpa [Nat.sub_add_cancel hoff] using m1_w12 ⟨n - 600, hnfin⟩
                          ·
                            by_cases h13 : n < 700
                            · have hoff : 650 ≤ n := by omega
                              have hnfin : n - 650 < 50 := by omega
                              simpa [Nat.sub_add_cancel hoff] using m1_w13 ⟨n - 650, hnfin⟩
                            ·
                              by_cases h14 : n < 750
                              · have hoff : 700 ≤ n := by omega
                                have hnfin : n - 700 < 50 := by omega
                                simpa [Nat.sub_add_cancel hoff] using m1_w14 ⟨n - 700, hnfin⟩
                              ·
                                by_cases h15 : n < 800
                                · have hoff : 750 ≤ n := by omega
                                  have hnfin : n - 750 < 50 := by omega
                                  simpa [Nat.sub_add_cancel hoff] using m1_w15 ⟨n - 750, hnfin⟩
                                ·
                                  by_cases h16 : n < 850
                                  · have hoff : 800 ≤ n := by omega
                                    have hnfin : n - 800 < 50 := by omega
                                    simpa [Nat.sub_add_cancel hoff] using m1_w16 ⟨n - 800, hnfin⟩
                                  ·
                                    by_cases h17 : n < 900
                                    · have hoff : 850 ≤ n := by omega
                                      have hnfin : n - 850 < 50 := by omega
                                      simpa [Nat.sub_add_cancel hoff] using m1_w17 ⟨n - 850, hnfin⟩
                                    ·
                                      by_cases h18 : n < 950
                                      · have hoff : 900 ≤ n := by omega
                                        have hnfin : n - 900 < 50 := by omega
                                        simpa [Nat.sub_add_cancel hoff] using m1_w18 ⟨n - 900, hnfin⟩
                                      ·
                                        by_cases h19 : n < 1000
                                        · have hoff : 950 ≤ n := by omega
                                          have hnfin : n - 950 < 50 := by omega
                                          simpa [Nat.sub_add_cancel hoff] using m1_w19 ⟨n - 950, hnfin⟩
                                        ·
                                          by_cases h20 : n < 1050
                                          · have hoff : 1000 ≤ n := by omega
                                            have hnfin : n - 1000 < 50 := by omega
                                            simpa [Nat.sub_add_cancel hoff] using m1_w20 ⟨n - 1000, hnfin⟩
                                          ·
                                            by_cases h21 : n < 1100
                                            · have hoff : 1050 ≤ n := by omega
                                              have hnfin : n - 1050 < 50 := by omega
                                              simpa [Nat.sub_add_cancel hoff] using m1_w21 ⟨n - 1050, hnfin⟩
                                            ·
                                              by_cases h22 : n < 1150
                                              · have hoff : 1100 ≤ n := by omega
                                                have hnfin : n - 1100 < 50 := by omega
                                                simpa [Nat.sub_add_cancel hoff] using m1_w22 ⟨n - 1100, hnfin⟩
                                              ·
                                                by_cases h23 : n < 1200
                                                · have hoff : 1150 ≤ n := by omega
                                                  have hnfin : n - 1150 < 50 := by omega
                                                  simpa [Nat.sub_add_cancel hoff] using m1_w23 ⟨n - 1150, hnfin⟩
                                                ·
                                                  by_cases h24 : n < 1250
                                                  · have hoff : 1200 ≤ n := by omega
                                                    have hnfin : n - 1200 < 50 := by omega
                                                    simpa [Nat.sub_add_cancel hoff] using m1_w24 ⟨n - 1200, hnfin⟩
                                                  ·
                                                    by_cases h25 : n < 1300
                                                    · have hoff : 1250 ≤ n := by omega
                                                      have hnfin : n - 1250 < 50 := by omega
                                                      simpa [Nat.sub_add_cancel hoff] using m1_w25 ⟨n - 1250, hnfin⟩
                                                    ·
                                                      by_cases h26 : n < 1350
                                                      · have hoff : 1300 ≤ n := by omega
                                                        have hnfin : n - 1300 < 50 := by omega
                                                        simpa [Nat.sub_add_cancel hoff] using m1_w26 ⟨n - 1300, hnfin⟩
                                                      ·
                                                        by_cases h27 : n < 1400
                                                        · have hoff : 1350 ≤ n := by omega
                                                          have hnfin : n - 1350 < 50 := by omega
                                                          simpa [Nat.sub_add_cancel hoff] using m1_w27 ⟨n - 1350, hnfin⟩
                                                        ·
                                                          by_cases h28 : n < 1450
                                                          · have hoff : 1400 ≤ n := by omega
                                                            have hnfin : n - 1400 < 50 := by omega
                                                            simpa [Nat.sub_add_cancel hoff] using m1_w28 ⟨n - 1400, hnfin⟩
                                                          ·
                                                            by_cases h29 : n < 1500
                                                            · have hoff : 1450 ≤ n := by omega
                                                              have hnfin : n - 1450 < 50 := by omega
                                                              simpa [Nat.sub_add_cancel hoff] using m1_w29 ⟨n - 1450, hnfin⟩
                                                            ·
                                                              by_cases h30 : n < 1550
                                                              · have hoff : 1500 ≤ n := by omega
                                                                have hnfin : n - 1500 < 50 := by omega
                                                                simpa [Nat.sub_add_cancel hoff] using m1_w30 ⟨n - 1500, hnfin⟩
                                                              ·
                                                                by_cases h31 : n < 1600
                                                                · have hoff : 1550 ≤ n := by omega
                                                                  have hnfin : n - 1550 < 50 := by omega
                                                                  simpa [Nat.sub_add_cancel hoff] using m1_w31 ⟨n - 1550, hnfin⟩
                                                                ·
                                                                  by_cases h32 : n < 1650
                                                                  · have hoff : 1600 ≤ n := by omega
                                                                    have hnfin : n - 1600 < 50 := by omega
                                                                    simpa [Nat.sub_add_cancel hoff] using m1_w32 ⟨n - 1600, hnfin⟩
                                                                  ·
                                                                    by_cases h33 : n < 1700
                                                                    · have hoff : 1650 ≤ n := by omega
                                                                      have hnfin : n - 1650 < 50 := by omega
                                                                      simpa [Nat.sub_add_cancel hoff] using m1_w33 ⟨n - 1650, hnfin⟩
                                                                    ·
                                                                      by_cases h34 : n < 1750
                                                                      · have hoff : 1700 ≤ n := by omega
                                                                        have hnfin : n - 1700 < 50 := by omega
                                                                        simpa [Nat.sub_add_cancel hoff] using m1_w34 ⟨n - 1700, hnfin⟩
                                                                      ·
                                                                        by_cases h35 : n < 1800
                                                                        · have hoff : 1750 ≤ n := by omega
                                                                          have hnfin : n - 1750 < 50 := by omega
                                                                          simpa [Nat.sub_add_cancel hoff] using m1_w35 ⟨n - 1750, hnfin⟩
                                                                        ·
                                                                          by_cases h36 : n < 1850
                                                                          · have hoff : 1800 ≤ n := by omega
                                                                            have hnfin : n - 1800 < 50 := by omega
                                                                            simpa [Nat.sub_add_cancel hoff] using m1_w36 ⟨n - 1800, hnfin⟩
                                                                          ·
                                                                            by_cases h37 : n < 1900
                                                                            · have hoff : 1850 ≤ n := by omega
                                                                              have hnfin : n - 1850 < 50 := by omega
                                                                              simpa [Nat.sub_add_cancel hoff] using m1_w37 ⟨n - 1850, hnfin⟩
                                                                            ·
                                                                              by_cases h38 : n < 1950
                                                                              · have hoff : 1900 ≤ n := by omega
                                                                                have hnfin : n - 1900 < 50 := by omega
                                                                                simpa [Nat.sub_add_cancel hoff] using m1_w38 ⟨n - 1900, hnfin⟩
                                                                              ·
                                                                                by_cases h39 : n < 2000
                                                                                · have hoff : 1950 ≤ n := by omega
                                                                                  have hnfin : n - 1950 < 50 := by omega
                                                                                  simpa [Nat.sub_add_cancel hoff] using m1_w39 ⟨n - 1950, hnfin⟩
                                                                                ·
                                                                                  by_cases h40 : n < 2050
                                                                                  · have hoff : 2000 ≤ n := by omega
                                                                                    have hnfin : n - 2000 < 50 := by omega
                                                                                    simpa [Nat.sub_add_cancel hoff] using m1_w40 ⟨n - 2000, hnfin⟩
                                                                                  ·
                                                                                    by_cases h41 : n < 2100
                                                                                    · have hoff : 2050 ≤ n := by omega
                                                                                      have hnfin : n - 2050 < 50 := by omega
                                                                                      simpa [Nat.sub_add_cancel hoff] using m1_w41 ⟨n - 2050, hnfin⟩
                                                                                    ·
                                                                                      by_cases h42 : n < 2150
                                                                                      · have hoff : 2100 ≤ n := by omega
                                                                                        have hnfin : n - 2100 < 50 := by omega
                                                                                        simpa [Nat.sub_add_cancel hoff] using m1_w42 ⟨n - 2100, hnfin⟩
                                                                                      ·
                                                                                        by_cases h43 : n < 2200
                                                                                        · have hoff : 2150 ≤ n := by omega
                                                                                          have hnfin : n - 2150 < 50 := by omega
                                                                                          simpa [Nat.sub_add_cancel hoff] using m1_w43 ⟨n - 2150, hnfin⟩
                                                                                        ·
                                                                                          by_cases h44 : n < 2250
                                                                                          · have hoff : 2200 ≤ n := by omega
                                                                                            have hnfin : n - 2200 < 50 := by omega
                                                                                            simpa [Nat.sub_add_cancel hoff] using m1_w44 ⟨n - 2200, hnfin⟩
                                                                                          ·
                                                                                            by_cases h45 : n < 2300
                                                                                            · have hoff : 2250 ≤ n := by omega
                                                                                              have hnfin : n - 2250 < 50 := by omega
                                                                                              simpa [Nat.sub_add_cancel hoff] using m1_w45 ⟨n - 2250, hnfin⟩
                                                                                            ·
                                                                                              by_cases h46 : n < 2350
                                                                                              · have hoff : 2300 ≤ n := by omega
                                                                                                have hnfin : n - 2300 < 50 := by omega
                                                                                                simpa [Nat.sub_add_cancel hoff] using m1_w46 ⟨n - 2300, hnfin⟩
                                                                                              ·
                                                                                                by_cases h47 : n < 2400
                                                                                                · have hoff : 2350 ≤ n := by omega
                                                                                                  have hnfin : n - 2350 < 50 := by omega
                                                                                                  simpa [Nat.sub_add_cancel hoff] using m1_w47 ⟨n - 2350, hnfin⟩
                                                                                                ·
                                                                                                  by_cases h48 : n < 2450
                                                                                                  · have hoff : 2400 ≤ n := by omega
                                                                                                    have hnfin : n - 2400 < 50 := by omega
                                                                                                    simpa [Nat.sub_add_cancel hoff] using m1_w48 ⟨n - 2400, hnfin⟩
                                                                                                  ·
                                                                                                    by_cases h49 : n < 2500
                                                                                                    · have hoff : 2450 ≤ n := by omega
                                                                                                      have hnfin : n - 2450 < 50 := by omega
                                                                                                      simpa [Nat.sub_add_cancel hoff] using m1_w49 ⟨n - 2450, hnfin⟩
                                                                                                    ·
                                                                                                      omega
end IntMul.Kappa.R8.Bit.Oppbank.LandMonoFixA0


