-- Prove2me | Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankLandMonoFixA16
-- name    : IntMul_Kappa_R8_Data_BitOppbankLandMonoFixA16
-- status  : Definition
-- author  : @Ethan Cheung Wang
-- created : 2026-10-28T21:16:55.533607+00:00
-- url     : https://prove2.me/theorems/d9c18f8b-0bf1-41b4-a8d1-b08730a56fc4
-- title:
--   Dim-gated densSup land mono FixA pack 16
-- statement:
--   # Dim-gated densSup land (PndFix), pack A16
--
--   Range consolidators for $n\in[40000,42500)$.
-- source:
--   R8 BitOppbank PndFix

-- LandMonoFixA16: PUBLIC dim-gated land + range consolidators (PndFix)
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
namespace IntMul.Kappa.R8.Bit.Oppbank.LandMonoFixA16
def arg0 (n : ℕ) : ℕ := Nat.land (argF n) 65535
def arg1 (n : ℕ) : ℕ := Nat.shiftRight (argF n) 16
theorem m0_w0 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 40000))) (dimF (n.val + 40000)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 40000))) (densSupG (n.val + 40000))) (densSupG (arg0 (n.val + 40000)))) = true := by decide
theorem m1_w0 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 40000))) (dimF (n.val + 40000)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 40000))) (densSupG (n.val + 40000))) (densSupG (arg1 (n.val + 40000)))) = true := by decide
theorem m0_w1 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 40050))) (dimF (n.val + 40050)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 40050))) (densSupG (n.val + 40050))) (densSupG (arg0 (n.val + 40050)))) = true := by decide
theorem m1_w1 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 40050))) (dimF (n.val + 40050)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 40050))) (densSupG (n.val + 40050))) (densSupG (arg1 (n.val + 40050)))) = true := by decide
theorem m0_w2 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 40100))) (dimF (n.val + 40100)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 40100))) (densSupG (n.val + 40100))) (densSupG (arg0 (n.val + 40100)))) = true := by decide
theorem m1_w2 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 40100))) (dimF (n.val + 40100)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 40100))) (densSupG (n.val + 40100))) (densSupG (arg1 (n.val + 40100)))) = true := by decide
theorem m0_w3 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 40150))) (dimF (n.val + 40150)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 40150))) (densSupG (n.val + 40150))) (densSupG (arg0 (n.val + 40150)))) = true := by decide
theorem m1_w3 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 40150))) (dimF (n.val + 40150)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 40150))) (densSupG (n.val + 40150))) (densSupG (arg1 (n.val + 40150)))) = true := by decide
theorem m0_w4 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 40200))) (dimF (n.val + 40200)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 40200))) (densSupG (n.val + 40200))) (densSupG (arg0 (n.val + 40200)))) = true := by decide
theorem m1_w4 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 40200))) (dimF (n.val + 40200)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 40200))) (densSupG (n.val + 40200))) (densSupG (arg1 (n.val + 40200)))) = true := by decide
theorem m0_w5 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 40250))) (dimF (n.val + 40250)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 40250))) (densSupG (n.val + 40250))) (densSupG (arg0 (n.val + 40250)))) = true := by decide
theorem m1_w5 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 40250))) (dimF (n.val + 40250)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 40250))) (densSupG (n.val + 40250))) (densSupG (arg1 (n.val + 40250)))) = true := by decide
theorem m0_w6 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 40300))) (dimF (n.val + 40300)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 40300))) (densSupG (n.val + 40300))) (densSupG (arg0 (n.val + 40300)))) = true := by decide
theorem m1_w6 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 40300))) (dimF (n.val + 40300)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 40300))) (densSupG (n.val + 40300))) (densSupG (arg1 (n.val + 40300)))) = true := by decide
theorem m0_w7 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 40350))) (dimF (n.val + 40350)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 40350))) (densSupG (n.val + 40350))) (densSupG (arg0 (n.val + 40350)))) = true := by decide
theorem m1_w7 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 40350))) (dimF (n.val + 40350)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 40350))) (densSupG (n.val + 40350))) (densSupG (arg1 (n.val + 40350)))) = true := by decide
theorem m0_w8 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 40400))) (dimF (n.val + 40400)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 40400))) (densSupG (n.val + 40400))) (densSupG (arg0 (n.val + 40400)))) = true := by decide
theorem m1_w8 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 40400))) (dimF (n.val + 40400)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 40400))) (densSupG (n.val + 40400))) (densSupG (arg1 (n.val + 40400)))) = true := by decide
theorem m0_w9 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 40450))) (dimF (n.val + 40450)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 40450))) (densSupG (n.val + 40450))) (densSupG (arg0 (n.val + 40450)))) = true := by decide
theorem m1_w9 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 40450))) (dimF (n.val + 40450)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 40450))) (densSupG (n.val + 40450))) (densSupG (arg1 (n.val + 40450)))) = true := by decide
theorem m0_w10 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 40500))) (dimF (n.val + 40500)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 40500))) (densSupG (n.val + 40500))) (densSupG (arg0 (n.val + 40500)))) = true := by decide
theorem m1_w10 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 40500))) (dimF (n.val + 40500)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 40500))) (densSupG (n.val + 40500))) (densSupG (arg1 (n.val + 40500)))) = true := by decide
theorem m0_w11 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 40550))) (dimF (n.val + 40550)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 40550))) (densSupG (n.val + 40550))) (densSupG (arg0 (n.val + 40550)))) = true := by decide
theorem m1_w11 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 40550))) (dimF (n.val + 40550)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 40550))) (densSupG (n.val + 40550))) (densSupG (arg1 (n.val + 40550)))) = true := by decide
theorem m0_w12 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 40600))) (dimF (n.val + 40600)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 40600))) (densSupG (n.val + 40600))) (densSupG (arg0 (n.val + 40600)))) = true := by decide
theorem m1_w12 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 40600))) (dimF (n.val + 40600)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 40600))) (densSupG (n.val + 40600))) (densSupG (arg1 (n.val + 40600)))) = true := by decide
theorem m0_w13 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 40650))) (dimF (n.val + 40650)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 40650))) (densSupG (n.val + 40650))) (densSupG (arg0 (n.val + 40650)))) = true := by decide
theorem m1_w13 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 40650))) (dimF (n.val + 40650)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 40650))) (densSupG (n.val + 40650))) (densSupG (arg1 (n.val + 40650)))) = true := by decide
theorem m0_w14 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 40700))) (dimF (n.val + 40700)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 40700))) (densSupG (n.val + 40700))) (densSupG (arg0 (n.val + 40700)))) = true := by decide
theorem m1_w14 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 40700))) (dimF (n.val + 40700)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 40700))) (densSupG (n.val + 40700))) (densSupG (arg1 (n.val + 40700)))) = true := by decide
theorem m0_w15 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 40750))) (dimF (n.val + 40750)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 40750))) (densSupG (n.val + 40750))) (densSupG (arg0 (n.val + 40750)))) = true := by decide
theorem m1_w15 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 40750))) (dimF (n.val + 40750)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 40750))) (densSupG (n.val + 40750))) (densSupG (arg1 (n.val + 40750)))) = true := by decide
theorem m0_w16 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 40800))) (dimF (n.val + 40800)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 40800))) (densSupG (n.val + 40800))) (densSupG (arg0 (n.val + 40800)))) = true := by decide
theorem m1_w16 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 40800))) (dimF (n.val + 40800)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 40800))) (densSupG (n.val + 40800))) (densSupG (arg1 (n.val + 40800)))) = true := by decide
theorem m0_w17 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 40850))) (dimF (n.val + 40850)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 40850))) (densSupG (n.val + 40850))) (densSupG (arg0 (n.val + 40850)))) = true := by decide
theorem m1_w17 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 40850))) (dimF (n.val + 40850)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 40850))) (densSupG (n.val + 40850))) (densSupG (arg1 (n.val + 40850)))) = true := by decide
theorem m0_w18 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 40900))) (dimF (n.val + 40900)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 40900))) (densSupG (n.val + 40900))) (densSupG (arg0 (n.val + 40900)))) = true := by decide
theorem m1_w18 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 40900))) (dimF (n.val + 40900)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 40900))) (densSupG (n.val + 40900))) (densSupG (arg1 (n.val + 40900)))) = true := by decide
theorem m0_w19 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 40950))) (dimF (n.val + 40950)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 40950))) (densSupG (n.val + 40950))) (densSupG (arg0 (n.val + 40950)))) = true := by decide
theorem m1_w19 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 40950))) (dimF (n.val + 40950)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 40950))) (densSupG (n.val + 40950))) (densSupG (arg1 (n.val + 40950)))) = true := by decide
theorem m0_w20 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 41000))) (dimF (n.val + 41000)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 41000))) (densSupG (n.val + 41000))) (densSupG (arg0 (n.val + 41000)))) = true := by decide
theorem m1_w20 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 41000))) (dimF (n.val + 41000)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 41000))) (densSupG (n.val + 41000))) (densSupG (arg1 (n.val + 41000)))) = true := by decide
theorem m0_w21 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 41050))) (dimF (n.val + 41050)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 41050))) (densSupG (n.val + 41050))) (densSupG (arg0 (n.val + 41050)))) = true := by decide
theorem m1_w21 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 41050))) (dimF (n.val + 41050)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 41050))) (densSupG (n.val + 41050))) (densSupG (arg1 (n.val + 41050)))) = true := by decide
theorem m0_w22 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 41100))) (dimF (n.val + 41100)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 41100))) (densSupG (n.val + 41100))) (densSupG (arg0 (n.val + 41100)))) = true := by decide
theorem m1_w22 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 41100))) (dimF (n.val + 41100)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 41100))) (densSupG (n.val + 41100))) (densSupG (arg1 (n.val + 41100)))) = true := by decide
theorem m0_w23 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 41150))) (dimF (n.val + 41150)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 41150))) (densSupG (n.val + 41150))) (densSupG (arg0 (n.val + 41150)))) = true := by decide
theorem m1_w23 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 41150))) (dimF (n.val + 41150)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 41150))) (densSupG (n.val + 41150))) (densSupG (arg1 (n.val + 41150)))) = true := by decide
theorem m0_w24 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 41200))) (dimF (n.val + 41200)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 41200))) (densSupG (n.val + 41200))) (densSupG (arg0 (n.val + 41200)))) = true := by decide
theorem m1_w24 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 41200))) (dimF (n.val + 41200)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 41200))) (densSupG (n.val + 41200))) (densSupG (arg1 (n.val + 41200)))) = true := by decide
theorem m0_w25 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 41250))) (dimF (n.val + 41250)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 41250))) (densSupG (n.val + 41250))) (densSupG (arg0 (n.val + 41250)))) = true := by decide
theorem m1_w25 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 41250))) (dimF (n.val + 41250)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 41250))) (densSupG (n.val + 41250))) (densSupG (arg1 (n.val + 41250)))) = true := by decide
theorem m0_w26 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 41300))) (dimF (n.val + 41300)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 41300))) (densSupG (n.val + 41300))) (densSupG (arg0 (n.val + 41300)))) = true := by decide
theorem m1_w26 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 41300))) (dimF (n.val + 41300)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 41300))) (densSupG (n.val + 41300))) (densSupG (arg1 (n.val + 41300)))) = true := by decide
theorem m0_w27 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 41350))) (dimF (n.val + 41350)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 41350))) (densSupG (n.val + 41350))) (densSupG (arg0 (n.val + 41350)))) = true := by decide
theorem m1_w27 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 41350))) (dimF (n.val + 41350)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 41350))) (densSupG (n.val + 41350))) (densSupG (arg1 (n.val + 41350)))) = true := by decide
theorem m0_w28 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 41400))) (dimF (n.val + 41400)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 41400))) (densSupG (n.val + 41400))) (densSupG (arg0 (n.val + 41400)))) = true := by decide
theorem m1_w28 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 41400))) (dimF (n.val + 41400)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 41400))) (densSupG (n.val + 41400))) (densSupG (arg1 (n.val + 41400)))) = true := by decide
theorem m0_w29 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 41450))) (dimF (n.val + 41450)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 41450))) (densSupG (n.val + 41450))) (densSupG (arg0 (n.val + 41450)))) = true := by decide
theorem m1_w29 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 41450))) (dimF (n.val + 41450)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 41450))) (densSupG (n.val + 41450))) (densSupG (arg1 (n.val + 41450)))) = true := by decide
theorem m0_w30 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 41500))) (dimF (n.val + 41500)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 41500))) (densSupG (n.val + 41500))) (densSupG (arg0 (n.val + 41500)))) = true := by decide
theorem m1_w30 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 41500))) (dimF (n.val + 41500)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 41500))) (densSupG (n.val + 41500))) (densSupG (arg1 (n.val + 41500)))) = true := by decide
theorem m0_w31 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 41550))) (dimF (n.val + 41550)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 41550))) (densSupG (n.val + 41550))) (densSupG (arg0 (n.val + 41550)))) = true := by decide
theorem m1_w31 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 41550))) (dimF (n.val + 41550)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 41550))) (densSupG (n.val + 41550))) (densSupG (arg1 (n.val + 41550)))) = true := by decide
theorem m0_w32 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 41600))) (dimF (n.val + 41600)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 41600))) (densSupG (n.val + 41600))) (densSupG (arg0 (n.val + 41600)))) = true := by decide
theorem m1_w32 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 41600))) (dimF (n.val + 41600)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 41600))) (densSupG (n.val + 41600))) (densSupG (arg1 (n.val + 41600)))) = true := by decide
theorem m0_w33 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 41650))) (dimF (n.val + 41650)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 41650))) (densSupG (n.val + 41650))) (densSupG (arg0 (n.val + 41650)))) = true := by decide
theorem m1_w33 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 41650))) (dimF (n.val + 41650)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 41650))) (densSupG (n.val + 41650))) (densSupG (arg1 (n.val + 41650)))) = true := by decide
theorem m0_w34 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 41700))) (dimF (n.val + 41700)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 41700))) (densSupG (n.val + 41700))) (densSupG (arg0 (n.val + 41700)))) = true := by decide
theorem m1_w34 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 41700))) (dimF (n.val + 41700)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 41700))) (densSupG (n.val + 41700))) (densSupG (arg1 (n.val + 41700)))) = true := by decide
theorem m0_w35 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 41750))) (dimF (n.val + 41750)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 41750))) (densSupG (n.val + 41750))) (densSupG (arg0 (n.val + 41750)))) = true := by decide
theorem m1_w35 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 41750))) (dimF (n.val + 41750)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 41750))) (densSupG (n.val + 41750))) (densSupG (arg1 (n.val + 41750)))) = true := by decide
theorem m0_w36 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 41800))) (dimF (n.val + 41800)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 41800))) (densSupG (n.val + 41800))) (densSupG (arg0 (n.val + 41800)))) = true := by decide
theorem m1_w36 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 41800))) (dimF (n.val + 41800)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 41800))) (densSupG (n.val + 41800))) (densSupG (arg1 (n.val + 41800)))) = true := by decide
theorem m0_w37 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 41850))) (dimF (n.val + 41850)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 41850))) (densSupG (n.val + 41850))) (densSupG (arg0 (n.val + 41850)))) = true := by decide
theorem m1_w37 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 41850))) (dimF (n.val + 41850)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 41850))) (densSupG (n.val + 41850))) (densSupG (arg1 (n.val + 41850)))) = true := by decide
theorem m0_w38 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 41900))) (dimF (n.val + 41900)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 41900))) (densSupG (n.val + 41900))) (densSupG (arg0 (n.val + 41900)))) = true := by decide
theorem m1_w38 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 41900))) (dimF (n.val + 41900)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 41900))) (densSupG (n.val + 41900))) (densSupG (arg1 (n.val + 41900)))) = true := by decide
theorem m0_w39 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 41950))) (dimF (n.val + 41950)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 41950))) (densSupG (n.val + 41950))) (densSupG (arg0 (n.val + 41950)))) = true := by decide
theorem m1_w39 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 41950))) (dimF (n.val + 41950)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 41950))) (densSupG (n.val + 41950))) (densSupG (arg1 (n.val + 41950)))) = true := by decide
theorem m0_w40 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 42000))) (dimF (n.val + 42000)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 42000))) (densSupG (n.val + 42000))) (densSupG (arg0 (n.val + 42000)))) = true := by decide
theorem m1_w40 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 42000))) (dimF (n.val + 42000)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 42000))) (densSupG (n.val + 42000))) (densSupG (arg1 (n.val + 42000)))) = true := by decide
theorem m0_w41 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 42050))) (dimF (n.val + 42050)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 42050))) (densSupG (n.val + 42050))) (densSupG (arg0 (n.val + 42050)))) = true := by decide
theorem m1_w41 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 42050))) (dimF (n.val + 42050)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 42050))) (densSupG (n.val + 42050))) (densSupG (arg1 (n.val + 42050)))) = true := by decide
theorem m0_w42 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 42100))) (dimF (n.val + 42100)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 42100))) (densSupG (n.val + 42100))) (densSupG (arg0 (n.val + 42100)))) = true := by decide
theorem m1_w42 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 42100))) (dimF (n.val + 42100)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 42100))) (densSupG (n.val + 42100))) (densSupG (arg1 (n.val + 42100)))) = true := by decide
theorem m0_w43 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 42150))) (dimF (n.val + 42150)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 42150))) (densSupG (n.val + 42150))) (densSupG (arg0 (n.val + 42150)))) = true := by decide
theorem m1_w43 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 42150))) (dimF (n.val + 42150)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 42150))) (densSupG (n.val + 42150))) (densSupG (arg1 (n.val + 42150)))) = true := by decide
theorem m0_w44 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 42200))) (dimF (n.val + 42200)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 42200))) (densSupG (n.val + 42200))) (densSupG (arg0 (n.val + 42200)))) = true := by decide
theorem m1_w44 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 42200))) (dimF (n.val + 42200)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 42200))) (densSupG (n.val + 42200))) (densSupG (arg1 (n.val + 42200)))) = true := by decide
theorem m0_w45 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 42250))) (dimF (n.val + 42250)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 42250))) (densSupG (n.val + 42250))) (densSupG (arg0 (n.val + 42250)))) = true := by decide
theorem m1_w45 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 42250))) (dimF (n.val + 42250)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 42250))) (densSupG (n.val + 42250))) (densSupG (arg1 (n.val + 42250)))) = true := by decide
theorem m0_w46 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 42300))) (dimF (n.val + 42300)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 42300))) (densSupG (n.val + 42300))) (densSupG (arg0 (n.val + 42300)))) = true := by decide
theorem m1_w46 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 42300))) (dimF (n.val + 42300)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 42300))) (densSupG (n.val + 42300))) (densSupG (arg1 (n.val + 42300)))) = true := by decide
theorem m0_w47 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 42350))) (dimF (n.val + 42350)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 42350))) (densSupG (n.val + 42350))) (densSupG (arg0 (n.val + 42350)))) = true := by decide
theorem m1_w47 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 42350))) (dimF (n.val + 42350)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 42350))) (densSupG (n.val + 42350))) (densSupG (arg1 (n.val + 42350)))) = true := by decide
theorem m0_w48 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 42400))) (dimF (n.val + 42400)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 42400))) (densSupG (n.val + 42400))) (densSupG (arg0 (n.val + 42400)))) = true := by decide
theorem m1_w48 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 42400))) (dimF (n.val + 42400)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 42400))) (densSupG (n.val + 42400))) (densSupG (arg1 (n.val + 42400)))) = true := by decide
theorem m0_w49 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 42450))) (dimF (n.val + 42450)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 42450))) (densSupG (n.val + 42450))) (densSupG (arg0 (n.val + 42450)))) = true := by decide
theorem m1_w49 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 42450))) (dimF (n.val + 42450)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 42450))) (densSupG (n.val + 42450))) (densSupG (arg1 (n.val + 42450)))) = true := by decide
theorem land0_range (n : ℕ) (hn0 : 40000 ≤ n) (hn1 : n < 42500) :
    (!Nat.blt (dimF (arg0 n)) (dimF n) ||
      Nat.beq (Nat.land (densSupG (arg0 n)) (densSupG n)) (densSupG (arg0 n))) = true := by
  by_cases h0 : n < 40050
  · have hoff : 40000 ≤ n := by omega
    have hnfin : n - 40000 < 50 := by omega
    simpa [Nat.sub_add_cancel hoff] using m0_w0 ⟨n - 40000, hnfin⟩
  ·
    by_cases h1 : n < 40100
    · have hoff : 40050 ≤ n := by omega
      have hnfin : n - 40050 < 50 := by omega
      simpa [Nat.sub_add_cancel hoff] using m0_w1 ⟨n - 40050, hnfin⟩
    ·
      by_cases h2 : n < 40150
      · have hoff : 40100 ≤ n := by omega
        have hnfin : n - 40100 < 50 := by omega
        simpa [Nat.sub_add_cancel hoff] using m0_w2 ⟨n - 40100, hnfin⟩
      ·
        by_cases h3 : n < 40200
        · have hoff : 40150 ≤ n := by omega
          have hnfin : n - 40150 < 50 := by omega
          simpa [Nat.sub_add_cancel hoff] using m0_w3 ⟨n - 40150, hnfin⟩
        ·
          by_cases h4 : n < 40250
          · have hoff : 40200 ≤ n := by omega
            have hnfin : n - 40200 < 50 := by omega
            simpa [Nat.sub_add_cancel hoff] using m0_w4 ⟨n - 40200, hnfin⟩
          ·
            by_cases h5 : n < 40300
            · have hoff : 40250 ≤ n := by omega
              have hnfin : n - 40250 < 50 := by omega
              simpa [Nat.sub_add_cancel hoff] using m0_w5 ⟨n - 40250, hnfin⟩
            ·
              by_cases h6 : n < 40350
              · have hoff : 40300 ≤ n := by omega
                have hnfin : n - 40300 < 50 := by omega
                simpa [Nat.sub_add_cancel hoff] using m0_w6 ⟨n - 40300, hnfin⟩
              ·
                by_cases h7 : n < 40400
                · have hoff : 40350 ≤ n := by omega
                  have hnfin : n - 40350 < 50 := by omega
                  simpa [Nat.sub_add_cancel hoff] using m0_w7 ⟨n - 40350, hnfin⟩
                ·
                  by_cases h8 : n < 40450
                  · have hoff : 40400 ≤ n := by omega
                    have hnfin : n - 40400 < 50 := by omega
                    simpa [Nat.sub_add_cancel hoff] using m0_w8 ⟨n - 40400, hnfin⟩
                  ·
                    by_cases h9 : n < 40500
                    · have hoff : 40450 ≤ n := by omega
                      have hnfin : n - 40450 < 50 := by omega
                      simpa [Nat.sub_add_cancel hoff] using m0_w9 ⟨n - 40450, hnfin⟩
                    ·
                      by_cases h10 : n < 40550
                      · have hoff : 40500 ≤ n := by omega
                        have hnfin : n - 40500 < 50 := by omega
                        simpa [Nat.sub_add_cancel hoff] using m0_w10 ⟨n - 40500, hnfin⟩
                      ·
                        by_cases h11 : n < 40600
                        · have hoff : 40550 ≤ n := by omega
                          have hnfin : n - 40550 < 50 := by omega
                          simpa [Nat.sub_add_cancel hoff] using m0_w11 ⟨n - 40550, hnfin⟩
                        ·
                          by_cases h12 : n < 40650
                          · have hoff : 40600 ≤ n := by omega
                            have hnfin : n - 40600 < 50 := by omega
                            simpa [Nat.sub_add_cancel hoff] using m0_w12 ⟨n - 40600, hnfin⟩
                          ·
                            by_cases h13 : n < 40700
                            · have hoff : 40650 ≤ n := by omega
                              have hnfin : n - 40650 < 50 := by omega
                              simpa [Nat.sub_add_cancel hoff] using m0_w13 ⟨n - 40650, hnfin⟩
                            ·
                              by_cases h14 : n < 40750
                              · have hoff : 40700 ≤ n := by omega
                                have hnfin : n - 40700 < 50 := by omega
                                simpa [Nat.sub_add_cancel hoff] using m0_w14 ⟨n - 40700, hnfin⟩
                              ·
                                by_cases h15 : n < 40800
                                · have hoff : 40750 ≤ n := by omega
                                  have hnfin : n - 40750 < 50 := by omega
                                  simpa [Nat.sub_add_cancel hoff] using m0_w15 ⟨n - 40750, hnfin⟩
                                ·
                                  by_cases h16 : n < 40850
                                  · have hoff : 40800 ≤ n := by omega
                                    have hnfin : n - 40800 < 50 := by omega
                                    simpa [Nat.sub_add_cancel hoff] using m0_w16 ⟨n - 40800, hnfin⟩
                                  ·
                                    by_cases h17 : n < 40900
                                    · have hoff : 40850 ≤ n := by omega
                                      have hnfin : n - 40850 < 50 := by omega
                                      simpa [Nat.sub_add_cancel hoff] using m0_w17 ⟨n - 40850, hnfin⟩
                                    ·
                                      by_cases h18 : n < 40950
                                      · have hoff : 40900 ≤ n := by omega
                                        have hnfin : n - 40900 < 50 := by omega
                                        simpa [Nat.sub_add_cancel hoff] using m0_w18 ⟨n - 40900, hnfin⟩
                                      ·
                                        by_cases h19 : n < 41000
                                        · have hoff : 40950 ≤ n := by omega
                                          have hnfin : n - 40950 < 50 := by omega
                                          simpa [Nat.sub_add_cancel hoff] using m0_w19 ⟨n - 40950, hnfin⟩
                                        ·
                                          by_cases h20 : n < 41050
                                          · have hoff : 41000 ≤ n := by omega
                                            have hnfin : n - 41000 < 50 := by omega
                                            simpa [Nat.sub_add_cancel hoff] using m0_w20 ⟨n - 41000, hnfin⟩
                                          ·
                                            by_cases h21 : n < 41100
                                            · have hoff : 41050 ≤ n := by omega
                                              have hnfin : n - 41050 < 50 := by omega
                                              simpa [Nat.sub_add_cancel hoff] using m0_w21 ⟨n - 41050, hnfin⟩
                                            ·
                                              by_cases h22 : n < 41150
                                              · have hoff : 41100 ≤ n := by omega
                                                have hnfin : n - 41100 < 50 := by omega
                                                simpa [Nat.sub_add_cancel hoff] using m0_w22 ⟨n - 41100, hnfin⟩
                                              ·
                                                by_cases h23 : n < 41200
                                                · have hoff : 41150 ≤ n := by omega
                                                  have hnfin : n - 41150 < 50 := by omega
                                                  simpa [Nat.sub_add_cancel hoff] using m0_w23 ⟨n - 41150, hnfin⟩
                                                ·
                                                  by_cases h24 : n < 41250
                                                  · have hoff : 41200 ≤ n := by omega
                                                    have hnfin : n - 41200 < 50 := by omega
                                                    simpa [Nat.sub_add_cancel hoff] using m0_w24 ⟨n - 41200, hnfin⟩
                                                  ·
                                                    by_cases h25 : n < 41300
                                                    · have hoff : 41250 ≤ n := by omega
                                                      have hnfin : n - 41250 < 50 := by omega
                                                      simpa [Nat.sub_add_cancel hoff] using m0_w25 ⟨n - 41250, hnfin⟩
                                                    ·
                                                      by_cases h26 : n < 41350
                                                      · have hoff : 41300 ≤ n := by omega
                                                        have hnfin : n - 41300 < 50 := by omega
                                                        simpa [Nat.sub_add_cancel hoff] using m0_w26 ⟨n - 41300, hnfin⟩
                                                      ·
                                                        by_cases h27 : n < 41400
                                                        · have hoff : 41350 ≤ n := by omega
                                                          have hnfin : n - 41350 < 50 := by omega
                                                          simpa [Nat.sub_add_cancel hoff] using m0_w27 ⟨n - 41350, hnfin⟩
                                                        ·
                                                          by_cases h28 : n < 41450
                                                          · have hoff : 41400 ≤ n := by omega
                                                            have hnfin : n - 41400 < 50 := by omega
                                                            simpa [Nat.sub_add_cancel hoff] using m0_w28 ⟨n - 41400, hnfin⟩
                                                          ·
                                                            by_cases h29 : n < 41500
                                                            · have hoff : 41450 ≤ n := by omega
                                                              have hnfin : n - 41450 < 50 := by omega
                                                              simpa [Nat.sub_add_cancel hoff] using m0_w29 ⟨n - 41450, hnfin⟩
                                                            ·
                                                              by_cases h30 : n < 41550
                                                              · have hoff : 41500 ≤ n := by omega
                                                                have hnfin : n - 41500 < 50 := by omega
                                                                simpa [Nat.sub_add_cancel hoff] using m0_w30 ⟨n - 41500, hnfin⟩
                                                              ·
                                                                by_cases h31 : n < 41600
                                                                · have hoff : 41550 ≤ n := by omega
                                                                  have hnfin : n - 41550 < 50 := by omega
                                                                  simpa [Nat.sub_add_cancel hoff] using m0_w31 ⟨n - 41550, hnfin⟩
                                                                ·
                                                                  by_cases h32 : n < 41650
                                                                  · have hoff : 41600 ≤ n := by omega
                                                                    have hnfin : n - 41600 < 50 := by omega
                                                                    simpa [Nat.sub_add_cancel hoff] using m0_w32 ⟨n - 41600, hnfin⟩
                                                                  ·
                                                                    by_cases h33 : n < 41700
                                                                    · have hoff : 41650 ≤ n := by omega
                                                                      have hnfin : n - 41650 < 50 := by omega
                                                                      simpa [Nat.sub_add_cancel hoff] using m0_w33 ⟨n - 41650, hnfin⟩
                                                                    ·
                                                                      by_cases h34 : n < 41750
                                                                      · have hoff : 41700 ≤ n := by omega
                                                                        have hnfin : n - 41700 < 50 := by omega
                                                                        simpa [Nat.sub_add_cancel hoff] using m0_w34 ⟨n - 41700, hnfin⟩
                                                                      ·
                                                                        by_cases h35 : n < 41800
                                                                        · have hoff : 41750 ≤ n := by omega
                                                                          have hnfin : n - 41750 < 50 := by omega
                                                                          simpa [Nat.sub_add_cancel hoff] using m0_w35 ⟨n - 41750, hnfin⟩
                                                                        ·
                                                                          by_cases h36 : n < 41850
                                                                          · have hoff : 41800 ≤ n := by omega
                                                                            have hnfin : n - 41800 < 50 := by omega
                                                                            simpa [Nat.sub_add_cancel hoff] using m0_w36 ⟨n - 41800, hnfin⟩
                                                                          ·
                                                                            by_cases h37 : n < 41900
                                                                            · have hoff : 41850 ≤ n := by omega
                                                                              have hnfin : n - 41850 < 50 := by omega
                                                                              simpa [Nat.sub_add_cancel hoff] using m0_w37 ⟨n - 41850, hnfin⟩
                                                                            ·
                                                                              by_cases h38 : n < 41950
                                                                              · have hoff : 41900 ≤ n := by omega
                                                                                have hnfin : n - 41900 < 50 := by omega
                                                                                simpa [Nat.sub_add_cancel hoff] using m0_w38 ⟨n - 41900, hnfin⟩
                                                                              ·
                                                                                by_cases h39 : n < 42000
                                                                                · have hoff : 41950 ≤ n := by omega
                                                                                  have hnfin : n - 41950 < 50 := by omega
                                                                                  simpa [Nat.sub_add_cancel hoff] using m0_w39 ⟨n - 41950, hnfin⟩
                                                                                ·
                                                                                  by_cases h40 : n < 42050
                                                                                  · have hoff : 42000 ≤ n := by omega
                                                                                    have hnfin : n - 42000 < 50 := by omega
                                                                                    simpa [Nat.sub_add_cancel hoff] using m0_w40 ⟨n - 42000, hnfin⟩
                                                                                  ·
                                                                                    by_cases h41 : n < 42100
                                                                                    · have hoff : 42050 ≤ n := by omega
                                                                                      have hnfin : n - 42050 < 50 := by omega
                                                                                      simpa [Nat.sub_add_cancel hoff] using m0_w41 ⟨n - 42050, hnfin⟩
                                                                                    ·
                                                                                      by_cases h42 : n < 42150
                                                                                      · have hoff : 42100 ≤ n := by omega
                                                                                        have hnfin : n - 42100 < 50 := by omega
                                                                                        simpa [Nat.sub_add_cancel hoff] using m0_w42 ⟨n - 42100, hnfin⟩
                                                                                      ·
                                                                                        by_cases h43 : n < 42200
                                                                                        · have hoff : 42150 ≤ n := by omega
                                                                                          have hnfin : n - 42150 < 50 := by omega
                                                                                          simpa [Nat.sub_add_cancel hoff] using m0_w43 ⟨n - 42150, hnfin⟩
                                                                                        ·
                                                                                          by_cases h44 : n < 42250
                                                                                          · have hoff : 42200 ≤ n := by omega
                                                                                            have hnfin : n - 42200 < 50 := by omega
                                                                                            simpa [Nat.sub_add_cancel hoff] using m0_w44 ⟨n - 42200, hnfin⟩
                                                                                          ·
                                                                                            by_cases h45 : n < 42300
                                                                                            · have hoff : 42250 ≤ n := by omega
                                                                                              have hnfin : n - 42250 < 50 := by omega
                                                                                              simpa [Nat.sub_add_cancel hoff] using m0_w45 ⟨n - 42250, hnfin⟩
                                                                                            ·
                                                                                              by_cases h46 : n < 42350
                                                                                              · have hoff : 42300 ≤ n := by omega
                                                                                                have hnfin : n - 42300 < 50 := by omega
                                                                                                simpa [Nat.sub_add_cancel hoff] using m0_w46 ⟨n - 42300, hnfin⟩
                                                                                              ·
                                                                                                by_cases h47 : n < 42400
                                                                                                · have hoff : 42350 ≤ n := by omega
                                                                                                  have hnfin : n - 42350 < 50 := by omega
                                                                                                  simpa [Nat.sub_add_cancel hoff] using m0_w47 ⟨n - 42350, hnfin⟩
                                                                                                ·
                                                                                                  by_cases h48 : n < 42450
                                                                                                  · have hoff : 42400 ≤ n := by omega
                                                                                                    have hnfin : n - 42400 < 50 := by omega
                                                                                                    simpa [Nat.sub_add_cancel hoff] using m0_w48 ⟨n - 42400, hnfin⟩
                                                                                                  ·
                                                                                                    by_cases h49 : n < 42500
                                                                                                    · have hoff : 42450 ≤ n := by omega
                                                                                                      have hnfin : n - 42450 < 50 := by omega
                                                                                                      simpa [Nat.sub_add_cancel hoff] using m0_w49 ⟨n - 42450, hnfin⟩
                                                                                                    ·
                                                                                                      omega
theorem land1_range (n : ℕ) (hn0 : 40000 ≤ n) (hn1 : n < 42500) :
    (!Nat.blt (dimF (arg1 n)) (dimF n) ||
      Nat.beq (Nat.land (densSupG (arg1 n)) (densSupG n)) (densSupG (arg1 n))) = true := by
  by_cases h0 : n < 40050
  · have hoff : 40000 ≤ n := by omega
    have hnfin : n - 40000 < 50 := by omega
    simpa [Nat.sub_add_cancel hoff] using m1_w0 ⟨n - 40000, hnfin⟩
  ·
    by_cases h1 : n < 40100
    · have hoff : 40050 ≤ n := by omega
      have hnfin : n - 40050 < 50 := by omega
      simpa [Nat.sub_add_cancel hoff] using m1_w1 ⟨n - 40050, hnfin⟩
    ·
      by_cases h2 : n < 40150
      · have hoff : 40100 ≤ n := by omega
        have hnfin : n - 40100 < 50 := by omega
        simpa [Nat.sub_add_cancel hoff] using m1_w2 ⟨n - 40100, hnfin⟩
      ·
        by_cases h3 : n < 40200
        · have hoff : 40150 ≤ n := by omega
          have hnfin : n - 40150 < 50 := by omega
          simpa [Nat.sub_add_cancel hoff] using m1_w3 ⟨n - 40150, hnfin⟩
        ·
          by_cases h4 : n < 40250
          · have hoff : 40200 ≤ n := by omega
            have hnfin : n - 40200 < 50 := by omega
            simpa [Nat.sub_add_cancel hoff] using m1_w4 ⟨n - 40200, hnfin⟩
          ·
            by_cases h5 : n < 40300
            · have hoff : 40250 ≤ n := by omega
              have hnfin : n - 40250 < 50 := by omega
              simpa [Nat.sub_add_cancel hoff] using m1_w5 ⟨n - 40250, hnfin⟩
            ·
              by_cases h6 : n < 40350
              · have hoff : 40300 ≤ n := by omega
                have hnfin : n - 40300 < 50 := by omega
                simpa [Nat.sub_add_cancel hoff] using m1_w6 ⟨n - 40300, hnfin⟩
              ·
                by_cases h7 : n < 40400
                · have hoff : 40350 ≤ n := by omega
                  have hnfin : n - 40350 < 50 := by omega
                  simpa [Nat.sub_add_cancel hoff] using m1_w7 ⟨n - 40350, hnfin⟩
                ·
                  by_cases h8 : n < 40450
                  · have hoff : 40400 ≤ n := by omega
                    have hnfin : n - 40400 < 50 := by omega
                    simpa [Nat.sub_add_cancel hoff] using m1_w8 ⟨n - 40400, hnfin⟩
                  ·
                    by_cases h9 : n < 40500
                    · have hoff : 40450 ≤ n := by omega
                      have hnfin : n - 40450 < 50 := by omega
                      simpa [Nat.sub_add_cancel hoff] using m1_w9 ⟨n - 40450, hnfin⟩
                    ·
                      by_cases h10 : n < 40550
                      · have hoff : 40500 ≤ n := by omega
                        have hnfin : n - 40500 < 50 := by omega
                        simpa [Nat.sub_add_cancel hoff] using m1_w10 ⟨n - 40500, hnfin⟩
                      ·
                        by_cases h11 : n < 40600
                        · have hoff : 40550 ≤ n := by omega
                          have hnfin : n - 40550 < 50 := by omega
                          simpa [Nat.sub_add_cancel hoff] using m1_w11 ⟨n - 40550, hnfin⟩
                        ·
                          by_cases h12 : n < 40650
                          · have hoff : 40600 ≤ n := by omega
                            have hnfin : n - 40600 < 50 := by omega
                            simpa [Nat.sub_add_cancel hoff] using m1_w12 ⟨n - 40600, hnfin⟩
                          ·
                            by_cases h13 : n < 40700
                            · have hoff : 40650 ≤ n := by omega
                              have hnfin : n - 40650 < 50 := by omega
                              simpa [Nat.sub_add_cancel hoff] using m1_w13 ⟨n - 40650, hnfin⟩
                            ·
                              by_cases h14 : n < 40750
                              · have hoff : 40700 ≤ n := by omega
                                have hnfin : n - 40700 < 50 := by omega
                                simpa [Nat.sub_add_cancel hoff] using m1_w14 ⟨n - 40700, hnfin⟩
                              ·
                                by_cases h15 : n < 40800
                                · have hoff : 40750 ≤ n := by omega
                                  have hnfin : n - 40750 < 50 := by omega
                                  simpa [Nat.sub_add_cancel hoff] using m1_w15 ⟨n - 40750, hnfin⟩
                                ·
                                  by_cases h16 : n < 40850
                                  · have hoff : 40800 ≤ n := by omega
                                    have hnfin : n - 40800 < 50 := by omega
                                    simpa [Nat.sub_add_cancel hoff] using m1_w16 ⟨n - 40800, hnfin⟩
                                  ·
                                    by_cases h17 : n < 40900
                                    · have hoff : 40850 ≤ n := by omega
                                      have hnfin : n - 40850 < 50 := by omega
                                      simpa [Nat.sub_add_cancel hoff] using m1_w17 ⟨n - 40850, hnfin⟩
                                    ·
                                      by_cases h18 : n < 40950
                                      · have hoff : 40900 ≤ n := by omega
                                        have hnfin : n - 40900 < 50 := by omega
                                        simpa [Nat.sub_add_cancel hoff] using m1_w18 ⟨n - 40900, hnfin⟩
                                      ·
                                        by_cases h19 : n < 41000
                                        · have hoff : 40950 ≤ n := by omega
                                          have hnfin : n - 40950 < 50 := by omega
                                          simpa [Nat.sub_add_cancel hoff] using m1_w19 ⟨n - 40950, hnfin⟩
                                        ·
                                          by_cases h20 : n < 41050
                                          · have hoff : 41000 ≤ n := by omega
                                            have hnfin : n - 41000 < 50 := by omega
                                            simpa [Nat.sub_add_cancel hoff] using m1_w20 ⟨n - 41000, hnfin⟩
                                          ·
                                            by_cases h21 : n < 41100
                                            · have hoff : 41050 ≤ n := by omega
                                              have hnfin : n - 41050 < 50 := by omega
                                              simpa [Nat.sub_add_cancel hoff] using m1_w21 ⟨n - 41050, hnfin⟩
                                            ·
                                              by_cases h22 : n < 41150
                                              · have hoff : 41100 ≤ n := by omega
                                                have hnfin : n - 41100 < 50 := by omega
                                                simpa [Nat.sub_add_cancel hoff] using m1_w22 ⟨n - 41100, hnfin⟩
                                              ·
                                                by_cases h23 : n < 41200
                                                · have hoff : 41150 ≤ n := by omega
                                                  have hnfin : n - 41150 < 50 := by omega
                                                  simpa [Nat.sub_add_cancel hoff] using m1_w23 ⟨n - 41150, hnfin⟩
                                                ·
                                                  by_cases h24 : n < 41250
                                                  · have hoff : 41200 ≤ n := by omega
                                                    have hnfin : n - 41200 < 50 := by omega
                                                    simpa [Nat.sub_add_cancel hoff] using m1_w24 ⟨n - 41200, hnfin⟩
                                                  ·
                                                    by_cases h25 : n < 41300
                                                    · have hoff : 41250 ≤ n := by omega
                                                      have hnfin : n - 41250 < 50 := by omega
                                                      simpa [Nat.sub_add_cancel hoff] using m1_w25 ⟨n - 41250, hnfin⟩
                                                    ·
                                                      by_cases h26 : n < 41350
                                                      · have hoff : 41300 ≤ n := by omega
                                                        have hnfin : n - 41300 < 50 := by omega
                                                        simpa [Nat.sub_add_cancel hoff] using m1_w26 ⟨n - 41300, hnfin⟩
                                                      ·
                                                        by_cases h27 : n < 41400
                                                        · have hoff : 41350 ≤ n := by omega
                                                          have hnfin : n - 41350 < 50 := by omega
                                                          simpa [Nat.sub_add_cancel hoff] using m1_w27 ⟨n - 41350, hnfin⟩
                                                        ·
                                                          by_cases h28 : n < 41450
                                                          · have hoff : 41400 ≤ n := by omega
                                                            have hnfin : n - 41400 < 50 := by omega
                                                            simpa [Nat.sub_add_cancel hoff] using m1_w28 ⟨n - 41400, hnfin⟩
                                                          ·
                                                            by_cases h29 : n < 41500
                                                            · have hoff : 41450 ≤ n := by omega
                                                              have hnfin : n - 41450 < 50 := by omega
                                                              simpa [Nat.sub_add_cancel hoff] using m1_w29 ⟨n - 41450, hnfin⟩
                                                            ·
                                                              by_cases h30 : n < 41550
                                                              · have hoff : 41500 ≤ n := by omega
                                                                have hnfin : n - 41500 < 50 := by omega
                                                                simpa [Nat.sub_add_cancel hoff] using m1_w30 ⟨n - 41500, hnfin⟩
                                                              ·
                                                                by_cases h31 : n < 41600
                                                                · have hoff : 41550 ≤ n := by omega
                                                                  have hnfin : n - 41550 < 50 := by omega
                                                                  simpa [Nat.sub_add_cancel hoff] using m1_w31 ⟨n - 41550, hnfin⟩
                                                                ·
                                                                  by_cases h32 : n < 41650
                                                                  · have hoff : 41600 ≤ n := by omega
                                                                    have hnfin : n - 41600 < 50 := by omega
                                                                    simpa [Nat.sub_add_cancel hoff] using m1_w32 ⟨n - 41600, hnfin⟩
                                                                  ·
                                                                    by_cases h33 : n < 41700
                                                                    · have hoff : 41650 ≤ n := by omega
                                                                      have hnfin : n - 41650 < 50 := by omega
                                                                      simpa [Nat.sub_add_cancel hoff] using m1_w33 ⟨n - 41650, hnfin⟩
                                                                    ·
                                                                      by_cases h34 : n < 41750
                                                                      · have hoff : 41700 ≤ n := by omega
                                                                        have hnfin : n - 41700 < 50 := by omega
                                                                        simpa [Nat.sub_add_cancel hoff] using m1_w34 ⟨n - 41700, hnfin⟩
                                                                      ·
                                                                        by_cases h35 : n < 41800
                                                                        · have hoff : 41750 ≤ n := by omega
                                                                          have hnfin : n - 41750 < 50 := by omega
                                                                          simpa [Nat.sub_add_cancel hoff] using m1_w35 ⟨n - 41750, hnfin⟩
                                                                        ·
                                                                          by_cases h36 : n < 41850
                                                                          · have hoff : 41800 ≤ n := by omega
                                                                            have hnfin : n - 41800 < 50 := by omega
                                                                            simpa [Nat.sub_add_cancel hoff] using m1_w36 ⟨n - 41800, hnfin⟩
                                                                          ·
                                                                            by_cases h37 : n < 41900
                                                                            · have hoff : 41850 ≤ n := by omega
                                                                              have hnfin : n - 41850 < 50 := by omega
                                                                              simpa [Nat.sub_add_cancel hoff] using m1_w37 ⟨n - 41850, hnfin⟩
                                                                            ·
                                                                              by_cases h38 : n < 41950
                                                                              · have hoff : 41900 ≤ n := by omega
                                                                                have hnfin : n - 41900 < 50 := by omega
                                                                                simpa [Nat.sub_add_cancel hoff] using m1_w38 ⟨n - 41900, hnfin⟩
                                                                              ·
                                                                                by_cases h39 : n < 42000
                                                                                · have hoff : 41950 ≤ n := by omega
                                                                                  have hnfin : n - 41950 < 50 := by omega
                                                                                  simpa [Nat.sub_add_cancel hoff] using m1_w39 ⟨n - 41950, hnfin⟩
                                                                                ·
                                                                                  by_cases h40 : n < 42050
                                                                                  · have hoff : 42000 ≤ n := by omega
                                                                                    have hnfin : n - 42000 < 50 := by omega
                                                                                    simpa [Nat.sub_add_cancel hoff] using m1_w40 ⟨n - 42000, hnfin⟩
                                                                                  ·
                                                                                    by_cases h41 : n < 42100
                                                                                    · have hoff : 42050 ≤ n := by omega
                                                                                      have hnfin : n - 42050 < 50 := by omega
                                                                                      simpa [Nat.sub_add_cancel hoff] using m1_w41 ⟨n - 42050, hnfin⟩
                                                                                    ·
                                                                                      by_cases h42 : n < 42150
                                                                                      · have hoff : 42100 ≤ n := by omega
                                                                                        have hnfin : n - 42100 < 50 := by omega
                                                                                        simpa [Nat.sub_add_cancel hoff] using m1_w42 ⟨n - 42100, hnfin⟩
                                                                                      ·
                                                                                        by_cases h43 : n < 42200
                                                                                        · have hoff : 42150 ≤ n := by omega
                                                                                          have hnfin : n - 42150 < 50 := by omega
                                                                                          simpa [Nat.sub_add_cancel hoff] using m1_w43 ⟨n - 42150, hnfin⟩
                                                                                        ·
                                                                                          by_cases h44 : n < 42250
                                                                                          · have hoff : 42200 ≤ n := by omega
                                                                                            have hnfin : n - 42200 < 50 := by omega
                                                                                            simpa [Nat.sub_add_cancel hoff] using m1_w44 ⟨n - 42200, hnfin⟩
                                                                                          ·
                                                                                            by_cases h45 : n < 42300
                                                                                            · have hoff : 42250 ≤ n := by omega
                                                                                              have hnfin : n - 42250 < 50 := by omega
                                                                                              simpa [Nat.sub_add_cancel hoff] using m1_w45 ⟨n - 42250, hnfin⟩
                                                                                            ·
                                                                                              by_cases h46 : n < 42350
                                                                                              · have hoff : 42300 ≤ n := by omega
                                                                                                have hnfin : n - 42300 < 50 := by omega
                                                                                                simpa [Nat.sub_add_cancel hoff] using m1_w46 ⟨n - 42300, hnfin⟩
                                                                                              ·
                                                                                                by_cases h47 : n < 42400
                                                                                                · have hoff : 42350 ≤ n := by omega
                                                                                                  have hnfin : n - 42350 < 50 := by omega
                                                                                                  simpa [Nat.sub_add_cancel hoff] using m1_w47 ⟨n - 42350, hnfin⟩
                                                                                                ·
                                                                                                  by_cases h48 : n < 42450
                                                                                                  · have hoff : 42400 ≤ n := by omega
                                                                                                    have hnfin : n - 42400 < 50 := by omega
                                                                                                    simpa [Nat.sub_add_cancel hoff] using m1_w48 ⟨n - 42400, hnfin⟩
                                                                                                  ·
                                                                                                    by_cases h49 : n < 42500
                                                                                                    · have hoff : 42450 ≤ n := by omega
                                                                                                      have hnfin : n - 42450 < 50 := by omega
                                                                                                      simpa [Nat.sub_add_cancel hoff] using m1_w49 ⟨n - 42450, hnfin⟩
                                                                                                    ·
                                                                                                      omega
end IntMul.Kappa.R8.Bit.Oppbank.LandMonoFixA16


