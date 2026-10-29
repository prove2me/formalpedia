-- Prove2me | Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankLandMonoFixA3
-- name    : IntMul_Kappa_R8_Data_BitOppbankLandMonoFixA3
-- status  : Definition
-- author  : @Ethan Cheung Wang
-- created : 2026-10-28T21:13:44.498488+00:00
-- url     : https://prove2.me/theorems/159e48d2-2ea0-4d0f-abe9-c520800687cf
-- title:
--   Dim-gated densSup land mono FixA pack 3
-- statement:
--   # Dim-gated densSup land (PndFix), pack A3
--
--   Range consolidators for $n\in[7500,10000)$.
-- source:
--   R8 BitOppbank PndFix

-- LandMonoFixA3: PUBLIC dim-gated land + range consolidators (PndFix)
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
namespace IntMul.Kappa.R8.Bit.Oppbank.LandMonoFixA3
def arg0 (n : ℕ) : ℕ := Nat.land (argF n) 65535
def arg1 (n : ℕ) : ℕ := Nat.shiftRight (argF n) 16
theorem m0_w0 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 7500))) (dimF (n.val + 7500)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 7500))) (densSupG (n.val + 7500))) (densSupG (arg0 (n.val + 7500)))) = true := by decide
theorem m1_w0 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 7500))) (dimF (n.val + 7500)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 7500))) (densSupG (n.val + 7500))) (densSupG (arg1 (n.val + 7500)))) = true := by decide
theorem m0_w1 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 7550))) (dimF (n.val + 7550)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 7550))) (densSupG (n.val + 7550))) (densSupG (arg0 (n.val + 7550)))) = true := by decide
theorem m1_w1 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 7550))) (dimF (n.val + 7550)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 7550))) (densSupG (n.val + 7550))) (densSupG (arg1 (n.val + 7550)))) = true := by decide
theorem m0_w2 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 7600))) (dimF (n.val + 7600)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 7600))) (densSupG (n.val + 7600))) (densSupG (arg0 (n.val + 7600)))) = true := by decide
theorem m1_w2 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 7600))) (dimF (n.val + 7600)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 7600))) (densSupG (n.val + 7600))) (densSupG (arg1 (n.val + 7600)))) = true := by decide
theorem m0_w3 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 7650))) (dimF (n.val + 7650)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 7650))) (densSupG (n.val + 7650))) (densSupG (arg0 (n.val + 7650)))) = true := by decide
theorem m1_w3 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 7650))) (dimF (n.val + 7650)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 7650))) (densSupG (n.val + 7650))) (densSupG (arg1 (n.val + 7650)))) = true := by decide
theorem m0_w4 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 7700))) (dimF (n.val + 7700)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 7700))) (densSupG (n.val + 7700))) (densSupG (arg0 (n.val + 7700)))) = true := by decide
theorem m1_w4 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 7700))) (dimF (n.val + 7700)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 7700))) (densSupG (n.val + 7700))) (densSupG (arg1 (n.val + 7700)))) = true := by decide
theorem m0_w5 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 7750))) (dimF (n.val + 7750)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 7750))) (densSupG (n.val + 7750))) (densSupG (arg0 (n.val + 7750)))) = true := by decide
theorem m1_w5 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 7750))) (dimF (n.val + 7750)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 7750))) (densSupG (n.val + 7750))) (densSupG (arg1 (n.val + 7750)))) = true := by decide
theorem m0_w6 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 7800))) (dimF (n.val + 7800)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 7800))) (densSupG (n.val + 7800))) (densSupG (arg0 (n.val + 7800)))) = true := by decide
theorem m1_w6 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 7800))) (dimF (n.val + 7800)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 7800))) (densSupG (n.val + 7800))) (densSupG (arg1 (n.val + 7800)))) = true := by decide
theorem m0_w7 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 7850))) (dimF (n.val + 7850)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 7850))) (densSupG (n.val + 7850))) (densSupG (arg0 (n.val + 7850)))) = true := by decide
theorem m1_w7 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 7850))) (dimF (n.val + 7850)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 7850))) (densSupG (n.val + 7850))) (densSupG (arg1 (n.val + 7850)))) = true := by decide
theorem m0_w8 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 7900))) (dimF (n.val + 7900)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 7900))) (densSupG (n.val + 7900))) (densSupG (arg0 (n.val + 7900)))) = true := by decide
theorem m1_w8 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 7900))) (dimF (n.val + 7900)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 7900))) (densSupG (n.val + 7900))) (densSupG (arg1 (n.val + 7900)))) = true := by decide
theorem m0_w9 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 7950))) (dimF (n.val + 7950)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 7950))) (densSupG (n.val + 7950))) (densSupG (arg0 (n.val + 7950)))) = true := by decide
theorem m1_w9 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 7950))) (dimF (n.val + 7950)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 7950))) (densSupG (n.val + 7950))) (densSupG (arg1 (n.val + 7950)))) = true := by decide
theorem m0_w10 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 8000))) (dimF (n.val + 8000)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 8000))) (densSupG (n.val + 8000))) (densSupG (arg0 (n.val + 8000)))) = true := by decide
theorem m1_w10 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 8000))) (dimF (n.val + 8000)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 8000))) (densSupG (n.val + 8000))) (densSupG (arg1 (n.val + 8000)))) = true := by decide
theorem m0_w11 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 8050))) (dimF (n.val + 8050)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 8050))) (densSupG (n.val + 8050))) (densSupG (arg0 (n.val + 8050)))) = true := by decide
theorem m1_w11 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 8050))) (dimF (n.val + 8050)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 8050))) (densSupG (n.val + 8050))) (densSupG (arg1 (n.val + 8050)))) = true := by decide
theorem m0_w12 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 8100))) (dimF (n.val + 8100)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 8100))) (densSupG (n.val + 8100))) (densSupG (arg0 (n.val + 8100)))) = true := by decide
theorem m1_w12 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 8100))) (dimF (n.val + 8100)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 8100))) (densSupG (n.val + 8100))) (densSupG (arg1 (n.val + 8100)))) = true := by decide
theorem m0_w13 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 8150))) (dimF (n.val + 8150)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 8150))) (densSupG (n.val + 8150))) (densSupG (arg0 (n.val + 8150)))) = true := by decide
theorem m1_w13 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 8150))) (dimF (n.val + 8150)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 8150))) (densSupG (n.val + 8150))) (densSupG (arg1 (n.val + 8150)))) = true := by decide
theorem m0_w14 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 8200))) (dimF (n.val + 8200)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 8200))) (densSupG (n.val + 8200))) (densSupG (arg0 (n.val + 8200)))) = true := by decide
theorem m1_w14 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 8200))) (dimF (n.val + 8200)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 8200))) (densSupG (n.val + 8200))) (densSupG (arg1 (n.val + 8200)))) = true := by decide
theorem m0_w15 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 8250))) (dimF (n.val + 8250)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 8250))) (densSupG (n.val + 8250))) (densSupG (arg0 (n.val + 8250)))) = true := by decide
theorem m1_w15 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 8250))) (dimF (n.val + 8250)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 8250))) (densSupG (n.val + 8250))) (densSupG (arg1 (n.val + 8250)))) = true := by decide
theorem m0_w16 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 8300))) (dimF (n.val + 8300)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 8300))) (densSupG (n.val + 8300))) (densSupG (arg0 (n.val + 8300)))) = true := by decide
theorem m1_w16 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 8300))) (dimF (n.val + 8300)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 8300))) (densSupG (n.val + 8300))) (densSupG (arg1 (n.val + 8300)))) = true := by decide
theorem m0_w17 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 8350))) (dimF (n.val + 8350)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 8350))) (densSupG (n.val + 8350))) (densSupG (arg0 (n.val + 8350)))) = true := by decide
theorem m1_w17 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 8350))) (dimF (n.val + 8350)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 8350))) (densSupG (n.val + 8350))) (densSupG (arg1 (n.val + 8350)))) = true := by decide
theorem m0_w18 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 8400))) (dimF (n.val + 8400)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 8400))) (densSupG (n.val + 8400))) (densSupG (arg0 (n.val + 8400)))) = true := by decide
theorem m1_w18 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 8400))) (dimF (n.val + 8400)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 8400))) (densSupG (n.val + 8400))) (densSupG (arg1 (n.val + 8400)))) = true := by decide
theorem m0_w19 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 8450))) (dimF (n.val + 8450)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 8450))) (densSupG (n.val + 8450))) (densSupG (arg0 (n.val + 8450)))) = true := by decide
theorem m1_w19 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 8450))) (dimF (n.val + 8450)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 8450))) (densSupG (n.val + 8450))) (densSupG (arg1 (n.val + 8450)))) = true := by decide
theorem m0_w20 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 8500))) (dimF (n.val + 8500)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 8500))) (densSupG (n.val + 8500))) (densSupG (arg0 (n.val + 8500)))) = true := by decide
theorem m1_w20 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 8500))) (dimF (n.val + 8500)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 8500))) (densSupG (n.val + 8500))) (densSupG (arg1 (n.val + 8500)))) = true := by decide
theorem m0_w21 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 8550))) (dimF (n.val + 8550)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 8550))) (densSupG (n.val + 8550))) (densSupG (arg0 (n.val + 8550)))) = true := by decide
theorem m1_w21 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 8550))) (dimF (n.val + 8550)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 8550))) (densSupG (n.val + 8550))) (densSupG (arg1 (n.val + 8550)))) = true := by decide
theorem m0_w22 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 8600))) (dimF (n.val + 8600)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 8600))) (densSupG (n.val + 8600))) (densSupG (arg0 (n.val + 8600)))) = true := by decide
theorem m1_w22 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 8600))) (dimF (n.val + 8600)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 8600))) (densSupG (n.val + 8600))) (densSupG (arg1 (n.val + 8600)))) = true := by decide
theorem m0_w23 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 8650))) (dimF (n.val + 8650)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 8650))) (densSupG (n.val + 8650))) (densSupG (arg0 (n.val + 8650)))) = true := by decide
theorem m1_w23 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 8650))) (dimF (n.val + 8650)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 8650))) (densSupG (n.val + 8650))) (densSupG (arg1 (n.val + 8650)))) = true := by decide
theorem m0_w24 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 8700))) (dimF (n.val + 8700)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 8700))) (densSupG (n.val + 8700))) (densSupG (arg0 (n.val + 8700)))) = true := by decide
theorem m1_w24 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 8700))) (dimF (n.val + 8700)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 8700))) (densSupG (n.val + 8700))) (densSupG (arg1 (n.val + 8700)))) = true := by decide
theorem m0_w25 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 8750))) (dimF (n.val + 8750)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 8750))) (densSupG (n.val + 8750))) (densSupG (arg0 (n.val + 8750)))) = true := by decide
theorem m1_w25 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 8750))) (dimF (n.val + 8750)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 8750))) (densSupG (n.val + 8750))) (densSupG (arg1 (n.val + 8750)))) = true := by decide
theorem m0_w26 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 8800))) (dimF (n.val + 8800)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 8800))) (densSupG (n.val + 8800))) (densSupG (arg0 (n.val + 8800)))) = true := by decide
theorem m1_w26 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 8800))) (dimF (n.val + 8800)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 8800))) (densSupG (n.val + 8800))) (densSupG (arg1 (n.val + 8800)))) = true := by decide
theorem m0_w27 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 8850))) (dimF (n.val + 8850)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 8850))) (densSupG (n.val + 8850))) (densSupG (arg0 (n.val + 8850)))) = true := by decide
theorem m1_w27 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 8850))) (dimF (n.val + 8850)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 8850))) (densSupG (n.val + 8850))) (densSupG (arg1 (n.val + 8850)))) = true := by decide
theorem m0_w28 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 8900))) (dimF (n.val + 8900)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 8900))) (densSupG (n.val + 8900))) (densSupG (arg0 (n.val + 8900)))) = true := by decide
theorem m1_w28 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 8900))) (dimF (n.val + 8900)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 8900))) (densSupG (n.val + 8900))) (densSupG (arg1 (n.val + 8900)))) = true := by decide
theorem m0_w29 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 8950))) (dimF (n.val + 8950)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 8950))) (densSupG (n.val + 8950))) (densSupG (arg0 (n.val + 8950)))) = true := by decide
theorem m1_w29 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 8950))) (dimF (n.val + 8950)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 8950))) (densSupG (n.val + 8950))) (densSupG (arg1 (n.val + 8950)))) = true := by decide
theorem m0_w30 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 9000))) (dimF (n.val + 9000)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 9000))) (densSupG (n.val + 9000))) (densSupG (arg0 (n.val + 9000)))) = true := by decide
theorem m1_w30 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 9000))) (dimF (n.val + 9000)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 9000))) (densSupG (n.val + 9000))) (densSupG (arg1 (n.val + 9000)))) = true := by decide
theorem m0_w31 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 9050))) (dimF (n.val + 9050)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 9050))) (densSupG (n.val + 9050))) (densSupG (arg0 (n.val + 9050)))) = true := by decide
theorem m1_w31 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 9050))) (dimF (n.val + 9050)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 9050))) (densSupG (n.val + 9050))) (densSupG (arg1 (n.val + 9050)))) = true := by decide
theorem m0_w32 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 9100))) (dimF (n.val + 9100)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 9100))) (densSupG (n.val + 9100))) (densSupG (arg0 (n.val + 9100)))) = true := by decide
theorem m1_w32 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 9100))) (dimF (n.val + 9100)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 9100))) (densSupG (n.val + 9100))) (densSupG (arg1 (n.val + 9100)))) = true := by decide
theorem m0_w33 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 9150))) (dimF (n.val + 9150)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 9150))) (densSupG (n.val + 9150))) (densSupG (arg0 (n.val + 9150)))) = true := by decide
theorem m1_w33 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 9150))) (dimF (n.val + 9150)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 9150))) (densSupG (n.val + 9150))) (densSupG (arg1 (n.val + 9150)))) = true := by decide
theorem m0_w34 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 9200))) (dimF (n.val + 9200)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 9200))) (densSupG (n.val + 9200))) (densSupG (arg0 (n.val + 9200)))) = true := by decide
theorem m1_w34 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 9200))) (dimF (n.val + 9200)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 9200))) (densSupG (n.val + 9200))) (densSupG (arg1 (n.val + 9200)))) = true := by decide
theorem m0_w35 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 9250))) (dimF (n.val + 9250)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 9250))) (densSupG (n.val + 9250))) (densSupG (arg0 (n.val + 9250)))) = true := by decide
theorem m1_w35 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 9250))) (dimF (n.val + 9250)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 9250))) (densSupG (n.val + 9250))) (densSupG (arg1 (n.val + 9250)))) = true := by decide
theorem m0_w36 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 9300))) (dimF (n.val + 9300)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 9300))) (densSupG (n.val + 9300))) (densSupG (arg0 (n.val + 9300)))) = true := by decide
theorem m1_w36 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 9300))) (dimF (n.val + 9300)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 9300))) (densSupG (n.val + 9300))) (densSupG (arg1 (n.val + 9300)))) = true := by decide
theorem m0_w37 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 9350))) (dimF (n.val + 9350)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 9350))) (densSupG (n.val + 9350))) (densSupG (arg0 (n.val + 9350)))) = true := by decide
theorem m1_w37 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 9350))) (dimF (n.val + 9350)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 9350))) (densSupG (n.val + 9350))) (densSupG (arg1 (n.val + 9350)))) = true := by decide
theorem m0_w38 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 9400))) (dimF (n.val + 9400)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 9400))) (densSupG (n.val + 9400))) (densSupG (arg0 (n.val + 9400)))) = true := by decide
theorem m1_w38 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 9400))) (dimF (n.val + 9400)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 9400))) (densSupG (n.val + 9400))) (densSupG (arg1 (n.val + 9400)))) = true := by decide
theorem m0_w39 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 9450))) (dimF (n.val + 9450)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 9450))) (densSupG (n.val + 9450))) (densSupG (arg0 (n.val + 9450)))) = true := by decide
theorem m1_w39 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 9450))) (dimF (n.val + 9450)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 9450))) (densSupG (n.val + 9450))) (densSupG (arg1 (n.val + 9450)))) = true := by decide
theorem m0_w40 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 9500))) (dimF (n.val + 9500)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 9500))) (densSupG (n.val + 9500))) (densSupG (arg0 (n.val + 9500)))) = true := by decide
theorem m1_w40 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 9500))) (dimF (n.val + 9500)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 9500))) (densSupG (n.val + 9500))) (densSupG (arg1 (n.val + 9500)))) = true := by decide
theorem m0_w41 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 9550))) (dimF (n.val + 9550)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 9550))) (densSupG (n.val + 9550))) (densSupG (arg0 (n.val + 9550)))) = true := by decide
theorem m1_w41 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 9550))) (dimF (n.val + 9550)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 9550))) (densSupG (n.val + 9550))) (densSupG (arg1 (n.val + 9550)))) = true := by decide
theorem m0_w42 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 9600))) (dimF (n.val + 9600)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 9600))) (densSupG (n.val + 9600))) (densSupG (arg0 (n.val + 9600)))) = true := by decide
theorem m1_w42 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 9600))) (dimF (n.val + 9600)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 9600))) (densSupG (n.val + 9600))) (densSupG (arg1 (n.val + 9600)))) = true := by decide
theorem m0_w43 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 9650))) (dimF (n.val + 9650)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 9650))) (densSupG (n.val + 9650))) (densSupG (arg0 (n.val + 9650)))) = true := by decide
theorem m1_w43 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 9650))) (dimF (n.val + 9650)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 9650))) (densSupG (n.val + 9650))) (densSupG (arg1 (n.val + 9650)))) = true := by decide
theorem m0_w44 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 9700))) (dimF (n.val + 9700)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 9700))) (densSupG (n.val + 9700))) (densSupG (arg0 (n.val + 9700)))) = true := by decide
theorem m1_w44 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 9700))) (dimF (n.val + 9700)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 9700))) (densSupG (n.val + 9700))) (densSupG (arg1 (n.val + 9700)))) = true := by decide
theorem m0_w45 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 9750))) (dimF (n.val + 9750)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 9750))) (densSupG (n.val + 9750))) (densSupG (arg0 (n.val + 9750)))) = true := by decide
theorem m1_w45 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 9750))) (dimF (n.val + 9750)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 9750))) (densSupG (n.val + 9750))) (densSupG (arg1 (n.val + 9750)))) = true := by decide
theorem m0_w46 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 9800))) (dimF (n.val + 9800)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 9800))) (densSupG (n.val + 9800))) (densSupG (arg0 (n.val + 9800)))) = true := by decide
theorem m1_w46 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 9800))) (dimF (n.val + 9800)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 9800))) (densSupG (n.val + 9800))) (densSupG (arg1 (n.val + 9800)))) = true := by decide
theorem m0_w47 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 9850))) (dimF (n.val + 9850)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 9850))) (densSupG (n.val + 9850))) (densSupG (arg0 (n.val + 9850)))) = true := by decide
theorem m1_w47 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 9850))) (dimF (n.val + 9850)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 9850))) (densSupG (n.val + 9850))) (densSupG (arg1 (n.val + 9850)))) = true := by decide
theorem m0_w48 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 9900))) (dimF (n.val + 9900)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 9900))) (densSupG (n.val + 9900))) (densSupG (arg0 (n.val + 9900)))) = true := by decide
theorem m1_w48 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 9900))) (dimF (n.val + 9900)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 9900))) (densSupG (n.val + 9900))) (densSupG (arg1 (n.val + 9900)))) = true := by decide
theorem m0_w49 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 9950))) (dimF (n.val + 9950)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 9950))) (densSupG (n.val + 9950))) (densSupG (arg0 (n.val + 9950)))) = true := by decide
theorem m1_w49 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 9950))) (dimF (n.val + 9950)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 9950))) (densSupG (n.val + 9950))) (densSupG (arg1 (n.val + 9950)))) = true := by decide
theorem land0_range (n : ℕ) (hn0 : 7500 ≤ n) (hn1 : n < 10000) :
    (!Nat.blt (dimF (arg0 n)) (dimF n) ||
      Nat.beq (Nat.land (densSupG (arg0 n)) (densSupG n)) (densSupG (arg0 n))) = true := by
  by_cases h0 : n < 7550
  · have hoff : 7500 ≤ n := by omega
    have hnfin : n - 7500 < 50 := by omega
    simpa [Nat.sub_add_cancel hoff] using m0_w0 ⟨n - 7500, hnfin⟩
  ·
    by_cases h1 : n < 7600
    · have hoff : 7550 ≤ n := by omega
      have hnfin : n - 7550 < 50 := by omega
      simpa [Nat.sub_add_cancel hoff] using m0_w1 ⟨n - 7550, hnfin⟩
    ·
      by_cases h2 : n < 7650
      · have hoff : 7600 ≤ n := by omega
        have hnfin : n - 7600 < 50 := by omega
        simpa [Nat.sub_add_cancel hoff] using m0_w2 ⟨n - 7600, hnfin⟩
      ·
        by_cases h3 : n < 7700
        · have hoff : 7650 ≤ n := by omega
          have hnfin : n - 7650 < 50 := by omega
          simpa [Nat.sub_add_cancel hoff] using m0_w3 ⟨n - 7650, hnfin⟩
        ·
          by_cases h4 : n < 7750
          · have hoff : 7700 ≤ n := by omega
            have hnfin : n - 7700 < 50 := by omega
            simpa [Nat.sub_add_cancel hoff] using m0_w4 ⟨n - 7700, hnfin⟩
          ·
            by_cases h5 : n < 7800
            · have hoff : 7750 ≤ n := by omega
              have hnfin : n - 7750 < 50 := by omega
              simpa [Nat.sub_add_cancel hoff] using m0_w5 ⟨n - 7750, hnfin⟩
            ·
              by_cases h6 : n < 7850
              · have hoff : 7800 ≤ n := by omega
                have hnfin : n - 7800 < 50 := by omega
                simpa [Nat.sub_add_cancel hoff] using m0_w6 ⟨n - 7800, hnfin⟩
              ·
                by_cases h7 : n < 7900
                · have hoff : 7850 ≤ n := by omega
                  have hnfin : n - 7850 < 50 := by omega
                  simpa [Nat.sub_add_cancel hoff] using m0_w7 ⟨n - 7850, hnfin⟩
                ·
                  by_cases h8 : n < 7950
                  · have hoff : 7900 ≤ n := by omega
                    have hnfin : n - 7900 < 50 := by omega
                    simpa [Nat.sub_add_cancel hoff] using m0_w8 ⟨n - 7900, hnfin⟩
                  ·
                    by_cases h9 : n < 8000
                    · have hoff : 7950 ≤ n := by omega
                      have hnfin : n - 7950 < 50 := by omega
                      simpa [Nat.sub_add_cancel hoff] using m0_w9 ⟨n - 7950, hnfin⟩
                    ·
                      by_cases h10 : n < 8050
                      · have hoff : 8000 ≤ n := by omega
                        have hnfin : n - 8000 < 50 := by omega
                        simpa [Nat.sub_add_cancel hoff] using m0_w10 ⟨n - 8000, hnfin⟩
                      ·
                        by_cases h11 : n < 8100
                        · have hoff : 8050 ≤ n := by omega
                          have hnfin : n - 8050 < 50 := by omega
                          simpa [Nat.sub_add_cancel hoff] using m0_w11 ⟨n - 8050, hnfin⟩
                        ·
                          by_cases h12 : n < 8150
                          · have hoff : 8100 ≤ n := by omega
                            have hnfin : n - 8100 < 50 := by omega
                            simpa [Nat.sub_add_cancel hoff] using m0_w12 ⟨n - 8100, hnfin⟩
                          ·
                            by_cases h13 : n < 8200
                            · have hoff : 8150 ≤ n := by omega
                              have hnfin : n - 8150 < 50 := by omega
                              simpa [Nat.sub_add_cancel hoff] using m0_w13 ⟨n - 8150, hnfin⟩
                            ·
                              by_cases h14 : n < 8250
                              · have hoff : 8200 ≤ n := by omega
                                have hnfin : n - 8200 < 50 := by omega
                                simpa [Nat.sub_add_cancel hoff] using m0_w14 ⟨n - 8200, hnfin⟩
                              ·
                                by_cases h15 : n < 8300
                                · have hoff : 8250 ≤ n := by omega
                                  have hnfin : n - 8250 < 50 := by omega
                                  simpa [Nat.sub_add_cancel hoff] using m0_w15 ⟨n - 8250, hnfin⟩
                                ·
                                  by_cases h16 : n < 8350
                                  · have hoff : 8300 ≤ n := by omega
                                    have hnfin : n - 8300 < 50 := by omega
                                    simpa [Nat.sub_add_cancel hoff] using m0_w16 ⟨n - 8300, hnfin⟩
                                  ·
                                    by_cases h17 : n < 8400
                                    · have hoff : 8350 ≤ n := by omega
                                      have hnfin : n - 8350 < 50 := by omega
                                      simpa [Nat.sub_add_cancel hoff] using m0_w17 ⟨n - 8350, hnfin⟩
                                    ·
                                      by_cases h18 : n < 8450
                                      · have hoff : 8400 ≤ n := by omega
                                        have hnfin : n - 8400 < 50 := by omega
                                        simpa [Nat.sub_add_cancel hoff] using m0_w18 ⟨n - 8400, hnfin⟩
                                      ·
                                        by_cases h19 : n < 8500
                                        · have hoff : 8450 ≤ n := by omega
                                          have hnfin : n - 8450 < 50 := by omega
                                          simpa [Nat.sub_add_cancel hoff] using m0_w19 ⟨n - 8450, hnfin⟩
                                        ·
                                          by_cases h20 : n < 8550
                                          · have hoff : 8500 ≤ n := by omega
                                            have hnfin : n - 8500 < 50 := by omega
                                            simpa [Nat.sub_add_cancel hoff] using m0_w20 ⟨n - 8500, hnfin⟩
                                          ·
                                            by_cases h21 : n < 8600
                                            · have hoff : 8550 ≤ n := by omega
                                              have hnfin : n - 8550 < 50 := by omega
                                              simpa [Nat.sub_add_cancel hoff] using m0_w21 ⟨n - 8550, hnfin⟩
                                            ·
                                              by_cases h22 : n < 8650
                                              · have hoff : 8600 ≤ n := by omega
                                                have hnfin : n - 8600 < 50 := by omega
                                                simpa [Nat.sub_add_cancel hoff] using m0_w22 ⟨n - 8600, hnfin⟩
                                              ·
                                                by_cases h23 : n < 8700
                                                · have hoff : 8650 ≤ n := by omega
                                                  have hnfin : n - 8650 < 50 := by omega
                                                  simpa [Nat.sub_add_cancel hoff] using m0_w23 ⟨n - 8650, hnfin⟩
                                                ·
                                                  by_cases h24 : n < 8750
                                                  · have hoff : 8700 ≤ n := by omega
                                                    have hnfin : n - 8700 < 50 := by omega
                                                    simpa [Nat.sub_add_cancel hoff] using m0_w24 ⟨n - 8700, hnfin⟩
                                                  ·
                                                    by_cases h25 : n < 8800
                                                    · have hoff : 8750 ≤ n := by omega
                                                      have hnfin : n - 8750 < 50 := by omega
                                                      simpa [Nat.sub_add_cancel hoff] using m0_w25 ⟨n - 8750, hnfin⟩
                                                    ·
                                                      by_cases h26 : n < 8850
                                                      · have hoff : 8800 ≤ n := by omega
                                                        have hnfin : n - 8800 < 50 := by omega
                                                        simpa [Nat.sub_add_cancel hoff] using m0_w26 ⟨n - 8800, hnfin⟩
                                                      ·
                                                        by_cases h27 : n < 8900
                                                        · have hoff : 8850 ≤ n := by omega
                                                          have hnfin : n - 8850 < 50 := by omega
                                                          simpa [Nat.sub_add_cancel hoff] using m0_w27 ⟨n - 8850, hnfin⟩
                                                        ·
                                                          by_cases h28 : n < 8950
                                                          · have hoff : 8900 ≤ n := by omega
                                                            have hnfin : n - 8900 < 50 := by omega
                                                            simpa [Nat.sub_add_cancel hoff] using m0_w28 ⟨n - 8900, hnfin⟩
                                                          ·
                                                            by_cases h29 : n < 9000
                                                            · have hoff : 8950 ≤ n := by omega
                                                              have hnfin : n - 8950 < 50 := by omega
                                                              simpa [Nat.sub_add_cancel hoff] using m0_w29 ⟨n - 8950, hnfin⟩
                                                            ·
                                                              by_cases h30 : n < 9050
                                                              · have hoff : 9000 ≤ n := by omega
                                                                have hnfin : n - 9000 < 50 := by omega
                                                                simpa [Nat.sub_add_cancel hoff] using m0_w30 ⟨n - 9000, hnfin⟩
                                                              ·
                                                                by_cases h31 : n < 9100
                                                                · have hoff : 9050 ≤ n := by omega
                                                                  have hnfin : n - 9050 < 50 := by omega
                                                                  simpa [Nat.sub_add_cancel hoff] using m0_w31 ⟨n - 9050, hnfin⟩
                                                                ·
                                                                  by_cases h32 : n < 9150
                                                                  · have hoff : 9100 ≤ n := by omega
                                                                    have hnfin : n - 9100 < 50 := by omega
                                                                    simpa [Nat.sub_add_cancel hoff] using m0_w32 ⟨n - 9100, hnfin⟩
                                                                  ·
                                                                    by_cases h33 : n < 9200
                                                                    · have hoff : 9150 ≤ n := by omega
                                                                      have hnfin : n - 9150 < 50 := by omega
                                                                      simpa [Nat.sub_add_cancel hoff] using m0_w33 ⟨n - 9150, hnfin⟩
                                                                    ·
                                                                      by_cases h34 : n < 9250
                                                                      · have hoff : 9200 ≤ n := by omega
                                                                        have hnfin : n - 9200 < 50 := by omega
                                                                        simpa [Nat.sub_add_cancel hoff] using m0_w34 ⟨n - 9200, hnfin⟩
                                                                      ·
                                                                        by_cases h35 : n < 9300
                                                                        · have hoff : 9250 ≤ n := by omega
                                                                          have hnfin : n - 9250 < 50 := by omega
                                                                          simpa [Nat.sub_add_cancel hoff] using m0_w35 ⟨n - 9250, hnfin⟩
                                                                        ·
                                                                          by_cases h36 : n < 9350
                                                                          · have hoff : 9300 ≤ n := by omega
                                                                            have hnfin : n - 9300 < 50 := by omega
                                                                            simpa [Nat.sub_add_cancel hoff] using m0_w36 ⟨n - 9300, hnfin⟩
                                                                          ·
                                                                            by_cases h37 : n < 9400
                                                                            · have hoff : 9350 ≤ n := by omega
                                                                              have hnfin : n - 9350 < 50 := by omega
                                                                              simpa [Nat.sub_add_cancel hoff] using m0_w37 ⟨n - 9350, hnfin⟩
                                                                            ·
                                                                              by_cases h38 : n < 9450
                                                                              · have hoff : 9400 ≤ n := by omega
                                                                                have hnfin : n - 9400 < 50 := by omega
                                                                                simpa [Nat.sub_add_cancel hoff] using m0_w38 ⟨n - 9400, hnfin⟩
                                                                              ·
                                                                                by_cases h39 : n < 9500
                                                                                · have hoff : 9450 ≤ n := by omega
                                                                                  have hnfin : n - 9450 < 50 := by omega
                                                                                  simpa [Nat.sub_add_cancel hoff] using m0_w39 ⟨n - 9450, hnfin⟩
                                                                                ·
                                                                                  by_cases h40 : n < 9550
                                                                                  · have hoff : 9500 ≤ n := by omega
                                                                                    have hnfin : n - 9500 < 50 := by omega
                                                                                    simpa [Nat.sub_add_cancel hoff] using m0_w40 ⟨n - 9500, hnfin⟩
                                                                                  ·
                                                                                    by_cases h41 : n < 9600
                                                                                    · have hoff : 9550 ≤ n := by omega
                                                                                      have hnfin : n - 9550 < 50 := by omega
                                                                                      simpa [Nat.sub_add_cancel hoff] using m0_w41 ⟨n - 9550, hnfin⟩
                                                                                    ·
                                                                                      by_cases h42 : n < 9650
                                                                                      · have hoff : 9600 ≤ n := by omega
                                                                                        have hnfin : n - 9600 < 50 := by omega
                                                                                        simpa [Nat.sub_add_cancel hoff] using m0_w42 ⟨n - 9600, hnfin⟩
                                                                                      ·
                                                                                        by_cases h43 : n < 9700
                                                                                        · have hoff : 9650 ≤ n := by omega
                                                                                          have hnfin : n - 9650 < 50 := by omega
                                                                                          simpa [Nat.sub_add_cancel hoff] using m0_w43 ⟨n - 9650, hnfin⟩
                                                                                        ·
                                                                                          by_cases h44 : n < 9750
                                                                                          · have hoff : 9700 ≤ n := by omega
                                                                                            have hnfin : n - 9700 < 50 := by omega
                                                                                            simpa [Nat.sub_add_cancel hoff] using m0_w44 ⟨n - 9700, hnfin⟩
                                                                                          ·
                                                                                            by_cases h45 : n < 9800
                                                                                            · have hoff : 9750 ≤ n := by omega
                                                                                              have hnfin : n - 9750 < 50 := by omega
                                                                                              simpa [Nat.sub_add_cancel hoff] using m0_w45 ⟨n - 9750, hnfin⟩
                                                                                            ·
                                                                                              by_cases h46 : n < 9850
                                                                                              · have hoff : 9800 ≤ n := by omega
                                                                                                have hnfin : n - 9800 < 50 := by omega
                                                                                                simpa [Nat.sub_add_cancel hoff] using m0_w46 ⟨n - 9800, hnfin⟩
                                                                                              ·
                                                                                                by_cases h47 : n < 9900
                                                                                                · have hoff : 9850 ≤ n := by omega
                                                                                                  have hnfin : n - 9850 < 50 := by omega
                                                                                                  simpa [Nat.sub_add_cancel hoff] using m0_w47 ⟨n - 9850, hnfin⟩
                                                                                                ·
                                                                                                  by_cases h48 : n < 9950
                                                                                                  · have hoff : 9900 ≤ n := by omega
                                                                                                    have hnfin : n - 9900 < 50 := by omega
                                                                                                    simpa [Nat.sub_add_cancel hoff] using m0_w48 ⟨n - 9900, hnfin⟩
                                                                                                  ·
                                                                                                    by_cases h49 : n < 10000
                                                                                                    · have hoff : 9950 ≤ n := by omega
                                                                                                      have hnfin : n - 9950 < 50 := by omega
                                                                                                      simpa [Nat.sub_add_cancel hoff] using m0_w49 ⟨n - 9950, hnfin⟩
                                                                                                    ·
                                                                                                      omega
theorem land1_range (n : ℕ) (hn0 : 7500 ≤ n) (hn1 : n < 10000) :
    (!Nat.blt (dimF (arg1 n)) (dimF n) ||
      Nat.beq (Nat.land (densSupG (arg1 n)) (densSupG n)) (densSupG (arg1 n))) = true := by
  by_cases h0 : n < 7550
  · have hoff : 7500 ≤ n := by omega
    have hnfin : n - 7500 < 50 := by omega
    simpa [Nat.sub_add_cancel hoff] using m1_w0 ⟨n - 7500, hnfin⟩
  ·
    by_cases h1 : n < 7600
    · have hoff : 7550 ≤ n := by omega
      have hnfin : n - 7550 < 50 := by omega
      simpa [Nat.sub_add_cancel hoff] using m1_w1 ⟨n - 7550, hnfin⟩
    ·
      by_cases h2 : n < 7650
      · have hoff : 7600 ≤ n := by omega
        have hnfin : n - 7600 < 50 := by omega
        simpa [Nat.sub_add_cancel hoff] using m1_w2 ⟨n - 7600, hnfin⟩
      ·
        by_cases h3 : n < 7700
        · have hoff : 7650 ≤ n := by omega
          have hnfin : n - 7650 < 50 := by omega
          simpa [Nat.sub_add_cancel hoff] using m1_w3 ⟨n - 7650, hnfin⟩
        ·
          by_cases h4 : n < 7750
          · have hoff : 7700 ≤ n := by omega
            have hnfin : n - 7700 < 50 := by omega
            simpa [Nat.sub_add_cancel hoff] using m1_w4 ⟨n - 7700, hnfin⟩
          ·
            by_cases h5 : n < 7800
            · have hoff : 7750 ≤ n := by omega
              have hnfin : n - 7750 < 50 := by omega
              simpa [Nat.sub_add_cancel hoff] using m1_w5 ⟨n - 7750, hnfin⟩
            ·
              by_cases h6 : n < 7850
              · have hoff : 7800 ≤ n := by omega
                have hnfin : n - 7800 < 50 := by omega
                simpa [Nat.sub_add_cancel hoff] using m1_w6 ⟨n - 7800, hnfin⟩
              ·
                by_cases h7 : n < 7900
                · have hoff : 7850 ≤ n := by omega
                  have hnfin : n - 7850 < 50 := by omega
                  simpa [Nat.sub_add_cancel hoff] using m1_w7 ⟨n - 7850, hnfin⟩
                ·
                  by_cases h8 : n < 7950
                  · have hoff : 7900 ≤ n := by omega
                    have hnfin : n - 7900 < 50 := by omega
                    simpa [Nat.sub_add_cancel hoff] using m1_w8 ⟨n - 7900, hnfin⟩
                  ·
                    by_cases h9 : n < 8000
                    · have hoff : 7950 ≤ n := by omega
                      have hnfin : n - 7950 < 50 := by omega
                      simpa [Nat.sub_add_cancel hoff] using m1_w9 ⟨n - 7950, hnfin⟩
                    ·
                      by_cases h10 : n < 8050
                      · have hoff : 8000 ≤ n := by omega
                        have hnfin : n - 8000 < 50 := by omega
                        simpa [Nat.sub_add_cancel hoff] using m1_w10 ⟨n - 8000, hnfin⟩
                      ·
                        by_cases h11 : n < 8100
                        · have hoff : 8050 ≤ n := by omega
                          have hnfin : n - 8050 < 50 := by omega
                          simpa [Nat.sub_add_cancel hoff] using m1_w11 ⟨n - 8050, hnfin⟩
                        ·
                          by_cases h12 : n < 8150
                          · have hoff : 8100 ≤ n := by omega
                            have hnfin : n - 8100 < 50 := by omega
                            simpa [Nat.sub_add_cancel hoff] using m1_w12 ⟨n - 8100, hnfin⟩
                          ·
                            by_cases h13 : n < 8200
                            · have hoff : 8150 ≤ n := by omega
                              have hnfin : n - 8150 < 50 := by omega
                              simpa [Nat.sub_add_cancel hoff] using m1_w13 ⟨n - 8150, hnfin⟩
                            ·
                              by_cases h14 : n < 8250
                              · have hoff : 8200 ≤ n := by omega
                                have hnfin : n - 8200 < 50 := by omega
                                simpa [Nat.sub_add_cancel hoff] using m1_w14 ⟨n - 8200, hnfin⟩
                              ·
                                by_cases h15 : n < 8300
                                · have hoff : 8250 ≤ n := by omega
                                  have hnfin : n - 8250 < 50 := by omega
                                  simpa [Nat.sub_add_cancel hoff] using m1_w15 ⟨n - 8250, hnfin⟩
                                ·
                                  by_cases h16 : n < 8350
                                  · have hoff : 8300 ≤ n := by omega
                                    have hnfin : n - 8300 < 50 := by omega
                                    simpa [Nat.sub_add_cancel hoff] using m1_w16 ⟨n - 8300, hnfin⟩
                                  ·
                                    by_cases h17 : n < 8400
                                    · have hoff : 8350 ≤ n := by omega
                                      have hnfin : n - 8350 < 50 := by omega
                                      simpa [Nat.sub_add_cancel hoff] using m1_w17 ⟨n - 8350, hnfin⟩
                                    ·
                                      by_cases h18 : n < 8450
                                      · have hoff : 8400 ≤ n := by omega
                                        have hnfin : n - 8400 < 50 := by omega
                                        simpa [Nat.sub_add_cancel hoff] using m1_w18 ⟨n - 8400, hnfin⟩
                                      ·
                                        by_cases h19 : n < 8500
                                        · have hoff : 8450 ≤ n := by omega
                                          have hnfin : n - 8450 < 50 := by omega
                                          simpa [Nat.sub_add_cancel hoff] using m1_w19 ⟨n - 8450, hnfin⟩
                                        ·
                                          by_cases h20 : n < 8550
                                          · have hoff : 8500 ≤ n := by omega
                                            have hnfin : n - 8500 < 50 := by omega
                                            simpa [Nat.sub_add_cancel hoff] using m1_w20 ⟨n - 8500, hnfin⟩
                                          ·
                                            by_cases h21 : n < 8600
                                            · have hoff : 8550 ≤ n := by omega
                                              have hnfin : n - 8550 < 50 := by omega
                                              simpa [Nat.sub_add_cancel hoff] using m1_w21 ⟨n - 8550, hnfin⟩
                                            ·
                                              by_cases h22 : n < 8650
                                              · have hoff : 8600 ≤ n := by omega
                                                have hnfin : n - 8600 < 50 := by omega
                                                simpa [Nat.sub_add_cancel hoff] using m1_w22 ⟨n - 8600, hnfin⟩
                                              ·
                                                by_cases h23 : n < 8700
                                                · have hoff : 8650 ≤ n := by omega
                                                  have hnfin : n - 8650 < 50 := by omega
                                                  simpa [Nat.sub_add_cancel hoff] using m1_w23 ⟨n - 8650, hnfin⟩
                                                ·
                                                  by_cases h24 : n < 8750
                                                  · have hoff : 8700 ≤ n := by omega
                                                    have hnfin : n - 8700 < 50 := by omega
                                                    simpa [Nat.sub_add_cancel hoff] using m1_w24 ⟨n - 8700, hnfin⟩
                                                  ·
                                                    by_cases h25 : n < 8800
                                                    · have hoff : 8750 ≤ n := by omega
                                                      have hnfin : n - 8750 < 50 := by omega
                                                      simpa [Nat.sub_add_cancel hoff] using m1_w25 ⟨n - 8750, hnfin⟩
                                                    ·
                                                      by_cases h26 : n < 8850
                                                      · have hoff : 8800 ≤ n := by omega
                                                        have hnfin : n - 8800 < 50 := by omega
                                                        simpa [Nat.sub_add_cancel hoff] using m1_w26 ⟨n - 8800, hnfin⟩
                                                      ·
                                                        by_cases h27 : n < 8900
                                                        · have hoff : 8850 ≤ n := by omega
                                                          have hnfin : n - 8850 < 50 := by omega
                                                          simpa [Nat.sub_add_cancel hoff] using m1_w27 ⟨n - 8850, hnfin⟩
                                                        ·
                                                          by_cases h28 : n < 8950
                                                          · have hoff : 8900 ≤ n := by omega
                                                            have hnfin : n - 8900 < 50 := by omega
                                                            simpa [Nat.sub_add_cancel hoff] using m1_w28 ⟨n - 8900, hnfin⟩
                                                          ·
                                                            by_cases h29 : n < 9000
                                                            · have hoff : 8950 ≤ n := by omega
                                                              have hnfin : n - 8950 < 50 := by omega
                                                              simpa [Nat.sub_add_cancel hoff] using m1_w29 ⟨n - 8950, hnfin⟩
                                                            ·
                                                              by_cases h30 : n < 9050
                                                              · have hoff : 9000 ≤ n := by omega
                                                                have hnfin : n - 9000 < 50 := by omega
                                                                simpa [Nat.sub_add_cancel hoff] using m1_w30 ⟨n - 9000, hnfin⟩
                                                              ·
                                                                by_cases h31 : n < 9100
                                                                · have hoff : 9050 ≤ n := by omega
                                                                  have hnfin : n - 9050 < 50 := by omega
                                                                  simpa [Nat.sub_add_cancel hoff] using m1_w31 ⟨n - 9050, hnfin⟩
                                                                ·
                                                                  by_cases h32 : n < 9150
                                                                  · have hoff : 9100 ≤ n := by omega
                                                                    have hnfin : n - 9100 < 50 := by omega
                                                                    simpa [Nat.sub_add_cancel hoff] using m1_w32 ⟨n - 9100, hnfin⟩
                                                                  ·
                                                                    by_cases h33 : n < 9200
                                                                    · have hoff : 9150 ≤ n := by omega
                                                                      have hnfin : n - 9150 < 50 := by omega
                                                                      simpa [Nat.sub_add_cancel hoff] using m1_w33 ⟨n - 9150, hnfin⟩
                                                                    ·
                                                                      by_cases h34 : n < 9250
                                                                      · have hoff : 9200 ≤ n := by omega
                                                                        have hnfin : n - 9200 < 50 := by omega
                                                                        simpa [Nat.sub_add_cancel hoff] using m1_w34 ⟨n - 9200, hnfin⟩
                                                                      ·
                                                                        by_cases h35 : n < 9300
                                                                        · have hoff : 9250 ≤ n := by omega
                                                                          have hnfin : n - 9250 < 50 := by omega
                                                                          simpa [Nat.sub_add_cancel hoff] using m1_w35 ⟨n - 9250, hnfin⟩
                                                                        ·
                                                                          by_cases h36 : n < 9350
                                                                          · have hoff : 9300 ≤ n := by omega
                                                                            have hnfin : n - 9300 < 50 := by omega
                                                                            simpa [Nat.sub_add_cancel hoff] using m1_w36 ⟨n - 9300, hnfin⟩
                                                                          ·
                                                                            by_cases h37 : n < 9400
                                                                            · have hoff : 9350 ≤ n := by omega
                                                                              have hnfin : n - 9350 < 50 := by omega
                                                                              simpa [Nat.sub_add_cancel hoff] using m1_w37 ⟨n - 9350, hnfin⟩
                                                                            ·
                                                                              by_cases h38 : n < 9450
                                                                              · have hoff : 9400 ≤ n := by omega
                                                                                have hnfin : n - 9400 < 50 := by omega
                                                                                simpa [Nat.sub_add_cancel hoff] using m1_w38 ⟨n - 9400, hnfin⟩
                                                                              ·
                                                                                by_cases h39 : n < 9500
                                                                                · have hoff : 9450 ≤ n := by omega
                                                                                  have hnfin : n - 9450 < 50 := by omega
                                                                                  simpa [Nat.sub_add_cancel hoff] using m1_w39 ⟨n - 9450, hnfin⟩
                                                                                ·
                                                                                  by_cases h40 : n < 9550
                                                                                  · have hoff : 9500 ≤ n := by omega
                                                                                    have hnfin : n - 9500 < 50 := by omega
                                                                                    simpa [Nat.sub_add_cancel hoff] using m1_w40 ⟨n - 9500, hnfin⟩
                                                                                  ·
                                                                                    by_cases h41 : n < 9600
                                                                                    · have hoff : 9550 ≤ n := by omega
                                                                                      have hnfin : n - 9550 < 50 := by omega
                                                                                      simpa [Nat.sub_add_cancel hoff] using m1_w41 ⟨n - 9550, hnfin⟩
                                                                                    ·
                                                                                      by_cases h42 : n < 9650
                                                                                      · have hoff : 9600 ≤ n := by omega
                                                                                        have hnfin : n - 9600 < 50 := by omega
                                                                                        simpa [Nat.sub_add_cancel hoff] using m1_w42 ⟨n - 9600, hnfin⟩
                                                                                      ·
                                                                                        by_cases h43 : n < 9700
                                                                                        · have hoff : 9650 ≤ n := by omega
                                                                                          have hnfin : n - 9650 < 50 := by omega
                                                                                          simpa [Nat.sub_add_cancel hoff] using m1_w43 ⟨n - 9650, hnfin⟩
                                                                                        ·
                                                                                          by_cases h44 : n < 9750
                                                                                          · have hoff : 9700 ≤ n := by omega
                                                                                            have hnfin : n - 9700 < 50 := by omega
                                                                                            simpa [Nat.sub_add_cancel hoff] using m1_w44 ⟨n - 9700, hnfin⟩
                                                                                          ·
                                                                                            by_cases h45 : n < 9800
                                                                                            · have hoff : 9750 ≤ n := by omega
                                                                                              have hnfin : n - 9750 < 50 := by omega
                                                                                              simpa [Nat.sub_add_cancel hoff] using m1_w45 ⟨n - 9750, hnfin⟩
                                                                                            ·
                                                                                              by_cases h46 : n < 9850
                                                                                              · have hoff : 9800 ≤ n := by omega
                                                                                                have hnfin : n - 9800 < 50 := by omega
                                                                                                simpa [Nat.sub_add_cancel hoff] using m1_w46 ⟨n - 9800, hnfin⟩
                                                                                              ·
                                                                                                by_cases h47 : n < 9900
                                                                                                · have hoff : 9850 ≤ n := by omega
                                                                                                  have hnfin : n - 9850 < 50 := by omega
                                                                                                  simpa [Nat.sub_add_cancel hoff] using m1_w47 ⟨n - 9850, hnfin⟩
                                                                                                ·
                                                                                                  by_cases h48 : n < 9950
                                                                                                  · have hoff : 9900 ≤ n := by omega
                                                                                                    have hnfin : n - 9900 < 50 := by omega
                                                                                                    simpa [Nat.sub_add_cancel hoff] using m1_w48 ⟨n - 9900, hnfin⟩
                                                                                                  ·
                                                                                                    by_cases h49 : n < 10000
                                                                                                    · have hoff : 9950 ≤ n := by omega
                                                                                                      have hnfin : n - 9950 < 50 := by omega
                                                                                                      simpa [Nat.sub_add_cancel hoff] using m1_w49 ⟨n - 9950, hnfin⟩
                                                                                                    ·
                                                                                                      omega
end IntMul.Kappa.R8.Bit.Oppbank.LandMonoFixA3


