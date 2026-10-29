-- Prove2me | Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankLandMonoFixA22
-- name    : IntMul_Kappa_R8_Data_BitOppbankLandMonoFixA22
-- status  : Definition
-- author  : @Ethan Cheung Wang
-- created : 2026-10-28T21:18:47.911022+00:00
-- url     : https://prove2.me/theorems/4c0c1855-eab6-47d1-952e-eed6f6482759
-- title:
--   Dim-gated densSup land mono FixA pack 22
-- statement:
--   # Dim-gated densSup land (PndFix), pack A22
--
--   Range consolidators for $n\in[55000,57500)$.
-- source:
--   R8 BitOppbank PndFix

-- LandMonoFixA22: PUBLIC dim-gated land + range consolidators (PndFix)
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
namespace IntMul.Kappa.R8.Bit.Oppbank.LandMonoFixA22
def arg0 (n : ℕ) : ℕ := Nat.land (argF n) 65535
def arg1 (n : ℕ) : ℕ := Nat.shiftRight (argF n) 16
theorem m0_w0 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 55000))) (dimF (n.val + 55000)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 55000))) (densSupG (n.val + 55000))) (densSupG (arg0 (n.val + 55000)))) = true := by decide
theorem m1_w0 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 55000))) (dimF (n.val + 55000)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 55000))) (densSupG (n.val + 55000))) (densSupG (arg1 (n.val + 55000)))) = true := by decide
theorem m0_w1 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 55050))) (dimF (n.val + 55050)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 55050))) (densSupG (n.val + 55050))) (densSupG (arg0 (n.val + 55050)))) = true := by decide
theorem m1_w1 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 55050))) (dimF (n.val + 55050)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 55050))) (densSupG (n.val + 55050))) (densSupG (arg1 (n.val + 55050)))) = true := by decide
theorem m0_w2 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 55100))) (dimF (n.val + 55100)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 55100))) (densSupG (n.val + 55100))) (densSupG (arg0 (n.val + 55100)))) = true := by decide
theorem m1_w2 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 55100))) (dimF (n.val + 55100)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 55100))) (densSupG (n.val + 55100))) (densSupG (arg1 (n.val + 55100)))) = true := by decide
theorem m0_w3 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 55150))) (dimF (n.val + 55150)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 55150))) (densSupG (n.val + 55150))) (densSupG (arg0 (n.val + 55150)))) = true := by decide
theorem m1_w3 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 55150))) (dimF (n.val + 55150)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 55150))) (densSupG (n.val + 55150))) (densSupG (arg1 (n.val + 55150)))) = true := by decide
theorem m0_w4 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 55200))) (dimF (n.val + 55200)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 55200))) (densSupG (n.val + 55200))) (densSupG (arg0 (n.val + 55200)))) = true := by decide
theorem m1_w4 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 55200))) (dimF (n.val + 55200)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 55200))) (densSupG (n.val + 55200))) (densSupG (arg1 (n.val + 55200)))) = true := by decide
theorem m0_w5 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 55250))) (dimF (n.val + 55250)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 55250))) (densSupG (n.val + 55250))) (densSupG (arg0 (n.val + 55250)))) = true := by decide
theorem m1_w5 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 55250))) (dimF (n.val + 55250)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 55250))) (densSupG (n.val + 55250))) (densSupG (arg1 (n.val + 55250)))) = true := by decide
theorem m0_w6 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 55300))) (dimF (n.val + 55300)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 55300))) (densSupG (n.val + 55300))) (densSupG (arg0 (n.val + 55300)))) = true := by decide
theorem m1_w6 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 55300))) (dimF (n.val + 55300)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 55300))) (densSupG (n.val + 55300))) (densSupG (arg1 (n.val + 55300)))) = true := by decide
theorem m0_w7 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 55350))) (dimF (n.val + 55350)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 55350))) (densSupG (n.val + 55350))) (densSupG (arg0 (n.val + 55350)))) = true := by decide
theorem m1_w7 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 55350))) (dimF (n.val + 55350)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 55350))) (densSupG (n.val + 55350))) (densSupG (arg1 (n.val + 55350)))) = true := by decide
theorem m0_w8 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 55400))) (dimF (n.val + 55400)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 55400))) (densSupG (n.val + 55400))) (densSupG (arg0 (n.val + 55400)))) = true := by decide
theorem m1_w8 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 55400))) (dimF (n.val + 55400)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 55400))) (densSupG (n.val + 55400))) (densSupG (arg1 (n.val + 55400)))) = true := by decide
theorem m0_w9 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 55450))) (dimF (n.val + 55450)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 55450))) (densSupG (n.val + 55450))) (densSupG (arg0 (n.val + 55450)))) = true := by decide
theorem m1_w9 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 55450))) (dimF (n.val + 55450)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 55450))) (densSupG (n.val + 55450))) (densSupG (arg1 (n.val + 55450)))) = true := by decide
theorem m0_w10 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 55500))) (dimF (n.val + 55500)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 55500))) (densSupG (n.val + 55500))) (densSupG (arg0 (n.val + 55500)))) = true := by decide
theorem m1_w10 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 55500))) (dimF (n.val + 55500)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 55500))) (densSupG (n.val + 55500))) (densSupG (arg1 (n.val + 55500)))) = true := by decide
theorem m0_w11 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 55550))) (dimF (n.val + 55550)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 55550))) (densSupG (n.val + 55550))) (densSupG (arg0 (n.val + 55550)))) = true := by decide
theorem m1_w11 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 55550))) (dimF (n.val + 55550)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 55550))) (densSupG (n.val + 55550))) (densSupG (arg1 (n.val + 55550)))) = true := by decide
theorem m0_w12 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 55600))) (dimF (n.val + 55600)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 55600))) (densSupG (n.val + 55600))) (densSupG (arg0 (n.val + 55600)))) = true := by decide
theorem m1_w12 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 55600))) (dimF (n.val + 55600)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 55600))) (densSupG (n.val + 55600))) (densSupG (arg1 (n.val + 55600)))) = true := by decide
theorem m0_w13 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 55650))) (dimF (n.val + 55650)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 55650))) (densSupG (n.val + 55650))) (densSupG (arg0 (n.val + 55650)))) = true := by decide
theorem m1_w13 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 55650))) (dimF (n.val + 55650)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 55650))) (densSupG (n.val + 55650))) (densSupG (arg1 (n.val + 55650)))) = true := by decide
theorem m0_w14 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 55700))) (dimF (n.val + 55700)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 55700))) (densSupG (n.val + 55700))) (densSupG (arg0 (n.val + 55700)))) = true := by decide
theorem m1_w14 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 55700))) (dimF (n.val + 55700)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 55700))) (densSupG (n.val + 55700))) (densSupG (arg1 (n.val + 55700)))) = true := by decide
theorem m0_w15 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 55750))) (dimF (n.val + 55750)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 55750))) (densSupG (n.val + 55750))) (densSupG (arg0 (n.val + 55750)))) = true := by decide
theorem m1_w15 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 55750))) (dimF (n.val + 55750)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 55750))) (densSupG (n.val + 55750))) (densSupG (arg1 (n.val + 55750)))) = true := by decide
theorem m0_w16 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 55800))) (dimF (n.val + 55800)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 55800))) (densSupG (n.val + 55800))) (densSupG (arg0 (n.val + 55800)))) = true := by decide
theorem m1_w16 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 55800))) (dimF (n.val + 55800)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 55800))) (densSupG (n.val + 55800))) (densSupG (arg1 (n.val + 55800)))) = true := by decide
theorem m0_w17 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 55850))) (dimF (n.val + 55850)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 55850))) (densSupG (n.val + 55850))) (densSupG (arg0 (n.val + 55850)))) = true := by decide
theorem m1_w17 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 55850))) (dimF (n.val + 55850)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 55850))) (densSupG (n.val + 55850))) (densSupG (arg1 (n.val + 55850)))) = true := by decide
theorem m0_w18 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 55900))) (dimF (n.val + 55900)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 55900))) (densSupG (n.val + 55900))) (densSupG (arg0 (n.val + 55900)))) = true := by decide
theorem m1_w18 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 55900))) (dimF (n.val + 55900)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 55900))) (densSupG (n.val + 55900))) (densSupG (arg1 (n.val + 55900)))) = true := by decide
theorem m0_w19 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 55950))) (dimF (n.val + 55950)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 55950))) (densSupG (n.val + 55950))) (densSupG (arg0 (n.val + 55950)))) = true := by decide
theorem m1_w19 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 55950))) (dimF (n.val + 55950)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 55950))) (densSupG (n.val + 55950))) (densSupG (arg1 (n.val + 55950)))) = true := by decide
theorem m0_w20 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 56000))) (dimF (n.val + 56000)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 56000))) (densSupG (n.val + 56000))) (densSupG (arg0 (n.val + 56000)))) = true := by decide
theorem m1_w20 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 56000))) (dimF (n.val + 56000)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 56000))) (densSupG (n.val + 56000))) (densSupG (arg1 (n.val + 56000)))) = true := by decide
theorem m0_w21 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 56050))) (dimF (n.val + 56050)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 56050))) (densSupG (n.val + 56050))) (densSupG (arg0 (n.val + 56050)))) = true := by decide
theorem m1_w21 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 56050))) (dimF (n.val + 56050)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 56050))) (densSupG (n.val + 56050))) (densSupG (arg1 (n.val + 56050)))) = true := by decide
theorem m0_w22 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 56100))) (dimF (n.val + 56100)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 56100))) (densSupG (n.val + 56100))) (densSupG (arg0 (n.val + 56100)))) = true := by decide
theorem m1_w22 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 56100))) (dimF (n.val + 56100)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 56100))) (densSupG (n.val + 56100))) (densSupG (arg1 (n.val + 56100)))) = true := by decide
theorem m0_w23 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 56150))) (dimF (n.val + 56150)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 56150))) (densSupG (n.val + 56150))) (densSupG (arg0 (n.val + 56150)))) = true := by decide
theorem m1_w23 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 56150))) (dimF (n.val + 56150)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 56150))) (densSupG (n.val + 56150))) (densSupG (arg1 (n.val + 56150)))) = true := by decide
theorem m0_w24 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 56200))) (dimF (n.val + 56200)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 56200))) (densSupG (n.val + 56200))) (densSupG (arg0 (n.val + 56200)))) = true := by decide
theorem m1_w24 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 56200))) (dimF (n.val + 56200)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 56200))) (densSupG (n.val + 56200))) (densSupG (arg1 (n.val + 56200)))) = true := by decide
theorem m0_w25 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 56250))) (dimF (n.val + 56250)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 56250))) (densSupG (n.val + 56250))) (densSupG (arg0 (n.val + 56250)))) = true := by decide
theorem m1_w25 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 56250))) (dimF (n.val + 56250)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 56250))) (densSupG (n.val + 56250))) (densSupG (arg1 (n.val + 56250)))) = true := by decide
theorem m0_w26 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 56300))) (dimF (n.val + 56300)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 56300))) (densSupG (n.val + 56300))) (densSupG (arg0 (n.val + 56300)))) = true := by decide
theorem m1_w26 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 56300))) (dimF (n.val + 56300)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 56300))) (densSupG (n.val + 56300))) (densSupG (arg1 (n.val + 56300)))) = true := by decide
theorem m0_w27 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 56350))) (dimF (n.val + 56350)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 56350))) (densSupG (n.val + 56350))) (densSupG (arg0 (n.val + 56350)))) = true := by decide
theorem m1_w27 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 56350))) (dimF (n.val + 56350)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 56350))) (densSupG (n.val + 56350))) (densSupG (arg1 (n.val + 56350)))) = true := by decide
theorem m0_w28 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 56400))) (dimF (n.val + 56400)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 56400))) (densSupG (n.val + 56400))) (densSupG (arg0 (n.val + 56400)))) = true := by decide
theorem m1_w28 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 56400))) (dimF (n.val + 56400)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 56400))) (densSupG (n.val + 56400))) (densSupG (arg1 (n.val + 56400)))) = true := by decide
theorem m0_w29 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 56450))) (dimF (n.val + 56450)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 56450))) (densSupG (n.val + 56450))) (densSupG (arg0 (n.val + 56450)))) = true := by decide
theorem m1_w29 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 56450))) (dimF (n.val + 56450)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 56450))) (densSupG (n.val + 56450))) (densSupG (arg1 (n.val + 56450)))) = true := by decide
theorem m0_w30 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 56500))) (dimF (n.val + 56500)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 56500))) (densSupG (n.val + 56500))) (densSupG (arg0 (n.val + 56500)))) = true := by decide
theorem m1_w30 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 56500))) (dimF (n.val + 56500)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 56500))) (densSupG (n.val + 56500))) (densSupG (arg1 (n.val + 56500)))) = true := by decide
theorem m0_w31 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 56550))) (dimF (n.val + 56550)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 56550))) (densSupG (n.val + 56550))) (densSupG (arg0 (n.val + 56550)))) = true := by decide
theorem m1_w31 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 56550))) (dimF (n.val + 56550)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 56550))) (densSupG (n.val + 56550))) (densSupG (arg1 (n.val + 56550)))) = true := by decide
theorem m0_w32 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 56600))) (dimF (n.val + 56600)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 56600))) (densSupG (n.val + 56600))) (densSupG (arg0 (n.val + 56600)))) = true := by decide
theorem m1_w32 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 56600))) (dimF (n.val + 56600)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 56600))) (densSupG (n.val + 56600))) (densSupG (arg1 (n.val + 56600)))) = true := by decide
theorem m0_w33 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 56650))) (dimF (n.val + 56650)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 56650))) (densSupG (n.val + 56650))) (densSupG (arg0 (n.val + 56650)))) = true := by decide
theorem m1_w33 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 56650))) (dimF (n.val + 56650)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 56650))) (densSupG (n.val + 56650))) (densSupG (arg1 (n.val + 56650)))) = true := by decide
theorem m0_w34 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 56700))) (dimF (n.val + 56700)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 56700))) (densSupG (n.val + 56700))) (densSupG (arg0 (n.val + 56700)))) = true := by decide
theorem m1_w34 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 56700))) (dimF (n.val + 56700)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 56700))) (densSupG (n.val + 56700))) (densSupG (arg1 (n.val + 56700)))) = true := by decide
theorem m0_w35 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 56750))) (dimF (n.val + 56750)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 56750))) (densSupG (n.val + 56750))) (densSupG (arg0 (n.val + 56750)))) = true := by decide
theorem m1_w35 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 56750))) (dimF (n.val + 56750)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 56750))) (densSupG (n.val + 56750))) (densSupG (arg1 (n.val + 56750)))) = true := by decide
theorem m0_w36 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 56800))) (dimF (n.val + 56800)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 56800))) (densSupG (n.val + 56800))) (densSupG (arg0 (n.val + 56800)))) = true := by decide
theorem m1_w36 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 56800))) (dimF (n.val + 56800)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 56800))) (densSupG (n.val + 56800))) (densSupG (arg1 (n.val + 56800)))) = true := by decide
theorem m0_w37 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 56850))) (dimF (n.val + 56850)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 56850))) (densSupG (n.val + 56850))) (densSupG (arg0 (n.val + 56850)))) = true := by decide
theorem m1_w37 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 56850))) (dimF (n.val + 56850)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 56850))) (densSupG (n.val + 56850))) (densSupG (arg1 (n.val + 56850)))) = true := by decide
theorem m0_w38 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 56900))) (dimF (n.val + 56900)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 56900))) (densSupG (n.val + 56900))) (densSupG (arg0 (n.val + 56900)))) = true := by decide
theorem m1_w38 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 56900))) (dimF (n.val + 56900)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 56900))) (densSupG (n.val + 56900))) (densSupG (arg1 (n.val + 56900)))) = true := by decide
theorem m0_w39 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 56950))) (dimF (n.val + 56950)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 56950))) (densSupG (n.val + 56950))) (densSupG (arg0 (n.val + 56950)))) = true := by decide
theorem m1_w39 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 56950))) (dimF (n.val + 56950)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 56950))) (densSupG (n.val + 56950))) (densSupG (arg1 (n.val + 56950)))) = true := by decide
theorem m0_w40 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 57000))) (dimF (n.val + 57000)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 57000))) (densSupG (n.val + 57000))) (densSupG (arg0 (n.val + 57000)))) = true := by decide
theorem m1_w40 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 57000))) (dimF (n.val + 57000)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 57000))) (densSupG (n.val + 57000))) (densSupG (arg1 (n.val + 57000)))) = true := by decide
theorem m0_w41 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 57050))) (dimF (n.val + 57050)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 57050))) (densSupG (n.val + 57050))) (densSupG (arg0 (n.val + 57050)))) = true := by decide
theorem m1_w41 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 57050))) (dimF (n.val + 57050)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 57050))) (densSupG (n.val + 57050))) (densSupG (arg1 (n.val + 57050)))) = true := by decide
theorem m0_w42 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 57100))) (dimF (n.val + 57100)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 57100))) (densSupG (n.val + 57100))) (densSupG (arg0 (n.val + 57100)))) = true := by decide
theorem m1_w42 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 57100))) (dimF (n.val + 57100)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 57100))) (densSupG (n.val + 57100))) (densSupG (arg1 (n.val + 57100)))) = true := by decide
theorem m0_w43 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 57150))) (dimF (n.val + 57150)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 57150))) (densSupG (n.val + 57150))) (densSupG (arg0 (n.val + 57150)))) = true := by decide
theorem m1_w43 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 57150))) (dimF (n.val + 57150)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 57150))) (densSupG (n.val + 57150))) (densSupG (arg1 (n.val + 57150)))) = true := by decide
theorem m0_w44 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 57200))) (dimF (n.val + 57200)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 57200))) (densSupG (n.val + 57200))) (densSupG (arg0 (n.val + 57200)))) = true := by decide
theorem m1_w44 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 57200))) (dimF (n.val + 57200)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 57200))) (densSupG (n.val + 57200))) (densSupG (arg1 (n.val + 57200)))) = true := by decide
theorem m0_w45 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 57250))) (dimF (n.val + 57250)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 57250))) (densSupG (n.val + 57250))) (densSupG (arg0 (n.val + 57250)))) = true := by decide
theorem m1_w45 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 57250))) (dimF (n.val + 57250)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 57250))) (densSupG (n.val + 57250))) (densSupG (arg1 (n.val + 57250)))) = true := by decide
theorem m0_w46 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 57300))) (dimF (n.val + 57300)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 57300))) (densSupG (n.val + 57300))) (densSupG (arg0 (n.val + 57300)))) = true := by decide
theorem m1_w46 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 57300))) (dimF (n.val + 57300)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 57300))) (densSupG (n.val + 57300))) (densSupG (arg1 (n.val + 57300)))) = true := by decide
theorem m0_w47 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 57350))) (dimF (n.val + 57350)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 57350))) (densSupG (n.val + 57350))) (densSupG (arg0 (n.val + 57350)))) = true := by decide
theorem m1_w47 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 57350))) (dimF (n.val + 57350)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 57350))) (densSupG (n.val + 57350))) (densSupG (arg1 (n.val + 57350)))) = true := by decide
theorem m0_w48 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 57400))) (dimF (n.val + 57400)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 57400))) (densSupG (n.val + 57400))) (densSupG (arg0 (n.val + 57400)))) = true := by decide
theorem m1_w48 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 57400))) (dimF (n.val + 57400)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 57400))) (densSupG (n.val + 57400))) (densSupG (arg1 (n.val + 57400)))) = true := by decide
theorem m0_w49 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 57450))) (dimF (n.val + 57450)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 57450))) (densSupG (n.val + 57450))) (densSupG (arg0 (n.val + 57450)))) = true := by decide
theorem m1_w49 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 57450))) (dimF (n.val + 57450)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 57450))) (densSupG (n.val + 57450))) (densSupG (arg1 (n.val + 57450)))) = true := by decide
theorem land0_range (n : ℕ) (hn0 : 55000 ≤ n) (hn1 : n < 57500) :
    (!Nat.blt (dimF (arg0 n)) (dimF n) ||
      Nat.beq (Nat.land (densSupG (arg0 n)) (densSupG n)) (densSupG (arg0 n))) = true := by
  by_cases h0 : n < 55050
  · have hoff : 55000 ≤ n := by omega
    have hnfin : n - 55000 < 50 := by omega
    simpa [Nat.sub_add_cancel hoff] using m0_w0 ⟨n - 55000, hnfin⟩
  ·
    by_cases h1 : n < 55100
    · have hoff : 55050 ≤ n := by omega
      have hnfin : n - 55050 < 50 := by omega
      simpa [Nat.sub_add_cancel hoff] using m0_w1 ⟨n - 55050, hnfin⟩
    ·
      by_cases h2 : n < 55150
      · have hoff : 55100 ≤ n := by omega
        have hnfin : n - 55100 < 50 := by omega
        simpa [Nat.sub_add_cancel hoff] using m0_w2 ⟨n - 55100, hnfin⟩
      ·
        by_cases h3 : n < 55200
        · have hoff : 55150 ≤ n := by omega
          have hnfin : n - 55150 < 50 := by omega
          simpa [Nat.sub_add_cancel hoff] using m0_w3 ⟨n - 55150, hnfin⟩
        ·
          by_cases h4 : n < 55250
          · have hoff : 55200 ≤ n := by omega
            have hnfin : n - 55200 < 50 := by omega
            simpa [Nat.sub_add_cancel hoff] using m0_w4 ⟨n - 55200, hnfin⟩
          ·
            by_cases h5 : n < 55300
            · have hoff : 55250 ≤ n := by omega
              have hnfin : n - 55250 < 50 := by omega
              simpa [Nat.sub_add_cancel hoff] using m0_w5 ⟨n - 55250, hnfin⟩
            ·
              by_cases h6 : n < 55350
              · have hoff : 55300 ≤ n := by omega
                have hnfin : n - 55300 < 50 := by omega
                simpa [Nat.sub_add_cancel hoff] using m0_w6 ⟨n - 55300, hnfin⟩
              ·
                by_cases h7 : n < 55400
                · have hoff : 55350 ≤ n := by omega
                  have hnfin : n - 55350 < 50 := by omega
                  simpa [Nat.sub_add_cancel hoff] using m0_w7 ⟨n - 55350, hnfin⟩
                ·
                  by_cases h8 : n < 55450
                  · have hoff : 55400 ≤ n := by omega
                    have hnfin : n - 55400 < 50 := by omega
                    simpa [Nat.sub_add_cancel hoff] using m0_w8 ⟨n - 55400, hnfin⟩
                  ·
                    by_cases h9 : n < 55500
                    · have hoff : 55450 ≤ n := by omega
                      have hnfin : n - 55450 < 50 := by omega
                      simpa [Nat.sub_add_cancel hoff] using m0_w9 ⟨n - 55450, hnfin⟩
                    ·
                      by_cases h10 : n < 55550
                      · have hoff : 55500 ≤ n := by omega
                        have hnfin : n - 55500 < 50 := by omega
                        simpa [Nat.sub_add_cancel hoff] using m0_w10 ⟨n - 55500, hnfin⟩
                      ·
                        by_cases h11 : n < 55600
                        · have hoff : 55550 ≤ n := by omega
                          have hnfin : n - 55550 < 50 := by omega
                          simpa [Nat.sub_add_cancel hoff] using m0_w11 ⟨n - 55550, hnfin⟩
                        ·
                          by_cases h12 : n < 55650
                          · have hoff : 55600 ≤ n := by omega
                            have hnfin : n - 55600 < 50 := by omega
                            simpa [Nat.sub_add_cancel hoff] using m0_w12 ⟨n - 55600, hnfin⟩
                          ·
                            by_cases h13 : n < 55700
                            · have hoff : 55650 ≤ n := by omega
                              have hnfin : n - 55650 < 50 := by omega
                              simpa [Nat.sub_add_cancel hoff] using m0_w13 ⟨n - 55650, hnfin⟩
                            ·
                              by_cases h14 : n < 55750
                              · have hoff : 55700 ≤ n := by omega
                                have hnfin : n - 55700 < 50 := by omega
                                simpa [Nat.sub_add_cancel hoff] using m0_w14 ⟨n - 55700, hnfin⟩
                              ·
                                by_cases h15 : n < 55800
                                · have hoff : 55750 ≤ n := by omega
                                  have hnfin : n - 55750 < 50 := by omega
                                  simpa [Nat.sub_add_cancel hoff] using m0_w15 ⟨n - 55750, hnfin⟩
                                ·
                                  by_cases h16 : n < 55850
                                  · have hoff : 55800 ≤ n := by omega
                                    have hnfin : n - 55800 < 50 := by omega
                                    simpa [Nat.sub_add_cancel hoff] using m0_w16 ⟨n - 55800, hnfin⟩
                                  ·
                                    by_cases h17 : n < 55900
                                    · have hoff : 55850 ≤ n := by omega
                                      have hnfin : n - 55850 < 50 := by omega
                                      simpa [Nat.sub_add_cancel hoff] using m0_w17 ⟨n - 55850, hnfin⟩
                                    ·
                                      by_cases h18 : n < 55950
                                      · have hoff : 55900 ≤ n := by omega
                                        have hnfin : n - 55900 < 50 := by omega
                                        simpa [Nat.sub_add_cancel hoff] using m0_w18 ⟨n - 55900, hnfin⟩
                                      ·
                                        by_cases h19 : n < 56000
                                        · have hoff : 55950 ≤ n := by omega
                                          have hnfin : n - 55950 < 50 := by omega
                                          simpa [Nat.sub_add_cancel hoff] using m0_w19 ⟨n - 55950, hnfin⟩
                                        ·
                                          by_cases h20 : n < 56050
                                          · have hoff : 56000 ≤ n := by omega
                                            have hnfin : n - 56000 < 50 := by omega
                                            simpa [Nat.sub_add_cancel hoff] using m0_w20 ⟨n - 56000, hnfin⟩
                                          ·
                                            by_cases h21 : n < 56100
                                            · have hoff : 56050 ≤ n := by omega
                                              have hnfin : n - 56050 < 50 := by omega
                                              simpa [Nat.sub_add_cancel hoff] using m0_w21 ⟨n - 56050, hnfin⟩
                                            ·
                                              by_cases h22 : n < 56150
                                              · have hoff : 56100 ≤ n := by omega
                                                have hnfin : n - 56100 < 50 := by omega
                                                simpa [Nat.sub_add_cancel hoff] using m0_w22 ⟨n - 56100, hnfin⟩
                                              ·
                                                by_cases h23 : n < 56200
                                                · have hoff : 56150 ≤ n := by omega
                                                  have hnfin : n - 56150 < 50 := by omega
                                                  simpa [Nat.sub_add_cancel hoff] using m0_w23 ⟨n - 56150, hnfin⟩
                                                ·
                                                  by_cases h24 : n < 56250
                                                  · have hoff : 56200 ≤ n := by omega
                                                    have hnfin : n - 56200 < 50 := by omega
                                                    simpa [Nat.sub_add_cancel hoff] using m0_w24 ⟨n - 56200, hnfin⟩
                                                  ·
                                                    by_cases h25 : n < 56300
                                                    · have hoff : 56250 ≤ n := by omega
                                                      have hnfin : n - 56250 < 50 := by omega
                                                      simpa [Nat.sub_add_cancel hoff] using m0_w25 ⟨n - 56250, hnfin⟩
                                                    ·
                                                      by_cases h26 : n < 56350
                                                      · have hoff : 56300 ≤ n := by omega
                                                        have hnfin : n - 56300 < 50 := by omega
                                                        simpa [Nat.sub_add_cancel hoff] using m0_w26 ⟨n - 56300, hnfin⟩
                                                      ·
                                                        by_cases h27 : n < 56400
                                                        · have hoff : 56350 ≤ n := by omega
                                                          have hnfin : n - 56350 < 50 := by omega
                                                          simpa [Nat.sub_add_cancel hoff] using m0_w27 ⟨n - 56350, hnfin⟩
                                                        ·
                                                          by_cases h28 : n < 56450
                                                          · have hoff : 56400 ≤ n := by omega
                                                            have hnfin : n - 56400 < 50 := by omega
                                                            simpa [Nat.sub_add_cancel hoff] using m0_w28 ⟨n - 56400, hnfin⟩
                                                          ·
                                                            by_cases h29 : n < 56500
                                                            · have hoff : 56450 ≤ n := by omega
                                                              have hnfin : n - 56450 < 50 := by omega
                                                              simpa [Nat.sub_add_cancel hoff] using m0_w29 ⟨n - 56450, hnfin⟩
                                                            ·
                                                              by_cases h30 : n < 56550
                                                              · have hoff : 56500 ≤ n := by omega
                                                                have hnfin : n - 56500 < 50 := by omega
                                                                simpa [Nat.sub_add_cancel hoff] using m0_w30 ⟨n - 56500, hnfin⟩
                                                              ·
                                                                by_cases h31 : n < 56600
                                                                · have hoff : 56550 ≤ n := by omega
                                                                  have hnfin : n - 56550 < 50 := by omega
                                                                  simpa [Nat.sub_add_cancel hoff] using m0_w31 ⟨n - 56550, hnfin⟩
                                                                ·
                                                                  by_cases h32 : n < 56650
                                                                  · have hoff : 56600 ≤ n := by omega
                                                                    have hnfin : n - 56600 < 50 := by omega
                                                                    simpa [Nat.sub_add_cancel hoff] using m0_w32 ⟨n - 56600, hnfin⟩
                                                                  ·
                                                                    by_cases h33 : n < 56700
                                                                    · have hoff : 56650 ≤ n := by omega
                                                                      have hnfin : n - 56650 < 50 := by omega
                                                                      simpa [Nat.sub_add_cancel hoff] using m0_w33 ⟨n - 56650, hnfin⟩
                                                                    ·
                                                                      by_cases h34 : n < 56750
                                                                      · have hoff : 56700 ≤ n := by omega
                                                                        have hnfin : n - 56700 < 50 := by omega
                                                                        simpa [Nat.sub_add_cancel hoff] using m0_w34 ⟨n - 56700, hnfin⟩
                                                                      ·
                                                                        by_cases h35 : n < 56800
                                                                        · have hoff : 56750 ≤ n := by omega
                                                                          have hnfin : n - 56750 < 50 := by omega
                                                                          simpa [Nat.sub_add_cancel hoff] using m0_w35 ⟨n - 56750, hnfin⟩
                                                                        ·
                                                                          by_cases h36 : n < 56850
                                                                          · have hoff : 56800 ≤ n := by omega
                                                                            have hnfin : n - 56800 < 50 := by omega
                                                                            simpa [Nat.sub_add_cancel hoff] using m0_w36 ⟨n - 56800, hnfin⟩
                                                                          ·
                                                                            by_cases h37 : n < 56900
                                                                            · have hoff : 56850 ≤ n := by omega
                                                                              have hnfin : n - 56850 < 50 := by omega
                                                                              simpa [Nat.sub_add_cancel hoff] using m0_w37 ⟨n - 56850, hnfin⟩
                                                                            ·
                                                                              by_cases h38 : n < 56950
                                                                              · have hoff : 56900 ≤ n := by omega
                                                                                have hnfin : n - 56900 < 50 := by omega
                                                                                simpa [Nat.sub_add_cancel hoff] using m0_w38 ⟨n - 56900, hnfin⟩
                                                                              ·
                                                                                by_cases h39 : n < 57000
                                                                                · have hoff : 56950 ≤ n := by omega
                                                                                  have hnfin : n - 56950 < 50 := by omega
                                                                                  simpa [Nat.sub_add_cancel hoff] using m0_w39 ⟨n - 56950, hnfin⟩
                                                                                ·
                                                                                  by_cases h40 : n < 57050
                                                                                  · have hoff : 57000 ≤ n := by omega
                                                                                    have hnfin : n - 57000 < 50 := by omega
                                                                                    simpa [Nat.sub_add_cancel hoff] using m0_w40 ⟨n - 57000, hnfin⟩
                                                                                  ·
                                                                                    by_cases h41 : n < 57100
                                                                                    · have hoff : 57050 ≤ n := by omega
                                                                                      have hnfin : n - 57050 < 50 := by omega
                                                                                      simpa [Nat.sub_add_cancel hoff] using m0_w41 ⟨n - 57050, hnfin⟩
                                                                                    ·
                                                                                      by_cases h42 : n < 57150
                                                                                      · have hoff : 57100 ≤ n := by omega
                                                                                        have hnfin : n - 57100 < 50 := by omega
                                                                                        simpa [Nat.sub_add_cancel hoff] using m0_w42 ⟨n - 57100, hnfin⟩
                                                                                      ·
                                                                                        by_cases h43 : n < 57200
                                                                                        · have hoff : 57150 ≤ n := by omega
                                                                                          have hnfin : n - 57150 < 50 := by omega
                                                                                          simpa [Nat.sub_add_cancel hoff] using m0_w43 ⟨n - 57150, hnfin⟩
                                                                                        ·
                                                                                          by_cases h44 : n < 57250
                                                                                          · have hoff : 57200 ≤ n := by omega
                                                                                            have hnfin : n - 57200 < 50 := by omega
                                                                                            simpa [Nat.sub_add_cancel hoff] using m0_w44 ⟨n - 57200, hnfin⟩
                                                                                          ·
                                                                                            by_cases h45 : n < 57300
                                                                                            · have hoff : 57250 ≤ n := by omega
                                                                                              have hnfin : n - 57250 < 50 := by omega
                                                                                              simpa [Nat.sub_add_cancel hoff] using m0_w45 ⟨n - 57250, hnfin⟩
                                                                                            ·
                                                                                              by_cases h46 : n < 57350
                                                                                              · have hoff : 57300 ≤ n := by omega
                                                                                                have hnfin : n - 57300 < 50 := by omega
                                                                                                simpa [Nat.sub_add_cancel hoff] using m0_w46 ⟨n - 57300, hnfin⟩
                                                                                              ·
                                                                                                by_cases h47 : n < 57400
                                                                                                · have hoff : 57350 ≤ n := by omega
                                                                                                  have hnfin : n - 57350 < 50 := by omega
                                                                                                  simpa [Nat.sub_add_cancel hoff] using m0_w47 ⟨n - 57350, hnfin⟩
                                                                                                ·
                                                                                                  by_cases h48 : n < 57450
                                                                                                  · have hoff : 57400 ≤ n := by omega
                                                                                                    have hnfin : n - 57400 < 50 := by omega
                                                                                                    simpa [Nat.sub_add_cancel hoff] using m0_w48 ⟨n - 57400, hnfin⟩
                                                                                                  ·
                                                                                                    by_cases h49 : n < 57500
                                                                                                    · have hoff : 57450 ≤ n := by omega
                                                                                                      have hnfin : n - 57450 < 50 := by omega
                                                                                                      simpa [Nat.sub_add_cancel hoff] using m0_w49 ⟨n - 57450, hnfin⟩
                                                                                                    ·
                                                                                                      omega
theorem land1_range (n : ℕ) (hn0 : 55000 ≤ n) (hn1 : n < 57500) :
    (!Nat.blt (dimF (arg1 n)) (dimF n) ||
      Nat.beq (Nat.land (densSupG (arg1 n)) (densSupG n)) (densSupG (arg1 n))) = true := by
  by_cases h0 : n < 55050
  · have hoff : 55000 ≤ n := by omega
    have hnfin : n - 55000 < 50 := by omega
    simpa [Nat.sub_add_cancel hoff] using m1_w0 ⟨n - 55000, hnfin⟩
  ·
    by_cases h1 : n < 55100
    · have hoff : 55050 ≤ n := by omega
      have hnfin : n - 55050 < 50 := by omega
      simpa [Nat.sub_add_cancel hoff] using m1_w1 ⟨n - 55050, hnfin⟩
    ·
      by_cases h2 : n < 55150
      · have hoff : 55100 ≤ n := by omega
        have hnfin : n - 55100 < 50 := by omega
        simpa [Nat.sub_add_cancel hoff] using m1_w2 ⟨n - 55100, hnfin⟩
      ·
        by_cases h3 : n < 55200
        · have hoff : 55150 ≤ n := by omega
          have hnfin : n - 55150 < 50 := by omega
          simpa [Nat.sub_add_cancel hoff] using m1_w3 ⟨n - 55150, hnfin⟩
        ·
          by_cases h4 : n < 55250
          · have hoff : 55200 ≤ n := by omega
            have hnfin : n - 55200 < 50 := by omega
            simpa [Nat.sub_add_cancel hoff] using m1_w4 ⟨n - 55200, hnfin⟩
          ·
            by_cases h5 : n < 55300
            · have hoff : 55250 ≤ n := by omega
              have hnfin : n - 55250 < 50 := by omega
              simpa [Nat.sub_add_cancel hoff] using m1_w5 ⟨n - 55250, hnfin⟩
            ·
              by_cases h6 : n < 55350
              · have hoff : 55300 ≤ n := by omega
                have hnfin : n - 55300 < 50 := by omega
                simpa [Nat.sub_add_cancel hoff] using m1_w6 ⟨n - 55300, hnfin⟩
              ·
                by_cases h7 : n < 55400
                · have hoff : 55350 ≤ n := by omega
                  have hnfin : n - 55350 < 50 := by omega
                  simpa [Nat.sub_add_cancel hoff] using m1_w7 ⟨n - 55350, hnfin⟩
                ·
                  by_cases h8 : n < 55450
                  · have hoff : 55400 ≤ n := by omega
                    have hnfin : n - 55400 < 50 := by omega
                    simpa [Nat.sub_add_cancel hoff] using m1_w8 ⟨n - 55400, hnfin⟩
                  ·
                    by_cases h9 : n < 55500
                    · have hoff : 55450 ≤ n := by omega
                      have hnfin : n - 55450 < 50 := by omega
                      simpa [Nat.sub_add_cancel hoff] using m1_w9 ⟨n - 55450, hnfin⟩
                    ·
                      by_cases h10 : n < 55550
                      · have hoff : 55500 ≤ n := by omega
                        have hnfin : n - 55500 < 50 := by omega
                        simpa [Nat.sub_add_cancel hoff] using m1_w10 ⟨n - 55500, hnfin⟩
                      ·
                        by_cases h11 : n < 55600
                        · have hoff : 55550 ≤ n := by omega
                          have hnfin : n - 55550 < 50 := by omega
                          simpa [Nat.sub_add_cancel hoff] using m1_w11 ⟨n - 55550, hnfin⟩
                        ·
                          by_cases h12 : n < 55650
                          · have hoff : 55600 ≤ n := by omega
                            have hnfin : n - 55600 < 50 := by omega
                            simpa [Nat.sub_add_cancel hoff] using m1_w12 ⟨n - 55600, hnfin⟩
                          ·
                            by_cases h13 : n < 55700
                            · have hoff : 55650 ≤ n := by omega
                              have hnfin : n - 55650 < 50 := by omega
                              simpa [Nat.sub_add_cancel hoff] using m1_w13 ⟨n - 55650, hnfin⟩
                            ·
                              by_cases h14 : n < 55750
                              · have hoff : 55700 ≤ n := by omega
                                have hnfin : n - 55700 < 50 := by omega
                                simpa [Nat.sub_add_cancel hoff] using m1_w14 ⟨n - 55700, hnfin⟩
                              ·
                                by_cases h15 : n < 55800
                                · have hoff : 55750 ≤ n := by omega
                                  have hnfin : n - 55750 < 50 := by omega
                                  simpa [Nat.sub_add_cancel hoff] using m1_w15 ⟨n - 55750, hnfin⟩
                                ·
                                  by_cases h16 : n < 55850
                                  · have hoff : 55800 ≤ n := by omega
                                    have hnfin : n - 55800 < 50 := by omega
                                    simpa [Nat.sub_add_cancel hoff] using m1_w16 ⟨n - 55800, hnfin⟩
                                  ·
                                    by_cases h17 : n < 55900
                                    · have hoff : 55850 ≤ n := by omega
                                      have hnfin : n - 55850 < 50 := by omega
                                      simpa [Nat.sub_add_cancel hoff] using m1_w17 ⟨n - 55850, hnfin⟩
                                    ·
                                      by_cases h18 : n < 55950
                                      · have hoff : 55900 ≤ n := by omega
                                        have hnfin : n - 55900 < 50 := by omega
                                        simpa [Nat.sub_add_cancel hoff] using m1_w18 ⟨n - 55900, hnfin⟩
                                      ·
                                        by_cases h19 : n < 56000
                                        · have hoff : 55950 ≤ n := by omega
                                          have hnfin : n - 55950 < 50 := by omega
                                          simpa [Nat.sub_add_cancel hoff] using m1_w19 ⟨n - 55950, hnfin⟩
                                        ·
                                          by_cases h20 : n < 56050
                                          · have hoff : 56000 ≤ n := by omega
                                            have hnfin : n - 56000 < 50 := by omega
                                            simpa [Nat.sub_add_cancel hoff] using m1_w20 ⟨n - 56000, hnfin⟩
                                          ·
                                            by_cases h21 : n < 56100
                                            · have hoff : 56050 ≤ n := by omega
                                              have hnfin : n - 56050 < 50 := by omega
                                              simpa [Nat.sub_add_cancel hoff] using m1_w21 ⟨n - 56050, hnfin⟩
                                            ·
                                              by_cases h22 : n < 56150
                                              · have hoff : 56100 ≤ n := by omega
                                                have hnfin : n - 56100 < 50 := by omega
                                                simpa [Nat.sub_add_cancel hoff] using m1_w22 ⟨n - 56100, hnfin⟩
                                              ·
                                                by_cases h23 : n < 56200
                                                · have hoff : 56150 ≤ n := by omega
                                                  have hnfin : n - 56150 < 50 := by omega
                                                  simpa [Nat.sub_add_cancel hoff] using m1_w23 ⟨n - 56150, hnfin⟩
                                                ·
                                                  by_cases h24 : n < 56250
                                                  · have hoff : 56200 ≤ n := by omega
                                                    have hnfin : n - 56200 < 50 := by omega
                                                    simpa [Nat.sub_add_cancel hoff] using m1_w24 ⟨n - 56200, hnfin⟩
                                                  ·
                                                    by_cases h25 : n < 56300
                                                    · have hoff : 56250 ≤ n := by omega
                                                      have hnfin : n - 56250 < 50 := by omega
                                                      simpa [Nat.sub_add_cancel hoff] using m1_w25 ⟨n - 56250, hnfin⟩
                                                    ·
                                                      by_cases h26 : n < 56350
                                                      · have hoff : 56300 ≤ n := by omega
                                                        have hnfin : n - 56300 < 50 := by omega
                                                        simpa [Nat.sub_add_cancel hoff] using m1_w26 ⟨n - 56300, hnfin⟩
                                                      ·
                                                        by_cases h27 : n < 56400
                                                        · have hoff : 56350 ≤ n := by omega
                                                          have hnfin : n - 56350 < 50 := by omega
                                                          simpa [Nat.sub_add_cancel hoff] using m1_w27 ⟨n - 56350, hnfin⟩
                                                        ·
                                                          by_cases h28 : n < 56450
                                                          · have hoff : 56400 ≤ n := by omega
                                                            have hnfin : n - 56400 < 50 := by omega
                                                            simpa [Nat.sub_add_cancel hoff] using m1_w28 ⟨n - 56400, hnfin⟩
                                                          ·
                                                            by_cases h29 : n < 56500
                                                            · have hoff : 56450 ≤ n := by omega
                                                              have hnfin : n - 56450 < 50 := by omega
                                                              simpa [Nat.sub_add_cancel hoff] using m1_w29 ⟨n - 56450, hnfin⟩
                                                            ·
                                                              by_cases h30 : n < 56550
                                                              · have hoff : 56500 ≤ n := by omega
                                                                have hnfin : n - 56500 < 50 := by omega
                                                                simpa [Nat.sub_add_cancel hoff] using m1_w30 ⟨n - 56500, hnfin⟩
                                                              ·
                                                                by_cases h31 : n < 56600
                                                                · have hoff : 56550 ≤ n := by omega
                                                                  have hnfin : n - 56550 < 50 := by omega
                                                                  simpa [Nat.sub_add_cancel hoff] using m1_w31 ⟨n - 56550, hnfin⟩
                                                                ·
                                                                  by_cases h32 : n < 56650
                                                                  · have hoff : 56600 ≤ n := by omega
                                                                    have hnfin : n - 56600 < 50 := by omega
                                                                    simpa [Nat.sub_add_cancel hoff] using m1_w32 ⟨n - 56600, hnfin⟩
                                                                  ·
                                                                    by_cases h33 : n < 56700
                                                                    · have hoff : 56650 ≤ n := by omega
                                                                      have hnfin : n - 56650 < 50 := by omega
                                                                      simpa [Nat.sub_add_cancel hoff] using m1_w33 ⟨n - 56650, hnfin⟩
                                                                    ·
                                                                      by_cases h34 : n < 56750
                                                                      · have hoff : 56700 ≤ n := by omega
                                                                        have hnfin : n - 56700 < 50 := by omega
                                                                        simpa [Nat.sub_add_cancel hoff] using m1_w34 ⟨n - 56700, hnfin⟩
                                                                      ·
                                                                        by_cases h35 : n < 56800
                                                                        · have hoff : 56750 ≤ n := by omega
                                                                          have hnfin : n - 56750 < 50 := by omega
                                                                          simpa [Nat.sub_add_cancel hoff] using m1_w35 ⟨n - 56750, hnfin⟩
                                                                        ·
                                                                          by_cases h36 : n < 56850
                                                                          · have hoff : 56800 ≤ n := by omega
                                                                            have hnfin : n - 56800 < 50 := by omega
                                                                            simpa [Nat.sub_add_cancel hoff] using m1_w36 ⟨n - 56800, hnfin⟩
                                                                          ·
                                                                            by_cases h37 : n < 56900
                                                                            · have hoff : 56850 ≤ n := by omega
                                                                              have hnfin : n - 56850 < 50 := by omega
                                                                              simpa [Nat.sub_add_cancel hoff] using m1_w37 ⟨n - 56850, hnfin⟩
                                                                            ·
                                                                              by_cases h38 : n < 56950
                                                                              · have hoff : 56900 ≤ n := by omega
                                                                                have hnfin : n - 56900 < 50 := by omega
                                                                                simpa [Nat.sub_add_cancel hoff] using m1_w38 ⟨n - 56900, hnfin⟩
                                                                              ·
                                                                                by_cases h39 : n < 57000
                                                                                · have hoff : 56950 ≤ n := by omega
                                                                                  have hnfin : n - 56950 < 50 := by omega
                                                                                  simpa [Nat.sub_add_cancel hoff] using m1_w39 ⟨n - 56950, hnfin⟩
                                                                                ·
                                                                                  by_cases h40 : n < 57050
                                                                                  · have hoff : 57000 ≤ n := by omega
                                                                                    have hnfin : n - 57000 < 50 := by omega
                                                                                    simpa [Nat.sub_add_cancel hoff] using m1_w40 ⟨n - 57000, hnfin⟩
                                                                                  ·
                                                                                    by_cases h41 : n < 57100
                                                                                    · have hoff : 57050 ≤ n := by omega
                                                                                      have hnfin : n - 57050 < 50 := by omega
                                                                                      simpa [Nat.sub_add_cancel hoff] using m1_w41 ⟨n - 57050, hnfin⟩
                                                                                    ·
                                                                                      by_cases h42 : n < 57150
                                                                                      · have hoff : 57100 ≤ n := by omega
                                                                                        have hnfin : n - 57100 < 50 := by omega
                                                                                        simpa [Nat.sub_add_cancel hoff] using m1_w42 ⟨n - 57100, hnfin⟩
                                                                                      ·
                                                                                        by_cases h43 : n < 57200
                                                                                        · have hoff : 57150 ≤ n := by omega
                                                                                          have hnfin : n - 57150 < 50 := by omega
                                                                                          simpa [Nat.sub_add_cancel hoff] using m1_w43 ⟨n - 57150, hnfin⟩
                                                                                        ·
                                                                                          by_cases h44 : n < 57250
                                                                                          · have hoff : 57200 ≤ n := by omega
                                                                                            have hnfin : n - 57200 < 50 := by omega
                                                                                            simpa [Nat.sub_add_cancel hoff] using m1_w44 ⟨n - 57200, hnfin⟩
                                                                                          ·
                                                                                            by_cases h45 : n < 57300
                                                                                            · have hoff : 57250 ≤ n := by omega
                                                                                              have hnfin : n - 57250 < 50 := by omega
                                                                                              simpa [Nat.sub_add_cancel hoff] using m1_w45 ⟨n - 57250, hnfin⟩
                                                                                            ·
                                                                                              by_cases h46 : n < 57350
                                                                                              · have hoff : 57300 ≤ n := by omega
                                                                                                have hnfin : n - 57300 < 50 := by omega
                                                                                                simpa [Nat.sub_add_cancel hoff] using m1_w46 ⟨n - 57300, hnfin⟩
                                                                                              ·
                                                                                                by_cases h47 : n < 57400
                                                                                                · have hoff : 57350 ≤ n := by omega
                                                                                                  have hnfin : n - 57350 < 50 := by omega
                                                                                                  simpa [Nat.sub_add_cancel hoff] using m1_w47 ⟨n - 57350, hnfin⟩
                                                                                                ·
                                                                                                  by_cases h48 : n < 57450
                                                                                                  · have hoff : 57400 ≤ n := by omega
                                                                                                    have hnfin : n - 57400 < 50 := by omega
                                                                                                    simpa [Nat.sub_add_cancel hoff] using m1_w48 ⟨n - 57400, hnfin⟩
                                                                                                  ·
                                                                                                    by_cases h49 : n < 57500
                                                                                                    · have hoff : 57450 ≤ n := by omega
                                                                                                      have hnfin : n - 57450 < 50 := by omega
                                                                                                      simpa [Nat.sub_add_cancel hoff] using m1_w49 ⟨n - 57450, hnfin⟩
                                                                                                    ·
                                                                                                      omega
end IntMul.Kappa.R8.Bit.Oppbank.LandMonoFixA22


