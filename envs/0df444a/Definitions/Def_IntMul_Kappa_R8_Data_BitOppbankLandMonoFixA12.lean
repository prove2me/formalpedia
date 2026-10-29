-- Prove2me | Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankLandMonoFixA12
-- name    : IntMul_Kappa_R8_Data_BitOppbankLandMonoFixA12
-- status  : Definition
-- author  : @Ethan Cheung Wang
-- created : 2026-10-28T21:16:29.558315+00:00
-- url     : https://prove2.me/theorems/144821ea-a459-441f-ae0d-e7b4526ee33e
-- title:
--   Dim-gated densSup land mono FixA pack 12
-- statement:
--   # Dim-gated densSup land (PndFix), pack A12
--
--   Range consolidators for $n\in[30000,32500)$.
-- source:
--   R8 BitOppbank PndFix

-- LandMonoFixA12: PUBLIC dim-gated land + range consolidators (PndFix)
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
namespace IntMul.Kappa.R8.Bit.Oppbank.LandMonoFixA12
def arg0 (n : ℕ) : ℕ := Nat.land (argF n) 65535
def arg1 (n : ℕ) : ℕ := Nat.shiftRight (argF n) 16
theorem m0_w0 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 30000))) (dimF (n.val + 30000)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 30000))) (densSupG (n.val + 30000))) (densSupG (arg0 (n.val + 30000)))) = true := by decide
theorem m1_w0 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 30000))) (dimF (n.val + 30000)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 30000))) (densSupG (n.val + 30000))) (densSupG (arg1 (n.val + 30000)))) = true := by decide
theorem m0_w1 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 30050))) (dimF (n.val + 30050)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 30050))) (densSupG (n.val + 30050))) (densSupG (arg0 (n.val + 30050)))) = true := by decide
theorem m1_w1 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 30050))) (dimF (n.val + 30050)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 30050))) (densSupG (n.val + 30050))) (densSupG (arg1 (n.val + 30050)))) = true := by decide
theorem m0_w2 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 30100))) (dimF (n.val + 30100)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 30100))) (densSupG (n.val + 30100))) (densSupG (arg0 (n.val + 30100)))) = true := by decide
theorem m1_w2 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 30100))) (dimF (n.val + 30100)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 30100))) (densSupG (n.val + 30100))) (densSupG (arg1 (n.val + 30100)))) = true := by decide
theorem m0_w3 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 30150))) (dimF (n.val + 30150)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 30150))) (densSupG (n.val + 30150))) (densSupG (arg0 (n.val + 30150)))) = true := by decide
theorem m1_w3 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 30150))) (dimF (n.val + 30150)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 30150))) (densSupG (n.val + 30150))) (densSupG (arg1 (n.val + 30150)))) = true := by decide
theorem m0_w4 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 30200))) (dimF (n.val + 30200)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 30200))) (densSupG (n.val + 30200))) (densSupG (arg0 (n.val + 30200)))) = true := by decide
theorem m1_w4 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 30200))) (dimF (n.val + 30200)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 30200))) (densSupG (n.val + 30200))) (densSupG (arg1 (n.val + 30200)))) = true := by decide
theorem m0_w5 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 30250))) (dimF (n.val + 30250)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 30250))) (densSupG (n.val + 30250))) (densSupG (arg0 (n.val + 30250)))) = true := by decide
theorem m1_w5 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 30250))) (dimF (n.val + 30250)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 30250))) (densSupG (n.val + 30250))) (densSupG (arg1 (n.val + 30250)))) = true := by decide
theorem m0_w6 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 30300))) (dimF (n.val + 30300)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 30300))) (densSupG (n.val + 30300))) (densSupG (arg0 (n.val + 30300)))) = true := by decide
theorem m1_w6 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 30300))) (dimF (n.val + 30300)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 30300))) (densSupG (n.val + 30300))) (densSupG (arg1 (n.val + 30300)))) = true := by decide
theorem m0_w7 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 30350))) (dimF (n.val + 30350)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 30350))) (densSupG (n.val + 30350))) (densSupG (arg0 (n.val + 30350)))) = true := by decide
theorem m1_w7 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 30350))) (dimF (n.val + 30350)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 30350))) (densSupG (n.val + 30350))) (densSupG (arg1 (n.val + 30350)))) = true := by decide
theorem m0_w8 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 30400))) (dimF (n.val + 30400)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 30400))) (densSupG (n.val + 30400))) (densSupG (arg0 (n.val + 30400)))) = true := by decide
theorem m1_w8 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 30400))) (dimF (n.val + 30400)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 30400))) (densSupG (n.val + 30400))) (densSupG (arg1 (n.val + 30400)))) = true := by decide
theorem m0_w9 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 30450))) (dimF (n.val + 30450)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 30450))) (densSupG (n.val + 30450))) (densSupG (arg0 (n.val + 30450)))) = true := by decide
theorem m1_w9 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 30450))) (dimF (n.val + 30450)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 30450))) (densSupG (n.val + 30450))) (densSupG (arg1 (n.val + 30450)))) = true := by decide
theorem m0_w10 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 30500))) (dimF (n.val + 30500)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 30500))) (densSupG (n.val + 30500))) (densSupG (arg0 (n.val + 30500)))) = true := by decide
theorem m1_w10 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 30500))) (dimF (n.val + 30500)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 30500))) (densSupG (n.val + 30500))) (densSupG (arg1 (n.val + 30500)))) = true := by decide
theorem m0_w11 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 30550))) (dimF (n.val + 30550)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 30550))) (densSupG (n.val + 30550))) (densSupG (arg0 (n.val + 30550)))) = true := by decide
theorem m1_w11 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 30550))) (dimF (n.val + 30550)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 30550))) (densSupG (n.val + 30550))) (densSupG (arg1 (n.val + 30550)))) = true := by decide
theorem m0_w12 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 30600))) (dimF (n.val + 30600)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 30600))) (densSupG (n.val + 30600))) (densSupG (arg0 (n.val + 30600)))) = true := by decide
theorem m1_w12 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 30600))) (dimF (n.val + 30600)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 30600))) (densSupG (n.val + 30600))) (densSupG (arg1 (n.val + 30600)))) = true := by decide
theorem m0_w13 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 30650))) (dimF (n.val + 30650)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 30650))) (densSupG (n.val + 30650))) (densSupG (arg0 (n.val + 30650)))) = true := by decide
theorem m1_w13 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 30650))) (dimF (n.val + 30650)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 30650))) (densSupG (n.val + 30650))) (densSupG (arg1 (n.val + 30650)))) = true := by decide
theorem m0_w14 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 30700))) (dimF (n.val + 30700)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 30700))) (densSupG (n.val + 30700))) (densSupG (arg0 (n.val + 30700)))) = true := by decide
theorem m1_w14 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 30700))) (dimF (n.val + 30700)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 30700))) (densSupG (n.val + 30700))) (densSupG (arg1 (n.val + 30700)))) = true := by decide
theorem m0_w15 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 30750))) (dimF (n.val + 30750)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 30750))) (densSupG (n.val + 30750))) (densSupG (arg0 (n.val + 30750)))) = true := by decide
theorem m1_w15 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 30750))) (dimF (n.val + 30750)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 30750))) (densSupG (n.val + 30750))) (densSupG (arg1 (n.val + 30750)))) = true := by decide
theorem m0_w16 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 30800))) (dimF (n.val + 30800)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 30800))) (densSupG (n.val + 30800))) (densSupG (arg0 (n.val + 30800)))) = true := by decide
theorem m1_w16 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 30800))) (dimF (n.val + 30800)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 30800))) (densSupG (n.val + 30800))) (densSupG (arg1 (n.val + 30800)))) = true := by decide
theorem m0_w17 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 30850))) (dimF (n.val + 30850)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 30850))) (densSupG (n.val + 30850))) (densSupG (arg0 (n.val + 30850)))) = true := by decide
theorem m1_w17 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 30850))) (dimF (n.val + 30850)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 30850))) (densSupG (n.val + 30850))) (densSupG (arg1 (n.val + 30850)))) = true := by decide
theorem m0_w18 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 30900))) (dimF (n.val + 30900)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 30900))) (densSupG (n.val + 30900))) (densSupG (arg0 (n.val + 30900)))) = true := by decide
theorem m1_w18 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 30900))) (dimF (n.val + 30900)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 30900))) (densSupG (n.val + 30900))) (densSupG (arg1 (n.val + 30900)))) = true := by decide
theorem m0_w19 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 30950))) (dimF (n.val + 30950)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 30950))) (densSupG (n.val + 30950))) (densSupG (arg0 (n.val + 30950)))) = true := by decide
theorem m1_w19 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 30950))) (dimF (n.val + 30950)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 30950))) (densSupG (n.val + 30950))) (densSupG (arg1 (n.val + 30950)))) = true := by decide
theorem m0_w20 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 31000))) (dimF (n.val + 31000)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 31000))) (densSupG (n.val + 31000))) (densSupG (arg0 (n.val + 31000)))) = true := by decide
theorem m1_w20 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 31000))) (dimF (n.val + 31000)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 31000))) (densSupG (n.val + 31000))) (densSupG (arg1 (n.val + 31000)))) = true := by decide
theorem m0_w21 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 31050))) (dimF (n.val + 31050)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 31050))) (densSupG (n.val + 31050))) (densSupG (arg0 (n.val + 31050)))) = true := by decide
theorem m1_w21 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 31050))) (dimF (n.val + 31050)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 31050))) (densSupG (n.val + 31050))) (densSupG (arg1 (n.val + 31050)))) = true := by decide
theorem m0_w22 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 31100))) (dimF (n.val + 31100)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 31100))) (densSupG (n.val + 31100))) (densSupG (arg0 (n.val + 31100)))) = true := by decide
theorem m1_w22 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 31100))) (dimF (n.val + 31100)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 31100))) (densSupG (n.val + 31100))) (densSupG (arg1 (n.val + 31100)))) = true := by decide
theorem m0_w23 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 31150))) (dimF (n.val + 31150)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 31150))) (densSupG (n.val + 31150))) (densSupG (arg0 (n.val + 31150)))) = true := by decide
theorem m1_w23 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 31150))) (dimF (n.val + 31150)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 31150))) (densSupG (n.val + 31150))) (densSupG (arg1 (n.val + 31150)))) = true := by decide
theorem m0_w24 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 31200))) (dimF (n.val + 31200)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 31200))) (densSupG (n.val + 31200))) (densSupG (arg0 (n.val + 31200)))) = true := by decide
theorem m1_w24 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 31200))) (dimF (n.val + 31200)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 31200))) (densSupG (n.val + 31200))) (densSupG (arg1 (n.val + 31200)))) = true := by decide
theorem m0_w25 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 31250))) (dimF (n.val + 31250)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 31250))) (densSupG (n.val + 31250))) (densSupG (arg0 (n.val + 31250)))) = true := by decide
theorem m1_w25 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 31250))) (dimF (n.val + 31250)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 31250))) (densSupG (n.val + 31250))) (densSupG (arg1 (n.val + 31250)))) = true := by decide
theorem m0_w26 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 31300))) (dimF (n.val + 31300)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 31300))) (densSupG (n.val + 31300))) (densSupG (arg0 (n.val + 31300)))) = true := by decide
theorem m1_w26 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 31300))) (dimF (n.val + 31300)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 31300))) (densSupG (n.val + 31300))) (densSupG (arg1 (n.val + 31300)))) = true := by decide
theorem m0_w27 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 31350))) (dimF (n.val + 31350)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 31350))) (densSupG (n.val + 31350))) (densSupG (arg0 (n.val + 31350)))) = true := by decide
theorem m1_w27 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 31350))) (dimF (n.val + 31350)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 31350))) (densSupG (n.val + 31350))) (densSupG (arg1 (n.val + 31350)))) = true := by decide
theorem m0_w28 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 31400))) (dimF (n.val + 31400)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 31400))) (densSupG (n.val + 31400))) (densSupG (arg0 (n.val + 31400)))) = true := by decide
theorem m1_w28 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 31400))) (dimF (n.val + 31400)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 31400))) (densSupG (n.val + 31400))) (densSupG (arg1 (n.val + 31400)))) = true := by decide
theorem m0_w29 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 31450))) (dimF (n.val + 31450)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 31450))) (densSupG (n.val + 31450))) (densSupG (arg0 (n.val + 31450)))) = true := by decide
theorem m1_w29 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 31450))) (dimF (n.val + 31450)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 31450))) (densSupG (n.val + 31450))) (densSupG (arg1 (n.val + 31450)))) = true := by decide
theorem m0_w30 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 31500))) (dimF (n.val + 31500)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 31500))) (densSupG (n.val + 31500))) (densSupG (arg0 (n.val + 31500)))) = true := by decide
theorem m1_w30 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 31500))) (dimF (n.val + 31500)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 31500))) (densSupG (n.val + 31500))) (densSupG (arg1 (n.val + 31500)))) = true := by decide
theorem m0_w31 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 31550))) (dimF (n.val + 31550)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 31550))) (densSupG (n.val + 31550))) (densSupG (arg0 (n.val + 31550)))) = true := by decide
theorem m1_w31 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 31550))) (dimF (n.val + 31550)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 31550))) (densSupG (n.val + 31550))) (densSupG (arg1 (n.val + 31550)))) = true := by decide
theorem m0_w32 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 31600))) (dimF (n.val + 31600)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 31600))) (densSupG (n.val + 31600))) (densSupG (arg0 (n.val + 31600)))) = true := by decide
theorem m1_w32 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 31600))) (dimF (n.val + 31600)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 31600))) (densSupG (n.val + 31600))) (densSupG (arg1 (n.val + 31600)))) = true := by decide
theorem m0_w33 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 31650))) (dimF (n.val + 31650)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 31650))) (densSupG (n.val + 31650))) (densSupG (arg0 (n.val + 31650)))) = true := by decide
theorem m1_w33 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 31650))) (dimF (n.val + 31650)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 31650))) (densSupG (n.val + 31650))) (densSupG (arg1 (n.val + 31650)))) = true := by decide
theorem m0_w34 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 31700))) (dimF (n.val + 31700)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 31700))) (densSupG (n.val + 31700))) (densSupG (arg0 (n.val + 31700)))) = true := by decide
theorem m1_w34 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 31700))) (dimF (n.val + 31700)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 31700))) (densSupG (n.val + 31700))) (densSupG (arg1 (n.val + 31700)))) = true := by decide
theorem m0_w35 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 31750))) (dimF (n.val + 31750)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 31750))) (densSupG (n.val + 31750))) (densSupG (arg0 (n.val + 31750)))) = true := by decide
theorem m1_w35 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 31750))) (dimF (n.val + 31750)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 31750))) (densSupG (n.val + 31750))) (densSupG (arg1 (n.val + 31750)))) = true := by decide
theorem m0_w36 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 31800))) (dimF (n.val + 31800)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 31800))) (densSupG (n.val + 31800))) (densSupG (arg0 (n.val + 31800)))) = true := by decide
theorem m1_w36 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 31800))) (dimF (n.val + 31800)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 31800))) (densSupG (n.val + 31800))) (densSupG (arg1 (n.val + 31800)))) = true := by decide
theorem m0_w37 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 31850))) (dimF (n.val + 31850)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 31850))) (densSupG (n.val + 31850))) (densSupG (arg0 (n.val + 31850)))) = true := by decide
theorem m1_w37 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 31850))) (dimF (n.val + 31850)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 31850))) (densSupG (n.val + 31850))) (densSupG (arg1 (n.val + 31850)))) = true := by decide
theorem m0_w38 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 31900))) (dimF (n.val + 31900)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 31900))) (densSupG (n.val + 31900))) (densSupG (arg0 (n.val + 31900)))) = true := by decide
theorem m1_w38 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 31900))) (dimF (n.val + 31900)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 31900))) (densSupG (n.val + 31900))) (densSupG (arg1 (n.val + 31900)))) = true := by decide
theorem m0_w39 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 31950))) (dimF (n.val + 31950)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 31950))) (densSupG (n.val + 31950))) (densSupG (arg0 (n.val + 31950)))) = true := by decide
theorem m1_w39 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 31950))) (dimF (n.val + 31950)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 31950))) (densSupG (n.val + 31950))) (densSupG (arg1 (n.val + 31950)))) = true := by decide
theorem m0_w40 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 32000))) (dimF (n.val + 32000)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 32000))) (densSupG (n.val + 32000))) (densSupG (arg0 (n.val + 32000)))) = true := by decide
theorem m1_w40 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 32000))) (dimF (n.val + 32000)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 32000))) (densSupG (n.val + 32000))) (densSupG (arg1 (n.val + 32000)))) = true := by decide
theorem m0_w41 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 32050))) (dimF (n.val + 32050)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 32050))) (densSupG (n.val + 32050))) (densSupG (arg0 (n.val + 32050)))) = true := by decide
theorem m1_w41 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 32050))) (dimF (n.val + 32050)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 32050))) (densSupG (n.val + 32050))) (densSupG (arg1 (n.val + 32050)))) = true := by decide
theorem m0_w42 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 32100))) (dimF (n.val + 32100)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 32100))) (densSupG (n.val + 32100))) (densSupG (arg0 (n.val + 32100)))) = true := by decide
theorem m1_w42 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 32100))) (dimF (n.val + 32100)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 32100))) (densSupG (n.val + 32100))) (densSupG (arg1 (n.val + 32100)))) = true := by decide
theorem m0_w43 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 32150))) (dimF (n.val + 32150)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 32150))) (densSupG (n.val + 32150))) (densSupG (arg0 (n.val + 32150)))) = true := by decide
theorem m1_w43 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 32150))) (dimF (n.val + 32150)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 32150))) (densSupG (n.val + 32150))) (densSupG (arg1 (n.val + 32150)))) = true := by decide
theorem m0_w44 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 32200))) (dimF (n.val + 32200)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 32200))) (densSupG (n.val + 32200))) (densSupG (arg0 (n.val + 32200)))) = true := by decide
theorem m1_w44 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 32200))) (dimF (n.val + 32200)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 32200))) (densSupG (n.val + 32200))) (densSupG (arg1 (n.val + 32200)))) = true := by decide
theorem m0_w45 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 32250))) (dimF (n.val + 32250)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 32250))) (densSupG (n.val + 32250))) (densSupG (arg0 (n.val + 32250)))) = true := by decide
theorem m1_w45 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 32250))) (dimF (n.val + 32250)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 32250))) (densSupG (n.val + 32250))) (densSupG (arg1 (n.val + 32250)))) = true := by decide
theorem m0_w46 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 32300))) (dimF (n.val + 32300)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 32300))) (densSupG (n.val + 32300))) (densSupG (arg0 (n.val + 32300)))) = true := by decide
theorem m1_w46 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 32300))) (dimF (n.val + 32300)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 32300))) (densSupG (n.val + 32300))) (densSupG (arg1 (n.val + 32300)))) = true := by decide
theorem m0_w47 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 32350))) (dimF (n.val + 32350)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 32350))) (densSupG (n.val + 32350))) (densSupG (arg0 (n.val + 32350)))) = true := by decide
theorem m1_w47 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 32350))) (dimF (n.val + 32350)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 32350))) (densSupG (n.val + 32350))) (densSupG (arg1 (n.val + 32350)))) = true := by decide
theorem m0_w48 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 32400))) (dimF (n.val + 32400)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 32400))) (densSupG (n.val + 32400))) (densSupG (arg0 (n.val + 32400)))) = true := by decide
theorem m1_w48 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 32400))) (dimF (n.val + 32400)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 32400))) (densSupG (n.val + 32400))) (densSupG (arg1 (n.val + 32400)))) = true := by decide
theorem m0_w49 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 32450))) (dimF (n.val + 32450)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 32450))) (densSupG (n.val + 32450))) (densSupG (arg0 (n.val + 32450)))) = true := by decide
theorem m1_w49 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 32450))) (dimF (n.val + 32450)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 32450))) (densSupG (n.val + 32450))) (densSupG (arg1 (n.val + 32450)))) = true := by decide
theorem land0_range (n : ℕ) (hn0 : 30000 ≤ n) (hn1 : n < 32500) :
    (!Nat.blt (dimF (arg0 n)) (dimF n) ||
      Nat.beq (Nat.land (densSupG (arg0 n)) (densSupG n)) (densSupG (arg0 n))) = true := by
  by_cases h0 : n < 30050
  · have hoff : 30000 ≤ n := by omega
    have hnfin : n - 30000 < 50 := by omega
    simpa [Nat.sub_add_cancel hoff] using m0_w0 ⟨n - 30000, hnfin⟩
  ·
    by_cases h1 : n < 30100
    · have hoff : 30050 ≤ n := by omega
      have hnfin : n - 30050 < 50 := by omega
      simpa [Nat.sub_add_cancel hoff] using m0_w1 ⟨n - 30050, hnfin⟩
    ·
      by_cases h2 : n < 30150
      · have hoff : 30100 ≤ n := by omega
        have hnfin : n - 30100 < 50 := by omega
        simpa [Nat.sub_add_cancel hoff] using m0_w2 ⟨n - 30100, hnfin⟩
      ·
        by_cases h3 : n < 30200
        · have hoff : 30150 ≤ n := by omega
          have hnfin : n - 30150 < 50 := by omega
          simpa [Nat.sub_add_cancel hoff] using m0_w3 ⟨n - 30150, hnfin⟩
        ·
          by_cases h4 : n < 30250
          · have hoff : 30200 ≤ n := by omega
            have hnfin : n - 30200 < 50 := by omega
            simpa [Nat.sub_add_cancel hoff] using m0_w4 ⟨n - 30200, hnfin⟩
          ·
            by_cases h5 : n < 30300
            · have hoff : 30250 ≤ n := by omega
              have hnfin : n - 30250 < 50 := by omega
              simpa [Nat.sub_add_cancel hoff] using m0_w5 ⟨n - 30250, hnfin⟩
            ·
              by_cases h6 : n < 30350
              · have hoff : 30300 ≤ n := by omega
                have hnfin : n - 30300 < 50 := by omega
                simpa [Nat.sub_add_cancel hoff] using m0_w6 ⟨n - 30300, hnfin⟩
              ·
                by_cases h7 : n < 30400
                · have hoff : 30350 ≤ n := by omega
                  have hnfin : n - 30350 < 50 := by omega
                  simpa [Nat.sub_add_cancel hoff] using m0_w7 ⟨n - 30350, hnfin⟩
                ·
                  by_cases h8 : n < 30450
                  · have hoff : 30400 ≤ n := by omega
                    have hnfin : n - 30400 < 50 := by omega
                    simpa [Nat.sub_add_cancel hoff] using m0_w8 ⟨n - 30400, hnfin⟩
                  ·
                    by_cases h9 : n < 30500
                    · have hoff : 30450 ≤ n := by omega
                      have hnfin : n - 30450 < 50 := by omega
                      simpa [Nat.sub_add_cancel hoff] using m0_w9 ⟨n - 30450, hnfin⟩
                    ·
                      by_cases h10 : n < 30550
                      · have hoff : 30500 ≤ n := by omega
                        have hnfin : n - 30500 < 50 := by omega
                        simpa [Nat.sub_add_cancel hoff] using m0_w10 ⟨n - 30500, hnfin⟩
                      ·
                        by_cases h11 : n < 30600
                        · have hoff : 30550 ≤ n := by omega
                          have hnfin : n - 30550 < 50 := by omega
                          simpa [Nat.sub_add_cancel hoff] using m0_w11 ⟨n - 30550, hnfin⟩
                        ·
                          by_cases h12 : n < 30650
                          · have hoff : 30600 ≤ n := by omega
                            have hnfin : n - 30600 < 50 := by omega
                            simpa [Nat.sub_add_cancel hoff] using m0_w12 ⟨n - 30600, hnfin⟩
                          ·
                            by_cases h13 : n < 30700
                            · have hoff : 30650 ≤ n := by omega
                              have hnfin : n - 30650 < 50 := by omega
                              simpa [Nat.sub_add_cancel hoff] using m0_w13 ⟨n - 30650, hnfin⟩
                            ·
                              by_cases h14 : n < 30750
                              · have hoff : 30700 ≤ n := by omega
                                have hnfin : n - 30700 < 50 := by omega
                                simpa [Nat.sub_add_cancel hoff] using m0_w14 ⟨n - 30700, hnfin⟩
                              ·
                                by_cases h15 : n < 30800
                                · have hoff : 30750 ≤ n := by omega
                                  have hnfin : n - 30750 < 50 := by omega
                                  simpa [Nat.sub_add_cancel hoff] using m0_w15 ⟨n - 30750, hnfin⟩
                                ·
                                  by_cases h16 : n < 30850
                                  · have hoff : 30800 ≤ n := by omega
                                    have hnfin : n - 30800 < 50 := by omega
                                    simpa [Nat.sub_add_cancel hoff] using m0_w16 ⟨n - 30800, hnfin⟩
                                  ·
                                    by_cases h17 : n < 30900
                                    · have hoff : 30850 ≤ n := by omega
                                      have hnfin : n - 30850 < 50 := by omega
                                      simpa [Nat.sub_add_cancel hoff] using m0_w17 ⟨n - 30850, hnfin⟩
                                    ·
                                      by_cases h18 : n < 30950
                                      · have hoff : 30900 ≤ n := by omega
                                        have hnfin : n - 30900 < 50 := by omega
                                        simpa [Nat.sub_add_cancel hoff] using m0_w18 ⟨n - 30900, hnfin⟩
                                      ·
                                        by_cases h19 : n < 31000
                                        · have hoff : 30950 ≤ n := by omega
                                          have hnfin : n - 30950 < 50 := by omega
                                          simpa [Nat.sub_add_cancel hoff] using m0_w19 ⟨n - 30950, hnfin⟩
                                        ·
                                          by_cases h20 : n < 31050
                                          · have hoff : 31000 ≤ n := by omega
                                            have hnfin : n - 31000 < 50 := by omega
                                            simpa [Nat.sub_add_cancel hoff] using m0_w20 ⟨n - 31000, hnfin⟩
                                          ·
                                            by_cases h21 : n < 31100
                                            · have hoff : 31050 ≤ n := by omega
                                              have hnfin : n - 31050 < 50 := by omega
                                              simpa [Nat.sub_add_cancel hoff] using m0_w21 ⟨n - 31050, hnfin⟩
                                            ·
                                              by_cases h22 : n < 31150
                                              · have hoff : 31100 ≤ n := by omega
                                                have hnfin : n - 31100 < 50 := by omega
                                                simpa [Nat.sub_add_cancel hoff] using m0_w22 ⟨n - 31100, hnfin⟩
                                              ·
                                                by_cases h23 : n < 31200
                                                · have hoff : 31150 ≤ n := by omega
                                                  have hnfin : n - 31150 < 50 := by omega
                                                  simpa [Nat.sub_add_cancel hoff] using m0_w23 ⟨n - 31150, hnfin⟩
                                                ·
                                                  by_cases h24 : n < 31250
                                                  · have hoff : 31200 ≤ n := by omega
                                                    have hnfin : n - 31200 < 50 := by omega
                                                    simpa [Nat.sub_add_cancel hoff] using m0_w24 ⟨n - 31200, hnfin⟩
                                                  ·
                                                    by_cases h25 : n < 31300
                                                    · have hoff : 31250 ≤ n := by omega
                                                      have hnfin : n - 31250 < 50 := by omega
                                                      simpa [Nat.sub_add_cancel hoff] using m0_w25 ⟨n - 31250, hnfin⟩
                                                    ·
                                                      by_cases h26 : n < 31350
                                                      · have hoff : 31300 ≤ n := by omega
                                                        have hnfin : n - 31300 < 50 := by omega
                                                        simpa [Nat.sub_add_cancel hoff] using m0_w26 ⟨n - 31300, hnfin⟩
                                                      ·
                                                        by_cases h27 : n < 31400
                                                        · have hoff : 31350 ≤ n := by omega
                                                          have hnfin : n - 31350 < 50 := by omega
                                                          simpa [Nat.sub_add_cancel hoff] using m0_w27 ⟨n - 31350, hnfin⟩
                                                        ·
                                                          by_cases h28 : n < 31450
                                                          · have hoff : 31400 ≤ n := by omega
                                                            have hnfin : n - 31400 < 50 := by omega
                                                            simpa [Nat.sub_add_cancel hoff] using m0_w28 ⟨n - 31400, hnfin⟩
                                                          ·
                                                            by_cases h29 : n < 31500
                                                            · have hoff : 31450 ≤ n := by omega
                                                              have hnfin : n - 31450 < 50 := by omega
                                                              simpa [Nat.sub_add_cancel hoff] using m0_w29 ⟨n - 31450, hnfin⟩
                                                            ·
                                                              by_cases h30 : n < 31550
                                                              · have hoff : 31500 ≤ n := by omega
                                                                have hnfin : n - 31500 < 50 := by omega
                                                                simpa [Nat.sub_add_cancel hoff] using m0_w30 ⟨n - 31500, hnfin⟩
                                                              ·
                                                                by_cases h31 : n < 31600
                                                                · have hoff : 31550 ≤ n := by omega
                                                                  have hnfin : n - 31550 < 50 := by omega
                                                                  simpa [Nat.sub_add_cancel hoff] using m0_w31 ⟨n - 31550, hnfin⟩
                                                                ·
                                                                  by_cases h32 : n < 31650
                                                                  · have hoff : 31600 ≤ n := by omega
                                                                    have hnfin : n - 31600 < 50 := by omega
                                                                    simpa [Nat.sub_add_cancel hoff] using m0_w32 ⟨n - 31600, hnfin⟩
                                                                  ·
                                                                    by_cases h33 : n < 31700
                                                                    · have hoff : 31650 ≤ n := by omega
                                                                      have hnfin : n - 31650 < 50 := by omega
                                                                      simpa [Nat.sub_add_cancel hoff] using m0_w33 ⟨n - 31650, hnfin⟩
                                                                    ·
                                                                      by_cases h34 : n < 31750
                                                                      · have hoff : 31700 ≤ n := by omega
                                                                        have hnfin : n - 31700 < 50 := by omega
                                                                        simpa [Nat.sub_add_cancel hoff] using m0_w34 ⟨n - 31700, hnfin⟩
                                                                      ·
                                                                        by_cases h35 : n < 31800
                                                                        · have hoff : 31750 ≤ n := by omega
                                                                          have hnfin : n - 31750 < 50 := by omega
                                                                          simpa [Nat.sub_add_cancel hoff] using m0_w35 ⟨n - 31750, hnfin⟩
                                                                        ·
                                                                          by_cases h36 : n < 31850
                                                                          · have hoff : 31800 ≤ n := by omega
                                                                            have hnfin : n - 31800 < 50 := by omega
                                                                            simpa [Nat.sub_add_cancel hoff] using m0_w36 ⟨n - 31800, hnfin⟩
                                                                          ·
                                                                            by_cases h37 : n < 31900
                                                                            · have hoff : 31850 ≤ n := by omega
                                                                              have hnfin : n - 31850 < 50 := by omega
                                                                              simpa [Nat.sub_add_cancel hoff] using m0_w37 ⟨n - 31850, hnfin⟩
                                                                            ·
                                                                              by_cases h38 : n < 31950
                                                                              · have hoff : 31900 ≤ n := by omega
                                                                                have hnfin : n - 31900 < 50 := by omega
                                                                                simpa [Nat.sub_add_cancel hoff] using m0_w38 ⟨n - 31900, hnfin⟩
                                                                              ·
                                                                                by_cases h39 : n < 32000
                                                                                · have hoff : 31950 ≤ n := by omega
                                                                                  have hnfin : n - 31950 < 50 := by omega
                                                                                  simpa [Nat.sub_add_cancel hoff] using m0_w39 ⟨n - 31950, hnfin⟩
                                                                                ·
                                                                                  by_cases h40 : n < 32050
                                                                                  · have hoff : 32000 ≤ n := by omega
                                                                                    have hnfin : n - 32000 < 50 := by omega
                                                                                    simpa [Nat.sub_add_cancel hoff] using m0_w40 ⟨n - 32000, hnfin⟩
                                                                                  ·
                                                                                    by_cases h41 : n < 32100
                                                                                    · have hoff : 32050 ≤ n := by omega
                                                                                      have hnfin : n - 32050 < 50 := by omega
                                                                                      simpa [Nat.sub_add_cancel hoff] using m0_w41 ⟨n - 32050, hnfin⟩
                                                                                    ·
                                                                                      by_cases h42 : n < 32150
                                                                                      · have hoff : 32100 ≤ n := by omega
                                                                                        have hnfin : n - 32100 < 50 := by omega
                                                                                        simpa [Nat.sub_add_cancel hoff] using m0_w42 ⟨n - 32100, hnfin⟩
                                                                                      ·
                                                                                        by_cases h43 : n < 32200
                                                                                        · have hoff : 32150 ≤ n := by omega
                                                                                          have hnfin : n - 32150 < 50 := by omega
                                                                                          simpa [Nat.sub_add_cancel hoff] using m0_w43 ⟨n - 32150, hnfin⟩
                                                                                        ·
                                                                                          by_cases h44 : n < 32250
                                                                                          · have hoff : 32200 ≤ n := by omega
                                                                                            have hnfin : n - 32200 < 50 := by omega
                                                                                            simpa [Nat.sub_add_cancel hoff] using m0_w44 ⟨n - 32200, hnfin⟩
                                                                                          ·
                                                                                            by_cases h45 : n < 32300
                                                                                            · have hoff : 32250 ≤ n := by omega
                                                                                              have hnfin : n - 32250 < 50 := by omega
                                                                                              simpa [Nat.sub_add_cancel hoff] using m0_w45 ⟨n - 32250, hnfin⟩
                                                                                            ·
                                                                                              by_cases h46 : n < 32350
                                                                                              · have hoff : 32300 ≤ n := by omega
                                                                                                have hnfin : n - 32300 < 50 := by omega
                                                                                                simpa [Nat.sub_add_cancel hoff] using m0_w46 ⟨n - 32300, hnfin⟩
                                                                                              ·
                                                                                                by_cases h47 : n < 32400
                                                                                                · have hoff : 32350 ≤ n := by omega
                                                                                                  have hnfin : n - 32350 < 50 := by omega
                                                                                                  simpa [Nat.sub_add_cancel hoff] using m0_w47 ⟨n - 32350, hnfin⟩
                                                                                                ·
                                                                                                  by_cases h48 : n < 32450
                                                                                                  · have hoff : 32400 ≤ n := by omega
                                                                                                    have hnfin : n - 32400 < 50 := by omega
                                                                                                    simpa [Nat.sub_add_cancel hoff] using m0_w48 ⟨n - 32400, hnfin⟩
                                                                                                  ·
                                                                                                    by_cases h49 : n < 32500
                                                                                                    · have hoff : 32450 ≤ n := by omega
                                                                                                      have hnfin : n - 32450 < 50 := by omega
                                                                                                      simpa [Nat.sub_add_cancel hoff] using m0_w49 ⟨n - 32450, hnfin⟩
                                                                                                    ·
                                                                                                      omega
theorem land1_range (n : ℕ) (hn0 : 30000 ≤ n) (hn1 : n < 32500) :
    (!Nat.blt (dimF (arg1 n)) (dimF n) ||
      Nat.beq (Nat.land (densSupG (arg1 n)) (densSupG n)) (densSupG (arg1 n))) = true := by
  by_cases h0 : n < 30050
  · have hoff : 30000 ≤ n := by omega
    have hnfin : n - 30000 < 50 := by omega
    simpa [Nat.sub_add_cancel hoff] using m1_w0 ⟨n - 30000, hnfin⟩
  ·
    by_cases h1 : n < 30100
    · have hoff : 30050 ≤ n := by omega
      have hnfin : n - 30050 < 50 := by omega
      simpa [Nat.sub_add_cancel hoff] using m1_w1 ⟨n - 30050, hnfin⟩
    ·
      by_cases h2 : n < 30150
      · have hoff : 30100 ≤ n := by omega
        have hnfin : n - 30100 < 50 := by omega
        simpa [Nat.sub_add_cancel hoff] using m1_w2 ⟨n - 30100, hnfin⟩
      ·
        by_cases h3 : n < 30200
        · have hoff : 30150 ≤ n := by omega
          have hnfin : n - 30150 < 50 := by omega
          simpa [Nat.sub_add_cancel hoff] using m1_w3 ⟨n - 30150, hnfin⟩
        ·
          by_cases h4 : n < 30250
          · have hoff : 30200 ≤ n := by omega
            have hnfin : n - 30200 < 50 := by omega
            simpa [Nat.sub_add_cancel hoff] using m1_w4 ⟨n - 30200, hnfin⟩
          ·
            by_cases h5 : n < 30300
            · have hoff : 30250 ≤ n := by omega
              have hnfin : n - 30250 < 50 := by omega
              simpa [Nat.sub_add_cancel hoff] using m1_w5 ⟨n - 30250, hnfin⟩
            ·
              by_cases h6 : n < 30350
              · have hoff : 30300 ≤ n := by omega
                have hnfin : n - 30300 < 50 := by omega
                simpa [Nat.sub_add_cancel hoff] using m1_w6 ⟨n - 30300, hnfin⟩
              ·
                by_cases h7 : n < 30400
                · have hoff : 30350 ≤ n := by omega
                  have hnfin : n - 30350 < 50 := by omega
                  simpa [Nat.sub_add_cancel hoff] using m1_w7 ⟨n - 30350, hnfin⟩
                ·
                  by_cases h8 : n < 30450
                  · have hoff : 30400 ≤ n := by omega
                    have hnfin : n - 30400 < 50 := by omega
                    simpa [Nat.sub_add_cancel hoff] using m1_w8 ⟨n - 30400, hnfin⟩
                  ·
                    by_cases h9 : n < 30500
                    · have hoff : 30450 ≤ n := by omega
                      have hnfin : n - 30450 < 50 := by omega
                      simpa [Nat.sub_add_cancel hoff] using m1_w9 ⟨n - 30450, hnfin⟩
                    ·
                      by_cases h10 : n < 30550
                      · have hoff : 30500 ≤ n := by omega
                        have hnfin : n - 30500 < 50 := by omega
                        simpa [Nat.sub_add_cancel hoff] using m1_w10 ⟨n - 30500, hnfin⟩
                      ·
                        by_cases h11 : n < 30600
                        · have hoff : 30550 ≤ n := by omega
                          have hnfin : n - 30550 < 50 := by omega
                          simpa [Nat.sub_add_cancel hoff] using m1_w11 ⟨n - 30550, hnfin⟩
                        ·
                          by_cases h12 : n < 30650
                          · have hoff : 30600 ≤ n := by omega
                            have hnfin : n - 30600 < 50 := by omega
                            simpa [Nat.sub_add_cancel hoff] using m1_w12 ⟨n - 30600, hnfin⟩
                          ·
                            by_cases h13 : n < 30700
                            · have hoff : 30650 ≤ n := by omega
                              have hnfin : n - 30650 < 50 := by omega
                              simpa [Nat.sub_add_cancel hoff] using m1_w13 ⟨n - 30650, hnfin⟩
                            ·
                              by_cases h14 : n < 30750
                              · have hoff : 30700 ≤ n := by omega
                                have hnfin : n - 30700 < 50 := by omega
                                simpa [Nat.sub_add_cancel hoff] using m1_w14 ⟨n - 30700, hnfin⟩
                              ·
                                by_cases h15 : n < 30800
                                · have hoff : 30750 ≤ n := by omega
                                  have hnfin : n - 30750 < 50 := by omega
                                  simpa [Nat.sub_add_cancel hoff] using m1_w15 ⟨n - 30750, hnfin⟩
                                ·
                                  by_cases h16 : n < 30850
                                  · have hoff : 30800 ≤ n := by omega
                                    have hnfin : n - 30800 < 50 := by omega
                                    simpa [Nat.sub_add_cancel hoff] using m1_w16 ⟨n - 30800, hnfin⟩
                                  ·
                                    by_cases h17 : n < 30900
                                    · have hoff : 30850 ≤ n := by omega
                                      have hnfin : n - 30850 < 50 := by omega
                                      simpa [Nat.sub_add_cancel hoff] using m1_w17 ⟨n - 30850, hnfin⟩
                                    ·
                                      by_cases h18 : n < 30950
                                      · have hoff : 30900 ≤ n := by omega
                                        have hnfin : n - 30900 < 50 := by omega
                                        simpa [Nat.sub_add_cancel hoff] using m1_w18 ⟨n - 30900, hnfin⟩
                                      ·
                                        by_cases h19 : n < 31000
                                        · have hoff : 30950 ≤ n := by omega
                                          have hnfin : n - 30950 < 50 := by omega
                                          simpa [Nat.sub_add_cancel hoff] using m1_w19 ⟨n - 30950, hnfin⟩
                                        ·
                                          by_cases h20 : n < 31050
                                          · have hoff : 31000 ≤ n := by omega
                                            have hnfin : n - 31000 < 50 := by omega
                                            simpa [Nat.sub_add_cancel hoff] using m1_w20 ⟨n - 31000, hnfin⟩
                                          ·
                                            by_cases h21 : n < 31100
                                            · have hoff : 31050 ≤ n := by omega
                                              have hnfin : n - 31050 < 50 := by omega
                                              simpa [Nat.sub_add_cancel hoff] using m1_w21 ⟨n - 31050, hnfin⟩
                                            ·
                                              by_cases h22 : n < 31150
                                              · have hoff : 31100 ≤ n := by omega
                                                have hnfin : n - 31100 < 50 := by omega
                                                simpa [Nat.sub_add_cancel hoff] using m1_w22 ⟨n - 31100, hnfin⟩
                                              ·
                                                by_cases h23 : n < 31200
                                                · have hoff : 31150 ≤ n := by omega
                                                  have hnfin : n - 31150 < 50 := by omega
                                                  simpa [Nat.sub_add_cancel hoff] using m1_w23 ⟨n - 31150, hnfin⟩
                                                ·
                                                  by_cases h24 : n < 31250
                                                  · have hoff : 31200 ≤ n := by omega
                                                    have hnfin : n - 31200 < 50 := by omega
                                                    simpa [Nat.sub_add_cancel hoff] using m1_w24 ⟨n - 31200, hnfin⟩
                                                  ·
                                                    by_cases h25 : n < 31300
                                                    · have hoff : 31250 ≤ n := by omega
                                                      have hnfin : n - 31250 < 50 := by omega
                                                      simpa [Nat.sub_add_cancel hoff] using m1_w25 ⟨n - 31250, hnfin⟩
                                                    ·
                                                      by_cases h26 : n < 31350
                                                      · have hoff : 31300 ≤ n := by omega
                                                        have hnfin : n - 31300 < 50 := by omega
                                                        simpa [Nat.sub_add_cancel hoff] using m1_w26 ⟨n - 31300, hnfin⟩
                                                      ·
                                                        by_cases h27 : n < 31400
                                                        · have hoff : 31350 ≤ n := by omega
                                                          have hnfin : n - 31350 < 50 := by omega
                                                          simpa [Nat.sub_add_cancel hoff] using m1_w27 ⟨n - 31350, hnfin⟩
                                                        ·
                                                          by_cases h28 : n < 31450
                                                          · have hoff : 31400 ≤ n := by omega
                                                            have hnfin : n - 31400 < 50 := by omega
                                                            simpa [Nat.sub_add_cancel hoff] using m1_w28 ⟨n - 31400, hnfin⟩
                                                          ·
                                                            by_cases h29 : n < 31500
                                                            · have hoff : 31450 ≤ n := by omega
                                                              have hnfin : n - 31450 < 50 := by omega
                                                              simpa [Nat.sub_add_cancel hoff] using m1_w29 ⟨n - 31450, hnfin⟩
                                                            ·
                                                              by_cases h30 : n < 31550
                                                              · have hoff : 31500 ≤ n := by omega
                                                                have hnfin : n - 31500 < 50 := by omega
                                                                simpa [Nat.sub_add_cancel hoff] using m1_w30 ⟨n - 31500, hnfin⟩
                                                              ·
                                                                by_cases h31 : n < 31600
                                                                · have hoff : 31550 ≤ n := by omega
                                                                  have hnfin : n - 31550 < 50 := by omega
                                                                  simpa [Nat.sub_add_cancel hoff] using m1_w31 ⟨n - 31550, hnfin⟩
                                                                ·
                                                                  by_cases h32 : n < 31650
                                                                  · have hoff : 31600 ≤ n := by omega
                                                                    have hnfin : n - 31600 < 50 := by omega
                                                                    simpa [Nat.sub_add_cancel hoff] using m1_w32 ⟨n - 31600, hnfin⟩
                                                                  ·
                                                                    by_cases h33 : n < 31700
                                                                    · have hoff : 31650 ≤ n := by omega
                                                                      have hnfin : n - 31650 < 50 := by omega
                                                                      simpa [Nat.sub_add_cancel hoff] using m1_w33 ⟨n - 31650, hnfin⟩
                                                                    ·
                                                                      by_cases h34 : n < 31750
                                                                      · have hoff : 31700 ≤ n := by omega
                                                                        have hnfin : n - 31700 < 50 := by omega
                                                                        simpa [Nat.sub_add_cancel hoff] using m1_w34 ⟨n - 31700, hnfin⟩
                                                                      ·
                                                                        by_cases h35 : n < 31800
                                                                        · have hoff : 31750 ≤ n := by omega
                                                                          have hnfin : n - 31750 < 50 := by omega
                                                                          simpa [Nat.sub_add_cancel hoff] using m1_w35 ⟨n - 31750, hnfin⟩
                                                                        ·
                                                                          by_cases h36 : n < 31850
                                                                          · have hoff : 31800 ≤ n := by omega
                                                                            have hnfin : n - 31800 < 50 := by omega
                                                                            simpa [Nat.sub_add_cancel hoff] using m1_w36 ⟨n - 31800, hnfin⟩
                                                                          ·
                                                                            by_cases h37 : n < 31900
                                                                            · have hoff : 31850 ≤ n := by omega
                                                                              have hnfin : n - 31850 < 50 := by omega
                                                                              simpa [Nat.sub_add_cancel hoff] using m1_w37 ⟨n - 31850, hnfin⟩
                                                                            ·
                                                                              by_cases h38 : n < 31950
                                                                              · have hoff : 31900 ≤ n := by omega
                                                                                have hnfin : n - 31900 < 50 := by omega
                                                                                simpa [Nat.sub_add_cancel hoff] using m1_w38 ⟨n - 31900, hnfin⟩
                                                                              ·
                                                                                by_cases h39 : n < 32000
                                                                                · have hoff : 31950 ≤ n := by omega
                                                                                  have hnfin : n - 31950 < 50 := by omega
                                                                                  simpa [Nat.sub_add_cancel hoff] using m1_w39 ⟨n - 31950, hnfin⟩
                                                                                ·
                                                                                  by_cases h40 : n < 32050
                                                                                  · have hoff : 32000 ≤ n := by omega
                                                                                    have hnfin : n - 32000 < 50 := by omega
                                                                                    simpa [Nat.sub_add_cancel hoff] using m1_w40 ⟨n - 32000, hnfin⟩
                                                                                  ·
                                                                                    by_cases h41 : n < 32100
                                                                                    · have hoff : 32050 ≤ n := by omega
                                                                                      have hnfin : n - 32050 < 50 := by omega
                                                                                      simpa [Nat.sub_add_cancel hoff] using m1_w41 ⟨n - 32050, hnfin⟩
                                                                                    ·
                                                                                      by_cases h42 : n < 32150
                                                                                      · have hoff : 32100 ≤ n := by omega
                                                                                        have hnfin : n - 32100 < 50 := by omega
                                                                                        simpa [Nat.sub_add_cancel hoff] using m1_w42 ⟨n - 32100, hnfin⟩
                                                                                      ·
                                                                                        by_cases h43 : n < 32200
                                                                                        · have hoff : 32150 ≤ n := by omega
                                                                                          have hnfin : n - 32150 < 50 := by omega
                                                                                          simpa [Nat.sub_add_cancel hoff] using m1_w43 ⟨n - 32150, hnfin⟩
                                                                                        ·
                                                                                          by_cases h44 : n < 32250
                                                                                          · have hoff : 32200 ≤ n := by omega
                                                                                            have hnfin : n - 32200 < 50 := by omega
                                                                                            simpa [Nat.sub_add_cancel hoff] using m1_w44 ⟨n - 32200, hnfin⟩
                                                                                          ·
                                                                                            by_cases h45 : n < 32300
                                                                                            · have hoff : 32250 ≤ n := by omega
                                                                                              have hnfin : n - 32250 < 50 := by omega
                                                                                              simpa [Nat.sub_add_cancel hoff] using m1_w45 ⟨n - 32250, hnfin⟩
                                                                                            ·
                                                                                              by_cases h46 : n < 32350
                                                                                              · have hoff : 32300 ≤ n := by omega
                                                                                                have hnfin : n - 32300 < 50 := by omega
                                                                                                simpa [Nat.sub_add_cancel hoff] using m1_w46 ⟨n - 32300, hnfin⟩
                                                                                              ·
                                                                                                by_cases h47 : n < 32400
                                                                                                · have hoff : 32350 ≤ n := by omega
                                                                                                  have hnfin : n - 32350 < 50 := by omega
                                                                                                  simpa [Nat.sub_add_cancel hoff] using m1_w47 ⟨n - 32350, hnfin⟩
                                                                                                ·
                                                                                                  by_cases h48 : n < 32450
                                                                                                  · have hoff : 32400 ≤ n := by omega
                                                                                                    have hnfin : n - 32400 < 50 := by omega
                                                                                                    simpa [Nat.sub_add_cancel hoff] using m1_w48 ⟨n - 32400, hnfin⟩
                                                                                                  ·
                                                                                                    by_cases h49 : n < 32500
                                                                                                    · have hoff : 32450 ≤ n := by omega
                                                                                                      have hnfin : n - 32450 < 50 := by omega
                                                                                                      simpa [Nat.sub_add_cancel hoff] using m1_w49 ⟨n - 32450, hnfin⟩
                                                                                                    ·
                                                                                                      omega
end IntMul.Kappa.R8.Bit.Oppbank.LandMonoFixA12


