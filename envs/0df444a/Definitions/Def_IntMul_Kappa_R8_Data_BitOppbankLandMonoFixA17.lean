-- Prove2me | Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankLandMonoFixA17
-- name    : IntMul_Kappa_R8_Data_BitOppbankLandMonoFixA17
-- status  : Definition
-- author  : @Ethan Cheung Wang
-- created : 2026-10-28T21:17:26.497988+00:00
-- url     : https://prove2.me/theorems/ab2b788b-f7b6-4f19-98e4-dd4dabb331ed
-- title:
--   Dim-gated densSup land mono FixA pack 17
-- statement:
--   # Dim-gated densSup land (PndFix), pack A17
--
--   Range consolidators for $n\in[42500,45000)$.
-- source:
--   R8 BitOppbank PndFix

-- LandMonoFixA17: PUBLIC dim-gated land + range consolidators (PndFix)
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
namespace IntMul.Kappa.R8.Bit.Oppbank.LandMonoFixA17
def arg0 (n : ℕ) : ℕ := Nat.land (argF n) 65535
def arg1 (n : ℕ) : ℕ := Nat.shiftRight (argF n) 16
theorem m0_w0 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 42500))) (dimF (n.val + 42500)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 42500))) (densSupG (n.val + 42500))) (densSupG (arg0 (n.val + 42500)))) = true := by decide
theorem m1_w0 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 42500))) (dimF (n.val + 42500)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 42500))) (densSupG (n.val + 42500))) (densSupG (arg1 (n.val + 42500)))) = true := by decide
theorem m0_w1 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 42550))) (dimF (n.val + 42550)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 42550))) (densSupG (n.val + 42550))) (densSupG (arg0 (n.val + 42550)))) = true := by decide
theorem m1_w1 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 42550))) (dimF (n.val + 42550)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 42550))) (densSupG (n.val + 42550))) (densSupG (arg1 (n.val + 42550)))) = true := by decide
theorem m0_w2 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 42600))) (dimF (n.val + 42600)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 42600))) (densSupG (n.val + 42600))) (densSupG (arg0 (n.val + 42600)))) = true := by decide
theorem m1_w2 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 42600))) (dimF (n.val + 42600)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 42600))) (densSupG (n.val + 42600))) (densSupG (arg1 (n.val + 42600)))) = true := by decide
theorem m0_w3 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 42650))) (dimF (n.val + 42650)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 42650))) (densSupG (n.val + 42650))) (densSupG (arg0 (n.val + 42650)))) = true := by decide
theorem m1_w3 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 42650))) (dimF (n.val + 42650)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 42650))) (densSupG (n.val + 42650))) (densSupG (arg1 (n.val + 42650)))) = true := by decide
theorem m0_w4 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 42700))) (dimF (n.val + 42700)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 42700))) (densSupG (n.val + 42700))) (densSupG (arg0 (n.val + 42700)))) = true := by decide
theorem m1_w4 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 42700))) (dimF (n.val + 42700)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 42700))) (densSupG (n.val + 42700))) (densSupG (arg1 (n.val + 42700)))) = true := by decide
theorem m0_w5 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 42750))) (dimF (n.val + 42750)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 42750))) (densSupG (n.val + 42750))) (densSupG (arg0 (n.val + 42750)))) = true := by decide
theorem m1_w5 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 42750))) (dimF (n.val + 42750)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 42750))) (densSupG (n.val + 42750))) (densSupG (arg1 (n.val + 42750)))) = true := by decide
theorem m0_w6 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 42800))) (dimF (n.val + 42800)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 42800))) (densSupG (n.val + 42800))) (densSupG (arg0 (n.val + 42800)))) = true := by decide
theorem m1_w6 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 42800))) (dimF (n.val + 42800)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 42800))) (densSupG (n.val + 42800))) (densSupG (arg1 (n.val + 42800)))) = true := by decide
theorem m0_w7 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 42850))) (dimF (n.val + 42850)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 42850))) (densSupG (n.val + 42850))) (densSupG (arg0 (n.val + 42850)))) = true := by decide
theorem m1_w7 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 42850))) (dimF (n.val + 42850)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 42850))) (densSupG (n.val + 42850))) (densSupG (arg1 (n.val + 42850)))) = true := by decide
theorem m0_w8 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 42900))) (dimF (n.val + 42900)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 42900))) (densSupG (n.val + 42900))) (densSupG (arg0 (n.val + 42900)))) = true := by decide
theorem m1_w8 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 42900))) (dimF (n.val + 42900)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 42900))) (densSupG (n.val + 42900))) (densSupG (arg1 (n.val + 42900)))) = true := by decide
theorem m0_w9 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 42950))) (dimF (n.val + 42950)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 42950))) (densSupG (n.val + 42950))) (densSupG (arg0 (n.val + 42950)))) = true := by decide
theorem m1_w9 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 42950))) (dimF (n.val + 42950)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 42950))) (densSupG (n.val + 42950))) (densSupG (arg1 (n.val + 42950)))) = true := by decide
theorem m0_w10 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 43000))) (dimF (n.val + 43000)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 43000))) (densSupG (n.val + 43000))) (densSupG (arg0 (n.val + 43000)))) = true := by decide
theorem m1_w10 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 43000))) (dimF (n.val + 43000)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 43000))) (densSupG (n.val + 43000))) (densSupG (arg1 (n.val + 43000)))) = true := by decide
theorem m0_w11 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 43050))) (dimF (n.val + 43050)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 43050))) (densSupG (n.val + 43050))) (densSupG (arg0 (n.val + 43050)))) = true := by decide
theorem m1_w11 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 43050))) (dimF (n.val + 43050)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 43050))) (densSupG (n.val + 43050))) (densSupG (arg1 (n.val + 43050)))) = true := by decide
theorem m0_w12 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 43100))) (dimF (n.val + 43100)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 43100))) (densSupG (n.val + 43100))) (densSupG (arg0 (n.val + 43100)))) = true := by decide
theorem m1_w12 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 43100))) (dimF (n.val + 43100)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 43100))) (densSupG (n.val + 43100))) (densSupG (arg1 (n.val + 43100)))) = true := by decide
theorem m0_w13 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 43150))) (dimF (n.val + 43150)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 43150))) (densSupG (n.val + 43150))) (densSupG (arg0 (n.val + 43150)))) = true := by decide
theorem m1_w13 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 43150))) (dimF (n.val + 43150)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 43150))) (densSupG (n.val + 43150))) (densSupG (arg1 (n.val + 43150)))) = true := by decide
theorem m0_w14 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 43200))) (dimF (n.val + 43200)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 43200))) (densSupG (n.val + 43200))) (densSupG (arg0 (n.val + 43200)))) = true := by decide
theorem m1_w14 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 43200))) (dimF (n.val + 43200)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 43200))) (densSupG (n.val + 43200))) (densSupG (arg1 (n.val + 43200)))) = true := by decide
theorem m0_w15 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 43250))) (dimF (n.val + 43250)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 43250))) (densSupG (n.val + 43250))) (densSupG (arg0 (n.val + 43250)))) = true := by decide
theorem m1_w15 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 43250))) (dimF (n.val + 43250)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 43250))) (densSupG (n.val + 43250))) (densSupG (arg1 (n.val + 43250)))) = true := by decide
theorem m0_w16 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 43300))) (dimF (n.val + 43300)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 43300))) (densSupG (n.val + 43300))) (densSupG (arg0 (n.val + 43300)))) = true := by decide
theorem m1_w16 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 43300))) (dimF (n.val + 43300)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 43300))) (densSupG (n.val + 43300))) (densSupG (arg1 (n.val + 43300)))) = true := by decide
theorem m0_w17 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 43350))) (dimF (n.val + 43350)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 43350))) (densSupG (n.val + 43350))) (densSupG (arg0 (n.val + 43350)))) = true := by decide
theorem m1_w17 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 43350))) (dimF (n.val + 43350)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 43350))) (densSupG (n.val + 43350))) (densSupG (arg1 (n.val + 43350)))) = true := by decide
theorem m0_w18 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 43400))) (dimF (n.val + 43400)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 43400))) (densSupG (n.val + 43400))) (densSupG (arg0 (n.val + 43400)))) = true := by decide
theorem m1_w18 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 43400))) (dimF (n.val + 43400)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 43400))) (densSupG (n.val + 43400))) (densSupG (arg1 (n.val + 43400)))) = true := by decide
theorem m0_w19 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 43450))) (dimF (n.val + 43450)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 43450))) (densSupG (n.val + 43450))) (densSupG (arg0 (n.val + 43450)))) = true := by decide
theorem m1_w19 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 43450))) (dimF (n.val + 43450)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 43450))) (densSupG (n.val + 43450))) (densSupG (arg1 (n.val + 43450)))) = true := by decide
theorem m0_w20 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 43500))) (dimF (n.val + 43500)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 43500))) (densSupG (n.val + 43500))) (densSupG (arg0 (n.val + 43500)))) = true := by decide
theorem m1_w20 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 43500))) (dimF (n.val + 43500)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 43500))) (densSupG (n.val + 43500))) (densSupG (arg1 (n.val + 43500)))) = true := by decide
theorem m0_w21 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 43550))) (dimF (n.val + 43550)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 43550))) (densSupG (n.val + 43550))) (densSupG (arg0 (n.val + 43550)))) = true := by decide
theorem m1_w21 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 43550))) (dimF (n.val + 43550)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 43550))) (densSupG (n.val + 43550))) (densSupG (arg1 (n.val + 43550)))) = true := by decide
theorem m0_w22 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 43600))) (dimF (n.val + 43600)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 43600))) (densSupG (n.val + 43600))) (densSupG (arg0 (n.val + 43600)))) = true := by decide
theorem m1_w22 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 43600))) (dimF (n.val + 43600)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 43600))) (densSupG (n.val + 43600))) (densSupG (arg1 (n.val + 43600)))) = true := by decide
theorem m0_w23 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 43650))) (dimF (n.val + 43650)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 43650))) (densSupG (n.val + 43650))) (densSupG (arg0 (n.val + 43650)))) = true := by decide
theorem m1_w23 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 43650))) (dimF (n.val + 43650)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 43650))) (densSupG (n.val + 43650))) (densSupG (arg1 (n.val + 43650)))) = true := by decide
theorem m0_w24 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 43700))) (dimF (n.val + 43700)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 43700))) (densSupG (n.val + 43700))) (densSupG (arg0 (n.val + 43700)))) = true := by decide
theorem m1_w24 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 43700))) (dimF (n.val + 43700)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 43700))) (densSupG (n.val + 43700))) (densSupG (arg1 (n.val + 43700)))) = true := by decide
theorem m0_w25 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 43750))) (dimF (n.val + 43750)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 43750))) (densSupG (n.val + 43750))) (densSupG (arg0 (n.val + 43750)))) = true := by decide
theorem m1_w25 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 43750))) (dimF (n.val + 43750)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 43750))) (densSupG (n.val + 43750))) (densSupG (arg1 (n.val + 43750)))) = true := by decide
theorem m0_w26 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 43800))) (dimF (n.val + 43800)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 43800))) (densSupG (n.val + 43800))) (densSupG (arg0 (n.val + 43800)))) = true := by decide
theorem m1_w26 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 43800))) (dimF (n.val + 43800)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 43800))) (densSupG (n.val + 43800))) (densSupG (arg1 (n.val + 43800)))) = true := by decide
theorem m0_w27 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 43850))) (dimF (n.val + 43850)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 43850))) (densSupG (n.val + 43850))) (densSupG (arg0 (n.val + 43850)))) = true := by decide
theorem m1_w27 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 43850))) (dimF (n.val + 43850)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 43850))) (densSupG (n.val + 43850))) (densSupG (arg1 (n.val + 43850)))) = true := by decide
theorem m0_w28 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 43900))) (dimF (n.val + 43900)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 43900))) (densSupG (n.val + 43900))) (densSupG (arg0 (n.val + 43900)))) = true := by decide
theorem m1_w28 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 43900))) (dimF (n.val + 43900)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 43900))) (densSupG (n.val + 43900))) (densSupG (arg1 (n.val + 43900)))) = true := by decide
theorem m0_w29 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 43950))) (dimF (n.val + 43950)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 43950))) (densSupG (n.val + 43950))) (densSupG (arg0 (n.val + 43950)))) = true := by decide
theorem m1_w29 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 43950))) (dimF (n.val + 43950)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 43950))) (densSupG (n.val + 43950))) (densSupG (arg1 (n.val + 43950)))) = true := by decide
theorem m0_w30 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 44000))) (dimF (n.val + 44000)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 44000))) (densSupG (n.val + 44000))) (densSupG (arg0 (n.val + 44000)))) = true := by decide
theorem m1_w30 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 44000))) (dimF (n.val + 44000)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 44000))) (densSupG (n.val + 44000))) (densSupG (arg1 (n.val + 44000)))) = true := by decide
theorem m0_w31 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 44050))) (dimF (n.val + 44050)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 44050))) (densSupG (n.val + 44050))) (densSupG (arg0 (n.val + 44050)))) = true := by decide
theorem m1_w31 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 44050))) (dimF (n.val + 44050)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 44050))) (densSupG (n.val + 44050))) (densSupG (arg1 (n.val + 44050)))) = true := by decide
theorem m0_w32 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 44100))) (dimF (n.val + 44100)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 44100))) (densSupG (n.val + 44100))) (densSupG (arg0 (n.val + 44100)))) = true := by decide
theorem m1_w32 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 44100))) (dimF (n.val + 44100)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 44100))) (densSupG (n.val + 44100))) (densSupG (arg1 (n.val + 44100)))) = true := by decide
theorem m0_w33 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 44150))) (dimF (n.val + 44150)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 44150))) (densSupG (n.val + 44150))) (densSupG (arg0 (n.val + 44150)))) = true := by decide
theorem m1_w33 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 44150))) (dimF (n.val + 44150)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 44150))) (densSupG (n.val + 44150))) (densSupG (arg1 (n.val + 44150)))) = true := by decide
theorem m0_w34 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 44200))) (dimF (n.val + 44200)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 44200))) (densSupG (n.val + 44200))) (densSupG (arg0 (n.val + 44200)))) = true := by decide
theorem m1_w34 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 44200))) (dimF (n.val + 44200)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 44200))) (densSupG (n.val + 44200))) (densSupG (arg1 (n.val + 44200)))) = true := by decide
theorem m0_w35 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 44250))) (dimF (n.val + 44250)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 44250))) (densSupG (n.val + 44250))) (densSupG (arg0 (n.val + 44250)))) = true := by decide
theorem m1_w35 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 44250))) (dimF (n.val + 44250)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 44250))) (densSupG (n.val + 44250))) (densSupG (arg1 (n.val + 44250)))) = true := by decide
theorem m0_w36 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 44300))) (dimF (n.val + 44300)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 44300))) (densSupG (n.val + 44300))) (densSupG (arg0 (n.val + 44300)))) = true := by decide
theorem m1_w36 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 44300))) (dimF (n.val + 44300)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 44300))) (densSupG (n.val + 44300))) (densSupG (arg1 (n.val + 44300)))) = true := by decide
theorem m0_w37 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 44350))) (dimF (n.val + 44350)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 44350))) (densSupG (n.val + 44350))) (densSupG (arg0 (n.val + 44350)))) = true := by decide
theorem m1_w37 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 44350))) (dimF (n.val + 44350)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 44350))) (densSupG (n.val + 44350))) (densSupG (arg1 (n.val + 44350)))) = true := by decide
theorem m0_w38 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 44400))) (dimF (n.val + 44400)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 44400))) (densSupG (n.val + 44400))) (densSupG (arg0 (n.val + 44400)))) = true := by decide
theorem m1_w38 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 44400))) (dimF (n.val + 44400)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 44400))) (densSupG (n.val + 44400))) (densSupG (arg1 (n.val + 44400)))) = true := by decide
theorem m0_w39 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 44450))) (dimF (n.val + 44450)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 44450))) (densSupG (n.val + 44450))) (densSupG (arg0 (n.val + 44450)))) = true := by decide
theorem m1_w39 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 44450))) (dimF (n.val + 44450)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 44450))) (densSupG (n.val + 44450))) (densSupG (arg1 (n.val + 44450)))) = true := by decide
theorem m0_w40 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 44500))) (dimF (n.val + 44500)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 44500))) (densSupG (n.val + 44500))) (densSupG (arg0 (n.val + 44500)))) = true := by decide
theorem m1_w40 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 44500))) (dimF (n.val + 44500)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 44500))) (densSupG (n.val + 44500))) (densSupG (arg1 (n.val + 44500)))) = true := by decide
theorem m0_w41 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 44550))) (dimF (n.val + 44550)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 44550))) (densSupG (n.val + 44550))) (densSupG (arg0 (n.val + 44550)))) = true := by decide
theorem m1_w41 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 44550))) (dimF (n.val + 44550)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 44550))) (densSupG (n.val + 44550))) (densSupG (arg1 (n.val + 44550)))) = true := by decide
theorem m0_w42 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 44600))) (dimF (n.val + 44600)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 44600))) (densSupG (n.val + 44600))) (densSupG (arg0 (n.val + 44600)))) = true := by decide
theorem m1_w42 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 44600))) (dimF (n.val + 44600)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 44600))) (densSupG (n.val + 44600))) (densSupG (arg1 (n.val + 44600)))) = true := by decide
theorem m0_w43 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 44650))) (dimF (n.val + 44650)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 44650))) (densSupG (n.val + 44650))) (densSupG (arg0 (n.val + 44650)))) = true := by decide
theorem m1_w43 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 44650))) (dimF (n.val + 44650)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 44650))) (densSupG (n.val + 44650))) (densSupG (arg1 (n.val + 44650)))) = true := by decide
theorem m0_w44 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 44700))) (dimF (n.val + 44700)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 44700))) (densSupG (n.val + 44700))) (densSupG (arg0 (n.val + 44700)))) = true := by decide
theorem m1_w44 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 44700))) (dimF (n.val + 44700)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 44700))) (densSupG (n.val + 44700))) (densSupG (arg1 (n.val + 44700)))) = true := by decide
theorem m0_w45 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 44750))) (dimF (n.val + 44750)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 44750))) (densSupG (n.val + 44750))) (densSupG (arg0 (n.val + 44750)))) = true := by decide
theorem m1_w45 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 44750))) (dimF (n.val + 44750)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 44750))) (densSupG (n.val + 44750))) (densSupG (arg1 (n.val + 44750)))) = true := by decide
theorem m0_w46 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 44800))) (dimF (n.val + 44800)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 44800))) (densSupG (n.val + 44800))) (densSupG (arg0 (n.val + 44800)))) = true := by decide
theorem m1_w46 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 44800))) (dimF (n.val + 44800)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 44800))) (densSupG (n.val + 44800))) (densSupG (arg1 (n.val + 44800)))) = true := by decide
theorem m0_w47 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 44850))) (dimF (n.val + 44850)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 44850))) (densSupG (n.val + 44850))) (densSupG (arg0 (n.val + 44850)))) = true := by decide
theorem m1_w47 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 44850))) (dimF (n.val + 44850)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 44850))) (densSupG (n.val + 44850))) (densSupG (arg1 (n.val + 44850)))) = true := by decide
theorem m0_w48 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 44900))) (dimF (n.val + 44900)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 44900))) (densSupG (n.val + 44900))) (densSupG (arg0 (n.val + 44900)))) = true := by decide
theorem m1_w48 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 44900))) (dimF (n.val + 44900)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 44900))) (densSupG (n.val + 44900))) (densSupG (arg1 (n.val + 44900)))) = true := by decide
theorem m0_w49 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 44950))) (dimF (n.val + 44950)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 44950))) (densSupG (n.val + 44950))) (densSupG (arg0 (n.val + 44950)))) = true := by decide
theorem m1_w49 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 44950))) (dimF (n.val + 44950)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 44950))) (densSupG (n.val + 44950))) (densSupG (arg1 (n.val + 44950)))) = true := by decide
theorem land0_range (n : ℕ) (hn0 : 42500 ≤ n) (hn1 : n < 45000) :
    (!Nat.blt (dimF (arg0 n)) (dimF n) ||
      Nat.beq (Nat.land (densSupG (arg0 n)) (densSupG n)) (densSupG (arg0 n))) = true := by
  by_cases h0 : n < 42550
  · have hoff : 42500 ≤ n := by omega
    have hnfin : n - 42500 < 50 := by omega
    simpa [Nat.sub_add_cancel hoff] using m0_w0 ⟨n - 42500, hnfin⟩
  ·
    by_cases h1 : n < 42600
    · have hoff : 42550 ≤ n := by omega
      have hnfin : n - 42550 < 50 := by omega
      simpa [Nat.sub_add_cancel hoff] using m0_w1 ⟨n - 42550, hnfin⟩
    ·
      by_cases h2 : n < 42650
      · have hoff : 42600 ≤ n := by omega
        have hnfin : n - 42600 < 50 := by omega
        simpa [Nat.sub_add_cancel hoff] using m0_w2 ⟨n - 42600, hnfin⟩
      ·
        by_cases h3 : n < 42700
        · have hoff : 42650 ≤ n := by omega
          have hnfin : n - 42650 < 50 := by omega
          simpa [Nat.sub_add_cancel hoff] using m0_w3 ⟨n - 42650, hnfin⟩
        ·
          by_cases h4 : n < 42750
          · have hoff : 42700 ≤ n := by omega
            have hnfin : n - 42700 < 50 := by omega
            simpa [Nat.sub_add_cancel hoff] using m0_w4 ⟨n - 42700, hnfin⟩
          ·
            by_cases h5 : n < 42800
            · have hoff : 42750 ≤ n := by omega
              have hnfin : n - 42750 < 50 := by omega
              simpa [Nat.sub_add_cancel hoff] using m0_w5 ⟨n - 42750, hnfin⟩
            ·
              by_cases h6 : n < 42850
              · have hoff : 42800 ≤ n := by omega
                have hnfin : n - 42800 < 50 := by omega
                simpa [Nat.sub_add_cancel hoff] using m0_w6 ⟨n - 42800, hnfin⟩
              ·
                by_cases h7 : n < 42900
                · have hoff : 42850 ≤ n := by omega
                  have hnfin : n - 42850 < 50 := by omega
                  simpa [Nat.sub_add_cancel hoff] using m0_w7 ⟨n - 42850, hnfin⟩
                ·
                  by_cases h8 : n < 42950
                  · have hoff : 42900 ≤ n := by omega
                    have hnfin : n - 42900 < 50 := by omega
                    simpa [Nat.sub_add_cancel hoff] using m0_w8 ⟨n - 42900, hnfin⟩
                  ·
                    by_cases h9 : n < 43000
                    · have hoff : 42950 ≤ n := by omega
                      have hnfin : n - 42950 < 50 := by omega
                      simpa [Nat.sub_add_cancel hoff] using m0_w9 ⟨n - 42950, hnfin⟩
                    ·
                      by_cases h10 : n < 43050
                      · have hoff : 43000 ≤ n := by omega
                        have hnfin : n - 43000 < 50 := by omega
                        simpa [Nat.sub_add_cancel hoff] using m0_w10 ⟨n - 43000, hnfin⟩
                      ·
                        by_cases h11 : n < 43100
                        · have hoff : 43050 ≤ n := by omega
                          have hnfin : n - 43050 < 50 := by omega
                          simpa [Nat.sub_add_cancel hoff] using m0_w11 ⟨n - 43050, hnfin⟩
                        ·
                          by_cases h12 : n < 43150
                          · have hoff : 43100 ≤ n := by omega
                            have hnfin : n - 43100 < 50 := by omega
                            simpa [Nat.sub_add_cancel hoff] using m0_w12 ⟨n - 43100, hnfin⟩
                          ·
                            by_cases h13 : n < 43200
                            · have hoff : 43150 ≤ n := by omega
                              have hnfin : n - 43150 < 50 := by omega
                              simpa [Nat.sub_add_cancel hoff] using m0_w13 ⟨n - 43150, hnfin⟩
                            ·
                              by_cases h14 : n < 43250
                              · have hoff : 43200 ≤ n := by omega
                                have hnfin : n - 43200 < 50 := by omega
                                simpa [Nat.sub_add_cancel hoff] using m0_w14 ⟨n - 43200, hnfin⟩
                              ·
                                by_cases h15 : n < 43300
                                · have hoff : 43250 ≤ n := by omega
                                  have hnfin : n - 43250 < 50 := by omega
                                  simpa [Nat.sub_add_cancel hoff] using m0_w15 ⟨n - 43250, hnfin⟩
                                ·
                                  by_cases h16 : n < 43350
                                  · have hoff : 43300 ≤ n := by omega
                                    have hnfin : n - 43300 < 50 := by omega
                                    simpa [Nat.sub_add_cancel hoff] using m0_w16 ⟨n - 43300, hnfin⟩
                                  ·
                                    by_cases h17 : n < 43400
                                    · have hoff : 43350 ≤ n := by omega
                                      have hnfin : n - 43350 < 50 := by omega
                                      simpa [Nat.sub_add_cancel hoff] using m0_w17 ⟨n - 43350, hnfin⟩
                                    ·
                                      by_cases h18 : n < 43450
                                      · have hoff : 43400 ≤ n := by omega
                                        have hnfin : n - 43400 < 50 := by omega
                                        simpa [Nat.sub_add_cancel hoff] using m0_w18 ⟨n - 43400, hnfin⟩
                                      ·
                                        by_cases h19 : n < 43500
                                        · have hoff : 43450 ≤ n := by omega
                                          have hnfin : n - 43450 < 50 := by omega
                                          simpa [Nat.sub_add_cancel hoff] using m0_w19 ⟨n - 43450, hnfin⟩
                                        ·
                                          by_cases h20 : n < 43550
                                          · have hoff : 43500 ≤ n := by omega
                                            have hnfin : n - 43500 < 50 := by omega
                                            simpa [Nat.sub_add_cancel hoff] using m0_w20 ⟨n - 43500, hnfin⟩
                                          ·
                                            by_cases h21 : n < 43600
                                            · have hoff : 43550 ≤ n := by omega
                                              have hnfin : n - 43550 < 50 := by omega
                                              simpa [Nat.sub_add_cancel hoff] using m0_w21 ⟨n - 43550, hnfin⟩
                                            ·
                                              by_cases h22 : n < 43650
                                              · have hoff : 43600 ≤ n := by omega
                                                have hnfin : n - 43600 < 50 := by omega
                                                simpa [Nat.sub_add_cancel hoff] using m0_w22 ⟨n - 43600, hnfin⟩
                                              ·
                                                by_cases h23 : n < 43700
                                                · have hoff : 43650 ≤ n := by omega
                                                  have hnfin : n - 43650 < 50 := by omega
                                                  simpa [Nat.sub_add_cancel hoff] using m0_w23 ⟨n - 43650, hnfin⟩
                                                ·
                                                  by_cases h24 : n < 43750
                                                  · have hoff : 43700 ≤ n := by omega
                                                    have hnfin : n - 43700 < 50 := by omega
                                                    simpa [Nat.sub_add_cancel hoff] using m0_w24 ⟨n - 43700, hnfin⟩
                                                  ·
                                                    by_cases h25 : n < 43800
                                                    · have hoff : 43750 ≤ n := by omega
                                                      have hnfin : n - 43750 < 50 := by omega
                                                      simpa [Nat.sub_add_cancel hoff] using m0_w25 ⟨n - 43750, hnfin⟩
                                                    ·
                                                      by_cases h26 : n < 43850
                                                      · have hoff : 43800 ≤ n := by omega
                                                        have hnfin : n - 43800 < 50 := by omega
                                                        simpa [Nat.sub_add_cancel hoff] using m0_w26 ⟨n - 43800, hnfin⟩
                                                      ·
                                                        by_cases h27 : n < 43900
                                                        · have hoff : 43850 ≤ n := by omega
                                                          have hnfin : n - 43850 < 50 := by omega
                                                          simpa [Nat.sub_add_cancel hoff] using m0_w27 ⟨n - 43850, hnfin⟩
                                                        ·
                                                          by_cases h28 : n < 43950
                                                          · have hoff : 43900 ≤ n := by omega
                                                            have hnfin : n - 43900 < 50 := by omega
                                                            simpa [Nat.sub_add_cancel hoff] using m0_w28 ⟨n - 43900, hnfin⟩
                                                          ·
                                                            by_cases h29 : n < 44000
                                                            · have hoff : 43950 ≤ n := by omega
                                                              have hnfin : n - 43950 < 50 := by omega
                                                              simpa [Nat.sub_add_cancel hoff] using m0_w29 ⟨n - 43950, hnfin⟩
                                                            ·
                                                              by_cases h30 : n < 44050
                                                              · have hoff : 44000 ≤ n := by omega
                                                                have hnfin : n - 44000 < 50 := by omega
                                                                simpa [Nat.sub_add_cancel hoff] using m0_w30 ⟨n - 44000, hnfin⟩
                                                              ·
                                                                by_cases h31 : n < 44100
                                                                · have hoff : 44050 ≤ n := by omega
                                                                  have hnfin : n - 44050 < 50 := by omega
                                                                  simpa [Nat.sub_add_cancel hoff] using m0_w31 ⟨n - 44050, hnfin⟩
                                                                ·
                                                                  by_cases h32 : n < 44150
                                                                  · have hoff : 44100 ≤ n := by omega
                                                                    have hnfin : n - 44100 < 50 := by omega
                                                                    simpa [Nat.sub_add_cancel hoff] using m0_w32 ⟨n - 44100, hnfin⟩
                                                                  ·
                                                                    by_cases h33 : n < 44200
                                                                    · have hoff : 44150 ≤ n := by omega
                                                                      have hnfin : n - 44150 < 50 := by omega
                                                                      simpa [Nat.sub_add_cancel hoff] using m0_w33 ⟨n - 44150, hnfin⟩
                                                                    ·
                                                                      by_cases h34 : n < 44250
                                                                      · have hoff : 44200 ≤ n := by omega
                                                                        have hnfin : n - 44200 < 50 := by omega
                                                                        simpa [Nat.sub_add_cancel hoff] using m0_w34 ⟨n - 44200, hnfin⟩
                                                                      ·
                                                                        by_cases h35 : n < 44300
                                                                        · have hoff : 44250 ≤ n := by omega
                                                                          have hnfin : n - 44250 < 50 := by omega
                                                                          simpa [Nat.sub_add_cancel hoff] using m0_w35 ⟨n - 44250, hnfin⟩
                                                                        ·
                                                                          by_cases h36 : n < 44350
                                                                          · have hoff : 44300 ≤ n := by omega
                                                                            have hnfin : n - 44300 < 50 := by omega
                                                                            simpa [Nat.sub_add_cancel hoff] using m0_w36 ⟨n - 44300, hnfin⟩
                                                                          ·
                                                                            by_cases h37 : n < 44400
                                                                            · have hoff : 44350 ≤ n := by omega
                                                                              have hnfin : n - 44350 < 50 := by omega
                                                                              simpa [Nat.sub_add_cancel hoff] using m0_w37 ⟨n - 44350, hnfin⟩
                                                                            ·
                                                                              by_cases h38 : n < 44450
                                                                              · have hoff : 44400 ≤ n := by omega
                                                                                have hnfin : n - 44400 < 50 := by omega
                                                                                simpa [Nat.sub_add_cancel hoff] using m0_w38 ⟨n - 44400, hnfin⟩
                                                                              ·
                                                                                by_cases h39 : n < 44500
                                                                                · have hoff : 44450 ≤ n := by omega
                                                                                  have hnfin : n - 44450 < 50 := by omega
                                                                                  simpa [Nat.sub_add_cancel hoff] using m0_w39 ⟨n - 44450, hnfin⟩
                                                                                ·
                                                                                  by_cases h40 : n < 44550
                                                                                  · have hoff : 44500 ≤ n := by omega
                                                                                    have hnfin : n - 44500 < 50 := by omega
                                                                                    simpa [Nat.sub_add_cancel hoff] using m0_w40 ⟨n - 44500, hnfin⟩
                                                                                  ·
                                                                                    by_cases h41 : n < 44600
                                                                                    · have hoff : 44550 ≤ n := by omega
                                                                                      have hnfin : n - 44550 < 50 := by omega
                                                                                      simpa [Nat.sub_add_cancel hoff] using m0_w41 ⟨n - 44550, hnfin⟩
                                                                                    ·
                                                                                      by_cases h42 : n < 44650
                                                                                      · have hoff : 44600 ≤ n := by omega
                                                                                        have hnfin : n - 44600 < 50 := by omega
                                                                                        simpa [Nat.sub_add_cancel hoff] using m0_w42 ⟨n - 44600, hnfin⟩
                                                                                      ·
                                                                                        by_cases h43 : n < 44700
                                                                                        · have hoff : 44650 ≤ n := by omega
                                                                                          have hnfin : n - 44650 < 50 := by omega
                                                                                          simpa [Nat.sub_add_cancel hoff] using m0_w43 ⟨n - 44650, hnfin⟩
                                                                                        ·
                                                                                          by_cases h44 : n < 44750
                                                                                          · have hoff : 44700 ≤ n := by omega
                                                                                            have hnfin : n - 44700 < 50 := by omega
                                                                                            simpa [Nat.sub_add_cancel hoff] using m0_w44 ⟨n - 44700, hnfin⟩
                                                                                          ·
                                                                                            by_cases h45 : n < 44800
                                                                                            · have hoff : 44750 ≤ n := by omega
                                                                                              have hnfin : n - 44750 < 50 := by omega
                                                                                              simpa [Nat.sub_add_cancel hoff] using m0_w45 ⟨n - 44750, hnfin⟩
                                                                                            ·
                                                                                              by_cases h46 : n < 44850
                                                                                              · have hoff : 44800 ≤ n := by omega
                                                                                                have hnfin : n - 44800 < 50 := by omega
                                                                                                simpa [Nat.sub_add_cancel hoff] using m0_w46 ⟨n - 44800, hnfin⟩
                                                                                              ·
                                                                                                by_cases h47 : n < 44900
                                                                                                · have hoff : 44850 ≤ n := by omega
                                                                                                  have hnfin : n - 44850 < 50 := by omega
                                                                                                  simpa [Nat.sub_add_cancel hoff] using m0_w47 ⟨n - 44850, hnfin⟩
                                                                                                ·
                                                                                                  by_cases h48 : n < 44950
                                                                                                  · have hoff : 44900 ≤ n := by omega
                                                                                                    have hnfin : n - 44900 < 50 := by omega
                                                                                                    simpa [Nat.sub_add_cancel hoff] using m0_w48 ⟨n - 44900, hnfin⟩
                                                                                                  ·
                                                                                                    by_cases h49 : n < 45000
                                                                                                    · have hoff : 44950 ≤ n := by omega
                                                                                                      have hnfin : n - 44950 < 50 := by omega
                                                                                                      simpa [Nat.sub_add_cancel hoff] using m0_w49 ⟨n - 44950, hnfin⟩
                                                                                                    ·
                                                                                                      omega
theorem land1_range (n : ℕ) (hn0 : 42500 ≤ n) (hn1 : n < 45000) :
    (!Nat.blt (dimF (arg1 n)) (dimF n) ||
      Nat.beq (Nat.land (densSupG (arg1 n)) (densSupG n)) (densSupG (arg1 n))) = true := by
  by_cases h0 : n < 42550
  · have hoff : 42500 ≤ n := by omega
    have hnfin : n - 42500 < 50 := by omega
    simpa [Nat.sub_add_cancel hoff] using m1_w0 ⟨n - 42500, hnfin⟩
  ·
    by_cases h1 : n < 42600
    · have hoff : 42550 ≤ n := by omega
      have hnfin : n - 42550 < 50 := by omega
      simpa [Nat.sub_add_cancel hoff] using m1_w1 ⟨n - 42550, hnfin⟩
    ·
      by_cases h2 : n < 42650
      · have hoff : 42600 ≤ n := by omega
        have hnfin : n - 42600 < 50 := by omega
        simpa [Nat.sub_add_cancel hoff] using m1_w2 ⟨n - 42600, hnfin⟩
      ·
        by_cases h3 : n < 42700
        · have hoff : 42650 ≤ n := by omega
          have hnfin : n - 42650 < 50 := by omega
          simpa [Nat.sub_add_cancel hoff] using m1_w3 ⟨n - 42650, hnfin⟩
        ·
          by_cases h4 : n < 42750
          · have hoff : 42700 ≤ n := by omega
            have hnfin : n - 42700 < 50 := by omega
            simpa [Nat.sub_add_cancel hoff] using m1_w4 ⟨n - 42700, hnfin⟩
          ·
            by_cases h5 : n < 42800
            · have hoff : 42750 ≤ n := by omega
              have hnfin : n - 42750 < 50 := by omega
              simpa [Nat.sub_add_cancel hoff] using m1_w5 ⟨n - 42750, hnfin⟩
            ·
              by_cases h6 : n < 42850
              · have hoff : 42800 ≤ n := by omega
                have hnfin : n - 42800 < 50 := by omega
                simpa [Nat.sub_add_cancel hoff] using m1_w6 ⟨n - 42800, hnfin⟩
              ·
                by_cases h7 : n < 42900
                · have hoff : 42850 ≤ n := by omega
                  have hnfin : n - 42850 < 50 := by omega
                  simpa [Nat.sub_add_cancel hoff] using m1_w7 ⟨n - 42850, hnfin⟩
                ·
                  by_cases h8 : n < 42950
                  · have hoff : 42900 ≤ n := by omega
                    have hnfin : n - 42900 < 50 := by omega
                    simpa [Nat.sub_add_cancel hoff] using m1_w8 ⟨n - 42900, hnfin⟩
                  ·
                    by_cases h9 : n < 43000
                    · have hoff : 42950 ≤ n := by omega
                      have hnfin : n - 42950 < 50 := by omega
                      simpa [Nat.sub_add_cancel hoff] using m1_w9 ⟨n - 42950, hnfin⟩
                    ·
                      by_cases h10 : n < 43050
                      · have hoff : 43000 ≤ n := by omega
                        have hnfin : n - 43000 < 50 := by omega
                        simpa [Nat.sub_add_cancel hoff] using m1_w10 ⟨n - 43000, hnfin⟩
                      ·
                        by_cases h11 : n < 43100
                        · have hoff : 43050 ≤ n := by omega
                          have hnfin : n - 43050 < 50 := by omega
                          simpa [Nat.sub_add_cancel hoff] using m1_w11 ⟨n - 43050, hnfin⟩
                        ·
                          by_cases h12 : n < 43150
                          · have hoff : 43100 ≤ n := by omega
                            have hnfin : n - 43100 < 50 := by omega
                            simpa [Nat.sub_add_cancel hoff] using m1_w12 ⟨n - 43100, hnfin⟩
                          ·
                            by_cases h13 : n < 43200
                            · have hoff : 43150 ≤ n := by omega
                              have hnfin : n - 43150 < 50 := by omega
                              simpa [Nat.sub_add_cancel hoff] using m1_w13 ⟨n - 43150, hnfin⟩
                            ·
                              by_cases h14 : n < 43250
                              · have hoff : 43200 ≤ n := by omega
                                have hnfin : n - 43200 < 50 := by omega
                                simpa [Nat.sub_add_cancel hoff] using m1_w14 ⟨n - 43200, hnfin⟩
                              ·
                                by_cases h15 : n < 43300
                                · have hoff : 43250 ≤ n := by omega
                                  have hnfin : n - 43250 < 50 := by omega
                                  simpa [Nat.sub_add_cancel hoff] using m1_w15 ⟨n - 43250, hnfin⟩
                                ·
                                  by_cases h16 : n < 43350
                                  · have hoff : 43300 ≤ n := by omega
                                    have hnfin : n - 43300 < 50 := by omega
                                    simpa [Nat.sub_add_cancel hoff] using m1_w16 ⟨n - 43300, hnfin⟩
                                  ·
                                    by_cases h17 : n < 43400
                                    · have hoff : 43350 ≤ n := by omega
                                      have hnfin : n - 43350 < 50 := by omega
                                      simpa [Nat.sub_add_cancel hoff] using m1_w17 ⟨n - 43350, hnfin⟩
                                    ·
                                      by_cases h18 : n < 43450
                                      · have hoff : 43400 ≤ n := by omega
                                        have hnfin : n - 43400 < 50 := by omega
                                        simpa [Nat.sub_add_cancel hoff] using m1_w18 ⟨n - 43400, hnfin⟩
                                      ·
                                        by_cases h19 : n < 43500
                                        · have hoff : 43450 ≤ n := by omega
                                          have hnfin : n - 43450 < 50 := by omega
                                          simpa [Nat.sub_add_cancel hoff] using m1_w19 ⟨n - 43450, hnfin⟩
                                        ·
                                          by_cases h20 : n < 43550
                                          · have hoff : 43500 ≤ n := by omega
                                            have hnfin : n - 43500 < 50 := by omega
                                            simpa [Nat.sub_add_cancel hoff] using m1_w20 ⟨n - 43500, hnfin⟩
                                          ·
                                            by_cases h21 : n < 43600
                                            · have hoff : 43550 ≤ n := by omega
                                              have hnfin : n - 43550 < 50 := by omega
                                              simpa [Nat.sub_add_cancel hoff] using m1_w21 ⟨n - 43550, hnfin⟩
                                            ·
                                              by_cases h22 : n < 43650
                                              · have hoff : 43600 ≤ n := by omega
                                                have hnfin : n - 43600 < 50 := by omega
                                                simpa [Nat.sub_add_cancel hoff] using m1_w22 ⟨n - 43600, hnfin⟩
                                              ·
                                                by_cases h23 : n < 43700
                                                · have hoff : 43650 ≤ n := by omega
                                                  have hnfin : n - 43650 < 50 := by omega
                                                  simpa [Nat.sub_add_cancel hoff] using m1_w23 ⟨n - 43650, hnfin⟩
                                                ·
                                                  by_cases h24 : n < 43750
                                                  · have hoff : 43700 ≤ n := by omega
                                                    have hnfin : n - 43700 < 50 := by omega
                                                    simpa [Nat.sub_add_cancel hoff] using m1_w24 ⟨n - 43700, hnfin⟩
                                                  ·
                                                    by_cases h25 : n < 43800
                                                    · have hoff : 43750 ≤ n := by omega
                                                      have hnfin : n - 43750 < 50 := by omega
                                                      simpa [Nat.sub_add_cancel hoff] using m1_w25 ⟨n - 43750, hnfin⟩
                                                    ·
                                                      by_cases h26 : n < 43850
                                                      · have hoff : 43800 ≤ n := by omega
                                                        have hnfin : n - 43800 < 50 := by omega
                                                        simpa [Nat.sub_add_cancel hoff] using m1_w26 ⟨n - 43800, hnfin⟩
                                                      ·
                                                        by_cases h27 : n < 43900
                                                        · have hoff : 43850 ≤ n := by omega
                                                          have hnfin : n - 43850 < 50 := by omega
                                                          simpa [Nat.sub_add_cancel hoff] using m1_w27 ⟨n - 43850, hnfin⟩
                                                        ·
                                                          by_cases h28 : n < 43950
                                                          · have hoff : 43900 ≤ n := by omega
                                                            have hnfin : n - 43900 < 50 := by omega
                                                            simpa [Nat.sub_add_cancel hoff] using m1_w28 ⟨n - 43900, hnfin⟩
                                                          ·
                                                            by_cases h29 : n < 44000
                                                            · have hoff : 43950 ≤ n := by omega
                                                              have hnfin : n - 43950 < 50 := by omega
                                                              simpa [Nat.sub_add_cancel hoff] using m1_w29 ⟨n - 43950, hnfin⟩
                                                            ·
                                                              by_cases h30 : n < 44050
                                                              · have hoff : 44000 ≤ n := by omega
                                                                have hnfin : n - 44000 < 50 := by omega
                                                                simpa [Nat.sub_add_cancel hoff] using m1_w30 ⟨n - 44000, hnfin⟩
                                                              ·
                                                                by_cases h31 : n < 44100
                                                                · have hoff : 44050 ≤ n := by omega
                                                                  have hnfin : n - 44050 < 50 := by omega
                                                                  simpa [Nat.sub_add_cancel hoff] using m1_w31 ⟨n - 44050, hnfin⟩
                                                                ·
                                                                  by_cases h32 : n < 44150
                                                                  · have hoff : 44100 ≤ n := by omega
                                                                    have hnfin : n - 44100 < 50 := by omega
                                                                    simpa [Nat.sub_add_cancel hoff] using m1_w32 ⟨n - 44100, hnfin⟩
                                                                  ·
                                                                    by_cases h33 : n < 44200
                                                                    · have hoff : 44150 ≤ n := by omega
                                                                      have hnfin : n - 44150 < 50 := by omega
                                                                      simpa [Nat.sub_add_cancel hoff] using m1_w33 ⟨n - 44150, hnfin⟩
                                                                    ·
                                                                      by_cases h34 : n < 44250
                                                                      · have hoff : 44200 ≤ n := by omega
                                                                        have hnfin : n - 44200 < 50 := by omega
                                                                        simpa [Nat.sub_add_cancel hoff] using m1_w34 ⟨n - 44200, hnfin⟩
                                                                      ·
                                                                        by_cases h35 : n < 44300
                                                                        · have hoff : 44250 ≤ n := by omega
                                                                          have hnfin : n - 44250 < 50 := by omega
                                                                          simpa [Nat.sub_add_cancel hoff] using m1_w35 ⟨n - 44250, hnfin⟩
                                                                        ·
                                                                          by_cases h36 : n < 44350
                                                                          · have hoff : 44300 ≤ n := by omega
                                                                            have hnfin : n - 44300 < 50 := by omega
                                                                            simpa [Nat.sub_add_cancel hoff] using m1_w36 ⟨n - 44300, hnfin⟩
                                                                          ·
                                                                            by_cases h37 : n < 44400
                                                                            · have hoff : 44350 ≤ n := by omega
                                                                              have hnfin : n - 44350 < 50 := by omega
                                                                              simpa [Nat.sub_add_cancel hoff] using m1_w37 ⟨n - 44350, hnfin⟩
                                                                            ·
                                                                              by_cases h38 : n < 44450
                                                                              · have hoff : 44400 ≤ n := by omega
                                                                                have hnfin : n - 44400 < 50 := by omega
                                                                                simpa [Nat.sub_add_cancel hoff] using m1_w38 ⟨n - 44400, hnfin⟩
                                                                              ·
                                                                                by_cases h39 : n < 44500
                                                                                · have hoff : 44450 ≤ n := by omega
                                                                                  have hnfin : n - 44450 < 50 := by omega
                                                                                  simpa [Nat.sub_add_cancel hoff] using m1_w39 ⟨n - 44450, hnfin⟩
                                                                                ·
                                                                                  by_cases h40 : n < 44550
                                                                                  · have hoff : 44500 ≤ n := by omega
                                                                                    have hnfin : n - 44500 < 50 := by omega
                                                                                    simpa [Nat.sub_add_cancel hoff] using m1_w40 ⟨n - 44500, hnfin⟩
                                                                                  ·
                                                                                    by_cases h41 : n < 44600
                                                                                    · have hoff : 44550 ≤ n := by omega
                                                                                      have hnfin : n - 44550 < 50 := by omega
                                                                                      simpa [Nat.sub_add_cancel hoff] using m1_w41 ⟨n - 44550, hnfin⟩
                                                                                    ·
                                                                                      by_cases h42 : n < 44650
                                                                                      · have hoff : 44600 ≤ n := by omega
                                                                                        have hnfin : n - 44600 < 50 := by omega
                                                                                        simpa [Nat.sub_add_cancel hoff] using m1_w42 ⟨n - 44600, hnfin⟩
                                                                                      ·
                                                                                        by_cases h43 : n < 44700
                                                                                        · have hoff : 44650 ≤ n := by omega
                                                                                          have hnfin : n - 44650 < 50 := by omega
                                                                                          simpa [Nat.sub_add_cancel hoff] using m1_w43 ⟨n - 44650, hnfin⟩
                                                                                        ·
                                                                                          by_cases h44 : n < 44750
                                                                                          · have hoff : 44700 ≤ n := by omega
                                                                                            have hnfin : n - 44700 < 50 := by omega
                                                                                            simpa [Nat.sub_add_cancel hoff] using m1_w44 ⟨n - 44700, hnfin⟩
                                                                                          ·
                                                                                            by_cases h45 : n < 44800
                                                                                            · have hoff : 44750 ≤ n := by omega
                                                                                              have hnfin : n - 44750 < 50 := by omega
                                                                                              simpa [Nat.sub_add_cancel hoff] using m1_w45 ⟨n - 44750, hnfin⟩
                                                                                            ·
                                                                                              by_cases h46 : n < 44850
                                                                                              · have hoff : 44800 ≤ n := by omega
                                                                                                have hnfin : n - 44800 < 50 := by omega
                                                                                                simpa [Nat.sub_add_cancel hoff] using m1_w46 ⟨n - 44800, hnfin⟩
                                                                                              ·
                                                                                                by_cases h47 : n < 44900
                                                                                                · have hoff : 44850 ≤ n := by omega
                                                                                                  have hnfin : n - 44850 < 50 := by omega
                                                                                                  simpa [Nat.sub_add_cancel hoff] using m1_w47 ⟨n - 44850, hnfin⟩
                                                                                                ·
                                                                                                  by_cases h48 : n < 44950
                                                                                                  · have hoff : 44900 ≤ n := by omega
                                                                                                    have hnfin : n - 44900 < 50 := by omega
                                                                                                    simpa [Nat.sub_add_cancel hoff] using m1_w48 ⟨n - 44900, hnfin⟩
                                                                                                  ·
                                                                                                    by_cases h49 : n < 45000
                                                                                                    · have hoff : 44950 ≤ n := by omega
                                                                                                      have hnfin : n - 44950 < 50 := by omega
                                                                                                      simpa [Nat.sub_add_cancel hoff] using m1_w49 ⟨n - 44950, hnfin⟩
                                                                                                    ·
                                                                                                      omega
end IntMul.Kappa.R8.Bit.Oppbank.LandMonoFixA17


