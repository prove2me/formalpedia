-- Prove2me | Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankLandMonoFixA18
-- name    : IntMul_Kappa_R8_Data_BitOppbankLandMonoFixA18
-- status  : Definition
-- author  : @Ethan Cheung Wang
-- created : 2026-10-28T21:18:08.061346+00:00
-- url     : https://prove2.me/theorems/ef053453-94ed-4224-809b-662f7030b895
-- title:
--   Dim-gated densSup land mono FixA pack 18
-- statement:
--   # Dim-gated densSup land (PndFix), pack A18
--
--   Range consolidators for $n\in[45000,47500)$.
-- source:
--   R8 BitOppbank PndFix

-- LandMonoFixA18: PUBLIC dim-gated land + range consolidators (PndFix)
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
namespace IntMul.Kappa.R8.Bit.Oppbank.LandMonoFixA18
def arg0 (n : ℕ) : ℕ := Nat.land (argF n) 65535
def arg1 (n : ℕ) : ℕ := Nat.shiftRight (argF n) 16
theorem m0_w0 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 45000))) (dimF (n.val + 45000)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 45000))) (densSupG (n.val + 45000))) (densSupG (arg0 (n.val + 45000)))) = true := by decide
theorem m1_w0 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 45000))) (dimF (n.val + 45000)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 45000))) (densSupG (n.val + 45000))) (densSupG (arg1 (n.val + 45000)))) = true := by decide
theorem m0_w1 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 45050))) (dimF (n.val + 45050)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 45050))) (densSupG (n.val + 45050))) (densSupG (arg0 (n.val + 45050)))) = true := by decide
theorem m1_w1 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 45050))) (dimF (n.val + 45050)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 45050))) (densSupG (n.val + 45050))) (densSupG (arg1 (n.val + 45050)))) = true := by decide
theorem m0_w2 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 45100))) (dimF (n.val + 45100)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 45100))) (densSupG (n.val + 45100))) (densSupG (arg0 (n.val + 45100)))) = true := by decide
theorem m1_w2 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 45100))) (dimF (n.val + 45100)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 45100))) (densSupG (n.val + 45100))) (densSupG (arg1 (n.val + 45100)))) = true := by decide
theorem m0_w3 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 45150))) (dimF (n.val + 45150)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 45150))) (densSupG (n.val + 45150))) (densSupG (arg0 (n.val + 45150)))) = true := by decide
theorem m1_w3 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 45150))) (dimF (n.val + 45150)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 45150))) (densSupG (n.val + 45150))) (densSupG (arg1 (n.val + 45150)))) = true := by decide
theorem m0_w4 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 45200))) (dimF (n.val + 45200)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 45200))) (densSupG (n.val + 45200))) (densSupG (arg0 (n.val + 45200)))) = true := by decide
theorem m1_w4 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 45200))) (dimF (n.val + 45200)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 45200))) (densSupG (n.val + 45200))) (densSupG (arg1 (n.val + 45200)))) = true := by decide
theorem m0_w5 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 45250))) (dimF (n.val + 45250)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 45250))) (densSupG (n.val + 45250))) (densSupG (arg0 (n.val + 45250)))) = true := by decide
theorem m1_w5 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 45250))) (dimF (n.val + 45250)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 45250))) (densSupG (n.val + 45250))) (densSupG (arg1 (n.val + 45250)))) = true := by decide
theorem m0_w6 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 45300))) (dimF (n.val + 45300)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 45300))) (densSupG (n.val + 45300))) (densSupG (arg0 (n.val + 45300)))) = true := by decide
theorem m1_w6 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 45300))) (dimF (n.val + 45300)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 45300))) (densSupG (n.val + 45300))) (densSupG (arg1 (n.val + 45300)))) = true := by decide
theorem m0_w7 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 45350))) (dimF (n.val + 45350)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 45350))) (densSupG (n.val + 45350))) (densSupG (arg0 (n.val + 45350)))) = true := by decide
theorem m1_w7 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 45350))) (dimF (n.val + 45350)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 45350))) (densSupG (n.val + 45350))) (densSupG (arg1 (n.val + 45350)))) = true := by decide
theorem m0_w8 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 45400))) (dimF (n.val + 45400)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 45400))) (densSupG (n.val + 45400))) (densSupG (arg0 (n.val + 45400)))) = true := by decide
theorem m1_w8 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 45400))) (dimF (n.val + 45400)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 45400))) (densSupG (n.val + 45400))) (densSupG (arg1 (n.val + 45400)))) = true := by decide
theorem m0_w9 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 45450))) (dimF (n.val + 45450)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 45450))) (densSupG (n.val + 45450))) (densSupG (arg0 (n.val + 45450)))) = true := by decide
theorem m1_w9 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 45450))) (dimF (n.val + 45450)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 45450))) (densSupG (n.val + 45450))) (densSupG (arg1 (n.val + 45450)))) = true := by decide
theorem m0_w10 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 45500))) (dimF (n.val + 45500)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 45500))) (densSupG (n.val + 45500))) (densSupG (arg0 (n.val + 45500)))) = true := by decide
theorem m1_w10 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 45500))) (dimF (n.val + 45500)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 45500))) (densSupG (n.val + 45500))) (densSupG (arg1 (n.val + 45500)))) = true := by decide
theorem m0_w11 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 45550))) (dimF (n.val + 45550)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 45550))) (densSupG (n.val + 45550))) (densSupG (arg0 (n.val + 45550)))) = true := by decide
theorem m1_w11 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 45550))) (dimF (n.val + 45550)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 45550))) (densSupG (n.val + 45550))) (densSupG (arg1 (n.val + 45550)))) = true := by decide
theorem m0_w12 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 45600))) (dimF (n.val + 45600)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 45600))) (densSupG (n.val + 45600))) (densSupG (arg0 (n.val + 45600)))) = true := by decide
theorem m1_w12 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 45600))) (dimF (n.val + 45600)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 45600))) (densSupG (n.val + 45600))) (densSupG (arg1 (n.val + 45600)))) = true := by decide
theorem m0_w13 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 45650))) (dimF (n.val + 45650)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 45650))) (densSupG (n.val + 45650))) (densSupG (arg0 (n.val + 45650)))) = true := by decide
theorem m1_w13 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 45650))) (dimF (n.val + 45650)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 45650))) (densSupG (n.val + 45650))) (densSupG (arg1 (n.val + 45650)))) = true := by decide
theorem m0_w14 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 45700))) (dimF (n.val + 45700)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 45700))) (densSupG (n.val + 45700))) (densSupG (arg0 (n.val + 45700)))) = true := by decide
theorem m1_w14 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 45700))) (dimF (n.val + 45700)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 45700))) (densSupG (n.val + 45700))) (densSupG (arg1 (n.val + 45700)))) = true := by decide
theorem m0_w15 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 45750))) (dimF (n.val + 45750)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 45750))) (densSupG (n.val + 45750))) (densSupG (arg0 (n.val + 45750)))) = true := by decide
theorem m1_w15 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 45750))) (dimF (n.val + 45750)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 45750))) (densSupG (n.val + 45750))) (densSupG (arg1 (n.val + 45750)))) = true := by decide
theorem m0_w16 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 45800))) (dimF (n.val + 45800)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 45800))) (densSupG (n.val + 45800))) (densSupG (arg0 (n.val + 45800)))) = true := by decide
theorem m1_w16 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 45800))) (dimF (n.val + 45800)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 45800))) (densSupG (n.val + 45800))) (densSupG (arg1 (n.val + 45800)))) = true := by decide
theorem m0_w17 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 45850))) (dimF (n.val + 45850)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 45850))) (densSupG (n.val + 45850))) (densSupG (arg0 (n.val + 45850)))) = true := by decide
theorem m1_w17 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 45850))) (dimF (n.val + 45850)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 45850))) (densSupG (n.val + 45850))) (densSupG (arg1 (n.val + 45850)))) = true := by decide
theorem m0_w18 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 45900))) (dimF (n.val + 45900)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 45900))) (densSupG (n.val + 45900))) (densSupG (arg0 (n.val + 45900)))) = true := by decide
theorem m1_w18 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 45900))) (dimF (n.val + 45900)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 45900))) (densSupG (n.val + 45900))) (densSupG (arg1 (n.val + 45900)))) = true := by decide
theorem m0_w19 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 45950))) (dimF (n.val + 45950)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 45950))) (densSupG (n.val + 45950))) (densSupG (arg0 (n.val + 45950)))) = true := by decide
theorem m1_w19 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 45950))) (dimF (n.val + 45950)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 45950))) (densSupG (n.val + 45950))) (densSupG (arg1 (n.val + 45950)))) = true := by decide
theorem m0_w20 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 46000))) (dimF (n.val + 46000)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 46000))) (densSupG (n.val + 46000))) (densSupG (arg0 (n.val + 46000)))) = true := by decide
theorem m1_w20 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 46000))) (dimF (n.val + 46000)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 46000))) (densSupG (n.val + 46000))) (densSupG (arg1 (n.val + 46000)))) = true := by decide
theorem m0_w21 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 46050))) (dimF (n.val + 46050)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 46050))) (densSupG (n.val + 46050))) (densSupG (arg0 (n.val + 46050)))) = true := by decide
theorem m1_w21 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 46050))) (dimF (n.val + 46050)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 46050))) (densSupG (n.val + 46050))) (densSupG (arg1 (n.val + 46050)))) = true := by decide
theorem m0_w22 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 46100))) (dimF (n.val + 46100)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 46100))) (densSupG (n.val + 46100))) (densSupG (arg0 (n.val + 46100)))) = true := by decide
theorem m1_w22 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 46100))) (dimF (n.val + 46100)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 46100))) (densSupG (n.val + 46100))) (densSupG (arg1 (n.val + 46100)))) = true := by decide
theorem m0_w23 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 46150))) (dimF (n.val + 46150)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 46150))) (densSupG (n.val + 46150))) (densSupG (arg0 (n.val + 46150)))) = true := by decide
theorem m1_w23 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 46150))) (dimF (n.val + 46150)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 46150))) (densSupG (n.val + 46150))) (densSupG (arg1 (n.val + 46150)))) = true := by decide
theorem m0_w24 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 46200))) (dimF (n.val + 46200)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 46200))) (densSupG (n.val + 46200))) (densSupG (arg0 (n.val + 46200)))) = true := by decide
theorem m1_w24 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 46200))) (dimF (n.val + 46200)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 46200))) (densSupG (n.val + 46200))) (densSupG (arg1 (n.val + 46200)))) = true := by decide
theorem m0_w25 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 46250))) (dimF (n.val + 46250)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 46250))) (densSupG (n.val + 46250))) (densSupG (arg0 (n.val + 46250)))) = true := by decide
theorem m1_w25 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 46250))) (dimF (n.val + 46250)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 46250))) (densSupG (n.val + 46250))) (densSupG (arg1 (n.val + 46250)))) = true := by decide
theorem m0_w26 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 46300))) (dimF (n.val + 46300)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 46300))) (densSupG (n.val + 46300))) (densSupG (arg0 (n.val + 46300)))) = true := by decide
theorem m1_w26 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 46300))) (dimF (n.val + 46300)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 46300))) (densSupG (n.val + 46300))) (densSupG (arg1 (n.val + 46300)))) = true := by decide
theorem m0_w27 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 46350))) (dimF (n.val + 46350)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 46350))) (densSupG (n.val + 46350))) (densSupG (arg0 (n.val + 46350)))) = true := by decide
theorem m1_w27 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 46350))) (dimF (n.val + 46350)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 46350))) (densSupG (n.val + 46350))) (densSupG (arg1 (n.val + 46350)))) = true := by decide
theorem m0_w28 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 46400))) (dimF (n.val + 46400)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 46400))) (densSupG (n.val + 46400))) (densSupG (arg0 (n.val + 46400)))) = true := by decide
theorem m1_w28 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 46400))) (dimF (n.val + 46400)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 46400))) (densSupG (n.val + 46400))) (densSupG (arg1 (n.val + 46400)))) = true := by decide
theorem m0_w29 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 46450))) (dimF (n.val + 46450)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 46450))) (densSupG (n.val + 46450))) (densSupG (arg0 (n.val + 46450)))) = true := by decide
theorem m1_w29 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 46450))) (dimF (n.val + 46450)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 46450))) (densSupG (n.val + 46450))) (densSupG (arg1 (n.val + 46450)))) = true := by decide
theorem m0_w30 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 46500))) (dimF (n.val + 46500)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 46500))) (densSupG (n.val + 46500))) (densSupG (arg0 (n.val + 46500)))) = true := by decide
theorem m1_w30 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 46500))) (dimF (n.val + 46500)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 46500))) (densSupG (n.val + 46500))) (densSupG (arg1 (n.val + 46500)))) = true := by decide
theorem m0_w31 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 46550))) (dimF (n.val + 46550)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 46550))) (densSupG (n.val + 46550))) (densSupG (arg0 (n.val + 46550)))) = true := by decide
theorem m1_w31 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 46550))) (dimF (n.val + 46550)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 46550))) (densSupG (n.val + 46550))) (densSupG (arg1 (n.val + 46550)))) = true := by decide
theorem m0_w32 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 46600))) (dimF (n.val + 46600)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 46600))) (densSupG (n.val + 46600))) (densSupG (arg0 (n.val + 46600)))) = true := by decide
theorem m1_w32 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 46600))) (dimF (n.val + 46600)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 46600))) (densSupG (n.val + 46600))) (densSupG (arg1 (n.val + 46600)))) = true := by decide
theorem m0_w33 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 46650))) (dimF (n.val + 46650)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 46650))) (densSupG (n.val + 46650))) (densSupG (arg0 (n.val + 46650)))) = true := by decide
theorem m1_w33 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 46650))) (dimF (n.val + 46650)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 46650))) (densSupG (n.val + 46650))) (densSupG (arg1 (n.val + 46650)))) = true := by decide
theorem m0_w34 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 46700))) (dimF (n.val + 46700)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 46700))) (densSupG (n.val + 46700))) (densSupG (arg0 (n.val + 46700)))) = true := by decide
theorem m1_w34 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 46700))) (dimF (n.val + 46700)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 46700))) (densSupG (n.val + 46700))) (densSupG (arg1 (n.val + 46700)))) = true := by decide
theorem m0_w35 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 46750))) (dimF (n.val + 46750)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 46750))) (densSupG (n.val + 46750))) (densSupG (arg0 (n.val + 46750)))) = true := by decide
theorem m1_w35 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 46750))) (dimF (n.val + 46750)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 46750))) (densSupG (n.val + 46750))) (densSupG (arg1 (n.val + 46750)))) = true := by decide
theorem m0_w36 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 46800))) (dimF (n.val + 46800)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 46800))) (densSupG (n.val + 46800))) (densSupG (arg0 (n.val + 46800)))) = true := by decide
theorem m1_w36 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 46800))) (dimF (n.val + 46800)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 46800))) (densSupG (n.val + 46800))) (densSupG (arg1 (n.val + 46800)))) = true := by decide
theorem m0_w37 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 46850))) (dimF (n.val + 46850)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 46850))) (densSupG (n.val + 46850))) (densSupG (arg0 (n.val + 46850)))) = true := by decide
theorem m1_w37 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 46850))) (dimF (n.val + 46850)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 46850))) (densSupG (n.val + 46850))) (densSupG (arg1 (n.val + 46850)))) = true := by decide
theorem m0_w38 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 46900))) (dimF (n.val + 46900)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 46900))) (densSupG (n.val + 46900))) (densSupG (arg0 (n.val + 46900)))) = true := by decide
theorem m1_w38 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 46900))) (dimF (n.val + 46900)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 46900))) (densSupG (n.val + 46900))) (densSupG (arg1 (n.val + 46900)))) = true := by decide
theorem m0_w39 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 46950))) (dimF (n.val + 46950)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 46950))) (densSupG (n.val + 46950))) (densSupG (arg0 (n.val + 46950)))) = true := by decide
theorem m1_w39 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 46950))) (dimF (n.val + 46950)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 46950))) (densSupG (n.val + 46950))) (densSupG (arg1 (n.val + 46950)))) = true := by decide
theorem m0_w40 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 47000))) (dimF (n.val + 47000)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 47000))) (densSupG (n.val + 47000))) (densSupG (arg0 (n.val + 47000)))) = true := by decide
theorem m1_w40 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 47000))) (dimF (n.val + 47000)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 47000))) (densSupG (n.val + 47000))) (densSupG (arg1 (n.val + 47000)))) = true := by decide
theorem m0_w41 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 47050))) (dimF (n.val + 47050)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 47050))) (densSupG (n.val + 47050))) (densSupG (arg0 (n.val + 47050)))) = true := by decide
theorem m1_w41 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 47050))) (dimF (n.val + 47050)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 47050))) (densSupG (n.val + 47050))) (densSupG (arg1 (n.val + 47050)))) = true := by decide
theorem m0_w42 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 47100))) (dimF (n.val + 47100)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 47100))) (densSupG (n.val + 47100))) (densSupG (arg0 (n.val + 47100)))) = true := by decide
theorem m1_w42 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 47100))) (dimF (n.val + 47100)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 47100))) (densSupG (n.val + 47100))) (densSupG (arg1 (n.val + 47100)))) = true := by decide
theorem m0_w43 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 47150))) (dimF (n.val + 47150)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 47150))) (densSupG (n.val + 47150))) (densSupG (arg0 (n.val + 47150)))) = true := by decide
theorem m1_w43 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 47150))) (dimF (n.val + 47150)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 47150))) (densSupG (n.val + 47150))) (densSupG (arg1 (n.val + 47150)))) = true := by decide
theorem m0_w44 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 47200))) (dimF (n.val + 47200)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 47200))) (densSupG (n.val + 47200))) (densSupG (arg0 (n.val + 47200)))) = true := by decide
theorem m1_w44 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 47200))) (dimF (n.val + 47200)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 47200))) (densSupG (n.val + 47200))) (densSupG (arg1 (n.val + 47200)))) = true := by decide
theorem m0_w45 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 47250))) (dimF (n.val + 47250)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 47250))) (densSupG (n.val + 47250))) (densSupG (arg0 (n.val + 47250)))) = true := by decide
theorem m1_w45 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 47250))) (dimF (n.val + 47250)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 47250))) (densSupG (n.val + 47250))) (densSupG (arg1 (n.val + 47250)))) = true := by decide
theorem m0_w46 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 47300))) (dimF (n.val + 47300)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 47300))) (densSupG (n.val + 47300))) (densSupG (arg0 (n.val + 47300)))) = true := by decide
theorem m1_w46 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 47300))) (dimF (n.val + 47300)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 47300))) (densSupG (n.val + 47300))) (densSupG (arg1 (n.val + 47300)))) = true := by decide
theorem m0_w47 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 47350))) (dimF (n.val + 47350)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 47350))) (densSupG (n.val + 47350))) (densSupG (arg0 (n.val + 47350)))) = true := by decide
theorem m1_w47 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 47350))) (dimF (n.val + 47350)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 47350))) (densSupG (n.val + 47350))) (densSupG (arg1 (n.val + 47350)))) = true := by decide
theorem m0_w48 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 47400))) (dimF (n.val + 47400)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 47400))) (densSupG (n.val + 47400))) (densSupG (arg0 (n.val + 47400)))) = true := by decide
theorem m1_w48 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 47400))) (dimF (n.val + 47400)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 47400))) (densSupG (n.val + 47400))) (densSupG (arg1 (n.val + 47400)))) = true := by decide
theorem m0_w49 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 47450))) (dimF (n.val + 47450)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 47450))) (densSupG (n.val + 47450))) (densSupG (arg0 (n.val + 47450)))) = true := by decide
theorem m1_w49 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 47450))) (dimF (n.val + 47450)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 47450))) (densSupG (n.val + 47450))) (densSupG (arg1 (n.val + 47450)))) = true := by decide
theorem land0_range (n : ℕ) (hn0 : 45000 ≤ n) (hn1 : n < 47500) :
    (!Nat.blt (dimF (arg0 n)) (dimF n) ||
      Nat.beq (Nat.land (densSupG (arg0 n)) (densSupG n)) (densSupG (arg0 n))) = true := by
  by_cases h0 : n < 45050
  · have hoff : 45000 ≤ n := by omega
    have hnfin : n - 45000 < 50 := by omega
    simpa [Nat.sub_add_cancel hoff] using m0_w0 ⟨n - 45000, hnfin⟩
  ·
    by_cases h1 : n < 45100
    · have hoff : 45050 ≤ n := by omega
      have hnfin : n - 45050 < 50 := by omega
      simpa [Nat.sub_add_cancel hoff] using m0_w1 ⟨n - 45050, hnfin⟩
    ·
      by_cases h2 : n < 45150
      · have hoff : 45100 ≤ n := by omega
        have hnfin : n - 45100 < 50 := by omega
        simpa [Nat.sub_add_cancel hoff] using m0_w2 ⟨n - 45100, hnfin⟩
      ·
        by_cases h3 : n < 45200
        · have hoff : 45150 ≤ n := by omega
          have hnfin : n - 45150 < 50 := by omega
          simpa [Nat.sub_add_cancel hoff] using m0_w3 ⟨n - 45150, hnfin⟩
        ·
          by_cases h4 : n < 45250
          · have hoff : 45200 ≤ n := by omega
            have hnfin : n - 45200 < 50 := by omega
            simpa [Nat.sub_add_cancel hoff] using m0_w4 ⟨n - 45200, hnfin⟩
          ·
            by_cases h5 : n < 45300
            · have hoff : 45250 ≤ n := by omega
              have hnfin : n - 45250 < 50 := by omega
              simpa [Nat.sub_add_cancel hoff] using m0_w5 ⟨n - 45250, hnfin⟩
            ·
              by_cases h6 : n < 45350
              · have hoff : 45300 ≤ n := by omega
                have hnfin : n - 45300 < 50 := by omega
                simpa [Nat.sub_add_cancel hoff] using m0_w6 ⟨n - 45300, hnfin⟩
              ·
                by_cases h7 : n < 45400
                · have hoff : 45350 ≤ n := by omega
                  have hnfin : n - 45350 < 50 := by omega
                  simpa [Nat.sub_add_cancel hoff] using m0_w7 ⟨n - 45350, hnfin⟩
                ·
                  by_cases h8 : n < 45450
                  · have hoff : 45400 ≤ n := by omega
                    have hnfin : n - 45400 < 50 := by omega
                    simpa [Nat.sub_add_cancel hoff] using m0_w8 ⟨n - 45400, hnfin⟩
                  ·
                    by_cases h9 : n < 45500
                    · have hoff : 45450 ≤ n := by omega
                      have hnfin : n - 45450 < 50 := by omega
                      simpa [Nat.sub_add_cancel hoff] using m0_w9 ⟨n - 45450, hnfin⟩
                    ·
                      by_cases h10 : n < 45550
                      · have hoff : 45500 ≤ n := by omega
                        have hnfin : n - 45500 < 50 := by omega
                        simpa [Nat.sub_add_cancel hoff] using m0_w10 ⟨n - 45500, hnfin⟩
                      ·
                        by_cases h11 : n < 45600
                        · have hoff : 45550 ≤ n := by omega
                          have hnfin : n - 45550 < 50 := by omega
                          simpa [Nat.sub_add_cancel hoff] using m0_w11 ⟨n - 45550, hnfin⟩
                        ·
                          by_cases h12 : n < 45650
                          · have hoff : 45600 ≤ n := by omega
                            have hnfin : n - 45600 < 50 := by omega
                            simpa [Nat.sub_add_cancel hoff] using m0_w12 ⟨n - 45600, hnfin⟩
                          ·
                            by_cases h13 : n < 45700
                            · have hoff : 45650 ≤ n := by omega
                              have hnfin : n - 45650 < 50 := by omega
                              simpa [Nat.sub_add_cancel hoff] using m0_w13 ⟨n - 45650, hnfin⟩
                            ·
                              by_cases h14 : n < 45750
                              · have hoff : 45700 ≤ n := by omega
                                have hnfin : n - 45700 < 50 := by omega
                                simpa [Nat.sub_add_cancel hoff] using m0_w14 ⟨n - 45700, hnfin⟩
                              ·
                                by_cases h15 : n < 45800
                                · have hoff : 45750 ≤ n := by omega
                                  have hnfin : n - 45750 < 50 := by omega
                                  simpa [Nat.sub_add_cancel hoff] using m0_w15 ⟨n - 45750, hnfin⟩
                                ·
                                  by_cases h16 : n < 45850
                                  · have hoff : 45800 ≤ n := by omega
                                    have hnfin : n - 45800 < 50 := by omega
                                    simpa [Nat.sub_add_cancel hoff] using m0_w16 ⟨n - 45800, hnfin⟩
                                  ·
                                    by_cases h17 : n < 45900
                                    · have hoff : 45850 ≤ n := by omega
                                      have hnfin : n - 45850 < 50 := by omega
                                      simpa [Nat.sub_add_cancel hoff] using m0_w17 ⟨n - 45850, hnfin⟩
                                    ·
                                      by_cases h18 : n < 45950
                                      · have hoff : 45900 ≤ n := by omega
                                        have hnfin : n - 45900 < 50 := by omega
                                        simpa [Nat.sub_add_cancel hoff] using m0_w18 ⟨n - 45900, hnfin⟩
                                      ·
                                        by_cases h19 : n < 46000
                                        · have hoff : 45950 ≤ n := by omega
                                          have hnfin : n - 45950 < 50 := by omega
                                          simpa [Nat.sub_add_cancel hoff] using m0_w19 ⟨n - 45950, hnfin⟩
                                        ·
                                          by_cases h20 : n < 46050
                                          · have hoff : 46000 ≤ n := by omega
                                            have hnfin : n - 46000 < 50 := by omega
                                            simpa [Nat.sub_add_cancel hoff] using m0_w20 ⟨n - 46000, hnfin⟩
                                          ·
                                            by_cases h21 : n < 46100
                                            · have hoff : 46050 ≤ n := by omega
                                              have hnfin : n - 46050 < 50 := by omega
                                              simpa [Nat.sub_add_cancel hoff] using m0_w21 ⟨n - 46050, hnfin⟩
                                            ·
                                              by_cases h22 : n < 46150
                                              · have hoff : 46100 ≤ n := by omega
                                                have hnfin : n - 46100 < 50 := by omega
                                                simpa [Nat.sub_add_cancel hoff] using m0_w22 ⟨n - 46100, hnfin⟩
                                              ·
                                                by_cases h23 : n < 46200
                                                · have hoff : 46150 ≤ n := by omega
                                                  have hnfin : n - 46150 < 50 := by omega
                                                  simpa [Nat.sub_add_cancel hoff] using m0_w23 ⟨n - 46150, hnfin⟩
                                                ·
                                                  by_cases h24 : n < 46250
                                                  · have hoff : 46200 ≤ n := by omega
                                                    have hnfin : n - 46200 < 50 := by omega
                                                    simpa [Nat.sub_add_cancel hoff] using m0_w24 ⟨n - 46200, hnfin⟩
                                                  ·
                                                    by_cases h25 : n < 46300
                                                    · have hoff : 46250 ≤ n := by omega
                                                      have hnfin : n - 46250 < 50 := by omega
                                                      simpa [Nat.sub_add_cancel hoff] using m0_w25 ⟨n - 46250, hnfin⟩
                                                    ·
                                                      by_cases h26 : n < 46350
                                                      · have hoff : 46300 ≤ n := by omega
                                                        have hnfin : n - 46300 < 50 := by omega
                                                        simpa [Nat.sub_add_cancel hoff] using m0_w26 ⟨n - 46300, hnfin⟩
                                                      ·
                                                        by_cases h27 : n < 46400
                                                        · have hoff : 46350 ≤ n := by omega
                                                          have hnfin : n - 46350 < 50 := by omega
                                                          simpa [Nat.sub_add_cancel hoff] using m0_w27 ⟨n - 46350, hnfin⟩
                                                        ·
                                                          by_cases h28 : n < 46450
                                                          · have hoff : 46400 ≤ n := by omega
                                                            have hnfin : n - 46400 < 50 := by omega
                                                            simpa [Nat.sub_add_cancel hoff] using m0_w28 ⟨n - 46400, hnfin⟩
                                                          ·
                                                            by_cases h29 : n < 46500
                                                            · have hoff : 46450 ≤ n := by omega
                                                              have hnfin : n - 46450 < 50 := by omega
                                                              simpa [Nat.sub_add_cancel hoff] using m0_w29 ⟨n - 46450, hnfin⟩
                                                            ·
                                                              by_cases h30 : n < 46550
                                                              · have hoff : 46500 ≤ n := by omega
                                                                have hnfin : n - 46500 < 50 := by omega
                                                                simpa [Nat.sub_add_cancel hoff] using m0_w30 ⟨n - 46500, hnfin⟩
                                                              ·
                                                                by_cases h31 : n < 46600
                                                                · have hoff : 46550 ≤ n := by omega
                                                                  have hnfin : n - 46550 < 50 := by omega
                                                                  simpa [Nat.sub_add_cancel hoff] using m0_w31 ⟨n - 46550, hnfin⟩
                                                                ·
                                                                  by_cases h32 : n < 46650
                                                                  · have hoff : 46600 ≤ n := by omega
                                                                    have hnfin : n - 46600 < 50 := by omega
                                                                    simpa [Nat.sub_add_cancel hoff] using m0_w32 ⟨n - 46600, hnfin⟩
                                                                  ·
                                                                    by_cases h33 : n < 46700
                                                                    · have hoff : 46650 ≤ n := by omega
                                                                      have hnfin : n - 46650 < 50 := by omega
                                                                      simpa [Nat.sub_add_cancel hoff] using m0_w33 ⟨n - 46650, hnfin⟩
                                                                    ·
                                                                      by_cases h34 : n < 46750
                                                                      · have hoff : 46700 ≤ n := by omega
                                                                        have hnfin : n - 46700 < 50 := by omega
                                                                        simpa [Nat.sub_add_cancel hoff] using m0_w34 ⟨n - 46700, hnfin⟩
                                                                      ·
                                                                        by_cases h35 : n < 46800
                                                                        · have hoff : 46750 ≤ n := by omega
                                                                          have hnfin : n - 46750 < 50 := by omega
                                                                          simpa [Nat.sub_add_cancel hoff] using m0_w35 ⟨n - 46750, hnfin⟩
                                                                        ·
                                                                          by_cases h36 : n < 46850
                                                                          · have hoff : 46800 ≤ n := by omega
                                                                            have hnfin : n - 46800 < 50 := by omega
                                                                            simpa [Nat.sub_add_cancel hoff] using m0_w36 ⟨n - 46800, hnfin⟩
                                                                          ·
                                                                            by_cases h37 : n < 46900
                                                                            · have hoff : 46850 ≤ n := by omega
                                                                              have hnfin : n - 46850 < 50 := by omega
                                                                              simpa [Nat.sub_add_cancel hoff] using m0_w37 ⟨n - 46850, hnfin⟩
                                                                            ·
                                                                              by_cases h38 : n < 46950
                                                                              · have hoff : 46900 ≤ n := by omega
                                                                                have hnfin : n - 46900 < 50 := by omega
                                                                                simpa [Nat.sub_add_cancel hoff] using m0_w38 ⟨n - 46900, hnfin⟩
                                                                              ·
                                                                                by_cases h39 : n < 47000
                                                                                · have hoff : 46950 ≤ n := by omega
                                                                                  have hnfin : n - 46950 < 50 := by omega
                                                                                  simpa [Nat.sub_add_cancel hoff] using m0_w39 ⟨n - 46950, hnfin⟩
                                                                                ·
                                                                                  by_cases h40 : n < 47050
                                                                                  · have hoff : 47000 ≤ n := by omega
                                                                                    have hnfin : n - 47000 < 50 := by omega
                                                                                    simpa [Nat.sub_add_cancel hoff] using m0_w40 ⟨n - 47000, hnfin⟩
                                                                                  ·
                                                                                    by_cases h41 : n < 47100
                                                                                    · have hoff : 47050 ≤ n := by omega
                                                                                      have hnfin : n - 47050 < 50 := by omega
                                                                                      simpa [Nat.sub_add_cancel hoff] using m0_w41 ⟨n - 47050, hnfin⟩
                                                                                    ·
                                                                                      by_cases h42 : n < 47150
                                                                                      · have hoff : 47100 ≤ n := by omega
                                                                                        have hnfin : n - 47100 < 50 := by omega
                                                                                        simpa [Nat.sub_add_cancel hoff] using m0_w42 ⟨n - 47100, hnfin⟩
                                                                                      ·
                                                                                        by_cases h43 : n < 47200
                                                                                        · have hoff : 47150 ≤ n := by omega
                                                                                          have hnfin : n - 47150 < 50 := by omega
                                                                                          simpa [Nat.sub_add_cancel hoff] using m0_w43 ⟨n - 47150, hnfin⟩
                                                                                        ·
                                                                                          by_cases h44 : n < 47250
                                                                                          · have hoff : 47200 ≤ n := by omega
                                                                                            have hnfin : n - 47200 < 50 := by omega
                                                                                            simpa [Nat.sub_add_cancel hoff] using m0_w44 ⟨n - 47200, hnfin⟩
                                                                                          ·
                                                                                            by_cases h45 : n < 47300
                                                                                            · have hoff : 47250 ≤ n := by omega
                                                                                              have hnfin : n - 47250 < 50 := by omega
                                                                                              simpa [Nat.sub_add_cancel hoff] using m0_w45 ⟨n - 47250, hnfin⟩
                                                                                            ·
                                                                                              by_cases h46 : n < 47350
                                                                                              · have hoff : 47300 ≤ n := by omega
                                                                                                have hnfin : n - 47300 < 50 := by omega
                                                                                                simpa [Nat.sub_add_cancel hoff] using m0_w46 ⟨n - 47300, hnfin⟩
                                                                                              ·
                                                                                                by_cases h47 : n < 47400
                                                                                                · have hoff : 47350 ≤ n := by omega
                                                                                                  have hnfin : n - 47350 < 50 := by omega
                                                                                                  simpa [Nat.sub_add_cancel hoff] using m0_w47 ⟨n - 47350, hnfin⟩
                                                                                                ·
                                                                                                  by_cases h48 : n < 47450
                                                                                                  · have hoff : 47400 ≤ n := by omega
                                                                                                    have hnfin : n - 47400 < 50 := by omega
                                                                                                    simpa [Nat.sub_add_cancel hoff] using m0_w48 ⟨n - 47400, hnfin⟩
                                                                                                  ·
                                                                                                    by_cases h49 : n < 47500
                                                                                                    · have hoff : 47450 ≤ n := by omega
                                                                                                      have hnfin : n - 47450 < 50 := by omega
                                                                                                      simpa [Nat.sub_add_cancel hoff] using m0_w49 ⟨n - 47450, hnfin⟩
                                                                                                    ·
                                                                                                      omega
theorem land1_range (n : ℕ) (hn0 : 45000 ≤ n) (hn1 : n < 47500) :
    (!Nat.blt (dimF (arg1 n)) (dimF n) ||
      Nat.beq (Nat.land (densSupG (arg1 n)) (densSupG n)) (densSupG (arg1 n))) = true := by
  by_cases h0 : n < 45050
  · have hoff : 45000 ≤ n := by omega
    have hnfin : n - 45000 < 50 := by omega
    simpa [Nat.sub_add_cancel hoff] using m1_w0 ⟨n - 45000, hnfin⟩
  ·
    by_cases h1 : n < 45100
    · have hoff : 45050 ≤ n := by omega
      have hnfin : n - 45050 < 50 := by omega
      simpa [Nat.sub_add_cancel hoff] using m1_w1 ⟨n - 45050, hnfin⟩
    ·
      by_cases h2 : n < 45150
      · have hoff : 45100 ≤ n := by omega
        have hnfin : n - 45100 < 50 := by omega
        simpa [Nat.sub_add_cancel hoff] using m1_w2 ⟨n - 45100, hnfin⟩
      ·
        by_cases h3 : n < 45200
        · have hoff : 45150 ≤ n := by omega
          have hnfin : n - 45150 < 50 := by omega
          simpa [Nat.sub_add_cancel hoff] using m1_w3 ⟨n - 45150, hnfin⟩
        ·
          by_cases h4 : n < 45250
          · have hoff : 45200 ≤ n := by omega
            have hnfin : n - 45200 < 50 := by omega
            simpa [Nat.sub_add_cancel hoff] using m1_w4 ⟨n - 45200, hnfin⟩
          ·
            by_cases h5 : n < 45300
            · have hoff : 45250 ≤ n := by omega
              have hnfin : n - 45250 < 50 := by omega
              simpa [Nat.sub_add_cancel hoff] using m1_w5 ⟨n - 45250, hnfin⟩
            ·
              by_cases h6 : n < 45350
              · have hoff : 45300 ≤ n := by omega
                have hnfin : n - 45300 < 50 := by omega
                simpa [Nat.sub_add_cancel hoff] using m1_w6 ⟨n - 45300, hnfin⟩
              ·
                by_cases h7 : n < 45400
                · have hoff : 45350 ≤ n := by omega
                  have hnfin : n - 45350 < 50 := by omega
                  simpa [Nat.sub_add_cancel hoff] using m1_w7 ⟨n - 45350, hnfin⟩
                ·
                  by_cases h8 : n < 45450
                  · have hoff : 45400 ≤ n := by omega
                    have hnfin : n - 45400 < 50 := by omega
                    simpa [Nat.sub_add_cancel hoff] using m1_w8 ⟨n - 45400, hnfin⟩
                  ·
                    by_cases h9 : n < 45500
                    · have hoff : 45450 ≤ n := by omega
                      have hnfin : n - 45450 < 50 := by omega
                      simpa [Nat.sub_add_cancel hoff] using m1_w9 ⟨n - 45450, hnfin⟩
                    ·
                      by_cases h10 : n < 45550
                      · have hoff : 45500 ≤ n := by omega
                        have hnfin : n - 45500 < 50 := by omega
                        simpa [Nat.sub_add_cancel hoff] using m1_w10 ⟨n - 45500, hnfin⟩
                      ·
                        by_cases h11 : n < 45600
                        · have hoff : 45550 ≤ n := by omega
                          have hnfin : n - 45550 < 50 := by omega
                          simpa [Nat.sub_add_cancel hoff] using m1_w11 ⟨n - 45550, hnfin⟩
                        ·
                          by_cases h12 : n < 45650
                          · have hoff : 45600 ≤ n := by omega
                            have hnfin : n - 45600 < 50 := by omega
                            simpa [Nat.sub_add_cancel hoff] using m1_w12 ⟨n - 45600, hnfin⟩
                          ·
                            by_cases h13 : n < 45700
                            · have hoff : 45650 ≤ n := by omega
                              have hnfin : n - 45650 < 50 := by omega
                              simpa [Nat.sub_add_cancel hoff] using m1_w13 ⟨n - 45650, hnfin⟩
                            ·
                              by_cases h14 : n < 45750
                              · have hoff : 45700 ≤ n := by omega
                                have hnfin : n - 45700 < 50 := by omega
                                simpa [Nat.sub_add_cancel hoff] using m1_w14 ⟨n - 45700, hnfin⟩
                              ·
                                by_cases h15 : n < 45800
                                · have hoff : 45750 ≤ n := by omega
                                  have hnfin : n - 45750 < 50 := by omega
                                  simpa [Nat.sub_add_cancel hoff] using m1_w15 ⟨n - 45750, hnfin⟩
                                ·
                                  by_cases h16 : n < 45850
                                  · have hoff : 45800 ≤ n := by omega
                                    have hnfin : n - 45800 < 50 := by omega
                                    simpa [Nat.sub_add_cancel hoff] using m1_w16 ⟨n - 45800, hnfin⟩
                                  ·
                                    by_cases h17 : n < 45900
                                    · have hoff : 45850 ≤ n := by omega
                                      have hnfin : n - 45850 < 50 := by omega
                                      simpa [Nat.sub_add_cancel hoff] using m1_w17 ⟨n - 45850, hnfin⟩
                                    ·
                                      by_cases h18 : n < 45950
                                      · have hoff : 45900 ≤ n := by omega
                                        have hnfin : n - 45900 < 50 := by omega
                                        simpa [Nat.sub_add_cancel hoff] using m1_w18 ⟨n - 45900, hnfin⟩
                                      ·
                                        by_cases h19 : n < 46000
                                        · have hoff : 45950 ≤ n := by omega
                                          have hnfin : n - 45950 < 50 := by omega
                                          simpa [Nat.sub_add_cancel hoff] using m1_w19 ⟨n - 45950, hnfin⟩
                                        ·
                                          by_cases h20 : n < 46050
                                          · have hoff : 46000 ≤ n := by omega
                                            have hnfin : n - 46000 < 50 := by omega
                                            simpa [Nat.sub_add_cancel hoff] using m1_w20 ⟨n - 46000, hnfin⟩
                                          ·
                                            by_cases h21 : n < 46100
                                            · have hoff : 46050 ≤ n := by omega
                                              have hnfin : n - 46050 < 50 := by omega
                                              simpa [Nat.sub_add_cancel hoff] using m1_w21 ⟨n - 46050, hnfin⟩
                                            ·
                                              by_cases h22 : n < 46150
                                              · have hoff : 46100 ≤ n := by omega
                                                have hnfin : n - 46100 < 50 := by omega
                                                simpa [Nat.sub_add_cancel hoff] using m1_w22 ⟨n - 46100, hnfin⟩
                                              ·
                                                by_cases h23 : n < 46200
                                                · have hoff : 46150 ≤ n := by omega
                                                  have hnfin : n - 46150 < 50 := by omega
                                                  simpa [Nat.sub_add_cancel hoff] using m1_w23 ⟨n - 46150, hnfin⟩
                                                ·
                                                  by_cases h24 : n < 46250
                                                  · have hoff : 46200 ≤ n := by omega
                                                    have hnfin : n - 46200 < 50 := by omega
                                                    simpa [Nat.sub_add_cancel hoff] using m1_w24 ⟨n - 46200, hnfin⟩
                                                  ·
                                                    by_cases h25 : n < 46300
                                                    · have hoff : 46250 ≤ n := by omega
                                                      have hnfin : n - 46250 < 50 := by omega
                                                      simpa [Nat.sub_add_cancel hoff] using m1_w25 ⟨n - 46250, hnfin⟩
                                                    ·
                                                      by_cases h26 : n < 46350
                                                      · have hoff : 46300 ≤ n := by omega
                                                        have hnfin : n - 46300 < 50 := by omega
                                                        simpa [Nat.sub_add_cancel hoff] using m1_w26 ⟨n - 46300, hnfin⟩
                                                      ·
                                                        by_cases h27 : n < 46400
                                                        · have hoff : 46350 ≤ n := by omega
                                                          have hnfin : n - 46350 < 50 := by omega
                                                          simpa [Nat.sub_add_cancel hoff] using m1_w27 ⟨n - 46350, hnfin⟩
                                                        ·
                                                          by_cases h28 : n < 46450
                                                          · have hoff : 46400 ≤ n := by omega
                                                            have hnfin : n - 46400 < 50 := by omega
                                                            simpa [Nat.sub_add_cancel hoff] using m1_w28 ⟨n - 46400, hnfin⟩
                                                          ·
                                                            by_cases h29 : n < 46500
                                                            · have hoff : 46450 ≤ n := by omega
                                                              have hnfin : n - 46450 < 50 := by omega
                                                              simpa [Nat.sub_add_cancel hoff] using m1_w29 ⟨n - 46450, hnfin⟩
                                                            ·
                                                              by_cases h30 : n < 46550
                                                              · have hoff : 46500 ≤ n := by omega
                                                                have hnfin : n - 46500 < 50 := by omega
                                                                simpa [Nat.sub_add_cancel hoff] using m1_w30 ⟨n - 46500, hnfin⟩
                                                              ·
                                                                by_cases h31 : n < 46600
                                                                · have hoff : 46550 ≤ n := by omega
                                                                  have hnfin : n - 46550 < 50 := by omega
                                                                  simpa [Nat.sub_add_cancel hoff] using m1_w31 ⟨n - 46550, hnfin⟩
                                                                ·
                                                                  by_cases h32 : n < 46650
                                                                  · have hoff : 46600 ≤ n := by omega
                                                                    have hnfin : n - 46600 < 50 := by omega
                                                                    simpa [Nat.sub_add_cancel hoff] using m1_w32 ⟨n - 46600, hnfin⟩
                                                                  ·
                                                                    by_cases h33 : n < 46700
                                                                    · have hoff : 46650 ≤ n := by omega
                                                                      have hnfin : n - 46650 < 50 := by omega
                                                                      simpa [Nat.sub_add_cancel hoff] using m1_w33 ⟨n - 46650, hnfin⟩
                                                                    ·
                                                                      by_cases h34 : n < 46750
                                                                      · have hoff : 46700 ≤ n := by omega
                                                                        have hnfin : n - 46700 < 50 := by omega
                                                                        simpa [Nat.sub_add_cancel hoff] using m1_w34 ⟨n - 46700, hnfin⟩
                                                                      ·
                                                                        by_cases h35 : n < 46800
                                                                        · have hoff : 46750 ≤ n := by omega
                                                                          have hnfin : n - 46750 < 50 := by omega
                                                                          simpa [Nat.sub_add_cancel hoff] using m1_w35 ⟨n - 46750, hnfin⟩
                                                                        ·
                                                                          by_cases h36 : n < 46850
                                                                          · have hoff : 46800 ≤ n := by omega
                                                                            have hnfin : n - 46800 < 50 := by omega
                                                                            simpa [Nat.sub_add_cancel hoff] using m1_w36 ⟨n - 46800, hnfin⟩
                                                                          ·
                                                                            by_cases h37 : n < 46900
                                                                            · have hoff : 46850 ≤ n := by omega
                                                                              have hnfin : n - 46850 < 50 := by omega
                                                                              simpa [Nat.sub_add_cancel hoff] using m1_w37 ⟨n - 46850, hnfin⟩
                                                                            ·
                                                                              by_cases h38 : n < 46950
                                                                              · have hoff : 46900 ≤ n := by omega
                                                                                have hnfin : n - 46900 < 50 := by omega
                                                                                simpa [Nat.sub_add_cancel hoff] using m1_w38 ⟨n - 46900, hnfin⟩
                                                                              ·
                                                                                by_cases h39 : n < 47000
                                                                                · have hoff : 46950 ≤ n := by omega
                                                                                  have hnfin : n - 46950 < 50 := by omega
                                                                                  simpa [Nat.sub_add_cancel hoff] using m1_w39 ⟨n - 46950, hnfin⟩
                                                                                ·
                                                                                  by_cases h40 : n < 47050
                                                                                  · have hoff : 47000 ≤ n := by omega
                                                                                    have hnfin : n - 47000 < 50 := by omega
                                                                                    simpa [Nat.sub_add_cancel hoff] using m1_w40 ⟨n - 47000, hnfin⟩
                                                                                  ·
                                                                                    by_cases h41 : n < 47100
                                                                                    · have hoff : 47050 ≤ n := by omega
                                                                                      have hnfin : n - 47050 < 50 := by omega
                                                                                      simpa [Nat.sub_add_cancel hoff] using m1_w41 ⟨n - 47050, hnfin⟩
                                                                                    ·
                                                                                      by_cases h42 : n < 47150
                                                                                      · have hoff : 47100 ≤ n := by omega
                                                                                        have hnfin : n - 47100 < 50 := by omega
                                                                                        simpa [Nat.sub_add_cancel hoff] using m1_w42 ⟨n - 47100, hnfin⟩
                                                                                      ·
                                                                                        by_cases h43 : n < 47200
                                                                                        · have hoff : 47150 ≤ n := by omega
                                                                                          have hnfin : n - 47150 < 50 := by omega
                                                                                          simpa [Nat.sub_add_cancel hoff] using m1_w43 ⟨n - 47150, hnfin⟩
                                                                                        ·
                                                                                          by_cases h44 : n < 47250
                                                                                          · have hoff : 47200 ≤ n := by omega
                                                                                            have hnfin : n - 47200 < 50 := by omega
                                                                                            simpa [Nat.sub_add_cancel hoff] using m1_w44 ⟨n - 47200, hnfin⟩
                                                                                          ·
                                                                                            by_cases h45 : n < 47300
                                                                                            · have hoff : 47250 ≤ n := by omega
                                                                                              have hnfin : n - 47250 < 50 := by omega
                                                                                              simpa [Nat.sub_add_cancel hoff] using m1_w45 ⟨n - 47250, hnfin⟩
                                                                                            ·
                                                                                              by_cases h46 : n < 47350
                                                                                              · have hoff : 47300 ≤ n := by omega
                                                                                                have hnfin : n - 47300 < 50 := by omega
                                                                                                simpa [Nat.sub_add_cancel hoff] using m1_w46 ⟨n - 47300, hnfin⟩
                                                                                              ·
                                                                                                by_cases h47 : n < 47400
                                                                                                · have hoff : 47350 ≤ n := by omega
                                                                                                  have hnfin : n - 47350 < 50 := by omega
                                                                                                  simpa [Nat.sub_add_cancel hoff] using m1_w47 ⟨n - 47350, hnfin⟩
                                                                                                ·
                                                                                                  by_cases h48 : n < 47450
                                                                                                  · have hoff : 47400 ≤ n := by omega
                                                                                                    have hnfin : n - 47400 < 50 := by omega
                                                                                                    simpa [Nat.sub_add_cancel hoff] using m1_w48 ⟨n - 47400, hnfin⟩
                                                                                                  ·
                                                                                                    by_cases h49 : n < 47500
                                                                                                    · have hoff : 47450 ≤ n := by omega
                                                                                                      have hnfin : n - 47450 < 50 := by omega
                                                                                                      simpa [Nat.sub_add_cancel hoff] using m1_w49 ⟨n - 47450, hnfin⟩
                                                                                                    ·
                                                                                                      omega
end IntMul.Kappa.R8.Bit.Oppbank.LandMonoFixA18


