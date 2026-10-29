-- Prove2me | Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankLandMonoFixA23
-- name    : IntMul_Kappa_R8_Data_BitOppbankLandMonoFixA23
-- status  : Definition
-- author  : @Ethan Cheung Wang
-- created : 2026-10-28T21:19:48.443205+00:00
-- url     : https://prove2.me/theorems/d77e5ca9-d103-4dad-ada6-73ba1fd78107
-- title:
--   Dim-gated densSup land mono FixA pack 23
-- statement:
--   # Dim-gated densSup land (PndFix), pack A23
--
--   Range consolidators for $n\in[57500,60000)$.
-- source:
--   R8 BitOppbank PndFix

-- LandMonoFixA23: PUBLIC dim-gated land + range consolidators (PndFix)
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
namespace IntMul.Kappa.R8.Bit.Oppbank.LandMonoFixA23
def arg0 (n : ℕ) : ℕ := Nat.land (argF n) 65535
def arg1 (n : ℕ) : ℕ := Nat.shiftRight (argF n) 16
theorem m0_w0 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 57500))) (dimF (n.val + 57500)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 57500))) (densSupG (n.val + 57500))) (densSupG (arg0 (n.val + 57500)))) = true := by decide
theorem m1_w0 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 57500))) (dimF (n.val + 57500)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 57500))) (densSupG (n.val + 57500))) (densSupG (arg1 (n.val + 57500)))) = true := by decide
theorem m0_w1 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 57550))) (dimF (n.val + 57550)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 57550))) (densSupG (n.val + 57550))) (densSupG (arg0 (n.val + 57550)))) = true := by decide
theorem m1_w1 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 57550))) (dimF (n.val + 57550)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 57550))) (densSupG (n.val + 57550))) (densSupG (arg1 (n.val + 57550)))) = true := by decide
theorem m0_w2 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 57600))) (dimF (n.val + 57600)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 57600))) (densSupG (n.val + 57600))) (densSupG (arg0 (n.val + 57600)))) = true := by decide
theorem m1_w2 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 57600))) (dimF (n.val + 57600)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 57600))) (densSupG (n.val + 57600))) (densSupG (arg1 (n.val + 57600)))) = true := by decide
theorem m0_w3 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 57650))) (dimF (n.val + 57650)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 57650))) (densSupG (n.val + 57650))) (densSupG (arg0 (n.val + 57650)))) = true := by decide
theorem m1_w3 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 57650))) (dimF (n.val + 57650)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 57650))) (densSupG (n.val + 57650))) (densSupG (arg1 (n.val + 57650)))) = true := by decide
theorem m0_w4 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 57700))) (dimF (n.val + 57700)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 57700))) (densSupG (n.val + 57700))) (densSupG (arg0 (n.val + 57700)))) = true := by decide
theorem m1_w4 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 57700))) (dimF (n.val + 57700)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 57700))) (densSupG (n.val + 57700))) (densSupG (arg1 (n.val + 57700)))) = true := by decide
theorem m0_w5 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 57750))) (dimF (n.val + 57750)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 57750))) (densSupG (n.val + 57750))) (densSupG (arg0 (n.val + 57750)))) = true := by decide
theorem m1_w5 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 57750))) (dimF (n.val + 57750)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 57750))) (densSupG (n.val + 57750))) (densSupG (arg1 (n.val + 57750)))) = true := by decide
theorem m0_w6 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 57800))) (dimF (n.val + 57800)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 57800))) (densSupG (n.val + 57800))) (densSupG (arg0 (n.val + 57800)))) = true := by decide
theorem m1_w6 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 57800))) (dimF (n.val + 57800)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 57800))) (densSupG (n.val + 57800))) (densSupG (arg1 (n.val + 57800)))) = true := by decide
theorem m0_w7 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 57850))) (dimF (n.val + 57850)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 57850))) (densSupG (n.val + 57850))) (densSupG (arg0 (n.val + 57850)))) = true := by decide
theorem m1_w7 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 57850))) (dimF (n.val + 57850)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 57850))) (densSupG (n.val + 57850))) (densSupG (arg1 (n.val + 57850)))) = true := by decide
theorem m0_w8 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 57900))) (dimF (n.val + 57900)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 57900))) (densSupG (n.val + 57900))) (densSupG (arg0 (n.val + 57900)))) = true := by decide
theorem m1_w8 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 57900))) (dimF (n.val + 57900)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 57900))) (densSupG (n.val + 57900))) (densSupG (arg1 (n.val + 57900)))) = true := by decide
theorem m0_w9 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 57950))) (dimF (n.val + 57950)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 57950))) (densSupG (n.val + 57950))) (densSupG (arg0 (n.val + 57950)))) = true := by decide
theorem m1_w9 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 57950))) (dimF (n.val + 57950)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 57950))) (densSupG (n.val + 57950))) (densSupG (arg1 (n.val + 57950)))) = true := by decide
theorem m0_w10 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 58000))) (dimF (n.val + 58000)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 58000))) (densSupG (n.val + 58000))) (densSupG (arg0 (n.val + 58000)))) = true := by decide
theorem m1_w10 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 58000))) (dimF (n.val + 58000)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 58000))) (densSupG (n.val + 58000))) (densSupG (arg1 (n.val + 58000)))) = true := by decide
theorem m0_w11 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 58050))) (dimF (n.val + 58050)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 58050))) (densSupG (n.val + 58050))) (densSupG (arg0 (n.val + 58050)))) = true := by decide
theorem m1_w11 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 58050))) (dimF (n.val + 58050)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 58050))) (densSupG (n.val + 58050))) (densSupG (arg1 (n.val + 58050)))) = true := by decide
theorem m0_w12 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 58100))) (dimF (n.val + 58100)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 58100))) (densSupG (n.val + 58100))) (densSupG (arg0 (n.val + 58100)))) = true := by decide
theorem m1_w12 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 58100))) (dimF (n.val + 58100)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 58100))) (densSupG (n.val + 58100))) (densSupG (arg1 (n.val + 58100)))) = true := by decide
theorem m0_w13 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 58150))) (dimF (n.val + 58150)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 58150))) (densSupG (n.val + 58150))) (densSupG (arg0 (n.val + 58150)))) = true := by decide
theorem m1_w13 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 58150))) (dimF (n.val + 58150)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 58150))) (densSupG (n.val + 58150))) (densSupG (arg1 (n.val + 58150)))) = true := by decide
theorem m0_w14 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 58200))) (dimF (n.val + 58200)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 58200))) (densSupG (n.val + 58200))) (densSupG (arg0 (n.val + 58200)))) = true := by decide
theorem m1_w14 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 58200))) (dimF (n.val + 58200)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 58200))) (densSupG (n.val + 58200))) (densSupG (arg1 (n.val + 58200)))) = true := by decide
theorem m0_w15 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 58250))) (dimF (n.val + 58250)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 58250))) (densSupG (n.val + 58250))) (densSupG (arg0 (n.val + 58250)))) = true := by decide
theorem m1_w15 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 58250))) (dimF (n.val + 58250)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 58250))) (densSupG (n.val + 58250))) (densSupG (arg1 (n.val + 58250)))) = true := by decide
theorem m0_w16 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 58300))) (dimF (n.val + 58300)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 58300))) (densSupG (n.val + 58300))) (densSupG (arg0 (n.val + 58300)))) = true := by decide
theorem m1_w16 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 58300))) (dimF (n.val + 58300)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 58300))) (densSupG (n.val + 58300))) (densSupG (arg1 (n.val + 58300)))) = true := by decide
theorem m0_w17 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 58350))) (dimF (n.val + 58350)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 58350))) (densSupG (n.val + 58350))) (densSupG (arg0 (n.val + 58350)))) = true := by decide
theorem m1_w17 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 58350))) (dimF (n.val + 58350)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 58350))) (densSupG (n.val + 58350))) (densSupG (arg1 (n.val + 58350)))) = true := by decide
theorem m0_w18 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 58400))) (dimF (n.val + 58400)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 58400))) (densSupG (n.val + 58400))) (densSupG (arg0 (n.val + 58400)))) = true := by decide
theorem m1_w18 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 58400))) (dimF (n.val + 58400)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 58400))) (densSupG (n.val + 58400))) (densSupG (arg1 (n.val + 58400)))) = true := by decide
theorem m0_w19 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 58450))) (dimF (n.val + 58450)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 58450))) (densSupG (n.val + 58450))) (densSupG (arg0 (n.val + 58450)))) = true := by decide
theorem m1_w19 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 58450))) (dimF (n.val + 58450)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 58450))) (densSupG (n.val + 58450))) (densSupG (arg1 (n.val + 58450)))) = true := by decide
theorem m0_w20 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 58500))) (dimF (n.val + 58500)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 58500))) (densSupG (n.val + 58500))) (densSupG (arg0 (n.val + 58500)))) = true := by decide
theorem m1_w20 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 58500))) (dimF (n.val + 58500)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 58500))) (densSupG (n.val + 58500))) (densSupG (arg1 (n.val + 58500)))) = true := by decide
theorem m0_w21 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 58550))) (dimF (n.val + 58550)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 58550))) (densSupG (n.val + 58550))) (densSupG (arg0 (n.val + 58550)))) = true := by decide
theorem m1_w21 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 58550))) (dimF (n.val + 58550)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 58550))) (densSupG (n.val + 58550))) (densSupG (arg1 (n.val + 58550)))) = true := by decide
theorem m0_w22 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 58600))) (dimF (n.val + 58600)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 58600))) (densSupG (n.val + 58600))) (densSupG (arg0 (n.val + 58600)))) = true := by decide
theorem m1_w22 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 58600))) (dimF (n.val + 58600)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 58600))) (densSupG (n.val + 58600))) (densSupG (arg1 (n.val + 58600)))) = true := by decide
theorem m0_w23 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 58650))) (dimF (n.val + 58650)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 58650))) (densSupG (n.val + 58650))) (densSupG (arg0 (n.val + 58650)))) = true := by decide
theorem m1_w23 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 58650))) (dimF (n.val + 58650)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 58650))) (densSupG (n.val + 58650))) (densSupG (arg1 (n.val + 58650)))) = true := by decide
theorem m0_w24 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 58700))) (dimF (n.val + 58700)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 58700))) (densSupG (n.val + 58700))) (densSupG (arg0 (n.val + 58700)))) = true := by decide
theorem m1_w24 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 58700))) (dimF (n.val + 58700)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 58700))) (densSupG (n.val + 58700))) (densSupG (arg1 (n.val + 58700)))) = true := by decide
theorem m0_w25 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 58750))) (dimF (n.val + 58750)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 58750))) (densSupG (n.val + 58750))) (densSupG (arg0 (n.val + 58750)))) = true := by decide
theorem m1_w25 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 58750))) (dimF (n.val + 58750)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 58750))) (densSupG (n.val + 58750))) (densSupG (arg1 (n.val + 58750)))) = true := by decide
theorem m0_w26 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 58800))) (dimF (n.val + 58800)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 58800))) (densSupG (n.val + 58800))) (densSupG (arg0 (n.val + 58800)))) = true := by decide
theorem m1_w26 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 58800))) (dimF (n.val + 58800)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 58800))) (densSupG (n.val + 58800))) (densSupG (arg1 (n.val + 58800)))) = true := by decide
theorem m0_w27 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 58850))) (dimF (n.val + 58850)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 58850))) (densSupG (n.val + 58850))) (densSupG (arg0 (n.val + 58850)))) = true := by decide
theorem m1_w27 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 58850))) (dimF (n.val + 58850)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 58850))) (densSupG (n.val + 58850))) (densSupG (arg1 (n.val + 58850)))) = true := by decide
theorem m0_w28 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 58900))) (dimF (n.val + 58900)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 58900))) (densSupG (n.val + 58900))) (densSupG (arg0 (n.val + 58900)))) = true := by decide
theorem m1_w28 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 58900))) (dimF (n.val + 58900)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 58900))) (densSupG (n.val + 58900))) (densSupG (arg1 (n.val + 58900)))) = true := by decide
theorem m0_w29 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 58950))) (dimF (n.val + 58950)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 58950))) (densSupG (n.val + 58950))) (densSupG (arg0 (n.val + 58950)))) = true := by decide
theorem m1_w29 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 58950))) (dimF (n.val + 58950)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 58950))) (densSupG (n.val + 58950))) (densSupG (arg1 (n.val + 58950)))) = true := by decide
theorem m0_w30 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 59000))) (dimF (n.val + 59000)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 59000))) (densSupG (n.val + 59000))) (densSupG (arg0 (n.val + 59000)))) = true := by decide
theorem m1_w30 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 59000))) (dimF (n.val + 59000)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 59000))) (densSupG (n.val + 59000))) (densSupG (arg1 (n.val + 59000)))) = true := by decide
theorem m0_w31 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 59050))) (dimF (n.val + 59050)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 59050))) (densSupG (n.val + 59050))) (densSupG (arg0 (n.val + 59050)))) = true := by decide
theorem m1_w31 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 59050))) (dimF (n.val + 59050)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 59050))) (densSupG (n.val + 59050))) (densSupG (arg1 (n.val + 59050)))) = true := by decide
theorem m0_w32 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 59100))) (dimF (n.val + 59100)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 59100))) (densSupG (n.val + 59100))) (densSupG (arg0 (n.val + 59100)))) = true := by decide
theorem m1_w32 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 59100))) (dimF (n.val + 59100)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 59100))) (densSupG (n.val + 59100))) (densSupG (arg1 (n.val + 59100)))) = true := by decide
theorem m0_w33 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 59150))) (dimF (n.val + 59150)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 59150))) (densSupG (n.val + 59150))) (densSupG (arg0 (n.val + 59150)))) = true := by decide
theorem m1_w33 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 59150))) (dimF (n.val + 59150)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 59150))) (densSupG (n.val + 59150))) (densSupG (arg1 (n.val + 59150)))) = true := by decide
theorem m0_w34 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 59200))) (dimF (n.val + 59200)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 59200))) (densSupG (n.val + 59200))) (densSupG (arg0 (n.val + 59200)))) = true := by decide
theorem m1_w34 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 59200))) (dimF (n.val + 59200)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 59200))) (densSupG (n.val + 59200))) (densSupG (arg1 (n.val + 59200)))) = true := by decide
theorem m0_w35 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 59250))) (dimF (n.val + 59250)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 59250))) (densSupG (n.val + 59250))) (densSupG (arg0 (n.val + 59250)))) = true := by decide
theorem m1_w35 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 59250))) (dimF (n.val + 59250)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 59250))) (densSupG (n.val + 59250))) (densSupG (arg1 (n.val + 59250)))) = true := by decide
theorem m0_w36 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 59300))) (dimF (n.val + 59300)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 59300))) (densSupG (n.val + 59300))) (densSupG (arg0 (n.val + 59300)))) = true := by decide
theorem m1_w36 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 59300))) (dimF (n.val + 59300)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 59300))) (densSupG (n.val + 59300))) (densSupG (arg1 (n.val + 59300)))) = true := by decide
theorem m0_w37 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 59350))) (dimF (n.val + 59350)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 59350))) (densSupG (n.val + 59350))) (densSupG (arg0 (n.val + 59350)))) = true := by decide
theorem m1_w37 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 59350))) (dimF (n.val + 59350)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 59350))) (densSupG (n.val + 59350))) (densSupG (arg1 (n.val + 59350)))) = true := by decide
theorem m0_w38 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 59400))) (dimF (n.val + 59400)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 59400))) (densSupG (n.val + 59400))) (densSupG (arg0 (n.val + 59400)))) = true := by decide
theorem m1_w38 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 59400))) (dimF (n.val + 59400)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 59400))) (densSupG (n.val + 59400))) (densSupG (arg1 (n.val + 59400)))) = true := by decide
theorem m0_w39 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 59450))) (dimF (n.val + 59450)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 59450))) (densSupG (n.val + 59450))) (densSupG (arg0 (n.val + 59450)))) = true := by decide
theorem m1_w39 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 59450))) (dimF (n.val + 59450)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 59450))) (densSupG (n.val + 59450))) (densSupG (arg1 (n.val + 59450)))) = true := by decide
theorem m0_w40 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 59500))) (dimF (n.val + 59500)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 59500))) (densSupG (n.val + 59500))) (densSupG (arg0 (n.val + 59500)))) = true := by decide
theorem m1_w40 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 59500))) (dimF (n.val + 59500)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 59500))) (densSupG (n.val + 59500))) (densSupG (arg1 (n.val + 59500)))) = true := by decide
theorem m0_w41 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 59550))) (dimF (n.val + 59550)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 59550))) (densSupG (n.val + 59550))) (densSupG (arg0 (n.val + 59550)))) = true := by decide
theorem m1_w41 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 59550))) (dimF (n.val + 59550)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 59550))) (densSupG (n.val + 59550))) (densSupG (arg1 (n.val + 59550)))) = true := by decide
theorem m0_w42 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 59600))) (dimF (n.val + 59600)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 59600))) (densSupG (n.val + 59600))) (densSupG (arg0 (n.val + 59600)))) = true := by decide
theorem m1_w42 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 59600))) (dimF (n.val + 59600)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 59600))) (densSupG (n.val + 59600))) (densSupG (arg1 (n.val + 59600)))) = true := by decide
theorem m0_w43 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 59650))) (dimF (n.val + 59650)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 59650))) (densSupG (n.val + 59650))) (densSupG (arg0 (n.val + 59650)))) = true := by decide
theorem m1_w43 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 59650))) (dimF (n.val + 59650)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 59650))) (densSupG (n.val + 59650))) (densSupG (arg1 (n.val + 59650)))) = true := by decide
theorem m0_w44 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 59700))) (dimF (n.val + 59700)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 59700))) (densSupG (n.val + 59700))) (densSupG (arg0 (n.val + 59700)))) = true := by decide
theorem m1_w44 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 59700))) (dimF (n.val + 59700)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 59700))) (densSupG (n.val + 59700))) (densSupG (arg1 (n.val + 59700)))) = true := by decide
theorem m0_w45 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 59750))) (dimF (n.val + 59750)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 59750))) (densSupG (n.val + 59750))) (densSupG (arg0 (n.val + 59750)))) = true := by decide
theorem m1_w45 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 59750))) (dimF (n.val + 59750)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 59750))) (densSupG (n.val + 59750))) (densSupG (arg1 (n.val + 59750)))) = true := by decide
theorem m0_w46 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 59800))) (dimF (n.val + 59800)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 59800))) (densSupG (n.val + 59800))) (densSupG (arg0 (n.val + 59800)))) = true := by decide
theorem m1_w46 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 59800))) (dimF (n.val + 59800)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 59800))) (densSupG (n.val + 59800))) (densSupG (arg1 (n.val + 59800)))) = true := by decide
theorem m0_w47 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 59850))) (dimF (n.val + 59850)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 59850))) (densSupG (n.val + 59850))) (densSupG (arg0 (n.val + 59850)))) = true := by decide
theorem m1_w47 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 59850))) (dimF (n.val + 59850)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 59850))) (densSupG (n.val + 59850))) (densSupG (arg1 (n.val + 59850)))) = true := by decide
theorem m0_w48 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 59900))) (dimF (n.val + 59900)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 59900))) (densSupG (n.val + 59900))) (densSupG (arg0 (n.val + 59900)))) = true := by decide
theorem m1_w48 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 59900))) (dimF (n.val + 59900)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 59900))) (densSupG (n.val + 59900))) (densSupG (arg1 (n.val + 59900)))) = true := by decide
theorem m0_w49 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 59950))) (dimF (n.val + 59950)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 59950))) (densSupG (n.val + 59950))) (densSupG (arg0 (n.val + 59950)))) = true := by decide
theorem m1_w49 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 59950))) (dimF (n.val + 59950)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 59950))) (densSupG (n.val + 59950))) (densSupG (arg1 (n.val + 59950)))) = true := by decide
theorem land0_range (n : ℕ) (hn0 : 57500 ≤ n) (hn1 : n < 60000) :
    (!Nat.blt (dimF (arg0 n)) (dimF n) ||
      Nat.beq (Nat.land (densSupG (arg0 n)) (densSupG n)) (densSupG (arg0 n))) = true := by
  by_cases h0 : n < 57550
  · have hoff : 57500 ≤ n := by omega
    have hnfin : n - 57500 < 50 := by omega
    simpa [Nat.sub_add_cancel hoff] using m0_w0 ⟨n - 57500, hnfin⟩
  ·
    by_cases h1 : n < 57600
    · have hoff : 57550 ≤ n := by omega
      have hnfin : n - 57550 < 50 := by omega
      simpa [Nat.sub_add_cancel hoff] using m0_w1 ⟨n - 57550, hnfin⟩
    ·
      by_cases h2 : n < 57650
      · have hoff : 57600 ≤ n := by omega
        have hnfin : n - 57600 < 50 := by omega
        simpa [Nat.sub_add_cancel hoff] using m0_w2 ⟨n - 57600, hnfin⟩
      ·
        by_cases h3 : n < 57700
        · have hoff : 57650 ≤ n := by omega
          have hnfin : n - 57650 < 50 := by omega
          simpa [Nat.sub_add_cancel hoff] using m0_w3 ⟨n - 57650, hnfin⟩
        ·
          by_cases h4 : n < 57750
          · have hoff : 57700 ≤ n := by omega
            have hnfin : n - 57700 < 50 := by omega
            simpa [Nat.sub_add_cancel hoff] using m0_w4 ⟨n - 57700, hnfin⟩
          ·
            by_cases h5 : n < 57800
            · have hoff : 57750 ≤ n := by omega
              have hnfin : n - 57750 < 50 := by omega
              simpa [Nat.sub_add_cancel hoff] using m0_w5 ⟨n - 57750, hnfin⟩
            ·
              by_cases h6 : n < 57850
              · have hoff : 57800 ≤ n := by omega
                have hnfin : n - 57800 < 50 := by omega
                simpa [Nat.sub_add_cancel hoff] using m0_w6 ⟨n - 57800, hnfin⟩
              ·
                by_cases h7 : n < 57900
                · have hoff : 57850 ≤ n := by omega
                  have hnfin : n - 57850 < 50 := by omega
                  simpa [Nat.sub_add_cancel hoff] using m0_w7 ⟨n - 57850, hnfin⟩
                ·
                  by_cases h8 : n < 57950
                  · have hoff : 57900 ≤ n := by omega
                    have hnfin : n - 57900 < 50 := by omega
                    simpa [Nat.sub_add_cancel hoff] using m0_w8 ⟨n - 57900, hnfin⟩
                  ·
                    by_cases h9 : n < 58000
                    · have hoff : 57950 ≤ n := by omega
                      have hnfin : n - 57950 < 50 := by omega
                      simpa [Nat.sub_add_cancel hoff] using m0_w9 ⟨n - 57950, hnfin⟩
                    ·
                      by_cases h10 : n < 58050
                      · have hoff : 58000 ≤ n := by omega
                        have hnfin : n - 58000 < 50 := by omega
                        simpa [Nat.sub_add_cancel hoff] using m0_w10 ⟨n - 58000, hnfin⟩
                      ·
                        by_cases h11 : n < 58100
                        · have hoff : 58050 ≤ n := by omega
                          have hnfin : n - 58050 < 50 := by omega
                          simpa [Nat.sub_add_cancel hoff] using m0_w11 ⟨n - 58050, hnfin⟩
                        ·
                          by_cases h12 : n < 58150
                          · have hoff : 58100 ≤ n := by omega
                            have hnfin : n - 58100 < 50 := by omega
                            simpa [Nat.sub_add_cancel hoff] using m0_w12 ⟨n - 58100, hnfin⟩
                          ·
                            by_cases h13 : n < 58200
                            · have hoff : 58150 ≤ n := by omega
                              have hnfin : n - 58150 < 50 := by omega
                              simpa [Nat.sub_add_cancel hoff] using m0_w13 ⟨n - 58150, hnfin⟩
                            ·
                              by_cases h14 : n < 58250
                              · have hoff : 58200 ≤ n := by omega
                                have hnfin : n - 58200 < 50 := by omega
                                simpa [Nat.sub_add_cancel hoff] using m0_w14 ⟨n - 58200, hnfin⟩
                              ·
                                by_cases h15 : n < 58300
                                · have hoff : 58250 ≤ n := by omega
                                  have hnfin : n - 58250 < 50 := by omega
                                  simpa [Nat.sub_add_cancel hoff] using m0_w15 ⟨n - 58250, hnfin⟩
                                ·
                                  by_cases h16 : n < 58350
                                  · have hoff : 58300 ≤ n := by omega
                                    have hnfin : n - 58300 < 50 := by omega
                                    simpa [Nat.sub_add_cancel hoff] using m0_w16 ⟨n - 58300, hnfin⟩
                                  ·
                                    by_cases h17 : n < 58400
                                    · have hoff : 58350 ≤ n := by omega
                                      have hnfin : n - 58350 < 50 := by omega
                                      simpa [Nat.sub_add_cancel hoff] using m0_w17 ⟨n - 58350, hnfin⟩
                                    ·
                                      by_cases h18 : n < 58450
                                      · have hoff : 58400 ≤ n := by omega
                                        have hnfin : n - 58400 < 50 := by omega
                                        simpa [Nat.sub_add_cancel hoff] using m0_w18 ⟨n - 58400, hnfin⟩
                                      ·
                                        by_cases h19 : n < 58500
                                        · have hoff : 58450 ≤ n := by omega
                                          have hnfin : n - 58450 < 50 := by omega
                                          simpa [Nat.sub_add_cancel hoff] using m0_w19 ⟨n - 58450, hnfin⟩
                                        ·
                                          by_cases h20 : n < 58550
                                          · have hoff : 58500 ≤ n := by omega
                                            have hnfin : n - 58500 < 50 := by omega
                                            simpa [Nat.sub_add_cancel hoff] using m0_w20 ⟨n - 58500, hnfin⟩
                                          ·
                                            by_cases h21 : n < 58600
                                            · have hoff : 58550 ≤ n := by omega
                                              have hnfin : n - 58550 < 50 := by omega
                                              simpa [Nat.sub_add_cancel hoff] using m0_w21 ⟨n - 58550, hnfin⟩
                                            ·
                                              by_cases h22 : n < 58650
                                              · have hoff : 58600 ≤ n := by omega
                                                have hnfin : n - 58600 < 50 := by omega
                                                simpa [Nat.sub_add_cancel hoff] using m0_w22 ⟨n - 58600, hnfin⟩
                                              ·
                                                by_cases h23 : n < 58700
                                                · have hoff : 58650 ≤ n := by omega
                                                  have hnfin : n - 58650 < 50 := by omega
                                                  simpa [Nat.sub_add_cancel hoff] using m0_w23 ⟨n - 58650, hnfin⟩
                                                ·
                                                  by_cases h24 : n < 58750
                                                  · have hoff : 58700 ≤ n := by omega
                                                    have hnfin : n - 58700 < 50 := by omega
                                                    simpa [Nat.sub_add_cancel hoff] using m0_w24 ⟨n - 58700, hnfin⟩
                                                  ·
                                                    by_cases h25 : n < 58800
                                                    · have hoff : 58750 ≤ n := by omega
                                                      have hnfin : n - 58750 < 50 := by omega
                                                      simpa [Nat.sub_add_cancel hoff] using m0_w25 ⟨n - 58750, hnfin⟩
                                                    ·
                                                      by_cases h26 : n < 58850
                                                      · have hoff : 58800 ≤ n := by omega
                                                        have hnfin : n - 58800 < 50 := by omega
                                                        simpa [Nat.sub_add_cancel hoff] using m0_w26 ⟨n - 58800, hnfin⟩
                                                      ·
                                                        by_cases h27 : n < 58900
                                                        · have hoff : 58850 ≤ n := by omega
                                                          have hnfin : n - 58850 < 50 := by omega
                                                          simpa [Nat.sub_add_cancel hoff] using m0_w27 ⟨n - 58850, hnfin⟩
                                                        ·
                                                          by_cases h28 : n < 58950
                                                          · have hoff : 58900 ≤ n := by omega
                                                            have hnfin : n - 58900 < 50 := by omega
                                                            simpa [Nat.sub_add_cancel hoff] using m0_w28 ⟨n - 58900, hnfin⟩
                                                          ·
                                                            by_cases h29 : n < 59000
                                                            · have hoff : 58950 ≤ n := by omega
                                                              have hnfin : n - 58950 < 50 := by omega
                                                              simpa [Nat.sub_add_cancel hoff] using m0_w29 ⟨n - 58950, hnfin⟩
                                                            ·
                                                              by_cases h30 : n < 59050
                                                              · have hoff : 59000 ≤ n := by omega
                                                                have hnfin : n - 59000 < 50 := by omega
                                                                simpa [Nat.sub_add_cancel hoff] using m0_w30 ⟨n - 59000, hnfin⟩
                                                              ·
                                                                by_cases h31 : n < 59100
                                                                · have hoff : 59050 ≤ n := by omega
                                                                  have hnfin : n - 59050 < 50 := by omega
                                                                  simpa [Nat.sub_add_cancel hoff] using m0_w31 ⟨n - 59050, hnfin⟩
                                                                ·
                                                                  by_cases h32 : n < 59150
                                                                  · have hoff : 59100 ≤ n := by omega
                                                                    have hnfin : n - 59100 < 50 := by omega
                                                                    simpa [Nat.sub_add_cancel hoff] using m0_w32 ⟨n - 59100, hnfin⟩
                                                                  ·
                                                                    by_cases h33 : n < 59200
                                                                    · have hoff : 59150 ≤ n := by omega
                                                                      have hnfin : n - 59150 < 50 := by omega
                                                                      simpa [Nat.sub_add_cancel hoff] using m0_w33 ⟨n - 59150, hnfin⟩
                                                                    ·
                                                                      by_cases h34 : n < 59250
                                                                      · have hoff : 59200 ≤ n := by omega
                                                                        have hnfin : n - 59200 < 50 := by omega
                                                                        simpa [Nat.sub_add_cancel hoff] using m0_w34 ⟨n - 59200, hnfin⟩
                                                                      ·
                                                                        by_cases h35 : n < 59300
                                                                        · have hoff : 59250 ≤ n := by omega
                                                                          have hnfin : n - 59250 < 50 := by omega
                                                                          simpa [Nat.sub_add_cancel hoff] using m0_w35 ⟨n - 59250, hnfin⟩
                                                                        ·
                                                                          by_cases h36 : n < 59350
                                                                          · have hoff : 59300 ≤ n := by omega
                                                                            have hnfin : n - 59300 < 50 := by omega
                                                                            simpa [Nat.sub_add_cancel hoff] using m0_w36 ⟨n - 59300, hnfin⟩
                                                                          ·
                                                                            by_cases h37 : n < 59400
                                                                            · have hoff : 59350 ≤ n := by omega
                                                                              have hnfin : n - 59350 < 50 := by omega
                                                                              simpa [Nat.sub_add_cancel hoff] using m0_w37 ⟨n - 59350, hnfin⟩
                                                                            ·
                                                                              by_cases h38 : n < 59450
                                                                              · have hoff : 59400 ≤ n := by omega
                                                                                have hnfin : n - 59400 < 50 := by omega
                                                                                simpa [Nat.sub_add_cancel hoff] using m0_w38 ⟨n - 59400, hnfin⟩
                                                                              ·
                                                                                by_cases h39 : n < 59500
                                                                                · have hoff : 59450 ≤ n := by omega
                                                                                  have hnfin : n - 59450 < 50 := by omega
                                                                                  simpa [Nat.sub_add_cancel hoff] using m0_w39 ⟨n - 59450, hnfin⟩
                                                                                ·
                                                                                  by_cases h40 : n < 59550
                                                                                  · have hoff : 59500 ≤ n := by omega
                                                                                    have hnfin : n - 59500 < 50 := by omega
                                                                                    simpa [Nat.sub_add_cancel hoff] using m0_w40 ⟨n - 59500, hnfin⟩
                                                                                  ·
                                                                                    by_cases h41 : n < 59600
                                                                                    · have hoff : 59550 ≤ n := by omega
                                                                                      have hnfin : n - 59550 < 50 := by omega
                                                                                      simpa [Nat.sub_add_cancel hoff] using m0_w41 ⟨n - 59550, hnfin⟩
                                                                                    ·
                                                                                      by_cases h42 : n < 59650
                                                                                      · have hoff : 59600 ≤ n := by omega
                                                                                        have hnfin : n - 59600 < 50 := by omega
                                                                                        simpa [Nat.sub_add_cancel hoff] using m0_w42 ⟨n - 59600, hnfin⟩
                                                                                      ·
                                                                                        by_cases h43 : n < 59700
                                                                                        · have hoff : 59650 ≤ n := by omega
                                                                                          have hnfin : n - 59650 < 50 := by omega
                                                                                          simpa [Nat.sub_add_cancel hoff] using m0_w43 ⟨n - 59650, hnfin⟩
                                                                                        ·
                                                                                          by_cases h44 : n < 59750
                                                                                          · have hoff : 59700 ≤ n := by omega
                                                                                            have hnfin : n - 59700 < 50 := by omega
                                                                                            simpa [Nat.sub_add_cancel hoff] using m0_w44 ⟨n - 59700, hnfin⟩
                                                                                          ·
                                                                                            by_cases h45 : n < 59800
                                                                                            · have hoff : 59750 ≤ n := by omega
                                                                                              have hnfin : n - 59750 < 50 := by omega
                                                                                              simpa [Nat.sub_add_cancel hoff] using m0_w45 ⟨n - 59750, hnfin⟩
                                                                                            ·
                                                                                              by_cases h46 : n < 59850
                                                                                              · have hoff : 59800 ≤ n := by omega
                                                                                                have hnfin : n - 59800 < 50 := by omega
                                                                                                simpa [Nat.sub_add_cancel hoff] using m0_w46 ⟨n - 59800, hnfin⟩
                                                                                              ·
                                                                                                by_cases h47 : n < 59900
                                                                                                · have hoff : 59850 ≤ n := by omega
                                                                                                  have hnfin : n - 59850 < 50 := by omega
                                                                                                  simpa [Nat.sub_add_cancel hoff] using m0_w47 ⟨n - 59850, hnfin⟩
                                                                                                ·
                                                                                                  by_cases h48 : n < 59950
                                                                                                  · have hoff : 59900 ≤ n := by omega
                                                                                                    have hnfin : n - 59900 < 50 := by omega
                                                                                                    simpa [Nat.sub_add_cancel hoff] using m0_w48 ⟨n - 59900, hnfin⟩
                                                                                                  ·
                                                                                                    by_cases h49 : n < 60000
                                                                                                    · have hoff : 59950 ≤ n := by omega
                                                                                                      have hnfin : n - 59950 < 50 := by omega
                                                                                                      simpa [Nat.sub_add_cancel hoff] using m0_w49 ⟨n - 59950, hnfin⟩
                                                                                                    ·
                                                                                                      omega
theorem land1_range (n : ℕ) (hn0 : 57500 ≤ n) (hn1 : n < 60000) :
    (!Nat.blt (dimF (arg1 n)) (dimF n) ||
      Nat.beq (Nat.land (densSupG (arg1 n)) (densSupG n)) (densSupG (arg1 n))) = true := by
  by_cases h0 : n < 57550
  · have hoff : 57500 ≤ n := by omega
    have hnfin : n - 57500 < 50 := by omega
    simpa [Nat.sub_add_cancel hoff] using m1_w0 ⟨n - 57500, hnfin⟩
  ·
    by_cases h1 : n < 57600
    · have hoff : 57550 ≤ n := by omega
      have hnfin : n - 57550 < 50 := by omega
      simpa [Nat.sub_add_cancel hoff] using m1_w1 ⟨n - 57550, hnfin⟩
    ·
      by_cases h2 : n < 57650
      · have hoff : 57600 ≤ n := by omega
        have hnfin : n - 57600 < 50 := by omega
        simpa [Nat.sub_add_cancel hoff] using m1_w2 ⟨n - 57600, hnfin⟩
      ·
        by_cases h3 : n < 57700
        · have hoff : 57650 ≤ n := by omega
          have hnfin : n - 57650 < 50 := by omega
          simpa [Nat.sub_add_cancel hoff] using m1_w3 ⟨n - 57650, hnfin⟩
        ·
          by_cases h4 : n < 57750
          · have hoff : 57700 ≤ n := by omega
            have hnfin : n - 57700 < 50 := by omega
            simpa [Nat.sub_add_cancel hoff] using m1_w4 ⟨n - 57700, hnfin⟩
          ·
            by_cases h5 : n < 57800
            · have hoff : 57750 ≤ n := by omega
              have hnfin : n - 57750 < 50 := by omega
              simpa [Nat.sub_add_cancel hoff] using m1_w5 ⟨n - 57750, hnfin⟩
            ·
              by_cases h6 : n < 57850
              · have hoff : 57800 ≤ n := by omega
                have hnfin : n - 57800 < 50 := by omega
                simpa [Nat.sub_add_cancel hoff] using m1_w6 ⟨n - 57800, hnfin⟩
              ·
                by_cases h7 : n < 57900
                · have hoff : 57850 ≤ n := by omega
                  have hnfin : n - 57850 < 50 := by omega
                  simpa [Nat.sub_add_cancel hoff] using m1_w7 ⟨n - 57850, hnfin⟩
                ·
                  by_cases h8 : n < 57950
                  · have hoff : 57900 ≤ n := by omega
                    have hnfin : n - 57900 < 50 := by omega
                    simpa [Nat.sub_add_cancel hoff] using m1_w8 ⟨n - 57900, hnfin⟩
                  ·
                    by_cases h9 : n < 58000
                    · have hoff : 57950 ≤ n := by omega
                      have hnfin : n - 57950 < 50 := by omega
                      simpa [Nat.sub_add_cancel hoff] using m1_w9 ⟨n - 57950, hnfin⟩
                    ·
                      by_cases h10 : n < 58050
                      · have hoff : 58000 ≤ n := by omega
                        have hnfin : n - 58000 < 50 := by omega
                        simpa [Nat.sub_add_cancel hoff] using m1_w10 ⟨n - 58000, hnfin⟩
                      ·
                        by_cases h11 : n < 58100
                        · have hoff : 58050 ≤ n := by omega
                          have hnfin : n - 58050 < 50 := by omega
                          simpa [Nat.sub_add_cancel hoff] using m1_w11 ⟨n - 58050, hnfin⟩
                        ·
                          by_cases h12 : n < 58150
                          · have hoff : 58100 ≤ n := by omega
                            have hnfin : n - 58100 < 50 := by omega
                            simpa [Nat.sub_add_cancel hoff] using m1_w12 ⟨n - 58100, hnfin⟩
                          ·
                            by_cases h13 : n < 58200
                            · have hoff : 58150 ≤ n := by omega
                              have hnfin : n - 58150 < 50 := by omega
                              simpa [Nat.sub_add_cancel hoff] using m1_w13 ⟨n - 58150, hnfin⟩
                            ·
                              by_cases h14 : n < 58250
                              · have hoff : 58200 ≤ n := by omega
                                have hnfin : n - 58200 < 50 := by omega
                                simpa [Nat.sub_add_cancel hoff] using m1_w14 ⟨n - 58200, hnfin⟩
                              ·
                                by_cases h15 : n < 58300
                                · have hoff : 58250 ≤ n := by omega
                                  have hnfin : n - 58250 < 50 := by omega
                                  simpa [Nat.sub_add_cancel hoff] using m1_w15 ⟨n - 58250, hnfin⟩
                                ·
                                  by_cases h16 : n < 58350
                                  · have hoff : 58300 ≤ n := by omega
                                    have hnfin : n - 58300 < 50 := by omega
                                    simpa [Nat.sub_add_cancel hoff] using m1_w16 ⟨n - 58300, hnfin⟩
                                  ·
                                    by_cases h17 : n < 58400
                                    · have hoff : 58350 ≤ n := by omega
                                      have hnfin : n - 58350 < 50 := by omega
                                      simpa [Nat.sub_add_cancel hoff] using m1_w17 ⟨n - 58350, hnfin⟩
                                    ·
                                      by_cases h18 : n < 58450
                                      · have hoff : 58400 ≤ n := by omega
                                        have hnfin : n - 58400 < 50 := by omega
                                        simpa [Nat.sub_add_cancel hoff] using m1_w18 ⟨n - 58400, hnfin⟩
                                      ·
                                        by_cases h19 : n < 58500
                                        · have hoff : 58450 ≤ n := by omega
                                          have hnfin : n - 58450 < 50 := by omega
                                          simpa [Nat.sub_add_cancel hoff] using m1_w19 ⟨n - 58450, hnfin⟩
                                        ·
                                          by_cases h20 : n < 58550
                                          · have hoff : 58500 ≤ n := by omega
                                            have hnfin : n - 58500 < 50 := by omega
                                            simpa [Nat.sub_add_cancel hoff] using m1_w20 ⟨n - 58500, hnfin⟩
                                          ·
                                            by_cases h21 : n < 58600
                                            · have hoff : 58550 ≤ n := by omega
                                              have hnfin : n - 58550 < 50 := by omega
                                              simpa [Nat.sub_add_cancel hoff] using m1_w21 ⟨n - 58550, hnfin⟩
                                            ·
                                              by_cases h22 : n < 58650
                                              · have hoff : 58600 ≤ n := by omega
                                                have hnfin : n - 58600 < 50 := by omega
                                                simpa [Nat.sub_add_cancel hoff] using m1_w22 ⟨n - 58600, hnfin⟩
                                              ·
                                                by_cases h23 : n < 58700
                                                · have hoff : 58650 ≤ n := by omega
                                                  have hnfin : n - 58650 < 50 := by omega
                                                  simpa [Nat.sub_add_cancel hoff] using m1_w23 ⟨n - 58650, hnfin⟩
                                                ·
                                                  by_cases h24 : n < 58750
                                                  · have hoff : 58700 ≤ n := by omega
                                                    have hnfin : n - 58700 < 50 := by omega
                                                    simpa [Nat.sub_add_cancel hoff] using m1_w24 ⟨n - 58700, hnfin⟩
                                                  ·
                                                    by_cases h25 : n < 58800
                                                    · have hoff : 58750 ≤ n := by omega
                                                      have hnfin : n - 58750 < 50 := by omega
                                                      simpa [Nat.sub_add_cancel hoff] using m1_w25 ⟨n - 58750, hnfin⟩
                                                    ·
                                                      by_cases h26 : n < 58850
                                                      · have hoff : 58800 ≤ n := by omega
                                                        have hnfin : n - 58800 < 50 := by omega
                                                        simpa [Nat.sub_add_cancel hoff] using m1_w26 ⟨n - 58800, hnfin⟩
                                                      ·
                                                        by_cases h27 : n < 58900
                                                        · have hoff : 58850 ≤ n := by omega
                                                          have hnfin : n - 58850 < 50 := by omega
                                                          simpa [Nat.sub_add_cancel hoff] using m1_w27 ⟨n - 58850, hnfin⟩
                                                        ·
                                                          by_cases h28 : n < 58950
                                                          · have hoff : 58900 ≤ n := by omega
                                                            have hnfin : n - 58900 < 50 := by omega
                                                            simpa [Nat.sub_add_cancel hoff] using m1_w28 ⟨n - 58900, hnfin⟩
                                                          ·
                                                            by_cases h29 : n < 59000
                                                            · have hoff : 58950 ≤ n := by omega
                                                              have hnfin : n - 58950 < 50 := by omega
                                                              simpa [Nat.sub_add_cancel hoff] using m1_w29 ⟨n - 58950, hnfin⟩
                                                            ·
                                                              by_cases h30 : n < 59050
                                                              · have hoff : 59000 ≤ n := by omega
                                                                have hnfin : n - 59000 < 50 := by omega
                                                                simpa [Nat.sub_add_cancel hoff] using m1_w30 ⟨n - 59000, hnfin⟩
                                                              ·
                                                                by_cases h31 : n < 59100
                                                                · have hoff : 59050 ≤ n := by omega
                                                                  have hnfin : n - 59050 < 50 := by omega
                                                                  simpa [Nat.sub_add_cancel hoff] using m1_w31 ⟨n - 59050, hnfin⟩
                                                                ·
                                                                  by_cases h32 : n < 59150
                                                                  · have hoff : 59100 ≤ n := by omega
                                                                    have hnfin : n - 59100 < 50 := by omega
                                                                    simpa [Nat.sub_add_cancel hoff] using m1_w32 ⟨n - 59100, hnfin⟩
                                                                  ·
                                                                    by_cases h33 : n < 59200
                                                                    · have hoff : 59150 ≤ n := by omega
                                                                      have hnfin : n - 59150 < 50 := by omega
                                                                      simpa [Nat.sub_add_cancel hoff] using m1_w33 ⟨n - 59150, hnfin⟩
                                                                    ·
                                                                      by_cases h34 : n < 59250
                                                                      · have hoff : 59200 ≤ n := by omega
                                                                        have hnfin : n - 59200 < 50 := by omega
                                                                        simpa [Nat.sub_add_cancel hoff] using m1_w34 ⟨n - 59200, hnfin⟩
                                                                      ·
                                                                        by_cases h35 : n < 59300
                                                                        · have hoff : 59250 ≤ n := by omega
                                                                          have hnfin : n - 59250 < 50 := by omega
                                                                          simpa [Nat.sub_add_cancel hoff] using m1_w35 ⟨n - 59250, hnfin⟩
                                                                        ·
                                                                          by_cases h36 : n < 59350
                                                                          · have hoff : 59300 ≤ n := by omega
                                                                            have hnfin : n - 59300 < 50 := by omega
                                                                            simpa [Nat.sub_add_cancel hoff] using m1_w36 ⟨n - 59300, hnfin⟩
                                                                          ·
                                                                            by_cases h37 : n < 59400
                                                                            · have hoff : 59350 ≤ n := by omega
                                                                              have hnfin : n - 59350 < 50 := by omega
                                                                              simpa [Nat.sub_add_cancel hoff] using m1_w37 ⟨n - 59350, hnfin⟩
                                                                            ·
                                                                              by_cases h38 : n < 59450
                                                                              · have hoff : 59400 ≤ n := by omega
                                                                                have hnfin : n - 59400 < 50 := by omega
                                                                                simpa [Nat.sub_add_cancel hoff] using m1_w38 ⟨n - 59400, hnfin⟩
                                                                              ·
                                                                                by_cases h39 : n < 59500
                                                                                · have hoff : 59450 ≤ n := by omega
                                                                                  have hnfin : n - 59450 < 50 := by omega
                                                                                  simpa [Nat.sub_add_cancel hoff] using m1_w39 ⟨n - 59450, hnfin⟩
                                                                                ·
                                                                                  by_cases h40 : n < 59550
                                                                                  · have hoff : 59500 ≤ n := by omega
                                                                                    have hnfin : n - 59500 < 50 := by omega
                                                                                    simpa [Nat.sub_add_cancel hoff] using m1_w40 ⟨n - 59500, hnfin⟩
                                                                                  ·
                                                                                    by_cases h41 : n < 59600
                                                                                    · have hoff : 59550 ≤ n := by omega
                                                                                      have hnfin : n - 59550 < 50 := by omega
                                                                                      simpa [Nat.sub_add_cancel hoff] using m1_w41 ⟨n - 59550, hnfin⟩
                                                                                    ·
                                                                                      by_cases h42 : n < 59650
                                                                                      · have hoff : 59600 ≤ n := by omega
                                                                                        have hnfin : n - 59600 < 50 := by omega
                                                                                        simpa [Nat.sub_add_cancel hoff] using m1_w42 ⟨n - 59600, hnfin⟩
                                                                                      ·
                                                                                        by_cases h43 : n < 59700
                                                                                        · have hoff : 59650 ≤ n := by omega
                                                                                          have hnfin : n - 59650 < 50 := by omega
                                                                                          simpa [Nat.sub_add_cancel hoff] using m1_w43 ⟨n - 59650, hnfin⟩
                                                                                        ·
                                                                                          by_cases h44 : n < 59750
                                                                                          · have hoff : 59700 ≤ n := by omega
                                                                                            have hnfin : n - 59700 < 50 := by omega
                                                                                            simpa [Nat.sub_add_cancel hoff] using m1_w44 ⟨n - 59700, hnfin⟩
                                                                                          ·
                                                                                            by_cases h45 : n < 59800
                                                                                            · have hoff : 59750 ≤ n := by omega
                                                                                              have hnfin : n - 59750 < 50 := by omega
                                                                                              simpa [Nat.sub_add_cancel hoff] using m1_w45 ⟨n - 59750, hnfin⟩
                                                                                            ·
                                                                                              by_cases h46 : n < 59850
                                                                                              · have hoff : 59800 ≤ n := by omega
                                                                                                have hnfin : n - 59800 < 50 := by omega
                                                                                                simpa [Nat.sub_add_cancel hoff] using m1_w46 ⟨n - 59800, hnfin⟩
                                                                                              ·
                                                                                                by_cases h47 : n < 59900
                                                                                                · have hoff : 59850 ≤ n := by omega
                                                                                                  have hnfin : n - 59850 < 50 := by omega
                                                                                                  simpa [Nat.sub_add_cancel hoff] using m1_w47 ⟨n - 59850, hnfin⟩
                                                                                                ·
                                                                                                  by_cases h48 : n < 59950
                                                                                                  · have hoff : 59900 ≤ n := by omega
                                                                                                    have hnfin : n - 59900 < 50 := by omega
                                                                                                    simpa [Nat.sub_add_cancel hoff] using m1_w48 ⟨n - 59900, hnfin⟩
                                                                                                  ·
                                                                                                    by_cases h49 : n < 60000
                                                                                                    · have hoff : 59950 ≤ n := by omega
                                                                                                      have hnfin : n - 59950 < 50 := by omega
                                                                                                      simpa [Nat.sub_add_cancel hoff] using m1_w49 ⟨n - 59950, hnfin⟩
                                                                                                    ·
                                                                                                      omega
end IntMul.Kappa.R8.Bit.Oppbank.LandMonoFixA23


