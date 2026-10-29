-- Prove2me | Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankLandMonoFixA9
-- name    : IntMul_Kappa_R8_Data_BitOppbankLandMonoFixA9
-- status  : Definition
-- author  : @Ethan Cheung Wang
-- created : 2026-10-28T21:15:31.947704+00:00
-- url     : https://prove2.me/theorems/4a9b9494-978f-445c-948c-dbb0e068a14c
-- title:
--   Dim-gated densSup land mono FixA pack 9
-- statement:
--   # Dim-gated densSup land (PndFix), pack A9
--
--   Range consolidators for $n\in[22500,25000)$.
-- source:
--   R8 BitOppbank PndFix

-- LandMonoFixA9: PUBLIC dim-gated land + range consolidators (PndFix)
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
namespace IntMul.Kappa.R8.Bit.Oppbank.LandMonoFixA9
def arg0 (n : ℕ) : ℕ := Nat.land (argF n) 65535
def arg1 (n : ℕ) : ℕ := Nat.shiftRight (argF n) 16
theorem m0_w0 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 22500))) (dimF (n.val + 22500)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 22500))) (densSupG (n.val + 22500))) (densSupG (arg0 (n.val + 22500)))) = true := by decide
theorem m1_w0 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 22500))) (dimF (n.val + 22500)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 22500))) (densSupG (n.val + 22500))) (densSupG (arg1 (n.val + 22500)))) = true := by decide
theorem m0_w1 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 22550))) (dimF (n.val + 22550)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 22550))) (densSupG (n.val + 22550))) (densSupG (arg0 (n.val + 22550)))) = true := by decide
theorem m1_w1 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 22550))) (dimF (n.val + 22550)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 22550))) (densSupG (n.val + 22550))) (densSupG (arg1 (n.val + 22550)))) = true := by decide
theorem m0_w2 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 22600))) (dimF (n.val + 22600)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 22600))) (densSupG (n.val + 22600))) (densSupG (arg0 (n.val + 22600)))) = true := by decide
theorem m1_w2 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 22600))) (dimF (n.val + 22600)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 22600))) (densSupG (n.val + 22600))) (densSupG (arg1 (n.val + 22600)))) = true := by decide
theorem m0_w3 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 22650))) (dimF (n.val + 22650)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 22650))) (densSupG (n.val + 22650))) (densSupG (arg0 (n.val + 22650)))) = true := by decide
theorem m1_w3 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 22650))) (dimF (n.val + 22650)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 22650))) (densSupG (n.val + 22650))) (densSupG (arg1 (n.val + 22650)))) = true := by decide
theorem m0_w4 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 22700))) (dimF (n.val + 22700)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 22700))) (densSupG (n.val + 22700))) (densSupG (arg0 (n.val + 22700)))) = true := by decide
theorem m1_w4 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 22700))) (dimF (n.val + 22700)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 22700))) (densSupG (n.val + 22700))) (densSupG (arg1 (n.val + 22700)))) = true := by decide
theorem m0_w5 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 22750))) (dimF (n.val + 22750)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 22750))) (densSupG (n.val + 22750))) (densSupG (arg0 (n.val + 22750)))) = true := by decide
theorem m1_w5 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 22750))) (dimF (n.val + 22750)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 22750))) (densSupG (n.val + 22750))) (densSupG (arg1 (n.val + 22750)))) = true := by decide
theorem m0_w6 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 22800))) (dimF (n.val + 22800)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 22800))) (densSupG (n.val + 22800))) (densSupG (arg0 (n.val + 22800)))) = true := by decide
theorem m1_w6 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 22800))) (dimF (n.val + 22800)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 22800))) (densSupG (n.val + 22800))) (densSupG (arg1 (n.val + 22800)))) = true := by decide
theorem m0_w7 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 22850))) (dimF (n.val + 22850)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 22850))) (densSupG (n.val + 22850))) (densSupG (arg0 (n.val + 22850)))) = true := by decide
theorem m1_w7 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 22850))) (dimF (n.val + 22850)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 22850))) (densSupG (n.val + 22850))) (densSupG (arg1 (n.val + 22850)))) = true := by decide
theorem m0_w8 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 22900))) (dimF (n.val + 22900)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 22900))) (densSupG (n.val + 22900))) (densSupG (arg0 (n.val + 22900)))) = true := by decide
theorem m1_w8 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 22900))) (dimF (n.val + 22900)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 22900))) (densSupG (n.val + 22900))) (densSupG (arg1 (n.val + 22900)))) = true := by decide
theorem m0_w9 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 22950))) (dimF (n.val + 22950)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 22950))) (densSupG (n.val + 22950))) (densSupG (arg0 (n.val + 22950)))) = true := by decide
theorem m1_w9 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 22950))) (dimF (n.val + 22950)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 22950))) (densSupG (n.val + 22950))) (densSupG (arg1 (n.val + 22950)))) = true := by decide
theorem m0_w10 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 23000))) (dimF (n.val + 23000)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 23000))) (densSupG (n.val + 23000))) (densSupG (arg0 (n.val + 23000)))) = true := by decide
theorem m1_w10 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 23000))) (dimF (n.val + 23000)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 23000))) (densSupG (n.val + 23000))) (densSupG (arg1 (n.val + 23000)))) = true := by decide
theorem m0_w11 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 23050))) (dimF (n.val + 23050)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 23050))) (densSupG (n.val + 23050))) (densSupG (arg0 (n.val + 23050)))) = true := by decide
theorem m1_w11 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 23050))) (dimF (n.val + 23050)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 23050))) (densSupG (n.val + 23050))) (densSupG (arg1 (n.val + 23050)))) = true := by decide
theorem m0_w12 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 23100))) (dimF (n.val + 23100)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 23100))) (densSupG (n.val + 23100))) (densSupG (arg0 (n.val + 23100)))) = true := by decide
theorem m1_w12 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 23100))) (dimF (n.val + 23100)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 23100))) (densSupG (n.val + 23100))) (densSupG (arg1 (n.val + 23100)))) = true := by decide
theorem m0_w13 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 23150))) (dimF (n.val + 23150)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 23150))) (densSupG (n.val + 23150))) (densSupG (arg0 (n.val + 23150)))) = true := by decide
theorem m1_w13 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 23150))) (dimF (n.val + 23150)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 23150))) (densSupG (n.val + 23150))) (densSupG (arg1 (n.val + 23150)))) = true := by decide
theorem m0_w14 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 23200))) (dimF (n.val + 23200)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 23200))) (densSupG (n.val + 23200))) (densSupG (arg0 (n.val + 23200)))) = true := by decide
theorem m1_w14 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 23200))) (dimF (n.val + 23200)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 23200))) (densSupG (n.val + 23200))) (densSupG (arg1 (n.val + 23200)))) = true := by decide
theorem m0_w15 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 23250))) (dimF (n.val + 23250)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 23250))) (densSupG (n.val + 23250))) (densSupG (arg0 (n.val + 23250)))) = true := by decide
theorem m1_w15 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 23250))) (dimF (n.val + 23250)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 23250))) (densSupG (n.val + 23250))) (densSupG (arg1 (n.val + 23250)))) = true := by decide
theorem m0_w16 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 23300))) (dimF (n.val + 23300)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 23300))) (densSupG (n.val + 23300))) (densSupG (arg0 (n.val + 23300)))) = true := by decide
theorem m1_w16 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 23300))) (dimF (n.val + 23300)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 23300))) (densSupG (n.val + 23300))) (densSupG (arg1 (n.val + 23300)))) = true := by decide
theorem m0_w17 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 23350))) (dimF (n.val + 23350)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 23350))) (densSupG (n.val + 23350))) (densSupG (arg0 (n.val + 23350)))) = true := by decide
theorem m1_w17 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 23350))) (dimF (n.val + 23350)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 23350))) (densSupG (n.val + 23350))) (densSupG (arg1 (n.val + 23350)))) = true := by decide
theorem m0_w18 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 23400))) (dimF (n.val + 23400)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 23400))) (densSupG (n.val + 23400))) (densSupG (arg0 (n.val + 23400)))) = true := by decide
theorem m1_w18 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 23400))) (dimF (n.val + 23400)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 23400))) (densSupG (n.val + 23400))) (densSupG (arg1 (n.val + 23400)))) = true := by decide
theorem m0_w19 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 23450))) (dimF (n.val + 23450)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 23450))) (densSupG (n.val + 23450))) (densSupG (arg0 (n.val + 23450)))) = true := by decide
theorem m1_w19 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 23450))) (dimF (n.val + 23450)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 23450))) (densSupG (n.val + 23450))) (densSupG (arg1 (n.val + 23450)))) = true := by decide
theorem m0_w20 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 23500))) (dimF (n.val + 23500)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 23500))) (densSupG (n.val + 23500))) (densSupG (arg0 (n.val + 23500)))) = true := by decide
theorem m1_w20 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 23500))) (dimF (n.val + 23500)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 23500))) (densSupG (n.val + 23500))) (densSupG (arg1 (n.val + 23500)))) = true := by decide
theorem m0_w21 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 23550))) (dimF (n.val + 23550)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 23550))) (densSupG (n.val + 23550))) (densSupG (arg0 (n.val + 23550)))) = true := by decide
theorem m1_w21 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 23550))) (dimF (n.val + 23550)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 23550))) (densSupG (n.val + 23550))) (densSupG (arg1 (n.val + 23550)))) = true := by decide
theorem m0_w22 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 23600))) (dimF (n.val + 23600)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 23600))) (densSupG (n.val + 23600))) (densSupG (arg0 (n.val + 23600)))) = true := by decide
theorem m1_w22 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 23600))) (dimF (n.val + 23600)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 23600))) (densSupG (n.val + 23600))) (densSupG (arg1 (n.val + 23600)))) = true := by decide
theorem m0_w23 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 23650))) (dimF (n.val + 23650)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 23650))) (densSupG (n.val + 23650))) (densSupG (arg0 (n.val + 23650)))) = true := by decide
theorem m1_w23 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 23650))) (dimF (n.val + 23650)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 23650))) (densSupG (n.val + 23650))) (densSupG (arg1 (n.val + 23650)))) = true := by decide
theorem m0_w24 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 23700))) (dimF (n.val + 23700)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 23700))) (densSupG (n.val + 23700))) (densSupG (arg0 (n.val + 23700)))) = true := by decide
theorem m1_w24 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 23700))) (dimF (n.val + 23700)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 23700))) (densSupG (n.val + 23700))) (densSupG (arg1 (n.val + 23700)))) = true := by decide
theorem m0_w25 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 23750))) (dimF (n.val + 23750)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 23750))) (densSupG (n.val + 23750))) (densSupG (arg0 (n.val + 23750)))) = true := by decide
theorem m1_w25 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 23750))) (dimF (n.val + 23750)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 23750))) (densSupG (n.val + 23750))) (densSupG (arg1 (n.val + 23750)))) = true := by decide
theorem m0_w26 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 23800))) (dimF (n.val + 23800)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 23800))) (densSupG (n.val + 23800))) (densSupG (arg0 (n.val + 23800)))) = true := by decide
theorem m1_w26 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 23800))) (dimF (n.val + 23800)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 23800))) (densSupG (n.val + 23800))) (densSupG (arg1 (n.val + 23800)))) = true := by decide
theorem m0_w27 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 23850))) (dimF (n.val + 23850)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 23850))) (densSupG (n.val + 23850))) (densSupG (arg0 (n.val + 23850)))) = true := by decide
theorem m1_w27 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 23850))) (dimF (n.val + 23850)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 23850))) (densSupG (n.val + 23850))) (densSupG (arg1 (n.val + 23850)))) = true := by decide
theorem m0_w28 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 23900))) (dimF (n.val + 23900)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 23900))) (densSupG (n.val + 23900))) (densSupG (arg0 (n.val + 23900)))) = true := by decide
theorem m1_w28 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 23900))) (dimF (n.val + 23900)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 23900))) (densSupG (n.val + 23900))) (densSupG (arg1 (n.val + 23900)))) = true := by decide
theorem m0_w29 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 23950))) (dimF (n.val + 23950)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 23950))) (densSupG (n.val + 23950))) (densSupG (arg0 (n.val + 23950)))) = true := by decide
theorem m1_w29 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 23950))) (dimF (n.val + 23950)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 23950))) (densSupG (n.val + 23950))) (densSupG (arg1 (n.val + 23950)))) = true := by decide
theorem m0_w30 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 24000))) (dimF (n.val + 24000)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 24000))) (densSupG (n.val + 24000))) (densSupG (arg0 (n.val + 24000)))) = true := by decide
theorem m1_w30 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 24000))) (dimF (n.val + 24000)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 24000))) (densSupG (n.val + 24000))) (densSupG (arg1 (n.val + 24000)))) = true := by decide
theorem m0_w31 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 24050))) (dimF (n.val + 24050)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 24050))) (densSupG (n.val + 24050))) (densSupG (arg0 (n.val + 24050)))) = true := by decide
theorem m1_w31 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 24050))) (dimF (n.val + 24050)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 24050))) (densSupG (n.val + 24050))) (densSupG (arg1 (n.val + 24050)))) = true := by decide
theorem m0_w32 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 24100))) (dimF (n.val + 24100)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 24100))) (densSupG (n.val + 24100))) (densSupG (arg0 (n.val + 24100)))) = true := by decide
theorem m1_w32 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 24100))) (dimF (n.val + 24100)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 24100))) (densSupG (n.val + 24100))) (densSupG (arg1 (n.val + 24100)))) = true := by decide
theorem m0_w33 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 24150))) (dimF (n.val + 24150)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 24150))) (densSupG (n.val + 24150))) (densSupG (arg0 (n.val + 24150)))) = true := by decide
theorem m1_w33 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 24150))) (dimF (n.val + 24150)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 24150))) (densSupG (n.val + 24150))) (densSupG (arg1 (n.val + 24150)))) = true := by decide
theorem m0_w34 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 24200))) (dimF (n.val + 24200)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 24200))) (densSupG (n.val + 24200))) (densSupG (arg0 (n.val + 24200)))) = true := by decide
theorem m1_w34 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 24200))) (dimF (n.val + 24200)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 24200))) (densSupG (n.val + 24200))) (densSupG (arg1 (n.val + 24200)))) = true := by decide
theorem m0_w35 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 24250))) (dimF (n.val + 24250)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 24250))) (densSupG (n.val + 24250))) (densSupG (arg0 (n.val + 24250)))) = true := by decide
theorem m1_w35 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 24250))) (dimF (n.val + 24250)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 24250))) (densSupG (n.val + 24250))) (densSupG (arg1 (n.val + 24250)))) = true := by decide
theorem m0_w36 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 24300))) (dimF (n.val + 24300)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 24300))) (densSupG (n.val + 24300))) (densSupG (arg0 (n.val + 24300)))) = true := by decide
theorem m1_w36 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 24300))) (dimF (n.val + 24300)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 24300))) (densSupG (n.val + 24300))) (densSupG (arg1 (n.val + 24300)))) = true := by decide
theorem m0_w37 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 24350))) (dimF (n.val + 24350)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 24350))) (densSupG (n.val + 24350))) (densSupG (arg0 (n.val + 24350)))) = true := by decide
theorem m1_w37 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 24350))) (dimF (n.val + 24350)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 24350))) (densSupG (n.val + 24350))) (densSupG (arg1 (n.val + 24350)))) = true := by decide
theorem m0_w38 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 24400))) (dimF (n.val + 24400)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 24400))) (densSupG (n.val + 24400))) (densSupG (arg0 (n.val + 24400)))) = true := by decide
theorem m1_w38 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 24400))) (dimF (n.val + 24400)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 24400))) (densSupG (n.val + 24400))) (densSupG (arg1 (n.val + 24400)))) = true := by decide
theorem m0_w39 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 24450))) (dimF (n.val + 24450)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 24450))) (densSupG (n.val + 24450))) (densSupG (arg0 (n.val + 24450)))) = true := by decide
theorem m1_w39 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 24450))) (dimF (n.val + 24450)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 24450))) (densSupG (n.val + 24450))) (densSupG (arg1 (n.val + 24450)))) = true := by decide
theorem m0_w40 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 24500))) (dimF (n.val + 24500)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 24500))) (densSupG (n.val + 24500))) (densSupG (arg0 (n.val + 24500)))) = true := by decide
theorem m1_w40 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 24500))) (dimF (n.val + 24500)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 24500))) (densSupG (n.val + 24500))) (densSupG (arg1 (n.val + 24500)))) = true := by decide
theorem m0_w41 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 24550))) (dimF (n.val + 24550)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 24550))) (densSupG (n.val + 24550))) (densSupG (arg0 (n.val + 24550)))) = true := by decide
theorem m1_w41 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 24550))) (dimF (n.val + 24550)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 24550))) (densSupG (n.val + 24550))) (densSupG (arg1 (n.val + 24550)))) = true := by decide
theorem m0_w42 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 24600))) (dimF (n.val + 24600)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 24600))) (densSupG (n.val + 24600))) (densSupG (arg0 (n.val + 24600)))) = true := by decide
theorem m1_w42 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 24600))) (dimF (n.val + 24600)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 24600))) (densSupG (n.val + 24600))) (densSupG (arg1 (n.val + 24600)))) = true := by decide
theorem m0_w43 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 24650))) (dimF (n.val + 24650)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 24650))) (densSupG (n.val + 24650))) (densSupG (arg0 (n.val + 24650)))) = true := by decide
theorem m1_w43 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 24650))) (dimF (n.val + 24650)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 24650))) (densSupG (n.val + 24650))) (densSupG (arg1 (n.val + 24650)))) = true := by decide
theorem m0_w44 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 24700))) (dimF (n.val + 24700)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 24700))) (densSupG (n.val + 24700))) (densSupG (arg0 (n.val + 24700)))) = true := by decide
theorem m1_w44 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 24700))) (dimF (n.val + 24700)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 24700))) (densSupG (n.val + 24700))) (densSupG (arg1 (n.val + 24700)))) = true := by decide
theorem m0_w45 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 24750))) (dimF (n.val + 24750)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 24750))) (densSupG (n.val + 24750))) (densSupG (arg0 (n.val + 24750)))) = true := by decide
theorem m1_w45 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 24750))) (dimF (n.val + 24750)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 24750))) (densSupG (n.val + 24750))) (densSupG (arg1 (n.val + 24750)))) = true := by decide
theorem m0_w46 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 24800))) (dimF (n.val + 24800)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 24800))) (densSupG (n.val + 24800))) (densSupG (arg0 (n.val + 24800)))) = true := by decide
theorem m1_w46 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 24800))) (dimF (n.val + 24800)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 24800))) (densSupG (n.val + 24800))) (densSupG (arg1 (n.val + 24800)))) = true := by decide
theorem m0_w47 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 24850))) (dimF (n.val + 24850)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 24850))) (densSupG (n.val + 24850))) (densSupG (arg0 (n.val + 24850)))) = true := by decide
theorem m1_w47 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 24850))) (dimF (n.val + 24850)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 24850))) (densSupG (n.val + 24850))) (densSupG (arg1 (n.val + 24850)))) = true := by decide
theorem m0_w48 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 24900))) (dimF (n.val + 24900)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 24900))) (densSupG (n.val + 24900))) (densSupG (arg0 (n.val + 24900)))) = true := by decide
theorem m1_w48 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 24900))) (dimF (n.val + 24900)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 24900))) (densSupG (n.val + 24900))) (densSupG (arg1 (n.val + 24900)))) = true := by decide
theorem m0_w49 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 24950))) (dimF (n.val + 24950)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 24950))) (densSupG (n.val + 24950))) (densSupG (arg0 (n.val + 24950)))) = true := by decide
theorem m1_w49 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 24950))) (dimF (n.val + 24950)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 24950))) (densSupG (n.val + 24950))) (densSupG (arg1 (n.val + 24950)))) = true := by decide
theorem land0_range (n : ℕ) (hn0 : 22500 ≤ n) (hn1 : n < 25000) :
    (!Nat.blt (dimF (arg0 n)) (dimF n) ||
      Nat.beq (Nat.land (densSupG (arg0 n)) (densSupG n)) (densSupG (arg0 n))) = true := by
  by_cases h0 : n < 22550
  · have hoff : 22500 ≤ n := by omega
    have hnfin : n - 22500 < 50 := by omega
    simpa [Nat.sub_add_cancel hoff] using m0_w0 ⟨n - 22500, hnfin⟩
  ·
    by_cases h1 : n < 22600
    · have hoff : 22550 ≤ n := by omega
      have hnfin : n - 22550 < 50 := by omega
      simpa [Nat.sub_add_cancel hoff] using m0_w1 ⟨n - 22550, hnfin⟩
    ·
      by_cases h2 : n < 22650
      · have hoff : 22600 ≤ n := by omega
        have hnfin : n - 22600 < 50 := by omega
        simpa [Nat.sub_add_cancel hoff] using m0_w2 ⟨n - 22600, hnfin⟩
      ·
        by_cases h3 : n < 22700
        · have hoff : 22650 ≤ n := by omega
          have hnfin : n - 22650 < 50 := by omega
          simpa [Nat.sub_add_cancel hoff] using m0_w3 ⟨n - 22650, hnfin⟩
        ·
          by_cases h4 : n < 22750
          · have hoff : 22700 ≤ n := by omega
            have hnfin : n - 22700 < 50 := by omega
            simpa [Nat.sub_add_cancel hoff] using m0_w4 ⟨n - 22700, hnfin⟩
          ·
            by_cases h5 : n < 22800
            · have hoff : 22750 ≤ n := by omega
              have hnfin : n - 22750 < 50 := by omega
              simpa [Nat.sub_add_cancel hoff] using m0_w5 ⟨n - 22750, hnfin⟩
            ·
              by_cases h6 : n < 22850
              · have hoff : 22800 ≤ n := by omega
                have hnfin : n - 22800 < 50 := by omega
                simpa [Nat.sub_add_cancel hoff] using m0_w6 ⟨n - 22800, hnfin⟩
              ·
                by_cases h7 : n < 22900
                · have hoff : 22850 ≤ n := by omega
                  have hnfin : n - 22850 < 50 := by omega
                  simpa [Nat.sub_add_cancel hoff] using m0_w7 ⟨n - 22850, hnfin⟩
                ·
                  by_cases h8 : n < 22950
                  · have hoff : 22900 ≤ n := by omega
                    have hnfin : n - 22900 < 50 := by omega
                    simpa [Nat.sub_add_cancel hoff] using m0_w8 ⟨n - 22900, hnfin⟩
                  ·
                    by_cases h9 : n < 23000
                    · have hoff : 22950 ≤ n := by omega
                      have hnfin : n - 22950 < 50 := by omega
                      simpa [Nat.sub_add_cancel hoff] using m0_w9 ⟨n - 22950, hnfin⟩
                    ·
                      by_cases h10 : n < 23050
                      · have hoff : 23000 ≤ n := by omega
                        have hnfin : n - 23000 < 50 := by omega
                        simpa [Nat.sub_add_cancel hoff] using m0_w10 ⟨n - 23000, hnfin⟩
                      ·
                        by_cases h11 : n < 23100
                        · have hoff : 23050 ≤ n := by omega
                          have hnfin : n - 23050 < 50 := by omega
                          simpa [Nat.sub_add_cancel hoff] using m0_w11 ⟨n - 23050, hnfin⟩
                        ·
                          by_cases h12 : n < 23150
                          · have hoff : 23100 ≤ n := by omega
                            have hnfin : n - 23100 < 50 := by omega
                            simpa [Nat.sub_add_cancel hoff] using m0_w12 ⟨n - 23100, hnfin⟩
                          ·
                            by_cases h13 : n < 23200
                            · have hoff : 23150 ≤ n := by omega
                              have hnfin : n - 23150 < 50 := by omega
                              simpa [Nat.sub_add_cancel hoff] using m0_w13 ⟨n - 23150, hnfin⟩
                            ·
                              by_cases h14 : n < 23250
                              · have hoff : 23200 ≤ n := by omega
                                have hnfin : n - 23200 < 50 := by omega
                                simpa [Nat.sub_add_cancel hoff] using m0_w14 ⟨n - 23200, hnfin⟩
                              ·
                                by_cases h15 : n < 23300
                                · have hoff : 23250 ≤ n := by omega
                                  have hnfin : n - 23250 < 50 := by omega
                                  simpa [Nat.sub_add_cancel hoff] using m0_w15 ⟨n - 23250, hnfin⟩
                                ·
                                  by_cases h16 : n < 23350
                                  · have hoff : 23300 ≤ n := by omega
                                    have hnfin : n - 23300 < 50 := by omega
                                    simpa [Nat.sub_add_cancel hoff] using m0_w16 ⟨n - 23300, hnfin⟩
                                  ·
                                    by_cases h17 : n < 23400
                                    · have hoff : 23350 ≤ n := by omega
                                      have hnfin : n - 23350 < 50 := by omega
                                      simpa [Nat.sub_add_cancel hoff] using m0_w17 ⟨n - 23350, hnfin⟩
                                    ·
                                      by_cases h18 : n < 23450
                                      · have hoff : 23400 ≤ n := by omega
                                        have hnfin : n - 23400 < 50 := by omega
                                        simpa [Nat.sub_add_cancel hoff] using m0_w18 ⟨n - 23400, hnfin⟩
                                      ·
                                        by_cases h19 : n < 23500
                                        · have hoff : 23450 ≤ n := by omega
                                          have hnfin : n - 23450 < 50 := by omega
                                          simpa [Nat.sub_add_cancel hoff] using m0_w19 ⟨n - 23450, hnfin⟩
                                        ·
                                          by_cases h20 : n < 23550
                                          · have hoff : 23500 ≤ n := by omega
                                            have hnfin : n - 23500 < 50 := by omega
                                            simpa [Nat.sub_add_cancel hoff] using m0_w20 ⟨n - 23500, hnfin⟩
                                          ·
                                            by_cases h21 : n < 23600
                                            · have hoff : 23550 ≤ n := by omega
                                              have hnfin : n - 23550 < 50 := by omega
                                              simpa [Nat.sub_add_cancel hoff] using m0_w21 ⟨n - 23550, hnfin⟩
                                            ·
                                              by_cases h22 : n < 23650
                                              · have hoff : 23600 ≤ n := by omega
                                                have hnfin : n - 23600 < 50 := by omega
                                                simpa [Nat.sub_add_cancel hoff] using m0_w22 ⟨n - 23600, hnfin⟩
                                              ·
                                                by_cases h23 : n < 23700
                                                · have hoff : 23650 ≤ n := by omega
                                                  have hnfin : n - 23650 < 50 := by omega
                                                  simpa [Nat.sub_add_cancel hoff] using m0_w23 ⟨n - 23650, hnfin⟩
                                                ·
                                                  by_cases h24 : n < 23750
                                                  · have hoff : 23700 ≤ n := by omega
                                                    have hnfin : n - 23700 < 50 := by omega
                                                    simpa [Nat.sub_add_cancel hoff] using m0_w24 ⟨n - 23700, hnfin⟩
                                                  ·
                                                    by_cases h25 : n < 23800
                                                    · have hoff : 23750 ≤ n := by omega
                                                      have hnfin : n - 23750 < 50 := by omega
                                                      simpa [Nat.sub_add_cancel hoff] using m0_w25 ⟨n - 23750, hnfin⟩
                                                    ·
                                                      by_cases h26 : n < 23850
                                                      · have hoff : 23800 ≤ n := by omega
                                                        have hnfin : n - 23800 < 50 := by omega
                                                        simpa [Nat.sub_add_cancel hoff] using m0_w26 ⟨n - 23800, hnfin⟩
                                                      ·
                                                        by_cases h27 : n < 23900
                                                        · have hoff : 23850 ≤ n := by omega
                                                          have hnfin : n - 23850 < 50 := by omega
                                                          simpa [Nat.sub_add_cancel hoff] using m0_w27 ⟨n - 23850, hnfin⟩
                                                        ·
                                                          by_cases h28 : n < 23950
                                                          · have hoff : 23900 ≤ n := by omega
                                                            have hnfin : n - 23900 < 50 := by omega
                                                            simpa [Nat.sub_add_cancel hoff] using m0_w28 ⟨n - 23900, hnfin⟩
                                                          ·
                                                            by_cases h29 : n < 24000
                                                            · have hoff : 23950 ≤ n := by omega
                                                              have hnfin : n - 23950 < 50 := by omega
                                                              simpa [Nat.sub_add_cancel hoff] using m0_w29 ⟨n - 23950, hnfin⟩
                                                            ·
                                                              by_cases h30 : n < 24050
                                                              · have hoff : 24000 ≤ n := by omega
                                                                have hnfin : n - 24000 < 50 := by omega
                                                                simpa [Nat.sub_add_cancel hoff] using m0_w30 ⟨n - 24000, hnfin⟩
                                                              ·
                                                                by_cases h31 : n < 24100
                                                                · have hoff : 24050 ≤ n := by omega
                                                                  have hnfin : n - 24050 < 50 := by omega
                                                                  simpa [Nat.sub_add_cancel hoff] using m0_w31 ⟨n - 24050, hnfin⟩
                                                                ·
                                                                  by_cases h32 : n < 24150
                                                                  · have hoff : 24100 ≤ n := by omega
                                                                    have hnfin : n - 24100 < 50 := by omega
                                                                    simpa [Nat.sub_add_cancel hoff] using m0_w32 ⟨n - 24100, hnfin⟩
                                                                  ·
                                                                    by_cases h33 : n < 24200
                                                                    · have hoff : 24150 ≤ n := by omega
                                                                      have hnfin : n - 24150 < 50 := by omega
                                                                      simpa [Nat.sub_add_cancel hoff] using m0_w33 ⟨n - 24150, hnfin⟩
                                                                    ·
                                                                      by_cases h34 : n < 24250
                                                                      · have hoff : 24200 ≤ n := by omega
                                                                        have hnfin : n - 24200 < 50 := by omega
                                                                        simpa [Nat.sub_add_cancel hoff] using m0_w34 ⟨n - 24200, hnfin⟩
                                                                      ·
                                                                        by_cases h35 : n < 24300
                                                                        · have hoff : 24250 ≤ n := by omega
                                                                          have hnfin : n - 24250 < 50 := by omega
                                                                          simpa [Nat.sub_add_cancel hoff] using m0_w35 ⟨n - 24250, hnfin⟩
                                                                        ·
                                                                          by_cases h36 : n < 24350
                                                                          · have hoff : 24300 ≤ n := by omega
                                                                            have hnfin : n - 24300 < 50 := by omega
                                                                            simpa [Nat.sub_add_cancel hoff] using m0_w36 ⟨n - 24300, hnfin⟩
                                                                          ·
                                                                            by_cases h37 : n < 24400
                                                                            · have hoff : 24350 ≤ n := by omega
                                                                              have hnfin : n - 24350 < 50 := by omega
                                                                              simpa [Nat.sub_add_cancel hoff] using m0_w37 ⟨n - 24350, hnfin⟩
                                                                            ·
                                                                              by_cases h38 : n < 24450
                                                                              · have hoff : 24400 ≤ n := by omega
                                                                                have hnfin : n - 24400 < 50 := by omega
                                                                                simpa [Nat.sub_add_cancel hoff] using m0_w38 ⟨n - 24400, hnfin⟩
                                                                              ·
                                                                                by_cases h39 : n < 24500
                                                                                · have hoff : 24450 ≤ n := by omega
                                                                                  have hnfin : n - 24450 < 50 := by omega
                                                                                  simpa [Nat.sub_add_cancel hoff] using m0_w39 ⟨n - 24450, hnfin⟩
                                                                                ·
                                                                                  by_cases h40 : n < 24550
                                                                                  · have hoff : 24500 ≤ n := by omega
                                                                                    have hnfin : n - 24500 < 50 := by omega
                                                                                    simpa [Nat.sub_add_cancel hoff] using m0_w40 ⟨n - 24500, hnfin⟩
                                                                                  ·
                                                                                    by_cases h41 : n < 24600
                                                                                    · have hoff : 24550 ≤ n := by omega
                                                                                      have hnfin : n - 24550 < 50 := by omega
                                                                                      simpa [Nat.sub_add_cancel hoff] using m0_w41 ⟨n - 24550, hnfin⟩
                                                                                    ·
                                                                                      by_cases h42 : n < 24650
                                                                                      · have hoff : 24600 ≤ n := by omega
                                                                                        have hnfin : n - 24600 < 50 := by omega
                                                                                        simpa [Nat.sub_add_cancel hoff] using m0_w42 ⟨n - 24600, hnfin⟩
                                                                                      ·
                                                                                        by_cases h43 : n < 24700
                                                                                        · have hoff : 24650 ≤ n := by omega
                                                                                          have hnfin : n - 24650 < 50 := by omega
                                                                                          simpa [Nat.sub_add_cancel hoff] using m0_w43 ⟨n - 24650, hnfin⟩
                                                                                        ·
                                                                                          by_cases h44 : n < 24750
                                                                                          · have hoff : 24700 ≤ n := by omega
                                                                                            have hnfin : n - 24700 < 50 := by omega
                                                                                            simpa [Nat.sub_add_cancel hoff] using m0_w44 ⟨n - 24700, hnfin⟩
                                                                                          ·
                                                                                            by_cases h45 : n < 24800
                                                                                            · have hoff : 24750 ≤ n := by omega
                                                                                              have hnfin : n - 24750 < 50 := by omega
                                                                                              simpa [Nat.sub_add_cancel hoff] using m0_w45 ⟨n - 24750, hnfin⟩
                                                                                            ·
                                                                                              by_cases h46 : n < 24850
                                                                                              · have hoff : 24800 ≤ n := by omega
                                                                                                have hnfin : n - 24800 < 50 := by omega
                                                                                                simpa [Nat.sub_add_cancel hoff] using m0_w46 ⟨n - 24800, hnfin⟩
                                                                                              ·
                                                                                                by_cases h47 : n < 24900
                                                                                                · have hoff : 24850 ≤ n := by omega
                                                                                                  have hnfin : n - 24850 < 50 := by omega
                                                                                                  simpa [Nat.sub_add_cancel hoff] using m0_w47 ⟨n - 24850, hnfin⟩
                                                                                                ·
                                                                                                  by_cases h48 : n < 24950
                                                                                                  · have hoff : 24900 ≤ n := by omega
                                                                                                    have hnfin : n - 24900 < 50 := by omega
                                                                                                    simpa [Nat.sub_add_cancel hoff] using m0_w48 ⟨n - 24900, hnfin⟩
                                                                                                  ·
                                                                                                    by_cases h49 : n < 25000
                                                                                                    · have hoff : 24950 ≤ n := by omega
                                                                                                      have hnfin : n - 24950 < 50 := by omega
                                                                                                      simpa [Nat.sub_add_cancel hoff] using m0_w49 ⟨n - 24950, hnfin⟩
                                                                                                    ·
                                                                                                      omega
theorem land1_range (n : ℕ) (hn0 : 22500 ≤ n) (hn1 : n < 25000) :
    (!Nat.blt (dimF (arg1 n)) (dimF n) ||
      Nat.beq (Nat.land (densSupG (arg1 n)) (densSupG n)) (densSupG (arg1 n))) = true := by
  by_cases h0 : n < 22550
  · have hoff : 22500 ≤ n := by omega
    have hnfin : n - 22500 < 50 := by omega
    simpa [Nat.sub_add_cancel hoff] using m1_w0 ⟨n - 22500, hnfin⟩
  ·
    by_cases h1 : n < 22600
    · have hoff : 22550 ≤ n := by omega
      have hnfin : n - 22550 < 50 := by omega
      simpa [Nat.sub_add_cancel hoff] using m1_w1 ⟨n - 22550, hnfin⟩
    ·
      by_cases h2 : n < 22650
      · have hoff : 22600 ≤ n := by omega
        have hnfin : n - 22600 < 50 := by omega
        simpa [Nat.sub_add_cancel hoff] using m1_w2 ⟨n - 22600, hnfin⟩
      ·
        by_cases h3 : n < 22700
        · have hoff : 22650 ≤ n := by omega
          have hnfin : n - 22650 < 50 := by omega
          simpa [Nat.sub_add_cancel hoff] using m1_w3 ⟨n - 22650, hnfin⟩
        ·
          by_cases h4 : n < 22750
          · have hoff : 22700 ≤ n := by omega
            have hnfin : n - 22700 < 50 := by omega
            simpa [Nat.sub_add_cancel hoff] using m1_w4 ⟨n - 22700, hnfin⟩
          ·
            by_cases h5 : n < 22800
            · have hoff : 22750 ≤ n := by omega
              have hnfin : n - 22750 < 50 := by omega
              simpa [Nat.sub_add_cancel hoff] using m1_w5 ⟨n - 22750, hnfin⟩
            ·
              by_cases h6 : n < 22850
              · have hoff : 22800 ≤ n := by omega
                have hnfin : n - 22800 < 50 := by omega
                simpa [Nat.sub_add_cancel hoff] using m1_w6 ⟨n - 22800, hnfin⟩
              ·
                by_cases h7 : n < 22900
                · have hoff : 22850 ≤ n := by omega
                  have hnfin : n - 22850 < 50 := by omega
                  simpa [Nat.sub_add_cancel hoff] using m1_w7 ⟨n - 22850, hnfin⟩
                ·
                  by_cases h8 : n < 22950
                  · have hoff : 22900 ≤ n := by omega
                    have hnfin : n - 22900 < 50 := by omega
                    simpa [Nat.sub_add_cancel hoff] using m1_w8 ⟨n - 22900, hnfin⟩
                  ·
                    by_cases h9 : n < 23000
                    · have hoff : 22950 ≤ n := by omega
                      have hnfin : n - 22950 < 50 := by omega
                      simpa [Nat.sub_add_cancel hoff] using m1_w9 ⟨n - 22950, hnfin⟩
                    ·
                      by_cases h10 : n < 23050
                      · have hoff : 23000 ≤ n := by omega
                        have hnfin : n - 23000 < 50 := by omega
                        simpa [Nat.sub_add_cancel hoff] using m1_w10 ⟨n - 23000, hnfin⟩
                      ·
                        by_cases h11 : n < 23100
                        · have hoff : 23050 ≤ n := by omega
                          have hnfin : n - 23050 < 50 := by omega
                          simpa [Nat.sub_add_cancel hoff] using m1_w11 ⟨n - 23050, hnfin⟩
                        ·
                          by_cases h12 : n < 23150
                          · have hoff : 23100 ≤ n := by omega
                            have hnfin : n - 23100 < 50 := by omega
                            simpa [Nat.sub_add_cancel hoff] using m1_w12 ⟨n - 23100, hnfin⟩
                          ·
                            by_cases h13 : n < 23200
                            · have hoff : 23150 ≤ n := by omega
                              have hnfin : n - 23150 < 50 := by omega
                              simpa [Nat.sub_add_cancel hoff] using m1_w13 ⟨n - 23150, hnfin⟩
                            ·
                              by_cases h14 : n < 23250
                              · have hoff : 23200 ≤ n := by omega
                                have hnfin : n - 23200 < 50 := by omega
                                simpa [Nat.sub_add_cancel hoff] using m1_w14 ⟨n - 23200, hnfin⟩
                              ·
                                by_cases h15 : n < 23300
                                · have hoff : 23250 ≤ n := by omega
                                  have hnfin : n - 23250 < 50 := by omega
                                  simpa [Nat.sub_add_cancel hoff] using m1_w15 ⟨n - 23250, hnfin⟩
                                ·
                                  by_cases h16 : n < 23350
                                  · have hoff : 23300 ≤ n := by omega
                                    have hnfin : n - 23300 < 50 := by omega
                                    simpa [Nat.sub_add_cancel hoff] using m1_w16 ⟨n - 23300, hnfin⟩
                                  ·
                                    by_cases h17 : n < 23400
                                    · have hoff : 23350 ≤ n := by omega
                                      have hnfin : n - 23350 < 50 := by omega
                                      simpa [Nat.sub_add_cancel hoff] using m1_w17 ⟨n - 23350, hnfin⟩
                                    ·
                                      by_cases h18 : n < 23450
                                      · have hoff : 23400 ≤ n := by omega
                                        have hnfin : n - 23400 < 50 := by omega
                                        simpa [Nat.sub_add_cancel hoff] using m1_w18 ⟨n - 23400, hnfin⟩
                                      ·
                                        by_cases h19 : n < 23500
                                        · have hoff : 23450 ≤ n := by omega
                                          have hnfin : n - 23450 < 50 := by omega
                                          simpa [Nat.sub_add_cancel hoff] using m1_w19 ⟨n - 23450, hnfin⟩
                                        ·
                                          by_cases h20 : n < 23550
                                          · have hoff : 23500 ≤ n := by omega
                                            have hnfin : n - 23500 < 50 := by omega
                                            simpa [Nat.sub_add_cancel hoff] using m1_w20 ⟨n - 23500, hnfin⟩
                                          ·
                                            by_cases h21 : n < 23600
                                            · have hoff : 23550 ≤ n := by omega
                                              have hnfin : n - 23550 < 50 := by omega
                                              simpa [Nat.sub_add_cancel hoff] using m1_w21 ⟨n - 23550, hnfin⟩
                                            ·
                                              by_cases h22 : n < 23650
                                              · have hoff : 23600 ≤ n := by omega
                                                have hnfin : n - 23600 < 50 := by omega
                                                simpa [Nat.sub_add_cancel hoff] using m1_w22 ⟨n - 23600, hnfin⟩
                                              ·
                                                by_cases h23 : n < 23700
                                                · have hoff : 23650 ≤ n := by omega
                                                  have hnfin : n - 23650 < 50 := by omega
                                                  simpa [Nat.sub_add_cancel hoff] using m1_w23 ⟨n - 23650, hnfin⟩
                                                ·
                                                  by_cases h24 : n < 23750
                                                  · have hoff : 23700 ≤ n := by omega
                                                    have hnfin : n - 23700 < 50 := by omega
                                                    simpa [Nat.sub_add_cancel hoff] using m1_w24 ⟨n - 23700, hnfin⟩
                                                  ·
                                                    by_cases h25 : n < 23800
                                                    · have hoff : 23750 ≤ n := by omega
                                                      have hnfin : n - 23750 < 50 := by omega
                                                      simpa [Nat.sub_add_cancel hoff] using m1_w25 ⟨n - 23750, hnfin⟩
                                                    ·
                                                      by_cases h26 : n < 23850
                                                      · have hoff : 23800 ≤ n := by omega
                                                        have hnfin : n - 23800 < 50 := by omega
                                                        simpa [Nat.sub_add_cancel hoff] using m1_w26 ⟨n - 23800, hnfin⟩
                                                      ·
                                                        by_cases h27 : n < 23900
                                                        · have hoff : 23850 ≤ n := by omega
                                                          have hnfin : n - 23850 < 50 := by omega
                                                          simpa [Nat.sub_add_cancel hoff] using m1_w27 ⟨n - 23850, hnfin⟩
                                                        ·
                                                          by_cases h28 : n < 23950
                                                          · have hoff : 23900 ≤ n := by omega
                                                            have hnfin : n - 23900 < 50 := by omega
                                                            simpa [Nat.sub_add_cancel hoff] using m1_w28 ⟨n - 23900, hnfin⟩
                                                          ·
                                                            by_cases h29 : n < 24000
                                                            · have hoff : 23950 ≤ n := by omega
                                                              have hnfin : n - 23950 < 50 := by omega
                                                              simpa [Nat.sub_add_cancel hoff] using m1_w29 ⟨n - 23950, hnfin⟩
                                                            ·
                                                              by_cases h30 : n < 24050
                                                              · have hoff : 24000 ≤ n := by omega
                                                                have hnfin : n - 24000 < 50 := by omega
                                                                simpa [Nat.sub_add_cancel hoff] using m1_w30 ⟨n - 24000, hnfin⟩
                                                              ·
                                                                by_cases h31 : n < 24100
                                                                · have hoff : 24050 ≤ n := by omega
                                                                  have hnfin : n - 24050 < 50 := by omega
                                                                  simpa [Nat.sub_add_cancel hoff] using m1_w31 ⟨n - 24050, hnfin⟩
                                                                ·
                                                                  by_cases h32 : n < 24150
                                                                  · have hoff : 24100 ≤ n := by omega
                                                                    have hnfin : n - 24100 < 50 := by omega
                                                                    simpa [Nat.sub_add_cancel hoff] using m1_w32 ⟨n - 24100, hnfin⟩
                                                                  ·
                                                                    by_cases h33 : n < 24200
                                                                    · have hoff : 24150 ≤ n := by omega
                                                                      have hnfin : n - 24150 < 50 := by omega
                                                                      simpa [Nat.sub_add_cancel hoff] using m1_w33 ⟨n - 24150, hnfin⟩
                                                                    ·
                                                                      by_cases h34 : n < 24250
                                                                      · have hoff : 24200 ≤ n := by omega
                                                                        have hnfin : n - 24200 < 50 := by omega
                                                                        simpa [Nat.sub_add_cancel hoff] using m1_w34 ⟨n - 24200, hnfin⟩
                                                                      ·
                                                                        by_cases h35 : n < 24300
                                                                        · have hoff : 24250 ≤ n := by omega
                                                                          have hnfin : n - 24250 < 50 := by omega
                                                                          simpa [Nat.sub_add_cancel hoff] using m1_w35 ⟨n - 24250, hnfin⟩
                                                                        ·
                                                                          by_cases h36 : n < 24350
                                                                          · have hoff : 24300 ≤ n := by omega
                                                                            have hnfin : n - 24300 < 50 := by omega
                                                                            simpa [Nat.sub_add_cancel hoff] using m1_w36 ⟨n - 24300, hnfin⟩
                                                                          ·
                                                                            by_cases h37 : n < 24400
                                                                            · have hoff : 24350 ≤ n := by omega
                                                                              have hnfin : n - 24350 < 50 := by omega
                                                                              simpa [Nat.sub_add_cancel hoff] using m1_w37 ⟨n - 24350, hnfin⟩
                                                                            ·
                                                                              by_cases h38 : n < 24450
                                                                              · have hoff : 24400 ≤ n := by omega
                                                                                have hnfin : n - 24400 < 50 := by omega
                                                                                simpa [Nat.sub_add_cancel hoff] using m1_w38 ⟨n - 24400, hnfin⟩
                                                                              ·
                                                                                by_cases h39 : n < 24500
                                                                                · have hoff : 24450 ≤ n := by omega
                                                                                  have hnfin : n - 24450 < 50 := by omega
                                                                                  simpa [Nat.sub_add_cancel hoff] using m1_w39 ⟨n - 24450, hnfin⟩
                                                                                ·
                                                                                  by_cases h40 : n < 24550
                                                                                  · have hoff : 24500 ≤ n := by omega
                                                                                    have hnfin : n - 24500 < 50 := by omega
                                                                                    simpa [Nat.sub_add_cancel hoff] using m1_w40 ⟨n - 24500, hnfin⟩
                                                                                  ·
                                                                                    by_cases h41 : n < 24600
                                                                                    · have hoff : 24550 ≤ n := by omega
                                                                                      have hnfin : n - 24550 < 50 := by omega
                                                                                      simpa [Nat.sub_add_cancel hoff] using m1_w41 ⟨n - 24550, hnfin⟩
                                                                                    ·
                                                                                      by_cases h42 : n < 24650
                                                                                      · have hoff : 24600 ≤ n := by omega
                                                                                        have hnfin : n - 24600 < 50 := by omega
                                                                                        simpa [Nat.sub_add_cancel hoff] using m1_w42 ⟨n - 24600, hnfin⟩
                                                                                      ·
                                                                                        by_cases h43 : n < 24700
                                                                                        · have hoff : 24650 ≤ n := by omega
                                                                                          have hnfin : n - 24650 < 50 := by omega
                                                                                          simpa [Nat.sub_add_cancel hoff] using m1_w43 ⟨n - 24650, hnfin⟩
                                                                                        ·
                                                                                          by_cases h44 : n < 24750
                                                                                          · have hoff : 24700 ≤ n := by omega
                                                                                            have hnfin : n - 24700 < 50 := by omega
                                                                                            simpa [Nat.sub_add_cancel hoff] using m1_w44 ⟨n - 24700, hnfin⟩
                                                                                          ·
                                                                                            by_cases h45 : n < 24800
                                                                                            · have hoff : 24750 ≤ n := by omega
                                                                                              have hnfin : n - 24750 < 50 := by omega
                                                                                              simpa [Nat.sub_add_cancel hoff] using m1_w45 ⟨n - 24750, hnfin⟩
                                                                                            ·
                                                                                              by_cases h46 : n < 24850
                                                                                              · have hoff : 24800 ≤ n := by omega
                                                                                                have hnfin : n - 24800 < 50 := by omega
                                                                                                simpa [Nat.sub_add_cancel hoff] using m1_w46 ⟨n - 24800, hnfin⟩
                                                                                              ·
                                                                                                by_cases h47 : n < 24900
                                                                                                · have hoff : 24850 ≤ n := by omega
                                                                                                  have hnfin : n - 24850 < 50 := by omega
                                                                                                  simpa [Nat.sub_add_cancel hoff] using m1_w47 ⟨n - 24850, hnfin⟩
                                                                                                ·
                                                                                                  by_cases h48 : n < 24950
                                                                                                  · have hoff : 24900 ≤ n := by omega
                                                                                                    have hnfin : n - 24900 < 50 := by omega
                                                                                                    simpa [Nat.sub_add_cancel hoff] using m1_w48 ⟨n - 24900, hnfin⟩
                                                                                                  ·
                                                                                                    by_cases h49 : n < 25000
                                                                                                    · have hoff : 24950 ≤ n := by omega
                                                                                                      have hnfin : n - 24950 < 50 := by omega
                                                                                                      simpa [Nat.sub_add_cancel hoff] using m1_w49 ⟨n - 24950, hnfin⟩
                                                                                                    ·
                                                                                                      omega
end IntMul.Kappa.R8.Bit.Oppbank.LandMonoFixA9


