-- Prove2me | Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankLandMonoFixA24
-- name    : IntMul_Kappa_R8_Data_BitOppbankLandMonoFixA24
-- status  : Definition
-- author  : @Ethan Cheung Wang
-- created : 2026-10-28T21:19:19.935826+00:00
-- url     : https://prove2.me/theorems/c334e4a8-0991-4e73-b622-405ee4d34e2a
-- title:
--   Dim-gated densSup land mono FixA pack 24
-- statement:
--   # Dim-gated densSup land (PndFix), pack A24
--
--   Range consolidators for $n\in[60000,62478)$.
-- source:
--   R8 BitOppbank PndFix

-- LandMonoFixA24: PUBLIC dim-gated land + range consolidators (PndFix)
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
namespace IntMul.Kappa.R8.Bit.Oppbank.LandMonoFixA24
def arg0 (n : ℕ) : ℕ := Nat.land (argF n) 65535
def arg1 (n : ℕ) : ℕ := Nat.shiftRight (argF n) 16
theorem m0_w0 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 60000))) (dimF (n.val + 60000)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 60000))) (densSupG (n.val + 60000))) (densSupG (arg0 (n.val + 60000)))) = true := by decide
theorem m1_w0 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 60000))) (dimF (n.val + 60000)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 60000))) (densSupG (n.val + 60000))) (densSupG (arg1 (n.val + 60000)))) = true := by decide
theorem m0_w1 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 60050))) (dimF (n.val + 60050)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 60050))) (densSupG (n.val + 60050))) (densSupG (arg0 (n.val + 60050)))) = true := by decide
theorem m1_w1 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 60050))) (dimF (n.val + 60050)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 60050))) (densSupG (n.val + 60050))) (densSupG (arg1 (n.val + 60050)))) = true := by decide
theorem m0_w2 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 60100))) (dimF (n.val + 60100)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 60100))) (densSupG (n.val + 60100))) (densSupG (arg0 (n.val + 60100)))) = true := by decide
theorem m1_w2 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 60100))) (dimF (n.val + 60100)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 60100))) (densSupG (n.val + 60100))) (densSupG (arg1 (n.val + 60100)))) = true := by decide
theorem m0_w3 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 60150))) (dimF (n.val + 60150)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 60150))) (densSupG (n.val + 60150))) (densSupG (arg0 (n.val + 60150)))) = true := by decide
theorem m1_w3 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 60150))) (dimF (n.val + 60150)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 60150))) (densSupG (n.val + 60150))) (densSupG (arg1 (n.val + 60150)))) = true := by decide
theorem m0_w4 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 60200))) (dimF (n.val + 60200)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 60200))) (densSupG (n.val + 60200))) (densSupG (arg0 (n.val + 60200)))) = true := by decide
theorem m1_w4 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 60200))) (dimF (n.val + 60200)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 60200))) (densSupG (n.val + 60200))) (densSupG (arg1 (n.val + 60200)))) = true := by decide
theorem m0_w5 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 60250))) (dimF (n.val + 60250)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 60250))) (densSupG (n.val + 60250))) (densSupG (arg0 (n.val + 60250)))) = true := by decide
theorem m1_w5 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 60250))) (dimF (n.val + 60250)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 60250))) (densSupG (n.val + 60250))) (densSupG (arg1 (n.val + 60250)))) = true := by decide
theorem m0_w6 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 60300))) (dimF (n.val + 60300)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 60300))) (densSupG (n.val + 60300))) (densSupG (arg0 (n.val + 60300)))) = true := by decide
theorem m1_w6 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 60300))) (dimF (n.val + 60300)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 60300))) (densSupG (n.val + 60300))) (densSupG (arg1 (n.val + 60300)))) = true := by decide
theorem m0_w7 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 60350))) (dimF (n.val + 60350)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 60350))) (densSupG (n.val + 60350))) (densSupG (arg0 (n.val + 60350)))) = true := by decide
theorem m1_w7 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 60350))) (dimF (n.val + 60350)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 60350))) (densSupG (n.val + 60350))) (densSupG (arg1 (n.val + 60350)))) = true := by decide
theorem m0_w8 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 60400))) (dimF (n.val + 60400)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 60400))) (densSupG (n.val + 60400))) (densSupG (arg0 (n.val + 60400)))) = true := by decide
theorem m1_w8 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 60400))) (dimF (n.val + 60400)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 60400))) (densSupG (n.val + 60400))) (densSupG (arg1 (n.val + 60400)))) = true := by decide
theorem m0_w9 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 60450))) (dimF (n.val + 60450)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 60450))) (densSupG (n.val + 60450))) (densSupG (arg0 (n.val + 60450)))) = true := by decide
theorem m1_w9 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 60450))) (dimF (n.val + 60450)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 60450))) (densSupG (n.val + 60450))) (densSupG (arg1 (n.val + 60450)))) = true := by decide
theorem m0_w10 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 60500))) (dimF (n.val + 60500)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 60500))) (densSupG (n.val + 60500))) (densSupG (arg0 (n.val + 60500)))) = true := by decide
theorem m1_w10 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 60500))) (dimF (n.val + 60500)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 60500))) (densSupG (n.val + 60500))) (densSupG (arg1 (n.val + 60500)))) = true := by decide
theorem m0_w11 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 60550))) (dimF (n.val + 60550)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 60550))) (densSupG (n.val + 60550))) (densSupG (arg0 (n.val + 60550)))) = true := by decide
theorem m1_w11 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 60550))) (dimF (n.val + 60550)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 60550))) (densSupG (n.val + 60550))) (densSupG (arg1 (n.val + 60550)))) = true := by decide
theorem m0_w12 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 60600))) (dimF (n.val + 60600)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 60600))) (densSupG (n.val + 60600))) (densSupG (arg0 (n.val + 60600)))) = true := by decide
theorem m1_w12 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 60600))) (dimF (n.val + 60600)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 60600))) (densSupG (n.val + 60600))) (densSupG (arg1 (n.val + 60600)))) = true := by decide
theorem m0_w13 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 60650))) (dimF (n.val + 60650)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 60650))) (densSupG (n.val + 60650))) (densSupG (arg0 (n.val + 60650)))) = true := by decide
theorem m1_w13 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 60650))) (dimF (n.val + 60650)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 60650))) (densSupG (n.val + 60650))) (densSupG (arg1 (n.val + 60650)))) = true := by decide
theorem m0_w14 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 60700))) (dimF (n.val + 60700)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 60700))) (densSupG (n.val + 60700))) (densSupG (arg0 (n.val + 60700)))) = true := by decide
theorem m1_w14 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 60700))) (dimF (n.val + 60700)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 60700))) (densSupG (n.val + 60700))) (densSupG (arg1 (n.val + 60700)))) = true := by decide
theorem m0_w15 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 60750))) (dimF (n.val + 60750)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 60750))) (densSupG (n.val + 60750))) (densSupG (arg0 (n.val + 60750)))) = true := by decide
theorem m1_w15 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 60750))) (dimF (n.val + 60750)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 60750))) (densSupG (n.val + 60750))) (densSupG (arg1 (n.val + 60750)))) = true := by decide
theorem m0_w16 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 60800))) (dimF (n.val + 60800)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 60800))) (densSupG (n.val + 60800))) (densSupG (arg0 (n.val + 60800)))) = true := by decide
theorem m1_w16 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 60800))) (dimF (n.val + 60800)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 60800))) (densSupG (n.val + 60800))) (densSupG (arg1 (n.val + 60800)))) = true := by decide
theorem m0_w17 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 60850))) (dimF (n.val + 60850)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 60850))) (densSupG (n.val + 60850))) (densSupG (arg0 (n.val + 60850)))) = true := by decide
theorem m1_w17 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 60850))) (dimF (n.val + 60850)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 60850))) (densSupG (n.val + 60850))) (densSupG (arg1 (n.val + 60850)))) = true := by decide
theorem m0_w18 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 60900))) (dimF (n.val + 60900)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 60900))) (densSupG (n.val + 60900))) (densSupG (arg0 (n.val + 60900)))) = true := by decide
theorem m1_w18 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 60900))) (dimF (n.val + 60900)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 60900))) (densSupG (n.val + 60900))) (densSupG (arg1 (n.val + 60900)))) = true := by decide
theorem m0_w19 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 60950))) (dimF (n.val + 60950)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 60950))) (densSupG (n.val + 60950))) (densSupG (arg0 (n.val + 60950)))) = true := by decide
theorem m1_w19 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 60950))) (dimF (n.val + 60950)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 60950))) (densSupG (n.val + 60950))) (densSupG (arg1 (n.val + 60950)))) = true := by decide
theorem m0_w20 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 61000))) (dimF (n.val + 61000)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 61000))) (densSupG (n.val + 61000))) (densSupG (arg0 (n.val + 61000)))) = true := by decide
theorem m1_w20 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 61000))) (dimF (n.val + 61000)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 61000))) (densSupG (n.val + 61000))) (densSupG (arg1 (n.val + 61000)))) = true := by decide
theorem m0_w21 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 61050))) (dimF (n.val + 61050)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 61050))) (densSupG (n.val + 61050))) (densSupG (arg0 (n.val + 61050)))) = true := by decide
theorem m1_w21 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 61050))) (dimF (n.val + 61050)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 61050))) (densSupG (n.val + 61050))) (densSupG (arg1 (n.val + 61050)))) = true := by decide
theorem m0_w22 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 61100))) (dimF (n.val + 61100)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 61100))) (densSupG (n.val + 61100))) (densSupG (arg0 (n.val + 61100)))) = true := by decide
theorem m1_w22 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 61100))) (dimF (n.val + 61100)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 61100))) (densSupG (n.val + 61100))) (densSupG (arg1 (n.val + 61100)))) = true := by decide
theorem m0_w23 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 61150))) (dimF (n.val + 61150)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 61150))) (densSupG (n.val + 61150))) (densSupG (arg0 (n.val + 61150)))) = true := by decide
theorem m1_w23 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 61150))) (dimF (n.val + 61150)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 61150))) (densSupG (n.val + 61150))) (densSupG (arg1 (n.val + 61150)))) = true := by decide
theorem m0_w24 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 61200))) (dimF (n.val + 61200)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 61200))) (densSupG (n.val + 61200))) (densSupG (arg0 (n.val + 61200)))) = true := by decide
theorem m1_w24 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 61200))) (dimF (n.val + 61200)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 61200))) (densSupG (n.val + 61200))) (densSupG (arg1 (n.val + 61200)))) = true := by decide
theorem m0_w25 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 61250))) (dimF (n.val + 61250)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 61250))) (densSupG (n.val + 61250))) (densSupG (arg0 (n.val + 61250)))) = true := by decide
theorem m1_w25 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 61250))) (dimF (n.val + 61250)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 61250))) (densSupG (n.val + 61250))) (densSupG (arg1 (n.val + 61250)))) = true := by decide
theorem m0_w26 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 61300))) (dimF (n.val + 61300)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 61300))) (densSupG (n.val + 61300))) (densSupG (arg0 (n.val + 61300)))) = true := by decide
theorem m1_w26 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 61300))) (dimF (n.val + 61300)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 61300))) (densSupG (n.val + 61300))) (densSupG (arg1 (n.val + 61300)))) = true := by decide
theorem m0_w27 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 61350))) (dimF (n.val + 61350)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 61350))) (densSupG (n.val + 61350))) (densSupG (arg0 (n.val + 61350)))) = true := by decide
theorem m1_w27 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 61350))) (dimF (n.val + 61350)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 61350))) (densSupG (n.val + 61350))) (densSupG (arg1 (n.val + 61350)))) = true := by decide
theorem m0_w28 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 61400))) (dimF (n.val + 61400)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 61400))) (densSupG (n.val + 61400))) (densSupG (arg0 (n.val + 61400)))) = true := by decide
theorem m1_w28 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 61400))) (dimF (n.val + 61400)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 61400))) (densSupG (n.val + 61400))) (densSupG (arg1 (n.val + 61400)))) = true := by decide
theorem m0_w29 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 61450))) (dimF (n.val + 61450)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 61450))) (densSupG (n.val + 61450))) (densSupG (arg0 (n.val + 61450)))) = true := by decide
theorem m1_w29 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 61450))) (dimF (n.val + 61450)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 61450))) (densSupG (n.val + 61450))) (densSupG (arg1 (n.val + 61450)))) = true := by decide
theorem m0_w30 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 61500))) (dimF (n.val + 61500)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 61500))) (densSupG (n.val + 61500))) (densSupG (arg0 (n.val + 61500)))) = true := by decide
theorem m1_w30 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 61500))) (dimF (n.val + 61500)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 61500))) (densSupG (n.val + 61500))) (densSupG (arg1 (n.val + 61500)))) = true := by decide
theorem m0_w31 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 61550))) (dimF (n.val + 61550)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 61550))) (densSupG (n.val + 61550))) (densSupG (arg0 (n.val + 61550)))) = true := by decide
theorem m1_w31 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 61550))) (dimF (n.val + 61550)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 61550))) (densSupG (n.val + 61550))) (densSupG (arg1 (n.val + 61550)))) = true := by decide
theorem m0_w32 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 61600))) (dimF (n.val + 61600)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 61600))) (densSupG (n.val + 61600))) (densSupG (arg0 (n.val + 61600)))) = true := by decide
theorem m1_w32 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 61600))) (dimF (n.val + 61600)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 61600))) (densSupG (n.val + 61600))) (densSupG (arg1 (n.val + 61600)))) = true := by decide
theorem m0_w33 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 61650))) (dimF (n.val + 61650)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 61650))) (densSupG (n.val + 61650))) (densSupG (arg0 (n.val + 61650)))) = true := by decide
theorem m1_w33 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 61650))) (dimF (n.val + 61650)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 61650))) (densSupG (n.val + 61650))) (densSupG (arg1 (n.val + 61650)))) = true := by decide
theorem m0_w34 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 61700))) (dimF (n.val + 61700)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 61700))) (densSupG (n.val + 61700))) (densSupG (arg0 (n.val + 61700)))) = true := by decide
theorem m1_w34 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 61700))) (dimF (n.val + 61700)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 61700))) (densSupG (n.val + 61700))) (densSupG (arg1 (n.val + 61700)))) = true := by decide
theorem m0_w35 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 61750))) (dimF (n.val + 61750)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 61750))) (densSupG (n.val + 61750))) (densSupG (arg0 (n.val + 61750)))) = true := by decide
theorem m1_w35 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 61750))) (dimF (n.val + 61750)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 61750))) (densSupG (n.val + 61750))) (densSupG (arg1 (n.val + 61750)))) = true := by decide
theorem m0_w36 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 61800))) (dimF (n.val + 61800)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 61800))) (densSupG (n.val + 61800))) (densSupG (arg0 (n.val + 61800)))) = true := by decide
theorem m1_w36 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 61800))) (dimF (n.val + 61800)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 61800))) (densSupG (n.val + 61800))) (densSupG (arg1 (n.val + 61800)))) = true := by decide
theorem m0_w37 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 61850))) (dimF (n.val + 61850)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 61850))) (densSupG (n.val + 61850))) (densSupG (arg0 (n.val + 61850)))) = true := by decide
theorem m1_w37 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 61850))) (dimF (n.val + 61850)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 61850))) (densSupG (n.val + 61850))) (densSupG (arg1 (n.val + 61850)))) = true := by decide
theorem m0_w38 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 61900))) (dimF (n.val + 61900)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 61900))) (densSupG (n.val + 61900))) (densSupG (arg0 (n.val + 61900)))) = true := by decide
theorem m1_w38 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 61900))) (dimF (n.val + 61900)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 61900))) (densSupG (n.val + 61900))) (densSupG (arg1 (n.val + 61900)))) = true := by decide
theorem m0_w39 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 61950))) (dimF (n.val + 61950)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 61950))) (densSupG (n.val + 61950))) (densSupG (arg0 (n.val + 61950)))) = true := by decide
theorem m1_w39 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 61950))) (dimF (n.val + 61950)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 61950))) (densSupG (n.val + 61950))) (densSupG (arg1 (n.val + 61950)))) = true := by decide
theorem m0_w40 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 62000))) (dimF (n.val + 62000)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 62000))) (densSupG (n.val + 62000))) (densSupG (arg0 (n.val + 62000)))) = true := by decide
theorem m1_w40 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 62000))) (dimF (n.val + 62000)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 62000))) (densSupG (n.val + 62000))) (densSupG (arg1 (n.val + 62000)))) = true := by decide
theorem m0_w41 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 62050))) (dimF (n.val + 62050)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 62050))) (densSupG (n.val + 62050))) (densSupG (arg0 (n.val + 62050)))) = true := by decide
theorem m1_w41 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 62050))) (dimF (n.val + 62050)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 62050))) (densSupG (n.val + 62050))) (densSupG (arg1 (n.val + 62050)))) = true := by decide
theorem m0_w42 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 62100))) (dimF (n.val + 62100)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 62100))) (densSupG (n.val + 62100))) (densSupG (arg0 (n.val + 62100)))) = true := by decide
theorem m1_w42 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 62100))) (dimF (n.val + 62100)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 62100))) (densSupG (n.val + 62100))) (densSupG (arg1 (n.val + 62100)))) = true := by decide
theorem m0_w43 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 62150))) (dimF (n.val + 62150)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 62150))) (densSupG (n.val + 62150))) (densSupG (arg0 (n.val + 62150)))) = true := by decide
theorem m1_w43 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 62150))) (dimF (n.val + 62150)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 62150))) (densSupG (n.val + 62150))) (densSupG (arg1 (n.val + 62150)))) = true := by decide
theorem m0_w44 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 62200))) (dimF (n.val + 62200)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 62200))) (densSupG (n.val + 62200))) (densSupG (arg0 (n.val + 62200)))) = true := by decide
theorem m1_w44 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 62200))) (dimF (n.val + 62200)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 62200))) (densSupG (n.val + 62200))) (densSupG (arg1 (n.val + 62200)))) = true := by decide
theorem m0_w45 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 62250))) (dimF (n.val + 62250)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 62250))) (densSupG (n.val + 62250))) (densSupG (arg0 (n.val + 62250)))) = true := by decide
theorem m1_w45 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 62250))) (dimF (n.val + 62250)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 62250))) (densSupG (n.val + 62250))) (densSupG (arg1 (n.val + 62250)))) = true := by decide
theorem m0_w46 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 62300))) (dimF (n.val + 62300)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 62300))) (densSupG (n.val + 62300))) (densSupG (arg0 (n.val + 62300)))) = true := by decide
theorem m1_w46 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 62300))) (dimF (n.val + 62300)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 62300))) (densSupG (n.val + 62300))) (densSupG (arg1 (n.val + 62300)))) = true := by decide
theorem m0_w47 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 62350))) (dimF (n.val + 62350)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 62350))) (densSupG (n.val + 62350))) (densSupG (arg0 (n.val + 62350)))) = true := by decide
theorem m1_w47 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 62350))) (dimF (n.val + 62350)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 62350))) (densSupG (n.val + 62350))) (densSupG (arg1 (n.val + 62350)))) = true := by decide
theorem m0_w48 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 62400))) (dimF (n.val + 62400)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 62400))) (densSupG (n.val + 62400))) (densSupG (arg0 (n.val + 62400)))) = true := by decide
theorem m1_w48 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 62400))) (dimF (n.val + 62400)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 62400))) (densSupG (n.val + 62400))) (densSupG (arg1 (n.val + 62400)))) = true := by decide
theorem m0_w49 : ∀ n : Fin 28,
  (!Nat.blt (dimF (arg0 (n.val + 62450))) (dimF (n.val + 62450)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 62450))) (densSupG (n.val + 62450))) (densSupG (arg0 (n.val + 62450)))) = true := by decide
theorem m1_w49 : ∀ n : Fin 28,
  (!Nat.blt (dimF (arg1 (n.val + 62450))) (dimF (n.val + 62450)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 62450))) (densSupG (n.val + 62450))) (densSupG (arg1 (n.val + 62450)))) = true := by decide
theorem land0_range (n : ℕ) (hn0 : 60000 ≤ n) (hn1 : n < 62478) :
    (!Nat.blt (dimF (arg0 n)) (dimF n) ||
      Nat.beq (Nat.land (densSupG (arg0 n)) (densSupG n)) (densSupG (arg0 n))) = true := by
  by_cases h0 : n < 60050
  · have hoff : 60000 ≤ n := by omega
    have hnfin : n - 60000 < 50 := by omega
    simpa [Nat.sub_add_cancel hoff] using m0_w0 ⟨n - 60000, hnfin⟩
  ·
    by_cases h1 : n < 60100
    · have hoff : 60050 ≤ n := by omega
      have hnfin : n - 60050 < 50 := by omega
      simpa [Nat.sub_add_cancel hoff] using m0_w1 ⟨n - 60050, hnfin⟩
    ·
      by_cases h2 : n < 60150
      · have hoff : 60100 ≤ n := by omega
        have hnfin : n - 60100 < 50 := by omega
        simpa [Nat.sub_add_cancel hoff] using m0_w2 ⟨n - 60100, hnfin⟩
      ·
        by_cases h3 : n < 60200
        · have hoff : 60150 ≤ n := by omega
          have hnfin : n - 60150 < 50 := by omega
          simpa [Nat.sub_add_cancel hoff] using m0_w3 ⟨n - 60150, hnfin⟩
        ·
          by_cases h4 : n < 60250
          · have hoff : 60200 ≤ n := by omega
            have hnfin : n - 60200 < 50 := by omega
            simpa [Nat.sub_add_cancel hoff] using m0_w4 ⟨n - 60200, hnfin⟩
          ·
            by_cases h5 : n < 60300
            · have hoff : 60250 ≤ n := by omega
              have hnfin : n - 60250 < 50 := by omega
              simpa [Nat.sub_add_cancel hoff] using m0_w5 ⟨n - 60250, hnfin⟩
            ·
              by_cases h6 : n < 60350
              · have hoff : 60300 ≤ n := by omega
                have hnfin : n - 60300 < 50 := by omega
                simpa [Nat.sub_add_cancel hoff] using m0_w6 ⟨n - 60300, hnfin⟩
              ·
                by_cases h7 : n < 60400
                · have hoff : 60350 ≤ n := by omega
                  have hnfin : n - 60350 < 50 := by omega
                  simpa [Nat.sub_add_cancel hoff] using m0_w7 ⟨n - 60350, hnfin⟩
                ·
                  by_cases h8 : n < 60450
                  · have hoff : 60400 ≤ n := by omega
                    have hnfin : n - 60400 < 50 := by omega
                    simpa [Nat.sub_add_cancel hoff] using m0_w8 ⟨n - 60400, hnfin⟩
                  ·
                    by_cases h9 : n < 60500
                    · have hoff : 60450 ≤ n := by omega
                      have hnfin : n - 60450 < 50 := by omega
                      simpa [Nat.sub_add_cancel hoff] using m0_w9 ⟨n - 60450, hnfin⟩
                    ·
                      by_cases h10 : n < 60550
                      · have hoff : 60500 ≤ n := by omega
                        have hnfin : n - 60500 < 50 := by omega
                        simpa [Nat.sub_add_cancel hoff] using m0_w10 ⟨n - 60500, hnfin⟩
                      ·
                        by_cases h11 : n < 60600
                        · have hoff : 60550 ≤ n := by omega
                          have hnfin : n - 60550 < 50 := by omega
                          simpa [Nat.sub_add_cancel hoff] using m0_w11 ⟨n - 60550, hnfin⟩
                        ·
                          by_cases h12 : n < 60650
                          · have hoff : 60600 ≤ n := by omega
                            have hnfin : n - 60600 < 50 := by omega
                            simpa [Nat.sub_add_cancel hoff] using m0_w12 ⟨n - 60600, hnfin⟩
                          ·
                            by_cases h13 : n < 60700
                            · have hoff : 60650 ≤ n := by omega
                              have hnfin : n - 60650 < 50 := by omega
                              simpa [Nat.sub_add_cancel hoff] using m0_w13 ⟨n - 60650, hnfin⟩
                            ·
                              by_cases h14 : n < 60750
                              · have hoff : 60700 ≤ n := by omega
                                have hnfin : n - 60700 < 50 := by omega
                                simpa [Nat.sub_add_cancel hoff] using m0_w14 ⟨n - 60700, hnfin⟩
                              ·
                                by_cases h15 : n < 60800
                                · have hoff : 60750 ≤ n := by omega
                                  have hnfin : n - 60750 < 50 := by omega
                                  simpa [Nat.sub_add_cancel hoff] using m0_w15 ⟨n - 60750, hnfin⟩
                                ·
                                  by_cases h16 : n < 60850
                                  · have hoff : 60800 ≤ n := by omega
                                    have hnfin : n - 60800 < 50 := by omega
                                    simpa [Nat.sub_add_cancel hoff] using m0_w16 ⟨n - 60800, hnfin⟩
                                  ·
                                    by_cases h17 : n < 60900
                                    · have hoff : 60850 ≤ n := by omega
                                      have hnfin : n - 60850 < 50 := by omega
                                      simpa [Nat.sub_add_cancel hoff] using m0_w17 ⟨n - 60850, hnfin⟩
                                    ·
                                      by_cases h18 : n < 60950
                                      · have hoff : 60900 ≤ n := by omega
                                        have hnfin : n - 60900 < 50 := by omega
                                        simpa [Nat.sub_add_cancel hoff] using m0_w18 ⟨n - 60900, hnfin⟩
                                      ·
                                        by_cases h19 : n < 61000
                                        · have hoff : 60950 ≤ n := by omega
                                          have hnfin : n - 60950 < 50 := by omega
                                          simpa [Nat.sub_add_cancel hoff] using m0_w19 ⟨n - 60950, hnfin⟩
                                        ·
                                          by_cases h20 : n < 61050
                                          · have hoff : 61000 ≤ n := by omega
                                            have hnfin : n - 61000 < 50 := by omega
                                            simpa [Nat.sub_add_cancel hoff] using m0_w20 ⟨n - 61000, hnfin⟩
                                          ·
                                            by_cases h21 : n < 61100
                                            · have hoff : 61050 ≤ n := by omega
                                              have hnfin : n - 61050 < 50 := by omega
                                              simpa [Nat.sub_add_cancel hoff] using m0_w21 ⟨n - 61050, hnfin⟩
                                            ·
                                              by_cases h22 : n < 61150
                                              · have hoff : 61100 ≤ n := by omega
                                                have hnfin : n - 61100 < 50 := by omega
                                                simpa [Nat.sub_add_cancel hoff] using m0_w22 ⟨n - 61100, hnfin⟩
                                              ·
                                                by_cases h23 : n < 61200
                                                · have hoff : 61150 ≤ n := by omega
                                                  have hnfin : n - 61150 < 50 := by omega
                                                  simpa [Nat.sub_add_cancel hoff] using m0_w23 ⟨n - 61150, hnfin⟩
                                                ·
                                                  by_cases h24 : n < 61250
                                                  · have hoff : 61200 ≤ n := by omega
                                                    have hnfin : n - 61200 < 50 := by omega
                                                    simpa [Nat.sub_add_cancel hoff] using m0_w24 ⟨n - 61200, hnfin⟩
                                                  ·
                                                    by_cases h25 : n < 61300
                                                    · have hoff : 61250 ≤ n := by omega
                                                      have hnfin : n - 61250 < 50 := by omega
                                                      simpa [Nat.sub_add_cancel hoff] using m0_w25 ⟨n - 61250, hnfin⟩
                                                    ·
                                                      by_cases h26 : n < 61350
                                                      · have hoff : 61300 ≤ n := by omega
                                                        have hnfin : n - 61300 < 50 := by omega
                                                        simpa [Nat.sub_add_cancel hoff] using m0_w26 ⟨n - 61300, hnfin⟩
                                                      ·
                                                        by_cases h27 : n < 61400
                                                        · have hoff : 61350 ≤ n := by omega
                                                          have hnfin : n - 61350 < 50 := by omega
                                                          simpa [Nat.sub_add_cancel hoff] using m0_w27 ⟨n - 61350, hnfin⟩
                                                        ·
                                                          by_cases h28 : n < 61450
                                                          · have hoff : 61400 ≤ n := by omega
                                                            have hnfin : n - 61400 < 50 := by omega
                                                            simpa [Nat.sub_add_cancel hoff] using m0_w28 ⟨n - 61400, hnfin⟩
                                                          ·
                                                            by_cases h29 : n < 61500
                                                            · have hoff : 61450 ≤ n := by omega
                                                              have hnfin : n - 61450 < 50 := by omega
                                                              simpa [Nat.sub_add_cancel hoff] using m0_w29 ⟨n - 61450, hnfin⟩
                                                            ·
                                                              by_cases h30 : n < 61550
                                                              · have hoff : 61500 ≤ n := by omega
                                                                have hnfin : n - 61500 < 50 := by omega
                                                                simpa [Nat.sub_add_cancel hoff] using m0_w30 ⟨n - 61500, hnfin⟩
                                                              ·
                                                                by_cases h31 : n < 61600
                                                                · have hoff : 61550 ≤ n := by omega
                                                                  have hnfin : n - 61550 < 50 := by omega
                                                                  simpa [Nat.sub_add_cancel hoff] using m0_w31 ⟨n - 61550, hnfin⟩
                                                                ·
                                                                  by_cases h32 : n < 61650
                                                                  · have hoff : 61600 ≤ n := by omega
                                                                    have hnfin : n - 61600 < 50 := by omega
                                                                    simpa [Nat.sub_add_cancel hoff] using m0_w32 ⟨n - 61600, hnfin⟩
                                                                  ·
                                                                    by_cases h33 : n < 61700
                                                                    · have hoff : 61650 ≤ n := by omega
                                                                      have hnfin : n - 61650 < 50 := by omega
                                                                      simpa [Nat.sub_add_cancel hoff] using m0_w33 ⟨n - 61650, hnfin⟩
                                                                    ·
                                                                      by_cases h34 : n < 61750
                                                                      · have hoff : 61700 ≤ n := by omega
                                                                        have hnfin : n - 61700 < 50 := by omega
                                                                        simpa [Nat.sub_add_cancel hoff] using m0_w34 ⟨n - 61700, hnfin⟩
                                                                      ·
                                                                        by_cases h35 : n < 61800
                                                                        · have hoff : 61750 ≤ n := by omega
                                                                          have hnfin : n - 61750 < 50 := by omega
                                                                          simpa [Nat.sub_add_cancel hoff] using m0_w35 ⟨n - 61750, hnfin⟩
                                                                        ·
                                                                          by_cases h36 : n < 61850
                                                                          · have hoff : 61800 ≤ n := by omega
                                                                            have hnfin : n - 61800 < 50 := by omega
                                                                            simpa [Nat.sub_add_cancel hoff] using m0_w36 ⟨n - 61800, hnfin⟩
                                                                          ·
                                                                            by_cases h37 : n < 61900
                                                                            · have hoff : 61850 ≤ n := by omega
                                                                              have hnfin : n - 61850 < 50 := by omega
                                                                              simpa [Nat.sub_add_cancel hoff] using m0_w37 ⟨n - 61850, hnfin⟩
                                                                            ·
                                                                              by_cases h38 : n < 61950
                                                                              · have hoff : 61900 ≤ n := by omega
                                                                                have hnfin : n - 61900 < 50 := by omega
                                                                                simpa [Nat.sub_add_cancel hoff] using m0_w38 ⟨n - 61900, hnfin⟩
                                                                              ·
                                                                                by_cases h39 : n < 62000
                                                                                · have hoff : 61950 ≤ n := by omega
                                                                                  have hnfin : n - 61950 < 50 := by omega
                                                                                  simpa [Nat.sub_add_cancel hoff] using m0_w39 ⟨n - 61950, hnfin⟩
                                                                                ·
                                                                                  by_cases h40 : n < 62050
                                                                                  · have hoff : 62000 ≤ n := by omega
                                                                                    have hnfin : n - 62000 < 50 := by omega
                                                                                    simpa [Nat.sub_add_cancel hoff] using m0_w40 ⟨n - 62000, hnfin⟩
                                                                                  ·
                                                                                    by_cases h41 : n < 62100
                                                                                    · have hoff : 62050 ≤ n := by omega
                                                                                      have hnfin : n - 62050 < 50 := by omega
                                                                                      simpa [Nat.sub_add_cancel hoff] using m0_w41 ⟨n - 62050, hnfin⟩
                                                                                    ·
                                                                                      by_cases h42 : n < 62150
                                                                                      · have hoff : 62100 ≤ n := by omega
                                                                                        have hnfin : n - 62100 < 50 := by omega
                                                                                        simpa [Nat.sub_add_cancel hoff] using m0_w42 ⟨n - 62100, hnfin⟩
                                                                                      ·
                                                                                        by_cases h43 : n < 62200
                                                                                        · have hoff : 62150 ≤ n := by omega
                                                                                          have hnfin : n - 62150 < 50 := by omega
                                                                                          simpa [Nat.sub_add_cancel hoff] using m0_w43 ⟨n - 62150, hnfin⟩
                                                                                        ·
                                                                                          by_cases h44 : n < 62250
                                                                                          · have hoff : 62200 ≤ n := by omega
                                                                                            have hnfin : n - 62200 < 50 := by omega
                                                                                            simpa [Nat.sub_add_cancel hoff] using m0_w44 ⟨n - 62200, hnfin⟩
                                                                                          ·
                                                                                            by_cases h45 : n < 62300
                                                                                            · have hoff : 62250 ≤ n := by omega
                                                                                              have hnfin : n - 62250 < 50 := by omega
                                                                                              simpa [Nat.sub_add_cancel hoff] using m0_w45 ⟨n - 62250, hnfin⟩
                                                                                            ·
                                                                                              by_cases h46 : n < 62350
                                                                                              · have hoff : 62300 ≤ n := by omega
                                                                                                have hnfin : n - 62300 < 50 := by omega
                                                                                                simpa [Nat.sub_add_cancel hoff] using m0_w46 ⟨n - 62300, hnfin⟩
                                                                                              ·
                                                                                                by_cases h47 : n < 62400
                                                                                                · have hoff : 62350 ≤ n := by omega
                                                                                                  have hnfin : n - 62350 < 50 := by omega
                                                                                                  simpa [Nat.sub_add_cancel hoff] using m0_w47 ⟨n - 62350, hnfin⟩
                                                                                                ·
                                                                                                  by_cases h48 : n < 62450
                                                                                                  · have hoff : 62400 ≤ n := by omega
                                                                                                    have hnfin : n - 62400 < 50 := by omega
                                                                                                    simpa [Nat.sub_add_cancel hoff] using m0_w48 ⟨n - 62400, hnfin⟩
                                                                                                  ·
                                                                                                    by_cases h49 : n < 62478
                                                                                                    · have hoff : 62450 ≤ n := by omega
                                                                                                      have hnfin : n - 62450 < 28 := by omega
                                                                                                      simpa [Nat.sub_add_cancel hoff] using m0_w49 ⟨n - 62450, hnfin⟩
                                                                                                    ·
                                                                                                      omega
theorem land1_range (n : ℕ) (hn0 : 60000 ≤ n) (hn1 : n < 62478) :
    (!Nat.blt (dimF (arg1 n)) (dimF n) ||
      Nat.beq (Nat.land (densSupG (arg1 n)) (densSupG n)) (densSupG (arg1 n))) = true := by
  by_cases h0 : n < 60050
  · have hoff : 60000 ≤ n := by omega
    have hnfin : n - 60000 < 50 := by omega
    simpa [Nat.sub_add_cancel hoff] using m1_w0 ⟨n - 60000, hnfin⟩
  ·
    by_cases h1 : n < 60100
    · have hoff : 60050 ≤ n := by omega
      have hnfin : n - 60050 < 50 := by omega
      simpa [Nat.sub_add_cancel hoff] using m1_w1 ⟨n - 60050, hnfin⟩
    ·
      by_cases h2 : n < 60150
      · have hoff : 60100 ≤ n := by omega
        have hnfin : n - 60100 < 50 := by omega
        simpa [Nat.sub_add_cancel hoff] using m1_w2 ⟨n - 60100, hnfin⟩
      ·
        by_cases h3 : n < 60200
        · have hoff : 60150 ≤ n := by omega
          have hnfin : n - 60150 < 50 := by omega
          simpa [Nat.sub_add_cancel hoff] using m1_w3 ⟨n - 60150, hnfin⟩
        ·
          by_cases h4 : n < 60250
          · have hoff : 60200 ≤ n := by omega
            have hnfin : n - 60200 < 50 := by omega
            simpa [Nat.sub_add_cancel hoff] using m1_w4 ⟨n - 60200, hnfin⟩
          ·
            by_cases h5 : n < 60300
            · have hoff : 60250 ≤ n := by omega
              have hnfin : n - 60250 < 50 := by omega
              simpa [Nat.sub_add_cancel hoff] using m1_w5 ⟨n - 60250, hnfin⟩
            ·
              by_cases h6 : n < 60350
              · have hoff : 60300 ≤ n := by omega
                have hnfin : n - 60300 < 50 := by omega
                simpa [Nat.sub_add_cancel hoff] using m1_w6 ⟨n - 60300, hnfin⟩
              ·
                by_cases h7 : n < 60400
                · have hoff : 60350 ≤ n := by omega
                  have hnfin : n - 60350 < 50 := by omega
                  simpa [Nat.sub_add_cancel hoff] using m1_w7 ⟨n - 60350, hnfin⟩
                ·
                  by_cases h8 : n < 60450
                  · have hoff : 60400 ≤ n := by omega
                    have hnfin : n - 60400 < 50 := by omega
                    simpa [Nat.sub_add_cancel hoff] using m1_w8 ⟨n - 60400, hnfin⟩
                  ·
                    by_cases h9 : n < 60500
                    · have hoff : 60450 ≤ n := by omega
                      have hnfin : n - 60450 < 50 := by omega
                      simpa [Nat.sub_add_cancel hoff] using m1_w9 ⟨n - 60450, hnfin⟩
                    ·
                      by_cases h10 : n < 60550
                      · have hoff : 60500 ≤ n := by omega
                        have hnfin : n - 60500 < 50 := by omega
                        simpa [Nat.sub_add_cancel hoff] using m1_w10 ⟨n - 60500, hnfin⟩
                      ·
                        by_cases h11 : n < 60600
                        · have hoff : 60550 ≤ n := by omega
                          have hnfin : n - 60550 < 50 := by omega
                          simpa [Nat.sub_add_cancel hoff] using m1_w11 ⟨n - 60550, hnfin⟩
                        ·
                          by_cases h12 : n < 60650
                          · have hoff : 60600 ≤ n := by omega
                            have hnfin : n - 60600 < 50 := by omega
                            simpa [Nat.sub_add_cancel hoff] using m1_w12 ⟨n - 60600, hnfin⟩
                          ·
                            by_cases h13 : n < 60700
                            · have hoff : 60650 ≤ n := by omega
                              have hnfin : n - 60650 < 50 := by omega
                              simpa [Nat.sub_add_cancel hoff] using m1_w13 ⟨n - 60650, hnfin⟩
                            ·
                              by_cases h14 : n < 60750
                              · have hoff : 60700 ≤ n := by omega
                                have hnfin : n - 60700 < 50 := by omega
                                simpa [Nat.sub_add_cancel hoff] using m1_w14 ⟨n - 60700, hnfin⟩
                              ·
                                by_cases h15 : n < 60800
                                · have hoff : 60750 ≤ n := by omega
                                  have hnfin : n - 60750 < 50 := by omega
                                  simpa [Nat.sub_add_cancel hoff] using m1_w15 ⟨n - 60750, hnfin⟩
                                ·
                                  by_cases h16 : n < 60850
                                  · have hoff : 60800 ≤ n := by omega
                                    have hnfin : n - 60800 < 50 := by omega
                                    simpa [Nat.sub_add_cancel hoff] using m1_w16 ⟨n - 60800, hnfin⟩
                                  ·
                                    by_cases h17 : n < 60900
                                    · have hoff : 60850 ≤ n := by omega
                                      have hnfin : n - 60850 < 50 := by omega
                                      simpa [Nat.sub_add_cancel hoff] using m1_w17 ⟨n - 60850, hnfin⟩
                                    ·
                                      by_cases h18 : n < 60950
                                      · have hoff : 60900 ≤ n := by omega
                                        have hnfin : n - 60900 < 50 := by omega
                                        simpa [Nat.sub_add_cancel hoff] using m1_w18 ⟨n - 60900, hnfin⟩
                                      ·
                                        by_cases h19 : n < 61000
                                        · have hoff : 60950 ≤ n := by omega
                                          have hnfin : n - 60950 < 50 := by omega
                                          simpa [Nat.sub_add_cancel hoff] using m1_w19 ⟨n - 60950, hnfin⟩
                                        ·
                                          by_cases h20 : n < 61050
                                          · have hoff : 61000 ≤ n := by omega
                                            have hnfin : n - 61000 < 50 := by omega
                                            simpa [Nat.sub_add_cancel hoff] using m1_w20 ⟨n - 61000, hnfin⟩
                                          ·
                                            by_cases h21 : n < 61100
                                            · have hoff : 61050 ≤ n := by omega
                                              have hnfin : n - 61050 < 50 := by omega
                                              simpa [Nat.sub_add_cancel hoff] using m1_w21 ⟨n - 61050, hnfin⟩
                                            ·
                                              by_cases h22 : n < 61150
                                              · have hoff : 61100 ≤ n := by omega
                                                have hnfin : n - 61100 < 50 := by omega
                                                simpa [Nat.sub_add_cancel hoff] using m1_w22 ⟨n - 61100, hnfin⟩
                                              ·
                                                by_cases h23 : n < 61200
                                                · have hoff : 61150 ≤ n := by omega
                                                  have hnfin : n - 61150 < 50 := by omega
                                                  simpa [Nat.sub_add_cancel hoff] using m1_w23 ⟨n - 61150, hnfin⟩
                                                ·
                                                  by_cases h24 : n < 61250
                                                  · have hoff : 61200 ≤ n := by omega
                                                    have hnfin : n - 61200 < 50 := by omega
                                                    simpa [Nat.sub_add_cancel hoff] using m1_w24 ⟨n - 61200, hnfin⟩
                                                  ·
                                                    by_cases h25 : n < 61300
                                                    · have hoff : 61250 ≤ n := by omega
                                                      have hnfin : n - 61250 < 50 := by omega
                                                      simpa [Nat.sub_add_cancel hoff] using m1_w25 ⟨n - 61250, hnfin⟩
                                                    ·
                                                      by_cases h26 : n < 61350
                                                      · have hoff : 61300 ≤ n := by omega
                                                        have hnfin : n - 61300 < 50 := by omega
                                                        simpa [Nat.sub_add_cancel hoff] using m1_w26 ⟨n - 61300, hnfin⟩
                                                      ·
                                                        by_cases h27 : n < 61400
                                                        · have hoff : 61350 ≤ n := by omega
                                                          have hnfin : n - 61350 < 50 := by omega
                                                          simpa [Nat.sub_add_cancel hoff] using m1_w27 ⟨n - 61350, hnfin⟩
                                                        ·
                                                          by_cases h28 : n < 61450
                                                          · have hoff : 61400 ≤ n := by omega
                                                            have hnfin : n - 61400 < 50 := by omega
                                                            simpa [Nat.sub_add_cancel hoff] using m1_w28 ⟨n - 61400, hnfin⟩
                                                          ·
                                                            by_cases h29 : n < 61500
                                                            · have hoff : 61450 ≤ n := by omega
                                                              have hnfin : n - 61450 < 50 := by omega
                                                              simpa [Nat.sub_add_cancel hoff] using m1_w29 ⟨n - 61450, hnfin⟩
                                                            ·
                                                              by_cases h30 : n < 61550
                                                              · have hoff : 61500 ≤ n := by omega
                                                                have hnfin : n - 61500 < 50 := by omega
                                                                simpa [Nat.sub_add_cancel hoff] using m1_w30 ⟨n - 61500, hnfin⟩
                                                              ·
                                                                by_cases h31 : n < 61600
                                                                · have hoff : 61550 ≤ n := by omega
                                                                  have hnfin : n - 61550 < 50 := by omega
                                                                  simpa [Nat.sub_add_cancel hoff] using m1_w31 ⟨n - 61550, hnfin⟩
                                                                ·
                                                                  by_cases h32 : n < 61650
                                                                  · have hoff : 61600 ≤ n := by omega
                                                                    have hnfin : n - 61600 < 50 := by omega
                                                                    simpa [Nat.sub_add_cancel hoff] using m1_w32 ⟨n - 61600, hnfin⟩
                                                                  ·
                                                                    by_cases h33 : n < 61700
                                                                    · have hoff : 61650 ≤ n := by omega
                                                                      have hnfin : n - 61650 < 50 := by omega
                                                                      simpa [Nat.sub_add_cancel hoff] using m1_w33 ⟨n - 61650, hnfin⟩
                                                                    ·
                                                                      by_cases h34 : n < 61750
                                                                      · have hoff : 61700 ≤ n := by omega
                                                                        have hnfin : n - 61700 < 50 := by omega
                                                                        simpa [Nat.sub_add_cancel hoff] using m1_w34 ⟨n - 61700, hnfin⟩
                                                                      ·
                                                                        by_cases h35 : n < 61800
                                                                        · have hoff : 61750 ≤ n := by omega
                                                                          have hnfin : n - 61750 < 50 := by omega
                                                                          simpa [Nat.sub_add_cancel hoff] using m1_w35 ⟨n - 61750, hnfin⟩
                                                                        ·
                                                                          by_cases h36 : n < 61850
                                                                          · have hoff : 61800 ≤ n := by omega
                                                                            have hnfin : n - 61800 < 50 := by omega
                                                                            simpa [Nat.sub_add_cancel hoff] using m1_w36 ⟨n - 61800, hnfin⟩
                                                                          ·
                                                                            by_cases h37 : n < 61900
                                                                            · have hoff : 61850 ≤ n := by omega
                                                                              have hnfin : n - 61850 < 50 := by omega
                                                                              simpa [Nat.sub_add_cancel hoff] using m1_w37 ⟨n - 61850, hnfin⟩
                                                                            ·
                                                                              by_cases h38 : n < 61950
                                                                              · have hoff : 61900 ≤ n := by omega
                                                                                have hnfin : n - 61900 < 50 := by omega
                                                                                simpa [Nat.sub_add_cancel hoff] using m1_w38 ⟨n - 61900, hnfin⟩
                                                                              ·
                                                                                by_cases h39 : n < 62000
                                                                                · have hoff : 61950 ≤ n := by omega
                                                                                  have hnfin : n - 61950 < 50 := by omega
                                                                                  simpa [Nat.sub_add_cancel hoff] using m1_w39 ⟨n - 61950, hnfin⟩
                                                                                ·
                                                                                  by_cases h40 : n < 62050
                                                                                  · have hoff : 62000 ≤ n := by omega
                                                                                    have hnfin : n - 62000 < 50 := by omega
                                                                                    simpa [Nat.sub_add_cancel hoff] using m1_w40 ⟨n - 62000, hnfin⟩
                                                                                  ·
                                                                                    by_cases h41 : n < 62100
                                                                                    · have hoff : 62050 ≤ n := by omega
                                                                                      have hnfin : n - 62050 < 50 := by omega
                                                                                      simpa [Nat.sub_add_cancel hoff] using m1_w41 ⟨n - 62050, hnfin⟩
                                                                                    ·
                                                                                      by_cases h42 : n < 62150
                                                                                      · have hoff : 62100 ≤ n := by omega
                                                                                        have hnfin : n - 62100 < 50 := by omega
                                                                                        simpa [Nat.sub_add_cancel hoff] using m1_w42 ⟨n - 62100, hnfin⟩
                                                                                      ·
                                                                                        by_cases h43 : n < 62200
                                                                                        · have hoff : 62150 ≤ n := by omega
                                                                                          have hnfin : n - 62150 < 50 := by omega
                                                                                          simpa [Nat.sub_add_cancel hoff] using m1_w43 ⟨n - 62150, hnfin⟩
                                                                                        ·
                                                                                          by_cases h44 : n < 62250
                                                                                          · have hoff : 62200 ≤ n := by omega
                                                                                            have hnfin : n - 62200 < 50 := by omega
                                                                                            simpa [Nat.sub_add_cancel hoff] using m1_w44 ⟨n - 62200, hnfin⟩
                                                                                          ·
                                                                                            by_cases h45 : n < 62300
                                                                                            · have hoff : 62250 ≤ n := by omega
                                                                                              have hnfin : n - 62250 < 50 := by omega
                                                                                              simpa [Nat.sub_add_cancel hoff] using m1_w45 ⟨n - 62250, hnfin⟩
                                                                                            ·
                                                                                              by_cases h46 : n < 62350
                                                                                              · have hoff : 62300 ≤ n := by omega
                                                                                                have hnfin : n - 62300 < 50 := by omega
                                                                                                simpa [Nat.sub_add_cancel hoff] using m1_w46 ⟨n - 62300, hnfin⟩
                                                                                              ·
                                                                                                by_cases h47 : n < 62400
                                                                                                · have hoff : 62350 ≤ n := by omega
                                                                                                  have hnfin : n - 62350 < 50 := by omega
                                                                                                  simpa [Nat.sub_add_cancel hoff] using m1_w47 ⟨n - 62350, hnfin⟩
                                                                                                ·
                                                                                                  by_cases h48 : n < 62450
                                                                                                  · have hoff : 62400 ≤ n := by omega
                                                                                                    have hnfin : n - 62400 < 50 := by omega
                                                                                                    simpa [Nat.sub_add_cancel hoff] using m1_w48 ⟨n - 62400, hnfin⟩
                                                                                                  ·
                                                                                                    by_cases h49 : n < 62478
                                                                                                    · have hoff : 62450 ≤ n := by omega
                                                                                                      have hnfin : n - 62450 < 28 := by omega
                                                                                                      simpa [Nat.sub_add_cancel hoff] using m1_w49 ⟨n - 62450, hnfin⟩
                                                                                                    ·
                                                                                                      omega
end IntMul.Kappa.R8.Bit.Oppbank.LandMonoFixA24


