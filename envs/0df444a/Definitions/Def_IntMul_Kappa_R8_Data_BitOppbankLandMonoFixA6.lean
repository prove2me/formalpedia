-- Prove2me | Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankLandMonoFixA6
-- name    : IntMul_Kappa_R8_Data_BitOppbankLandMonoFixA6
-- status  : Definition
-- author  : @Ethan Cheung Wang
-- created : 2026-10-28T21:13:43.113214+00:00
-- url     : https://prove2.me/theorems/0178c2a3-0355-4bec-9b95-1e9571213408
-- title:
--   Dim-gated densSup land mono FixA pack 6
-- statement:
--   # Dim-gated densSup land (PndFix), pack A6
--
--   Range consolidators for $n\in[15000,17500)$.
-- source:
--   R8 BitOppbank PndFix

-- LandMonoFixA6: PUBLIC dim-gated land + range consolidators (PndFix)
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
namespace IntMul.Kappa.R8.Bit.Oppbank.LandMonoFixA6
def arg0 (n : ℕ) : ℕ := Nat.land (argF n) 65535
def arg1 (n : ℕ) : ℕ := Nat.shiftRight (argF n) 16
theorem m0_w0 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 15000))) (dimF (n.val + 15000)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 15000))) (densSupG (n.val + 15000))) (densSupG (arg0 (n.val + 15000)))) = true := by decide
theorem m1_w0 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 15000))) (dimF (n.val + 15000)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 15000))) (densSupG (n.val + 15000))) (densSupG (arg1 (n.val + 15000)))) = true := by decide
theorem m0_w1 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 15050))) (dimF (n.val + 15050)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 15050))) (densSupG (n.val + 15050))) (densSupG (arg0 (n.val + 15050)))) = true := by decide
theorem m1_w1 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 15050))) (dimF (n.val + 15050)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 15050))) (densSupG (n.val + 15050))) (densSupG (arg1 (n.val + 15050)))) = true := by decide
theorem m0_w2 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 15100))) (dimF (n.val + 15100)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 15100))) (densSupG (n.val + 15100))) (densSupG (arg0 (n.val + 15100)))) = true := by decide
theorem m1_w2 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 15100))) (dimF (n.val + 15100)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 15100))) (densSupG (n.val + 15100))) (densSupG (arg1 (n.val + 15100)))) = true := by decide
theorem m0_w3 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 15150))) (dimF (n.val + 15150)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 15150))) (densSupG (n.val + 15150))) (densSupG (arg0 (n.val + 15150)))) = true := by decide
theorem m1_w3 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 15150))) (dimF (n.val + 15150)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 15150))) (densSupG (n.val + 15150))) (densSupG (arg1 (n.val + 15150)))) = true := by decide
theorem m0_w4 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 15200))) (dimF (n.val + 15200)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 15200))) (densSupG (n.val + 15200))) (densSupG (arg0 (n.val + 15200)))) = true := by decide
theorem m1_w4 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 15200))) (dimF (n.val + 15200)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 15200))) (densSupG (n.val + 15200))) (densSupG (arg1 (n.val + 15200)))) = true := by decide
theorem m0_w5 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 15250))) (dimF (n.val + 15250)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 15250))) (densSupG (n.val + 15250))) (densSupG (arg0 (n.val + 15250)))) = true := by decide
theorem m1_w5 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 15250))) (dimF (n.val + 15250)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 15250))) (densSupG (n.val + 15250))) (densSupG (arg1 (n.val + 15250)))) = true := by decide
theorem m0_w6 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 15300))) (dimF (n.val + 15300)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 15300))) (densSupG (n.val + 15300))) (densSupG (arg0 (n.val + 15300)))) = true := by decide
theorem m1_w6 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 15300))) (dimF (n.val + 15300)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 15300))) (densSupG (n.val + 15300))) (densSupG (arg1 (n.val + 15300)))) = true := by decide
theorem m0_w7 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 15350))) (dimF (n.val + 15350)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 15350))) (densSupG (n.val + 15350))) (densSupG (arg0 (n.val + 15350)))) = true := by decide
theorem m1_w7 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 15350))) (dimF (n.val + 15350)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 15350))) (densSupG (n.val + 15350))) (densSupG (arg1 (n.val + 15350)))) = true := by decide
theorem m0_w8 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 15400))) (dimF (n.val + 15400)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 15400))) (densSupG (n.val + 15400))) (densSupG (arg0 (n.val + 15400)))) = true := by decide
theorem m1_w8 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 15400))) (dimF (n.val + 15400)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 15400))) (densSupG (n.val + 15400))) (densSupG (arg1 (n.val + 15400)))) = true := by decide
theorem m0_w9 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 15450))) (dimF (n.val + 15450)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 15450))) (densSupG (n.val + 15450))) (densSupG (arg0 (n.val + 15450)))) = true := by decide
theorem m1_w9 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 15450))) (dimF (n.val + 15450)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 15450))) (densSupG (n.val + 15450))) (densSupG (arg1 (n.val + 15450)))) = true := by decide
theorem m0_w10 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 15500))) (dimF (n.val + 15500)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 15500))) (densSupG (n.val + 15500))) (densSupG (arg0 (n.val + 15500)))) = true := by decide
theorem m1_w10 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 15500))) (dimF (n.val + 15500)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 15500))) (densSupG (n.val + 15500))) (densSupG (arg1 (n.val + 15500)))) = true := by decide
theorem m0_w11 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 15550))) (dimF (n.val + 15550)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 15550))) (densSupG (n.val + 15550))) (densSupG (arg0 (n.val + 15550)))) = true := by decide
theorem m1_w11 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 15550))) (dimF (n.val + 15550)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 15550))) (densSupG (n.val + 15550))) (densSupG (arg1 (n.val + 15550)))) = true := by decide
theorem m0_w12 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 15600))) (dimF (n.val + 15600)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 15600))) (densSupG (n.val + 15600))) (densSupG (arg0 (n.val + 15600)))) = true := by decide
theorem m1_w12 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 15600))) (dimF (n.val + 15600)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 15600))) (densSupG (n.val + 15600))) (densSupG (arg1 (n.val + 15600)))) = true := by decide
theorem m0_w13 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 15650))) (dimF (n.val + 15650)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 15650))) (densSupG (n.val + 15650))) (densSupG (arg0 (n.val + 15650)))) = true := by decide
theorem m1_w13 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 15650))) (dimF (n.val + 15650)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 15650))) (densSupG (n.val + 15650))) (densSupG (arg1 (n.val + 15650)))) = true := by decide
theorem m0_w14 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 15700))) (dimF (n.val + 15700)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 15700))) (densSupG (n.val + 15700))) (densSupG (arg0 (n.val + 15700)))) = true := by decide
theorem m1_w14 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 15700))) (dimF (n.val + 15700)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 15700))) (densSupG (n.val + 15700))) (densSupG (arg1 (n.val + 15700)))) = true := by decide
theorem m0_w15 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 15750))) (dimF (n.val + 15750)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 15750))) (densSupG (n.val + 15750))) (densSupG (arg0 (n.val + 15750)))) = true := by decide
theorem m1_w15 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 15750))) (dimF (n.val + 15750)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 15750))) (densSupG (n.val + 15750))) (densSupG (arg1 (n.val + 15750)))) = true := by decide
theorem m0_w16 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 15800))) (dimF (n.val + 15800)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 15800))) (densSupG (n.val + 15800))) (densSupG (arg0 (n.val + 15800)))) = true := by decide
theorem m1_w16 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 15800))) (dimF (n.val + 15800)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 15800))) (densSupG (n.val + 15800))) (densSupG (arg1 (n.val + 15800)))) = true := by decide
theorem m0_w17 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 15850))) (dimF (n.val + 15850)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 15850))) (densSupG (n.val + 15850))) (densSupG (arg0 (n.val + 15850)))) = true := by decide
theorem m1_w17 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 15850))) (dimF (n.val + 15850)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 15850))) (densSupG (n.val + 15850))) (densSupG (arg1 (n.val + 15850)))) = true := by decide
theorem m0_w18 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 15900))) (dimF (n.val + 15900)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 15900))) (densSupG (n.val + 15900))) (densSupG (arg0 (n.val + 15900)))) = true := by decide
theorem m1_w18 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 15900))) (dimF (n.val + 15900)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 15900))) (densSupG (n.val + 15900))) (densSupG (arg1 (n.val + 15900)))) = true := by decide
theorem m0_w19 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 15950))) (dimF (n.val + 15950)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 15950))) (densSupG (n.val + 15950))) (densSupG (arg0 (n.val + 15950)))) = true := by decide
theorem m1_w19 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 15950))) (dimF (n.val + 15950)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 15950))) (densSupG (n.val + 15950))) (densSupG (arg1 (n.val + 15950)))) = true := by decide
theorem m0_w20 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 16000))) (dimF (n.val + 16000)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 16000))) (densSupG (n.val + 16000))) (densSupG (arg0 (n.val + 16000)))) = true := by decide
theorem m1_w20 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 16000))) (dimF (n.val + 16000)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 16000))) (densSupG (n.val + 16000))) (densSupG (arg1 (n.val + 16000)))) = true := by decide
theorem m0_w21 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 16050))) (dimF (n.val + 16050)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 16050))) (densSupG (n.val + 16050))) (densSupG (arg0 (n.val + 16050)))) = true := by decide
theorem m1_w21 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 16050))) (dimF (n.val + 16050)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 16050))) (densSupG (n.val + 16050))) (densSupG (arg1 (n.val + 16050)))) = true := by decide
theorem m0_w22 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 16100))) (dimF (n.val + 16100)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 16100))) (densSupG (n.val + 16100))) (densSupG (arg0 (n.val + 16100)))) = true := by decide
theorem m1_w22 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 16100))) (dimF (n.val + 16100)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 16100))) (densSupG (n.val + 16100))) (densSupG (arg1 (n.val + 16100)))) = true := by decide
theorem m0_w23 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 16150))) (dimF (n.val + 16150)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 16150))) (densSupG (n.val + 16150))) (densSupG (arg0 (n.val + 16150)))) = true := by decide
theorem m1_w23 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 16150))) (dimF (n.val + 16150)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 16150))) (densSupG (n.val + 16150))) (densSupG (arg1 (n.val + 16150)))) = true := by decide
theorem m0_w24 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 16200))) (dimF (n.val + 16200)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 16200))) (densSupG (n.val + 16200))) (densSupG (arg0 (n.val + 16200)))) = true := by decide
theorem m1_w24 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 16200))) (dimF (n.val + 16200)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 16200))) (densSupG (n.val + 16200))) (densSupG (arg1 (n.val + 16200)))) = true := by decide
theorem m0_w25 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 16250))) (dimF (n.val + 16250)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 16250))) (densSupG (n.val + 16250))) (densSupG (arg0 (n.val + 16250)))) = true := by decide
theorem m1_w25 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 16250))) (dimF (n.val + 16250)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 16250))) (densSupG (n.val + 16250))) (densSupG (arg1 (n.val + 16250)))) = true := by decide
theorem m0_w26 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 16300))) (dimF (n.val + 16300)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 16300))) (densSupG (n.val + 16300))) (densSupG (arg0 (n.val + 16300)))) = true := by decide
theorem m1_w26 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 16300))) (dimF (n.val + 16300)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 16300))) (densSupG (n.val + 16300))) (densSupG (arg1 (n.val + 16300)))) = true := by decide
theorem m0_w27 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 16350))) (dimF (n.val + 16350)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 16350))) (densSupG (n.val + 16350))) (densSupG (arg0 (n.val + 16350)))) = true := by decide
theorem m1_w27 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 16350))) (dimF (n.val + 16350)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 16350))) (densSupG (n.val + 16350))) (densSupG (arg1 (n.val + 16350)))) = true := by decide
theorem m0_w28 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 16400))) (dimF (n.val + 16400)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 16400))) (densSupG (n.val + 16400))) (densSupG (arg0 (n.val + 16400)))) = true := by decide
theorem m1_w28 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 16400))) (dimF (n.val + 16400)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 16400))) (densSupG (n.val + 16400))) (densSupG (arg1 (n.val + 16400)))) = true := by decide
theorem m0_w29 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 16450))) (dimF (n.val + 16450)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 16450))) (densSupG (n.val + 16450))) (densSupG (arg0 (n.val + 16450)))) = true := by decide
theorem m1_w29 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 16450))) (dimF (n.val + 16450)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 16450))) (densSupG (n.val + 16450))) (densSupG (arg1 (n.val + 16450)))) = true := by decide
theorem m0_w30 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 16500))) (dimF (n.val + 16500)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 16500))) (densSupG (n.val + 16500))) (densSupG (arg0 (n.val + 16500)))) = true := by decide
theorem m1_w30 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 16500))) (dimF (n.val + 16500)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 16500))) (densSupG (n.val + 16500))) (densSupG (arg1 (n.val + 16500)))) = true := by decide
theorem m0_w31 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 16550))) (dimF (n.val + 16550)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 16550))) (densSupG (n.val + 16550))) (densSupG (arg0 (n.val + 16550)))) = true := by decide
theorem m1_w31 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 16550))) (dimF (n.val + 16550)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 16550))) (densSupG (n.val + 16550))) (densSupG (arg1 (n.val + 16550)))) = true := by decide
theorem m0_w32 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 16600))) (dimF (n.val + 16600)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 16600))) (densSupG (n.val + 16600))) (densSupG (arg0 (n.val + 16600)))) = true := by decide
theorem m1_w32 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 16600))) (dimF (n.val + 16600)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 16600))) (densSupG (n.val + 16600))) (densSupG (arg1 (n.val + 16600)))) = true := by decide
theorem m0_w33 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 16650))) (dimF (n.val + 16650)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 16650))) (densSupG (n.val + 16650))) (densSupG (arg0 (n.val + 16650)))) = true := by decide
theorem m1_w33 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 16650))) (dimF (n.val + 16650)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 16650))) (densSupG (n.val + 16650))) (densSupG (arg1 (n.val + 16650)))) = true := by decide
theorem m0_w34 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 16700))) (dimF (n.val + 16700)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 16700))) (densSupG (n.val + 16700))) (densSupG (arg0 (n.val + 16700)))) = true := by decide
theorem m1_w34 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 16700))) (dimF (n.val + 16700)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 16700))) (densSupG (n.val + 16700))) (densSupG (arg1 (n.val + 16700)))) = true := by decide
theorem m0_w35 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 16750))) (dimF (n.val + 16750)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 16750))) (densSupG (n.val + 16750))) (densSupG (arg0 (n.val + 16750)))) = true := by decide
theorem m1_w35 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 16750))) (dimF (n.val + 16750)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 16750))) (densSupG (n.val + 16750))) (densSupG (arg1 (n.val + 16750)))) = true := by decide
theorem m0_w36 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 16800))) (dimF (n.val + 16800)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 16800))) (densSupG (n.val + 16800))) (densSupG (arg0 (n.val + 16800)))) = true := by decide
theorem m1_w36 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 16800))) (dimF (n.val + 16800)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 16800))) (densSupG (n.val + 16800))) (densSupG (arg1 (n.val + 16800)))) = true := by decide
theorem m0_w37 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 16850))) (dimF (n.val + 16850)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 16850))) (densSupG (n.val + 16850))) (densSupG (arg0 (n.val + 16850)))) = true := by decide
theorem m1_w37 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 16850))) (dimF (n.val + 16850)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 16850))) (densSupG (n.val + 16850))) (densSupG (arg1 (n.val + 16850)))) = true := by decide
theorem m0_w38 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 16900))) (dimF (n.val + 16900)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 16900))) (densSupG (n.val + 16900))) (densSupG (arg0 (n.val + 16900)))) = true := by decide
theorem m1_w38 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 16900))) (dimF (n.val + 16900)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 16900))) (densSupG (n.val + 16900))) (densSupG (arg1 (n.val + 16900)))) = true := by decide
theorem m0_w39 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 16950))) (dimF (n.val + 16950)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 16950))) (densSupG (n.val + 16950))) (densSupG (arg0 (n.val + 16950)))) = true := by decide
theorem m1_w39 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 16950))) (dimF (n.val + 16950)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 16950))) (densSupG (n.val + 16950))) (densSupG (arg1 (n.val + 16950)))) = true := by decide
theorem m0_w40 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 17000))) (dimF (n.val + 17000)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 17000))) (densSupG (n.val + 17000))) (densSupG (arg0 (n.val + 17000)))) = true := by decide
theorem m1_w40 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 17000))) (dimF (n.val + 17000)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 17000))) (densSupG (n.val + 17000))) (densSupG (arg1 (n.val + 17000)))) = true := by decide
theorem m0_w41 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 17050))) (dimF (n.val + 17050)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 17050))) (densSupG (n.val + 17050))) (densSupG (arg0 (n.val + 17050)))) = true := by decide
theorem m1_w41 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 17050))) (dimF (n.val + 17050)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 17050))) (densSupG (n.val + 17050))) (densSupG (arg1 (n.val + 17050)))) = true := by decide
theorem m0_w42 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 17100))) (dimF (n.val + 17100)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 17100))) (densSupG (n.val + 17100))) (densSupG (arg0 (n.val + 17100)))) = true := by decide
theorem m1_w42 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 17100))) (dimF (n.val + 17100)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 17100))) (densSupG (n.val + 17100))) (densSupG (arg1 (n.val + 17100)))) = true := by decide
theorem m0_w43 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 17150))) (dimF (n.val + 17150)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 17150))) (densSupG (n.val + 17150))) (densSupG (arg0 (n.val + 17150)))) = true := by decide
theorem m1_w43 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 17150))) (dimF (n.val + 17150)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 17150))) (densSupG (n.val + 17150))) (densSupG (arg1 (n.val + 17150)))) = true := by decide
theorem m0_w44 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 17200))) (dimF (n.val + 17200)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 17200))) (densSupG (n.val + 17200))) (densSupG (arg0 (n.val + 17200)))) = true := by decide
theorem m1_w44 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 17200))) (dimF (n.val + 17200)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 17200))) (densSupG (n.val + 17200))) (densSupG (arg1 (n.val + 17200)))) = true := by decide
theorem m0_w45 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 17250))) (dimF (n.val + 17250)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 17250))) (densSupG (n.val + 17250))) (densSupG (arg0 (n.val + 17250)))) = true := by decide
theorem m1_w45 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 17250))) (dimF (n.val + 17250)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 17250))) (densSupG (n.val + 17250))) (densSupG (arg1 (n.val + 17250)))) = true := by decide
theorem m0_w46 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 17300))) (dimF (n.val + 17300)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 17300))) (densSupG (n.val + 17300))) (densSupG (arg0 (n.val + 17300)))) = true := by decide
theorem m1_w46 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 17300))) (dimF (n.val + 17300)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 17300))) (densSupG (n.val + 17300))) (densSupG (arg1 (n.val + 17300)))) = true := by decide
theorem m0_w47 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 17350))) (dimF (n.val + 17350)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 17350))) (densSupG (n.val + 17350))) (densSupG (arg0 (n.val + 17350)))) = true := by decide
theorem m1_w47 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 17350))) (dimF (n.val + 17350)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 17350))) (densSupG (n.val + 17350))) (densSupG (arg1 (n.val + 17350)))) = true := by decide
theorem m0_w48 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 17400))) (dimF (n.val + 17400)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 17400))) (densSupG (n.val + 17400))) (densSupG (arg0 (n.val + 17400)))) = true := by decide
theorem m1_w48 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 17400))) (dimF (n.val + 17400)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 17400))) (densSupG (n.val + 17400))) (densSupG (arg1 (n.val + 17400)))) = true := by decide
theorem m0_w49 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 17450))) (dimF (n.val + 17450)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 17450))) (densSupG (n.val + 17450))) (densSupG (arg0 (n.val + 17450)))) = true := by decide
theorem m1_w49 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 17450))) (dimF (n.val + 17450)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 17450))) (densSupG (n.val + 17450))) (densSupG (arg1 (n.val + 17450)))) = true := by decide
theorem land0_range (n : ℕ) (hn0 : 15000 ≤ n) (hn1 : n < 17500) :
    (!Nat.blt (dimF (arg0 n)) (dimF n) ||
      Nat.beq (Nat.land (densSupG (arg0 n)) (densSupG n)) (densSupG (arg0 n))) = true := by
  by_cases h0 : n < 15050
  · have hoff : 15000 ≤ n := by omega
    have hnfin : n - 15000 < 50 := by omega
    simpa [Nat.sub_add_cancel hoff] using m0_w0 ⟨n - 15000, hnfin⟩
  ·
    by_cases h1 : n < 15100
    · have hoff : 15050 ≤ n := by omega
      have hnfin : n - 15050 < 50 := by omega
      simpa [Nat.sub_add_cancel hoff] using m0_w1 ⟨n - 15050, hnfin⟩
    ·
      by_cases h2 : n < 15150
      · have hoff : 15100 ≤ n := by omega
        have hnfin : n - 15100 < 50 := by omega
        simpa [Nat.sub_add_cancel hoff] using m0_w2 ⟨n - 15100, hnfin⟩
      ·
        by_cases h3 : n < 15200
        · have hoff : 15150 ≤ n := by omega
          have hnfin : n - 15150 < 50 := by omega
          simpa [Nat.sub_add_cancel hoff] using m0_w3 ⟨n - 15150, hnfin⟩
        ·
          by_cases h4 : n < 15250
          · have hoff : 15200 ≤ n := by omega
            have hnfin : n - 15200 < 50 := by omega
            simpa [Nat.sub_add_cancel hoff] using m0_w4 ⟨n - 15200, hnfin⟩
          ·
            by_cases h5 : n < 15300
            · have hoff : 15250 ≤ n := by omega
              have hnfin : n - 15250 < 50 := by omega
              simpa [Nat.sub_add_cancel hoff] using m0_w5 ⟨n - 15250, hnfin⟩
            ·
              by_cases h6 : n < 15350
              · have hoff : 15300 ≤ n := by omega
                have hnfin : n - 15300 < 50 := by omega
                simpa [Nat.sub_add_cancel hoff] using m0_w6 ⟨n - 15300, hnfin⟩
              ·
                by_cases h7 : n < 15400
                · have hoff : 15350 ≤ n := by omega
                  have hnfin : n - 15350 < 50 := by omega
                  simpa [Nat.sub_add_cancel hoff] using m0_w7 ⟨n - 15350, hnfin⟩
                ·
                  by_cases h8 : n < 15450
                  · have hoff : 15400 ≤ n := by omega
                    have hnfin : n - 15400 < 50 := by omega
                    simpa [Nat.sub_add_cancel hoff] using m0_w8 ⟨n - 15400, hnfin⟩
                  ·
                    by_cases h9 : n < 15500
                    · have hoff : 15450 ≤ n := by omega
                      have hnfin : n - 15450 < 50 := by omega
                      simpa [Nat.sub_add_cancel hoff] using m0_w9 ⟨n - 15450, hnfin⟩
                    ·
                      by_cases h10 : n < 15550
                      · have hoff : 15500 ≤ n := by omega
                        have hnfin : n - 15500 < 50 := by omega
                        simpa [Nat.sub_add_cancel hoff] using m0_w10 ⟨n - 15500, hnfin⟩
                      ·
                        by_cases h11 : n < 15600
                        · have hoff : 15550 ≤ n := by omega
                          have hnfin : n - 15550 < 50 := by omega
                          simpa [Nat.sub_add_cancel hoff] using m0_w11 ⟨n - 15550, hnfin⟩
                        ·
                          by_cases h12 : n < 15650
                          · have hoff : 15600 ≤ n := by omega
                            have hnfin : n - 15600 < 50 := by omega
                            simpa [Nat.sub_add_cancel hoff] using m0_w12 ⟨n - 15600, hnfin⟩
                          ·
                            by_cases h13 : n < 15700
                            · have hoff : 15650 ≤ n := by omega
                              have hnfin : n - 15650 < 50 := by omega
                              simpa [Nat.sub_add_cancel hoff] using m0_w13 ⟨n - 15650, hnfin⟩
                            ·
                              by_cases h14 : n < 15750
                              · have hoff : 15700 ≤ n := by omega
                                have hnfin : n - 15700 < 50 := by omega
                                simpa [Nat.sub_add_cancel hoff] using m0_w14 ⟨n - 15700, hnfin⟩
                              ·
                                by_cases h15 : n < 15800
                                · have hoff : 15750 ≤ n := by omega
                                  have hnfin : n - 15750 < 50 := by omega
                                  simpa [Nat.sub_add_cancel hoff] using m0_w15 ⟨n - 15750, hnfin⟩
                                ·
                                  by_cases h16 : n < 15850
                                  · have hoff : 15800 ≤ n := by omega
                                    have hnfin : n - 15800 < 50 := by omega
                                    simpa [Nat.sub_add_cancel hoff] using m0_w16 ⟨n - 15800, hnfin⟩
                                  ·
                                    by_cases h17 : n < 15900
                                    · have hoff : 15850 ≤ n := by omega
                                      have hnfin : n - 15850 < 50 := by omega
                                      simpa [Nat.sub_add_cancel hoff] using m0_w17 ⟨n - 15850, hnfin⟩
                                    ·
                                      by_cases h18 : n < 15950
                                      · have hoff : 15900 ≤ n := by omega
                                        have hnfin : n - 15900 < 50 := by omega
                                        simpa [Nat.sub_add_cancel hoff] using m0_w18 ⟨n - 15900, hnfin⟩
                                      ·
                                        by_cases h19 : n < 16000
                                        · have hoff : 15950 ≤ n := by omega
                                          have hnfin : n - 15950 < 50 := by omega
                                          simpa [Nat.sub_add_cancel hoff] using m0_w19 ⟨n - 15950, hnfin⟩
                                        ·
                                          by_cases h20 : n < 16050
                                          · have hoff : 16000 ≤ n := by omega
                                            have hnfin : n - 16000 < 50 := by omega
                                            simpa [Nat.sub_add_cancel hoff] using m0_w20 ⟨n - 16000, hnfin⟩
                                          ·
                                            by_cases h21 : n < 16100
                                            · have hoff : 16050 ≤ n := by omega
                                              have hnfin : n - 16050 < 50 := by omega
                                              simpa [Nat.sub_add_cancel hoff] using m0_w21 ⟨n - 16050, hnfin⟩
                                            ·
                                              by_cases h22 : n < 16150
                                              · have hoff : 16100 ≤ n := by omega
                                                have hnfin : n - 16100 < 50 := by omega
                                                simpa [Nat.sub_add_cancel hoff] using m0_w22 ⟨n - 16100, hnfin⟩
                                              ·
                                                by_cases h23 : n < 16200
                                                · have hoff : 16150 ≤ n := by omega
                                                  have hnfin : n - 16150 < 50 := by omega
                                                  simpa [Nat.sub_add_cancel hoff] using m0_w23 ⟨n - 16150, hnfin⟩
                                                ·
                                                  by_cases h24 : n < 16250
                                                  · have hoff : 16200 ≤ n := by omega
                                                    have hnfin : n - 16200 < 50 := by omega
                                                    simpa [Nat.sub_add_cancel hoff] using m0_w24 ⟨n - 16200, hnfin⟩
                                                  ·
                                                    by_cases h25 : n < 16300
                                                    · have hoff : 16250 ≤ n := by omega
                                                      have hnfin : n - 16250 < 50 := by omega
                                                      simpa [Nat.sub_add_cancel hoff] using m0_w25 ⟨n - 16250, hnfin⟩
                                                    ·
                                                      by_cases h26 : n < 16350
                                                      · have hoff : 16300 ≤ n := by omega
                                                        have hnfin : n - 16300 < 50 := by omega
                                                        simpa [Nat.sub_add_cancel hoff] using m0_w26 ⟨n - 16300, hnfin⟩
                                                      ·
                                                        by_cases h27 : n < 16400
                                                        · have hoff : 16350 ≤ n := by omega
                                                          have hnfin : n - 16350 < 50 := by omega
                                                          simpa [Nat.sub_add_cancel hoff] using m0_w27 ⟨n - 16350, hnfin⟩
                                                        ·
                                                          by_cases h28 : n < 16450
                                                          · have hoff : 16400 ≤ n := by omega
                                                            have hnfin : n - 16400 < 50 := by omega
                                                            simpa [Nat.sub_add_cancel hoff] using m0_w28 ⟨n - 16400, hnfin⟩
                                                          ·
                                                            by_cases h29 : n < 16500
                                                            · have hoff : 16450 ≤ n := by omega
                                                              have hnfin : n - 16450 < 50 := by omega
                                                              simpa [Nat.sub_add_cancel hoff] using m0_w29 ⟨n - 16450, hnfin⟩
                                                            ·
                                                              by_cases h30 : n < 16550
                                                              · have hoff : 16500 ≤ n := by omega
                                                                have hnfin : n - 16500 < 50 := by omega
                                                                simpa [Nat.sub_add_cancel hoff] using m0_w30 ⟨n - 16500, hnfin⟩
                                                              ·
                                                                by_cases h31 : n < 16600
                                                                · have hoff : 16550 ≤ n := by omega
                                                                  have hnfin : n - 16550 < 50 := by omega
                                                                  simpa [Nat.sub_add_cancel hoff] using m0_w31 ⟨n - 16550, hnfin⟩
                                                                ·
                                                                  by_cases h32 : n < 16650
                                                                  · have hoff : 16600 ≤ n := by omega
                                                                    have hnfin : n - 16600 < 50 := by omega
                                                                    simpa [Nat.sub_add_cancel hoff] using m0_w32 ⟨n - 16600, hnfin⟩
                                                                  ·
                                                                    by_cases h33 : n < 16700
                                                                    · have hoff : 16650 ≤ n := by omega
                                                                      have hnfin : n - 16650 < 50 := by omega
                                                                      simpa [Nat.sub_add_cancel hoff] using m0_w33 ⟨n - 16650, hnfin⟩
                                                                    ·
                                                                      by_cases h34 : n < 16750
                                                                      · have hoff : 16700 ≤ n := by omega
                                                                        have hnfin : n - 16700 < 50 := by omega
                                                                        simpa [Nat.sub_add_cancel hoff] using m0_w34 ⟨n - 16700, hnfin⟩
                                                                      ·
                                                                        by_cases h35 : n < 16800
                                                                        · have hoff : 16750 ≤ n := by omega
                                                                          have hnfin : n - 16750 < 50 := by omega
                                                                          simpa [Nat.sub_add_cancel hoff] using m0_w35 ⟨n - 16750, hnfin⟩
                                                                        ·
                                                                          by_cases h36 : n < 16850
                                                                          · have hoff : 16800 ≤ n := by omega
                                                                            have hnfin : n - 16800 < 50 := by omega
                                                                            simpa [Nat.sub_add_cancel hoff] using m0_w36 ⟨n - 16800, hnfin⟩
                                                                          ·
                                                                            by_cases h37 : n < 16900
                                                                            · have hoff : 16850 ≤ n := by omega
                                                                              have hnfin : n - 16850 < 50 := by omega
                                                                              simpa [Nat.sub_add_cancel hoff] using m0_w37 ⟨n - 16850, hnfin⟩
                                                                            ·
                                                                              by_cases h38 : n < 16950
                                                                              · have hoff : 16900 ≤ n := by omega
                                                                                have hnfin : n - 16900 < 50 := by omega
                                                                                simpa [Nat.sub_add_cancel hoff] using m0_w38 ⟨n - 16900, hnfin⟩
                                                                              ·
                                                                                by_cases h39 : n < 17000
                                                                                · have hoff : 16950 ≤ n := by omega
                                                                                  have hnfin : n - 16950 < 50 := by omega
                                                                                  simpa [Nat.sub_add_cancel hoff] using m0_w39 ⟨n - 16950, hnfin⟩
                                                                                ·
                                                                                  by_cases h40 : n < 17050
                                                                                  · have hoff : 17000 ≤ n := by omega
                                                                                    have hnfin : n - 17000 < 50 := by omega
                                                                                    simpa [Nat.sub_add_cancel hoff] using m0_w40 ⟨n - 17000, hnfin⟩
                                                                                  ·
                                                                                    by_cases h41 : n < 17100
                                                                                    · have hoff : 17050 ≤ n := by omega
                                                                                      have hnfin : n - 17050 < 50 := by omega
                                                                                      simpa [Nat.sub_add_cancel hoff] using m0_w41 ⟨n - 17050, hnfin⟩
                                                                                    ·
                                                                                      by_cases h42 : n < 17150
                                                                                      · have hoff : 17100 ≤ n := by omega
                                                                                        have hnfin : n - 17100 < 50 := by omega
                                                                                        simpa [Nat.sub_add_cancel hoff] using m0_w42 ⟨n - 17100, hnfin⟩
                                                                                      ·
                                                                                        by_cases h43 : n < 17200
                                                                                        · have hoff : 17150 ≤ n := by omega
                                                                                          have hnfin : n - 17150 < 50 := by omega
                                                                                          simpa [Nat.sub_add_cancel hoff] using m0_w43 ⟨n - 17150, hnfin⟩
                                                                                        ·
                                                                                          by_cases h44 : n < 17250
                                                                                          · have hoff : 17200 ≤ n := by omega
                                                                                            have hnfin : n - 17200 < 50 := by omega
                                                                                            simpa [Nat.sub_add_cancel hoff] using m0_w44 ⟨n - 17200, hnfin⟩
                                                                                          ·
                                                                                            by_cases h45 : n < 17300
                                                                                            · have hoff : 17250 ≤ n := by omega
                                                                                              have hnfin : n - 17250 < 50 := by omega
                                                                                              simpa [Nat.sub_add_cancel hoff] using m0_w45 ⟨n - 17250, hnfin⟩
                                                                                            ·
                                                                                              by_cases h46 : n < 17350
                                                                                              · have hoff : 17300 ≤ n := by omega
                                                                                                have hnfin : n - 17300 < 50 := by omega
                                                                                                simpa [Nat.sub_add_cancel hoff] using m0_w46 ⟨n - 17300, hnfin⟩
                                                                                              ·
                                                                                                by_cases h47 : n < 17400
                                                                                                · have hoff : 17350 ≤ n := by omega
                                                                                                  have hnfin : n - 17350 < 50 := by omega
                                                                                                  simpa [Nat.sub_add_cancel hoff] using m0_w47 ⟨n - 17350, hnfin⟩
                                                                                                ·
                                                                                                  by_cases h48 : n < 17450
                                                                                                  · have hoff : 17400 ≤ n := by omega
                                                                                                    have hnfin : n - 17400 < 50 := by omega
                                                                                                    simpa [Nat.sub_add_cancel hoff] using m0_w48 ⟨n - 17400, hnfin⟩
                                                                                                  ·
                                                                                                    by_cases h49 : n < 17500
                                                                                                    · have hoff : 17450 ≤ n := by omega
                                                                                                      have hnfin : n - 17450 < 50 := by omega
                                                                                                      simpa [Nat.sub_add_cancel hoff] using m0_w49 ⟨n - 17450, hnfin⟩
                                                                                                    ·
                                                                                                      omega
theorem land1_range (n : ℕ) (hn0 : 15000 ≤ n) (hn1 : n < 17500) :
    (!Nat.blt (dimF (arg1 n)) (dimF n) ||
      Nat.beq (Nat.land (densSupG (arg1 n)) (densSupG n)) (densSupG (arg1 n))) = true := by
  by_cases h0 : n < 15050
  · have hoff : 15000 ≤ n := by omega
    have hnfin : n - 15000 < 50 := by omega
    simpa [Nat.sub_add_cancel hoff] using m1_w0 ⟨n - 15000, hnfin⟩
  ·
    by_cases h1 : n < 15100
    · have hoff : 15050 ≤ n := by omega
      have hnfin : n - 15050 < 50 := by omega
      simpa [Nat.sub_add_cancel hoff] using m1_w1 ⟨n - 15050, hnfin⟩
    ·
      by_cases h2 : n < 15150
      · have hoff : 15100 ≤ n := by omega
        have hnfin : n - 15100 < 50 := by omega
        simpa [Nat.sub_add_cancel hoff] using m1_w2 ⟨n - 15100, hnfin⟩
      ·
        by_cases h3 : n < 15200
        · have hoff : 15150 ≤ n := by omega
          have hnfin : n - 15150 < 50 := by omega
          simpa [Nat.sub_add_cancel hoff] using m1_w3 ⟨n - 15150, hnfin⟩
        ·
          by_cases h4 : n < 15250
          · have hoff : 15200 ≤ n := by omega
            have hnfin : n - 15200 < 50 := by omega
            simpa [Nat.sub_add_cancel hoff] using m1_w4 ⟨n - 15200, hnfin⟩
          ·
            by_cases h5 : n < 15300
            · have hoff : 15250 ≤ n := by omega
              have hnfin : n - 15250 < 50 := by omega
              simpa [Nat.sub_add_cancel hoff] using m1_w5 ⟨n - 15250, hnfin⟩
            ·
              by_cases h6 : n < 15350
              · have hoff : 15300 ≤ n := by omega
                have hnfin : n - 15300 < 50 := by omega
                simpa [Nat.sub_add_cancel hoff] using m1_w6 ⟨n - 15300, hnfin⟩
              ·
                by_cases h7 : n < 15400
                · have hoff : 15350 ≤ n := by omega
                  have hnfin : n - 15350 < 50 := by omega
                  simpa [Nat.sub_add_cancel hoff] using m1_w7 ⟨n - 15350, hnfin⟩
                ·
                  by_cases h8 : n < 15450
                  · have hoff : 15400 ≤ n := by omega
                    have hnfin : n - 15400 < 50 := by omega
                    simpa [Nat.sub_add_cancel hoff] using m1_w8 ⟨n - 15400, hnfin⟩
                  ·
                    by_cases h9 : n < 15500
                    · have hoff : 15450 ≤ n := by omega
                      have hnfin : n - 15450 < 50 := by omega
                      simpa [Nat.sub_add_cancel hoff] using m1_w9 ⟨n - 15450, hnfin⟩
                    ·
                      by_cases h10 : n < 15550
                      · have hoff : 15500 ≤ n := by omega
                        have hnfin : n - 15500 < 50 := by omega
                        simpa [Nat.sub_add_cancel hoff] using m1_w10 ⟨n - 15500, hnfin⟩
                      ·
                        by_cases h11 : n < 15600
                        · have hoff : 15550 ≤ n := by omega
                          have hnfin : n - 15550 < 50 := by omega
                          simpa [Nat.sub_add_cancel hoff] using m1_w11 ⟨n - 15550, hnfin⟩
                        ·
                          by_cases h12 : n < 15650
                          · have hoff : 15600 ≤ n := by omega
                            have hnfin : n - 15600 < 50 := by omega
                            simpa [Nat.sub_add_cancel hoff] using m1_w12 ⟨n - 15600, hnfin⟩
                          ·
                            by_cases h13 : n < 15700
                            · have hoff : 15650 ≤ n := by omega
                              have hnfin : n - 15650 < 50 := by omega
                              simpa [Nat.sub_add_cancel hoff] using m1_w13 ⟨n - 15650, hnfin⟩
                            ·
                              by_cases h14 : n < 15750
                              · have hoff : 15700 ≤ n := by omega
                                have hnfin : n - 15700 < 50 := by omega
                                simpa [Nat.sub_add_cancel hoff] using m1_w14 ⟨n - 15700, hnfin⟩
                              ·
                                by_cases h15 : n < 15800
                                · have hoff : 15750 ≤ n := by omega
                                  have hnfin : n - 15750 < 50 := by omega
                                  simpa [Nat.sub_add_cancel hoff] using m1_w15 ⟨n - 15750, hnfin⟩
                                ·
                                  by_cases h16 : n < 15850
                                  · have hoff : 15800 ≤ n := by omega
                                    have hnfin : n - 15800 < 50 := by omega
                                    simpa [Nat.sub_add_cancel hoff] using m1_w16 ⟨n - 15800, hnfin⟩
                                  ·
                                    by_cases h17 : n < 15900
                                    · have hoff : 15850 ≤ n := by omega
                                      have hnfin : n - 15850 < 50 := by omega
                                      simpa [Nat.sub_add_cancel hoff] using m1_w17 ⟨n - 15850, hnfin⟩
                                    ·
                                      by_cases h18 : n < 15950
                                      · have hoff : 15900 ≤ n := by omega
                                        have hnfin : n - 15900 < 50 := by omega
                                        simpa [Nat.sub_add_cancel hoff] using m1_w18 ⟨n - 15900, hnfin⟩
                                      ·
                                        by_cases h19 : n < 16000
                                        · have hoff : 15950 ≤ n := by omega
                                          have hnfin : n - 15950 < 50 := by omega
                                          simpa [Nat.sub_add_cancel hoff] using m1_w19 ⟨n - 15950, hnfin⟩
                                        ·
                                          by_cases h20 : n < 16050
                                          · have hoff : 16000 ≤ n := by omega
                                            have hnfin : n - 16000 < 50 := by omega
                                            simpa [Nat.sub_add_cancel hoff] using m1_w20 ⟨n - 16000, hnfin⟩
                                          ·
                                            by_cases h21 : n < 16100
                                            · have hoff : 16050 ≤ n := by omega
                                              have hnfin : n - 16050 < 50 := by omega
                                              simpa [Nat.sub_add_cancel hoff] using m1_w21 ⟨n - 16050, hnfin⟩
                                            ·
                                              by_cases h22 : n < 16150
                                              · have hoff : 16100 ≤ n := by omega
                                                have hnfin : n - 16100 < 50 := by omega
                                                simpa [Nat.sub_add_cancel hoff] using m1_w22 ⟨n - 16100, hnfin⟩
                                              ·
                                                by_cases h23 : n < 16200
                                                · have hoff : 16150 ≤ n := by omega
                                                  have hnfin : n - 16150 < 50 := by omega
                                                  simpa [Nat.sub_add_cancel hoff] using m1_w23 ⟨n - 16150, hnfin⟩
                                                ·
                                                  by_cases h24 : n < 16250
                                                  · have hoff : 16200 ≤ n := by omega
                                                    have hnfin : n - 16200 < 50 := by omega
                                                    simpa [Nat.sub_add_cancel hoff] using m1_w24 ⟨n - 16200, hnfin⟩
                                                  ·
                                                    by_cases h25 : n < 16300
                                                    · have hoff : 16250 ≤ n := by omega
                                                      have hnfin : n - 16250 < 50 := by omega
                                                      simpa [Nat.sub_add_cancel hoff] using m1_w25 ⟨n - 16250, hnfin⟩
                                                    ·
                                                      by_cases h26 : n < 16350
                                                      · have hoff : 16300 ≤ n := by omega
                                                        have hnfin : n - 16300 < 50 := by omega
                                                        simpa [Nat.sub_add_cancel hoff] using m1_w26 ⟨n - 16300, hnfin⟩
                                                      ·
                                                        by_cases h27 : n < 16400
                                                        · have hoff : 16350 ≤ n := by omega
                                                          have hnfin : n - 16350 < 50 := by omega
                                                          simpa [Nat.sub_add_cancel hoff] using m1_w27 ⟨n - 16350, hnfin⟩
                                                        ·
                                                          by_cases h28 : n < 16450
                                                          · have hoff : 16400 ≤ n := by omega
                                                            have hnfin : n - 16400 < 50 := by omega
                                                            simpa [Nat.sub_add_cancel hoff] using m1_w28 ⟨n - 16400, hnfin⟩
                                                          ·
                                                            by_cases h29 : n < 16500
                                                            · have hoff : 16450 ≤ n := by omega
                                                              have hnfin : n - 16450 < 50 := by omega
                                                              simpa [Nat.sub_add_cancel hoff] using m1_w29 ⟨n - 16450, hnfin⟩
                                                            ·
                                                              by_cases h30 : n < 16550
                                                              · have hoff : 16500 ≤ n := by omega
                                                                have hnfin : n - 16500 < 50 := by omega
                                                                simpa [Nat.sub_add_cancel hoff] using m1_w30 ⟨n - 16500, hnfin⟩
                                                              ·
                                                                by_cases h31 : n < 16600
                                                                · have hoff : 16550 ≤ n := by omega
                                                                  have hnfin : n - 16550 < 50 := by omega
                                                                  simpa [Nat.sub_add_cancel hoff] using m1_w31 ⟨n - 16550, hnfin⟩
                                                                ·
                                                                  by_cases h32 : n < 16650
                                                                  · have hoff : 16600 ≤ n := by omega
                                                                    have hnfin : n - 16600 < 50 := by omega
                                                                    simpa [Nat.sub_add_cancel hoff] using m1_w32 ⟨n - 16600, hnfin⟩
                                                                  ·
                                                                    by_cases h33 : n < 16700
                                                                    · have hoff : 16650 ≤ n := by omega
                                                                      have hnfin : n - 16650 < 50 := by omega
                                                                      simpa [Nat.sub_add_cancel hoff] using m1_w33 ⟨n - 16650, hnfin⟩
                                                                    ·
                                                                      by_cases h34 : n < 16750
                                                                      · have hoff : 16700 ≤ n := by omega
                                                                        have hnfin : n - 16700 < 50 := by omega
                                                                        simpa [Nat.sub_add_cancel hoff] using m1_w34 ⟨n - 16700, hnfin⟩
                                                                      ·
                                                                        by_cases h35 : n < 16800
                                                                        · have hoff : 16750 ≤ n := by omega
                                                                          have hnfin : n - 16750 < 50 := by omega
                                                                          simpa [Nat.sub_add_cancel hoff] using m1_w35 ⟨n - 16750, hnfin⟩
                                                                        ·
                                                                          by_cases h36 : n < 16850
                                                                          · have hoff : 16800 ≤ n := by omega
                                                                            have hnfin : n - 16800 < 50 := by omega
                                                                            simpa [Nat.sub_add_cancel hoff] using m1_w36 ⟨n - 16800, hnfin⟩
                                                                          ·
                                                                            by_cases h37 : n < 16900
                                                                            · have hoff : 16850 ≤ n := by omega
                                                                              have hnfin : n - 16850 < 50 := by omega
                                                                              simpa [Nat.sub_add_cancel hoff] using m1_w37 ⟨n - 16850, hnfin⟩
                                                                            ·
                                                                              by_cases h38 : n < 16950
                                                                              · have hoff : 16900 ≤ n := by omega
                                                                                have hnfin : n - 16900 < 50 := by omega
                                                                                simpa [Nat.sub_add_cancel hoff] using m1_w38 ⟨n - 16900, hnfin⟩
                                                                              ·
                                                                                by_cases h39 : n < 17000
                                                                                · have hoff : 16950 ≤ n := by omega
                                                                                  have hnfin : n - 16950 < 50 := by omega
                                                                                  simpa [Nat.sub_add_cancel hoff] using m1_w39 ⟨n - 16950, hnfin⟩
                                                                                ·
                                                                                  by_cases h40 : n < 17050
                                                                                  · have hoff : 17000 ≤ n := by omega
                                                                                    have hnfin : n - 17000 < 50 := by omega
                                                                                    simpa [Nat.sub_add_cancel hoff] using m1_w40 ⟨n - 17000, hnfin⟩
                                                                                  ·
                                                                                    by_cases h41 : n < 17100
                                                                                    · have hoff : 17050 ≤ n := by omega
                                                                                      have hnfin : n - 17050 < 50 := by omega
                                                                                      simpa [Nat.sub_add_cancel hoff] using m1_w41 ⟨n - 17050, hnfin⟩
                                                                                    ·
                                                                                      by_cases h42 : n < 17150
                                                                                      · have hoff : 17100 ≤ n := by omega
                                                                                        have hnfin : n - 17100 < 50 := by omega
                                                                                        simpa [Nat.sub_add_cancel hoff] using m1_w42 ⟨n - 17100, hnfin⟩
                                                                                      ·
                                                                                        by_cases h43 : n < 17200
                                                                                        · have hoff : 17150 ≤ n := by omega
                                                                                          have hnfin : n - 17150 < 50 := by omega
                                                                                          simpa [Nat.sub_add_cancel hoff] using m1_w43 ⟨n - 17150, hnfin⟩
                                                                                        ·
                                                                                          by_cases h44 : n < 17250
                                                                                          · have hoff : 17200 ≤ n := by omega
                                                                                            have hnfin : n - 17200 < 50 := by omega
                                                                                            simpa [Nat.sub_add_cancel hoff] using m1_w44 ⟨n - 17200, hnfin⟩
                                                                                          ·
                                                                                            by_cases h45 : n < 17300
                                                                                            · have hoff : 17250 ≤ n := by omega
                                                                                              have hnfin : n - 17250 < 50 := by omega
                                                                                              simpa [Nat.sub_add_cancel hoff] using m1_w45 ⟨n - 17250, hnfin⟩
                                                                                            ·
                                                                                              by_cases h46 : n < 17350
                                                                                              · have hoff : 17300 ≤ n := by omega
                                                                                                have hnfin : n - 17300 < 50 := by omega
                                                                                                simpa [Nat.sub_add_cancel hoff] using m1_w46 ⟨n - 17300, hnfin⟩
                                                                                              ·
                                                                                                by_cases h47 : n < 17400
                                                                                                · have hoff : 17350 ≤ n := by omega
                                                                                                  have hnfin : n - 17350 < 50 := by omega
                                                                                                  simpa [Nat.sub_add_cancel hoff] using m1_w47 ⟨n - 17350, hnfin⟩
                                                                                                ·
                                                                                                  by_cases h48 : n < 17450
                                                                                                  · have hoff : 17400 ≤ n := by omega
                                                                                                    have hnfin : n - 17400 < 50 := by omega
                                                                                                    simpa [Nat.sub_add_cancel hoff] using m1_w48 ⟨n - 17400, hnfin⟩
                                                                                                  ·
                                                                                                    by_cases h49 : n < 17500
                                                                                                    · have hoff : 17450 ≤ n := by omega
                                                                                                      have hnfin : n - 17450 < 50 := by omega
                                                                                                      simpa [Nat.sub_add_cancel hoff] using m1_w49 ⟨n - 17450, hnfin⟩
                                                                                                    ·
                                                                                                      omega
end IntMul.Kappa.R8.Bit.Oppbank.LandMonoFixA6


