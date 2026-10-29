-- Prove2me | Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankLandMonoDim3
-- name    : IntMul_Kappa_R8_Data_BitOppbankLandMonoDim3
-- status  : Definition
-- author  : @Ethan Cheung Wang
-- created : 2026-10-28T21:09:37.278387+00:00
-- url     : https://prove2.me/theorems/7953f28b-9d01-4c4e-aabf-374a22ee7dcb
-- title:
--   Dim-gated densSup land mono pack 3
-- statement:
--   # Dim-gated densSup land certificates, pack 3
--
--   For densified windows covering roughly $[7500,10000)$,
--   $$
--   \dim F(\mathrm{arg}_i n)<\dim F(n)
--   \Rightarrow
--   \mathrm{densSupG}(\mathrm{arg}_i n)\mathbin{\&}\mathrm{densSupG}(n)=\mathrm{densSupG}(\mathrm{arg}_i n).
--   $$
--   `decide` on Fin 50 (no `native_decide`).
-- source:
--   R8 BitOppbank densSup_land_mono

-- LandMonoDim pack 3: dim-gated densSupG child-land on windows starting in offsets list
-- Proves (dimF(arg_i n) < dimF n) → land(densSupG(arg_i n), densSupG n)=densSupG(arg_i n)

import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankPnd
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankSupG
import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 1000000
set_option exponentiation.threshold 2000

open IntMul.Kappa.R8.Bit.Oppbank.Pnd
open IntMul.Kappa.R8.Bit.Oppbank.SupG

namespace IntMul.Kappa.R8.Bit.Oppbank.LandMonoDim3

private def arg0 (n : ℕ) : ℕ := Nat.land (argF n) 65535
private def arg1 (n : ℕ) : ℕ := Nat.shiftRight (argF n) 16

private theorem m0_w0 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 7500))) (dimF (n.val + 7500)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 7500))) (densSupG (n.val + 7500))) (densSupG (arg0 (n.val + 7500)))) = true := by decide
private theorem m1_w0 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 7500))) (dimF (n.val + 7500)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 7500))) (densSupG (n.val + 7500))) (densSupG (arg1 (n.val + 7500)))) = true := by decide
private theorem m0_w1 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 7550))) (dimF (n.val + 7550)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 7550))) (densSupG (n.val + 7550))) (densSupG (arg0 (n.val + 7550)))) = true := by decide
private theorem m1_w1 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 7550))) (dimF (n.val + 7550)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 7550))) (densSupG (n.val + 7550))) (densSupG (arg1 (n.val + 7550)))) = true := by decide
private theorem m0_w2 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 7600))) (dimF (n.val + 7600)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 7600))) (densSupG (n.val + 7600))) (densSupG (arg0 (n.val + 7600)))) = true := by decide
private theorem m1_w2 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 7600))) (dimF (n.val + 7600)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 7600))) (densSupG (n.val + 7600))) (densSupG (arg1 (n.val + 7600)))) = true := by decide
private theorem m0_w3 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 7650))) (dimF (n.val + 7650)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 7650))) (densSupG (n.val + 7650))) (densSupG (arg0 (n.val + 7650)))) = true := by decide
private theorem m1_w3 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 7650))) (dimF (n.val + 7650)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 7650))) (densSupG (n.val + 7650))) (densSupG (arg1 (n.val + 7650)))) = true := by decide
private theorem m0_w4 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 7700))) (dimF (n.val + 7700)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 7700))) (densSupG (n.val + 7700))) (densSupG (arg0 (n.val + 7700)))) = true := by decide
private theorem m1_w4 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 7700))) (dimF (n.val + 7700)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 7700))) (densSupG (n.val + 7700))) (densSupG (arg1 (n.val + 7700)))) = true := by decide
private theorem m0_w5 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 7750))) (dimF (n.val + 7750)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 7750))) (densSupG (n.val + 7750))) (densSupG (arg0 (n.val + 7750)))) = true := by decide
private theorem m1_w5 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 7750))) (dimF (n.val + 7750)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 7750))) (densSupG (n.val + 7750))) (densSupG (arg1 (n.val + 7750)))) = true := by decide
private theorem m0_w6 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 7800))) (dimF (n.val + 7800)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 7800))) (densSupG (n.val + 7800))) (densSupG (arg0 (n.val + 7800)))) = true := by decide
private theorem m1_w6 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 7800))) (dimF (n.val + 7800)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 7800))) (densSupG (n.val + 7800))) (densSupG (arg1 (n.val + 7800)))) = true := by decide
private theorem m0_w7 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 7850))) (dimF (n.val + 7850)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 7850))) (densSupG (n.val + 7850))) (densSupG (arg0 (n.val + 7850)))) = true := by decide
private theorem m1_w7 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 7850))) (dimF (n.val + 7850)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 7850))) (densSupG (n.val + 7850))) (densSupG (arg1 (n.val + 7850)))) = true := by decide
private theorem m0_w8 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 7900))) (dimF (n.val + 7900)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 7900))) (densSupG (n.val + 7900))) (densSupG (arg0 (n.val + 7900)))) = true := by decide
private theorem m1_w8 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 7900))) (dimF (n.val + 7900)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 7900))) (densSupG (n.val + 7900))) (densSupG (arg1 (n.val + 7900)))) = true := by decide
private theorem m0_w9 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 7950))) (dimF (n.val + 7950)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 7950))) (densSupG (n.val + 7950))) (densSupG (arg0 (n.val + 7950)))) = true := by decide
private theorem m1_w9 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 7950))) (dimF (n.val + 7950)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 7950))) (densSupG (n.val + 7950))) (densSupG (arg1 (n.val + 7950)))) = true := by decide
private theorem m0_w10 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 8000))) (dimF (n.val + 8000)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 8000))) (densSupG (n.val + 8000))) (densSupG (arg0 (n.val + 8000)))) = true := by decide
private theorem m1_w10 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 8000))) (dimF (n.val + 8000)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 8000))) (densSupG (n.val + 8000))) (densSupG (arg1 (n.val + 8000)))) = true := by decide
private theorem m0_w11 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 8050))) (dimF (n.val + 8050)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 8050))) (densSupG (n.val + 8050))) (densSupG (arg0 (n.val + 8050)))) = true := by decide
private theorem m1_w11 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 8050))) (dimF (n.val + 8050)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 8050))) (densSupG (n.val + 8050))) (densSupG (arg1 (n.val + 8050)))) = true := by decide
private theorem m0_w12 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 8100))) (dimF (n.val + 8100)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 8100))) (densSupG (n.val + 8100))) (densSupG (arg0 (n.val + 8100)))) = true := by decide
private theorem m1_w12 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 8100))) (dimF (n.val + 8100)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 8100))) (densSupG (n.val + 8100))) (densSupG (arg1 (n.val + 8100)))) = true := by decide
private theorem m0_w13 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 8150))) (dimF (n.val + 8150)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 8150))) (densSupG (n.val + 8150))) (densSupG (arg0 (n.val + 8150)))) = true := by decide
private theorem m1_w13 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 8150))) (dimF (n.val + 8150)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 8150))) (densSupG (n.val + 8150))) (densSupG (arg1 (n.val + 8150)))) = true := by decide
private theorem m0_w14 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 8200))) (dimF (n.val + 8200)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 8200))) (densSupG (n.val + 8200))) (densSupG (arg0 (n.val + 8200)))) = true := by decide
private theorem m1_w14 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 8200))) (dimF (n.val + 8200)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 8200))) (densSupG (n.val + 8200))) (densSupG (arg1 (n.val + 8200)))) = true := by decide
private theorem m0_w15 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 8250))) (dimF (n.val + 8250)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 8250))) (densSupG (n.val + 8250))) (densSupG (arg0 (n.val + 8250)))) = true := by decide
private theorem m1_w15 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 8250))) (dimF (n.val + 8250)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 8250))) (densSupG (n.val + 8250))) (densSupG (arg1 (n.val + 8250)))) = true := by decide
private theorem m0_w16 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 8300))) (dimF (n.val + 8300)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 8300))) (densSupG (n.val + 8300))) (densSupG (arg0 (n.val + 8300)))) = true := by decide
private theorem m1_w16 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 8300))) (dimF (n.val + 8300)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 8300))) (densSupG (n.val + 8300))) (densSupG (arg1 (n.val + 8300)))) = true := by decide
private theorem m0_w17 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 8350))) (dimF (n.val + 8350)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 8350))) (densSupG (n.val + 8350))) (densSupG (arg0 (n.val + 8350)))) = true := by decide
private theorem m1_w17 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 8350))) (dimF (n.val + 8350)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 8350))) (densSupG (n.val + 8350))) (densSupG (arg1 (n.val + 8350)))) = true := by decide
private theorem m0_w18 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 8400))) (dimF (n.val + 8400)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 8400))) (densSupG (n.val + 8400))) (densSupG (arg0 (n.val + 8400)))) = true := by decide
private theorem m1_w18 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 8400))) (dimF (n.val + 8400)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 8400))) (densSupG (n.val + 8400))) (densSupG (arg1 (n.val + 8400)))) = true := by decide
private theorem m0_w19 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 8450))) (dimF (n.val + 8450)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 8450))) (densSupG (n.val + 8450))) (densSupG (arg0 (n.val + 8450)))) = true := by decide
private theorem m1_w19 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 8450))) (dimF (n.val + 8450)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 8450))) (densSupG (n.val + 8450))) (densSupG (arg1 (n.val + 8450)))) = true := by decide
private theorem m0_w20 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 8500))) (dimF (n.val + 8500)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 8500))) (densSupG (n.val + 8500))) (densSupG (arg0 (n.val + 8500)))) = true := by decide
private theorem m1_w20 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 8500))) (dimF (n.val + 8500)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 8500))) (densSupG (n.val + 8500))) (densSupG (arg1 (n.val + 8500)))) = true := by decide
private theorem m0_w21 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 8550))) (dimF (n.val + 8550)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 8550))) (densSupG (n.val + 8550))) (densSupG (arg0 (n.val + 8550)))) = true := by decide
private theorem m1_w21 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 8550))) (dimF (n.val + 8550)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 8550))) (densSupG (n.val + 8550))) (densSupG (arg1 (n.val + 8550)))) = true := by decide
private theorem m0_w22 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 8600))) (dimF (n.val + 8600)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 8600))) (densSupG (n.val + 8600))) (densSupG (arg0 (n.val + 8600)))) = true := by decide
private theorem m1_w22 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 8600))) (dimF (n.val + 8600)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 8600))) (densSupG (n.val + 8600))) (densSupG (arg1 (n.val + 8600)))) = true := by decide
private theorem m0_w23 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 8650))) (dimF (n.val + 8650)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 8650))) (densSupG (n.val + 8650))) (densSupG (arg0 (n.val + 8650)))) = true := by decide
private theorem m1_w23 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 8650))) (dimF (n.val + 8650)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 8650))) (densSupG (n.val + 8650))) (densSupG (arg1 (n.val + 8650)))) = true := by decide
private theorem m0_w24 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 8700))) (dimF (n.val + 8700)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 8700))) (densSupG (n.val + 8700))) (densSupG (arg0 (n.val + 8700)))) = true := by decide
private theorem m1_w24 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 8700))) (dimF (n.val + 8700)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 8700))) (densSupG (n.val + 8700))) (densSupG (arg1 (n.val + 8700)))) = true := by decide
private theorem m0_w25 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 8750))) (dimF (n.val + 8750)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 8750))) (densSupG (n.val + 8750))) (densSupG (arg0 (n.val + 8750)))) = true := by decide
private theorem m1_w25 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 8750))) (dimF (n.val + 8750)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 8750))) (densSupG (n.val + 8750))) (densSupG (arg1 (n.val + 8750)))) = true := by decide
private theorem m0_w26 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 8800))) (dimF (n.val + 8800)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 8800))) (densSupG (n.val + 8800))) (densSupG (arg0 (n.val + 8800)))) = true := by decide
private theorem m1_w26 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 8800))) (dimF (n.val + 8800)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 8800))) (densSupG (n.val + 8800))) (densSupG (arg1 (n.val + 8800)))) = true := by decide
private theorem m0_w27 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 8850))) (dimF (n.val + 8850)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 8850))) (densSupG (n.val + 8850))) (densSupG (arg0 (n.val + 8850)))) = true := by decide
private theorem m1_w27 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 8850))) (dimF (n.val + 8850)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 8850))) (densSupG (n.val + 8850))) (densSupG (arg1 (n.val + 8850)))) = true := by decide
private theorem m0_w28 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 8900))) (dimF (n.val + 8900)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 8900))) (densSupG (n.val + 8900))) (densSupG (arg0 (n.val + 8900)))) = true := by decide
private theorem m1_w28 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 8900))) (dimF (n.val + 8900)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 8900))) (densSupG (n.val + 8900))) (densSupG (arg1 (n.val + 8900)))) = true := by decide
private theorem m0_w29 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 8950))) (dimF (n.val + 8950)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 8950))) (densSupG (n.val + 8950))) (densSupG (arg0 (n.val + 8950)))) = true := by decide
private theorem m1_w29 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 8950))) (dimF (n.val + 8950)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 8950))) (densSupG (n.val + 8950))) (densSupG (arg1 (n.val + 8950)))) = true := by decide
private theorem m0_w30 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 9000))) (dimF (n.val + 9000)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 9000))) (densSupG (n.val + 9000))) (densSupG (arg0 (n.val + 9000)))) = true := by decide
private theorem m1_w30 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 9000))) (dimF (n.val + 9000)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 9000))) (densSupG (n.val + 9000))) (densSupG (arg1 (n.val + 9000)))) = true := by decide
private theorem m0_w31 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 9050))) (dimF (n.val + 9050)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 9050))) (densSupG (n.val + 9050))) (densSupG (arg0 (n.val + 9050)))) = true := by decide
private theorem m1_w31 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 9050))) (dimF (n.val + 9050)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 9050))) (densSupG (n.val + 9050))) (densSupG (arg1 (n.val + 9050)))) = true := by decide
private theorem m0_w32 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 9100))) (dimF (n.val + 9100)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 9100))) (densSupG (n.val + 9100))) (densSupG (arg0 (n.val + 9100)))) = true := by decide
private theorem m1_w32 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 9100))) (dimF (n.val + 9100)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 9100))) (densSupG (n.val + 9100))) (densSupG (arg1 (n.val + 9100)))) = true := by decide
private theorem m0_w33 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 9150))) (dimF (n.val + 9150)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 9150))) (densSupG (n.val + 9150))) (densSupG (arg0 (n.val + 9150)))) = true := by decide
private theorem m1_w33 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 9150))) (dimF (n.val + 9150)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 9150))) (densSupG (n.val + 9150))) (densSupG (arg1 (n.val + 9150)))) = true := by decide
private theorem m0_w34 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 9200))) (dimF (n.val + 9200)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 9200))) (densSupG (n.val + 9200))) (densSupG (arg0 (n.val + 9200)))) = true := by decide
private theorem m1_w34 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 9200))) (dimF (n.val + 9200)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 9200))) (densSupG (n.val + 9200))) (densSupG (arg1 (n.val + 9200)))) = true := by decide
private theorem m0_w35 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 9250))) (dimF (n.val + 9250)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 9250))) (densSupG (n.val + 9250))) (densSupG (arg0 (n.val + 9250)))) = true := by decide
private theorem m1_w35 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 9250))) (dimF (n.val + 9250)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 9250))) (densSupG (n.val + 9250))) (densSupG (arg1 (n.val + 9250)))) = true := by decide
private theorem m0_w36 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 9300))) (dimF (n.val + 9300)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 9300))) (densSupG (n.val + 9300))) (densSupG (arg0 (n.val + 9300)))) = true := by decide
private theorem m1_w36 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 9300))) (dimF (n.val + 9300)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 9300))) (densSupG (n.val + 9300))) (densSupG (arg1 (n.val + 9300)))) = true := by decide
private theorem m0_w37 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 9350))) (dimF (n.val + 9350)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 9350))) (densSupG (n.val + 9350))) (densSupG (arg0 (n.val + 9350)))) = true := by decide
private theorem m1_w37 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 9350))) (dimF (n.val + 9350)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 9350))) (densSupG (n.val + 9350))) (densSupG (arg1 (n.val + 9350)))) = true := by decide
private theorem m0_w38 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 9400))) (dimF (n.val + 9400)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 9400))) (densSupG (n.val + 9400))) (densSupG (arg0 (n.val + 9400)))) = true := by decide
private theorem m1_w38 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 9400))) (dimF (n.val + 9400)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 9400))) (densSupG (n.val + 9400))) (densSupG (arg1 (n.val + 9400)))) = true := by decide
private theorem m0_w39 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 9450))) (dimF (n.val + 9450)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 9450))) (densSupG (n.val + 9450))) (densSupG (arg0 (n.val + 9450)))) = true := by decide
private theorem m1_w39 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 9450))) (dimF (n.val + 9450)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 9450))) (densSupG (n.val + 9450))) (densSupG (arg1 (n.val + 9450)))) = true := by decide
private theorem m0_w40 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 9500))) (dimF (n.val + 9500)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 9500))) (densSupG (n.val + 9500))) (densSupG (arg0 (n.val + 9500)))) = true := by decide
private theorem m1_w40 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 9500))) (dimF (n.val + 9500)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 9500))) (densSupG (n.val + 9500))) (densSupG (arg1 (n.val + 9500)))) = true := by decide
private theorem m0_w41 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 9550))) (dimF (n.val + 9550)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 9550))) (densSupG (n.val + 9550))) (densSupG (arg0 (n.val + 9550)))) = true := by decide
private theorem m1_w41 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 9550))) (dimF (n.val + 9550)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 9550))) (densSupG (n.val + 9550))) (densSupG (arg1 (n.val + 9550)))) = true := by decide
private theorem m0_w42 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 9600))) (dimF (n.val + 9600)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 9600))) (densSupG (n.val + 9600))) (densSupG (arg0 (n.val + 9600)))) = true := by decide
private theorem m1_w42 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 9600))) (dimF (n.val + 9600)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 9600))) (densSupG (n.val + 9600))) (densSupG (arg1 (n.val + 9600)))) = true := by decide
private theorem m0_w43 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 9650))) (dimF (n.val + 9650)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 9650))) (densSupG (n.val + 9650))) (densSupG (arg0 (n.val + 9650)))) = true := by decide
private theorem m1_w43 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 9650))) (dimF (n.val + 9650)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 9650))) (densSupG (n.val + 9650))) (densSupG (arg1 (n.val + 9650)))) = true := by decide
private theorem m0_w44 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 9700))) (dimF (n.val + 9700)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 9700))) (densSupG (n.val + 9700))) (densSupG (arg0 (n.val + 9700)))) = true := by decide
private theorem m1_w44 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 9700))) (dimF (n.val + 9700)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 9700))) (densSupG (n.val + 9700))) (densSupG (arg1 (n.val + 9700)))) = true := by decide
private theorem m0_w45 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 9750))) (dimF (n.val + 9750)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 9750))) (densSupG (n.val + 9750))) (densSupG (arg0 (n.val + 9750)))) = true := by decide
private theorem m1_w45 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 9750))) (dimF (n.val + 9750)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 9750))) (densSupG (n.val + 9750))) (densSupG (arg1 (n.val + 9750)))) = true := by decide
private theorem m0_w46 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 9800))) (dimF (n.val + 9800)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 9800))) (densSupG (n.val + 9800))) (densSupG (arg0 (n.val + 9800)))) = true := by decide
private theorem m1_w46 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 9800))) (dimF (n.val + 9800)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 9800))) (densSupG (n.val + 9800))) (densSupG (arg1 (n.val + 9800)))) = true := by decide
private theorem m0_w47 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 9850))) (dimF (n.val + 9850)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 9850))) (densSupG (n.val + 9850))) (densSupG (arg0 (n.val + 9850)))) = true := by decide
private theorem m1_w47 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 9850))) (dimF (n.val + 9850)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 9850))) (densSupG (n.val + 9850))) (densSupG (arg1 (n.val + 9850)))) = true := by decide
private theorem m0_w48 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 9900))) (dimF (n.val + 9900)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 9900))) (densSupG (n.val + 9900))) (densSupG (arg0 (n.val + 9900)))) = true := by decide
private theorem m1_w48 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 9900))) (dimF (n.val + 9900)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 9900))) (densSupG (n.val + 9900))) (densSupG (arg1 (n.val + 9900)))) = true := by decide
private theorem m0_w49 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 9950))) (dimF (n.val + 9950)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 9950))) (densSupG (n.val + 9950))) (densSupG (arg0 (n.val + 9950)))) = true := by decide
private theorem m1_w49 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 9950))) (dimF (n.val + 9950)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 9950))) (densSupG (n.val + 9950))) (densSupG (arg1 (n.val + 9950)))) = true := by decide

end IntMul.Kappa.R8.Bit.Oppbank.LandMonoDim3


