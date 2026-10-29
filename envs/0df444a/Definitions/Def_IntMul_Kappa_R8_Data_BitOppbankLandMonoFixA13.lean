-- Prove2me | Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankLandMonoFixA13
-- name    : IntMul_Kappa_R8_Data_BitOppbankLandMonoFixA13
-- status  : Definition
-- author  : @Ethan Cheung Wang
-- created : 2026-10-28T21:16:37.103869+00:00
-- url     : https://prove2.me/theorems/068257f5-b609-4af7-bfaa-9efd3fb3f9c9
-- title:
--   Dim-gated densSup land mono FixA pack 13
-- statement:
--   # Dim-gated densSup land (PndFix), pack A13
--
--   Range consolidators for $n\in[32500,35000)$.
-- source:
--   R8 BitOppbank PndFix

-- LandMonoFixA13: PUBLIC dim-gated land + range consolidators (PndFix)
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
namespace IntMul.Kappa.R8.Bit.Oppbank.LandMonoFixA13
def arg0 (n : ℕ) : ℕ := Nat.land (argF n) 65535
def arg1 (n : ℕ) : ℕ := Nat.shiftRight (argF n) 16
theorem m0_w0 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 32500))) (dimF (n.val + 32500)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 32500))) (densSupG (n.val + 32500))) (densSupG (arg0 (n.val + 32500)))) = true := by decide
theorem m1_w0 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 32500))) (dimF (n.val + 32500)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 32500))) (densSupG (n.val + 32500))) (densSupG (arg1 (n.val + 32500)))) = true := by decide
theorem m0_w1 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 32550))) (dimF (n.val + 32550)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 32550))) (densSupG (n.val + 32550))) (densSupG (arg0 (n.val + 32550)))) = true := by decide
theorem m1_w1 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 32550))) (dimF (n.val + 32550)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 32550))) (densSupG (n.val + 32550))) (densSupG (arg1 (n.val + 32550)))) = true := by decide
theorem m0_w2 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 32600))) (dimF (n.val + 32600)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 32600))) (densSupG (n.val + 32600))) (densSupG (arg0 (n.val + 32600)))) = true := by decide
theorem m1_w2 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 32600))) (dimF (n.val + 32600)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 32600))) (densSupG (n.val + 32600))) (densSupG (arg1 (n.val + 32600)))) = true := by decide
theorem m0_w3 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 32650))) (dimF (n.val + 32650)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 32650))) (densSupG (n.val + 32650))) (densSupG (arg0 (n.val + 32650)))) = true := by decide
theorem m1_w3 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 32650))) (dimF (n.val + 32650)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 32650))) (densSupG (n.val + 32650))) (densSupG (arg1 (n.val + 32650)))) = true := by decide
theorem m0_w4 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 32700))) (dimF (n.val + 32700)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 32700))) (densSupG (n.val + 32700))) (densSupG (arg0 (n.val + 32700)))) = true := by decide
theorem m1_w4 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 32700))) (dimF (n.val + 32700)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 32700))) (densSupG (n.val + 32700))) (densSupG (arg1 (n.val + 32700)))) = true := by decide
theorem m0_w5 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 32750))) (dimF (n.val + 32750)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 32750))) (densSupG (n.val + 32750))) (densSupG (arg0 (n.val + 32750)))) = true := by decide
theorem m1_w5 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 32750))) (dimF (n.val + 32750)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 32750))) (densSupG (n.val + 32750))) (densSupG (arg1 (n.val + 32750)))) = true := by decide
theorem m0_w6 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 32800))) (dimF (n.val + 32800)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 32800))) (densSupG (n.val + 32800))) (densSupG (arg0 (n.val + 32800)))) = true := by decide
theorem m1_w6 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 32800))) (dimF (n.val + 32800)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 32800))) (densSupG (n.val + 32800))) (densSupG (arg1 (n.val + 32800)))) = true := by decide
theorem m0_w7 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 32850))) (dimF (n.val + 32850)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 32850))) (densSupG (n.val + 32850))) (densSupG (arg0 (n.val + 32850)))) = true := by decide
theorem m1_w7 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 32850))) (dimF (n.val + 32850)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 32850))) (densSupG (n.val + 32850))) (densSupG (arg1 (n.val + 32850)))) = true := by decide
theorem m0_w8 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 32900))) (dimF (n.val + 32900)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 32900))) (densSupG (n.val + 32900))) (densSupG (arg0 (n.val + 32900)))) = true := by decide
theorem m1_w8 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 32900))) (dimF (n.val + 32900)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 32900))) (densSupG (n.val + 32900))) (densSupG (arg1 (n.val + 32900)))) = true := by decide
theorem m0_w9 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 32950))) (dimF (n.val + 32950)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 32950))) (densSupG (n.val + 32950))) (densSupG (arg0 (n.val + 32950)))) = true := by decide
theorem m1_w9 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 32950))) (dimF (n.val + 32950)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 32950))) (densSupG (n.val + 32950))) (densSupG (arg1 (n.val + 32950)))) = true := by decide
theorem m0_w10 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 33000))) (dimF (n.val + 33000)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 33000))) (densSupG (n.val + 33000))) (densSupG (arg0 (n.val + 33000)))) = true := by decide
theorem m1_w10 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 33000))) (dimF (n.val + 33000)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 33000))) (densSupG (n.val + 33000))) (densSupG (arg1 (n.val + 33000)))) = true := by decide
theorem m0_w11 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 33050))) (dimF (n.val + 33050)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 33050))) (densSupG (n.val + 33050))) (densSupG (arg0 (n.val + 33050)))) = true := by decide
theorem m1_w11 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 33050))) (dimF (n.val + 33050)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 33050))) (densSupG (n.val + 33050))) (densSupG (arg1 (n.val + 33050)))) = true := by decide
theorem m0_w12 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 33100))) (dimF (n.val + 33100)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 33100))) (densSupG (n.val + 33100))) (densSupG (arg0 (n.val + 33100)))) = true := by decide
theorem m1_w12 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 33100))) (dimF (n.val + 33100)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 33100))) (densSupG (n.val + 33100))) (densSupG (arg1 (n.val + 33100)))) = true := by decide
theorem m0_w13 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 33150))) (dimF (n.val + 33150)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 33150))) (densSupG (n.val + 33150))) (densSupG (arg0 (n.val + 33150)))) = true := by decide
theorem m1_w13 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 33150))) (dimF (n.val + 33150)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 33150))) (densSupG (n.val + 33150))) (densSupG (arg1 (n.val + 33150)))) = true := by decide
theorem m0_w14 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 33200))) (dimF (n.val + 33200)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 33200))) (densSupG (n.val + 33200))) (densSupG (arg0 (n.val + 33200)))) = true := by decide
theorem m1_w14 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 33200))) (dimF (n.val + 33200)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 33200))) (densSupG (n.val + 33200))) (densSupG (arg1 (n.val + 33200)))) = true := by decide
theorem m0_w15 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 33250))) (dimF (n.val + 33250)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 33250))) (densSupG (n.val + 33250))) (densSupG (arg0 (n.val + 33250)))) = true := by decide
theorem m1_w15 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 33250))) (dimF (n.val + 33250)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 33250))) (densSupG (n.val + 33250))) (densSupG (arg1 (n.val + 33250)))) = true := by decide
theorem m0_w16 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 33300))) (dimF (n.val + 33300)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 33300))) (densSupG (n.val + 33300))) (densSupG (arg0 (n.val + 33300)))) = true := by decide
theorem m1_w16 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 33300))) (dimF (n.val + 33300)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 33300))) (densSupG (n.val + 33300))) (densSupG (arg1 (n.val + 33300)))) = true := by decide
theorem m0_w17 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 33350))) (dimF (n.val + 33350)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 33350))) (densSupG (n.val + 33350))) (densSupG (arg0 (n.val + 33350)))) = true := by decide
theorem m1_w17 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 33350))) (dimF (n.val + 33350)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 33350))) (densSupG (n.val + 33350))) (densSupG (arg1 (n.val + 33350)))) = true := by decide
theorem m0_w18 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 33400))) (dimF (n.val + 33400)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 33400))) (densSupG (n.val + 33400))) (densSupG (arg0 (n.val + 33400)))) = true := by decide
theorem m1_w18 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 33400))) (dimF (n.val + 33400)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 33400))) (densSupG (n.val + 33400))) (densSupG (arg1 (n.val + 33400)))) = true := by decide
theorem m0_w19 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 33450))) (dimF (n.val + 33450)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 33450))) (densSupG (n.val + 33450))) (densSupG (arg0 (n.val + 33450)))) = true := by decide
theorem m1_w19 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 33450))) (dimF (n.val + 33450)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 33450))) (densSupG (n.val + 33450))) (densSupG (arg1 (n.val + 33450)))) = true := by decide
theorem m0_w20 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 33500))) (dimF (n.val + 33500)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 33500))) (densSupG (n.val + 33500))) (densSupG (arg0 (n.val + 33500)))) = true := by decide
theorem m1_w20 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 33500))) (dimF (n.val + 33500)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 33500))) (densSupG (n.val + 33500))) (densSupG (arg1 (n.val + 33500)))) = true := by decide
theorem m0_w21 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 33550))) (dimF (n.val + 33550)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 33550))) (densSupG (n.val + 33550))) (densSupG (arg0 (n.val + 33550)))) = true := by decide
theorem m1_w21 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 33550))) (dimF (n.val + 33550)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 33550))) (densSupG (n.val + 33550))) (densSupG (arg1 (n.val + 33550)))) = true := by decide
theorem m0_w22 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 33600))) (dimF (n.val + 33600)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 33600))) (densSupG (n.val + 33600))) (densSupG (arg0 (n.val + 33600)))) = true := by decide
theorem m1_w22 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 33600))) (dimF (n.val + 33600)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 33600))) (densSupG (n.val + 33600))) (densSupG (arg1 (n.val + 33600)))) = true := by decide
theorem m0_w23 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 33650))) (dimF (n.val + 33650)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 33650))) (densSupG (n.val + 33650))) (densSupG (arg0 (n.val + 33650)))) = true := by decide
theorem m1_w23 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 33650))) (dimF (n.val + 33650)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 33650))) (densSupG (n.val + 33650))) (densSupG (arg1 (n.val + 33650)))) = true := by decide
theorem m0_w24 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 33700))) (dimF (n.val + 33700)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 33700))) (densSupG (n.val + 33700))) (densSupG (arg0 (n.val + 33700)))) = true := by decide
theorem m1_w24 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 33700))) (dimF (n.val + 33700)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 33700))) (densSupG (n.val + 33700))) (densSupG (arg1 (n.val + 33700)))) = true := by decide
theorem m0_w25 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 33750))) (dimF (n.val + 33750)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 33750))) (densSupG (n.val + 33750))) (densSupG (arg0 (n.val + 33750)))) = true := by decide
theorem m1_w25 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 33750))) (dimF (n.val + 33750)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 33750))) (densSupG (n.val + 33750))) (densSupG (arg1 (n.val + 33750)))) = true := by decide
theorem m0_w26 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 33800))) (dimF (n.val + 33800)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 33800))) (densSupG (n.val + 33800))) (densSupG (arg0 (n.val + 33800)))) = true := by decide
theorem m1_w26 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 33800))) (dimF (n.val + 33800)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 33800))) (densSupG (n.val + 33800))) (densSupG (arg1 (n.val + 33800)))) = true := by decide
theorem m0_w27 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 33850))) (dimF (n.val + 33850)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 33850))) (densSupG (n.val + 33850))) (densSupG (arg0 (n.val + 33850)))) = true := by decide
theorem m1_w27 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 33850))) (dimF (n.val + 33850)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 33850))) (densSupG (n.val + 33850))) (densSupG (arg1 (n.val + 33850)))) = true := by decide
theorem m0_w28 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 33900))) (dimF (n.val + 33900)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 33900))) (densSupG (n.val + 33900))) (densSupG (arg0 (n.val + 33900)))) = true := by decide
theorem m1_w28 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 33900))) (dimF (n.val + 33900)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 33900))) (densSupG (n.val + 33900))) (densSupG (arg1 (n.val + 33900)))) = true := by decide
theorem m0_w29 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 33950))) (dimF (n.val + 33950)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 33950))) (densSupG (n.val + 33950))) (densSupG (arg0 (n.val + 33950)))) = true := by decide
theorem m1_w29 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 33950))) (dimF (n.val + 33950)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 33950))) (densSupG (n.val + 33950))) (densSupG (arg1 (n.val + 33950)))) = true := by decide
theorem m0_w30 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 34000))) (dimF (n.val + 34000)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 34000))) (densSupG (n.val + 34000))) (densSupG (arg0 (n.val + 34000)))) = true := by decide
theorem m1_w30 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 34000))) (dimF (n.val + 34000)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 34000))) (densSupG (n.val + 34000))) (densSupG (arg1 (n.val + 34000)))) = true := by decide
theorem m0_w31 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 34050))) (dimF (n.val + 34050)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 34050))) (densSupG (n.val + 34050))) (densSupG (arg0 (n.val + 34050)))) = true := by decide
theorem m1_w31 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 34050))) (dimF (n.val + 34050)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 34050))) (densSupG (n.val + 34050))) (densSupG (arg1 (n.val + 34050)))) = true := by decide
theorem m0_w32 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 34100))) (dimF (n.val + 34100)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 34100))) (densSupG (n.val + 34100))) (densSupG (arg0 (n.val + 34100)))) = true := by decide
theorem m1_w32 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 34100))) (dimF (n.val + 34100)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 34100))) (densSupG (n.val + 34100))) (densSupG (arg1 (n.val + 34100)))) = true := by decide
theorem m0_w33 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 34150))) (dimF (n.val + 34150)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 34150))) (densSupG (n.val + 34150))) (densSupG (arg0 (n.val + 34150)))) = true := by decide
theorem m1_w33 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 34150))) (dimF (n.val + 34150)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 34150))) (densSupG (n.val + 34150))) (densSupG (arg1 (n.val + 34150)))) = true := by decide
theorem m0_w34 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 34200))) (dimF (n.val + 34200)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 34200))) (densSupG (n.val + 34200))) (densSupG (arg0 (n.val + 34200)))) = true := by decide
theorem m1_w34 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 34200))) (dimF (n.val + 34200)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 34200))) (densSupG (n.val + 34200))) (densSupG (arg1 (n.val + 34200)))) = true := by decide
theorem m0_w35 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 34250))) (dimF (n.val + 34250)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 34250))) (densSupG (n.val + 34250))) (densSupG (arg0 (n.val + 34250)))) = true := by decide
theorem m1_w35 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 34250))) (dimF (n.val + 34250)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 34250))) (densSupG (n.val + 34250))) (densSupG (arg1 (n.val + 34250)))) = true := by decide
theorem m0_w36 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 34300))) (dimF (n.val + 34300)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 34300))) (densSupG (n.val + 34300))) (densSupG (arg0 (n.val + 34300)))) = true := by decide
theorem m1_w36 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 34300))) (dimF (n.val + 34300)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 34300))) (densSupG (n.val + 34300))) (densSupG (arg1 (n.val + 34300)))) = true := by decide
theorem m0_w37 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 34350))) (dimF (n.val + 34350)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 34350))) (densSupG (n.val + 34350))) (densSupG (arg0 (n.val + 34350)))) = true := by decide
theorem m1_w37 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 34350))) (dimF (n.val + 34350)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 34350))) (densSupG (n.val + 34350))) (densSupG (arg1 (n.val + 34350)))) = true := by decide
theorem m0_w38 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 34400))) (dimF (n.val + 34400)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 34400))) (densSupG (n.val + 34400))) (densSupG (arg0 (n.val + 34400)))) = true := by decide
theorem m1_w38 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 34400))) (dimF (n.val + 34400)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 34400))) (densSupG (n.val + 34400))) (densSupG (arg1 (n.val + 34400)))) = true := by decide
theorem m0_w39 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 34450))) (dimF (n.val + 34450)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 34450))) (densSupG (n.val + 34450))) (densSupG (arg0 (n.val + 34450)))) = true := by decide
theorem m1_w39 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 34450))) (dimF (n.val + 34450)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 34450))) (densSupG (n.val + 34450))) (densSupG (arg1 (n.val + 34450)))) = true := by decide
theorem m0_w40 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 34500))) (dimF (n.val + 34500)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 34500))) (densSupG (n.val + 34500))) (densSupG (arg0 (n.val + 34500)))) = true := by decide
theorem m1_w40 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 34500))) (dimF (n.val + 34500)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 34500))) (densSupG (n.val + 34500))) (densSupG (arg1 (n.val + 34500)))) = true := by decide
theorem m0_w41 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 34550))) (dimF (n.val + 34550)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 34550))) (densSupG (n.val + 34550))) (densSupG (arg0 (n.val + 34550)))) = true := by decide
theorem m1_w41 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 34550))) (dimF (n.val + 34550)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 34550))) (densSupG (n.val + 34550))) (densSupG (arg1 (n.val + 34550)))) = true := by decide
theorem m0_w42 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 34600))) (dimF (n.val + 34600)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 34600))) (densSupG (n.val + 34600))) (densSupG (arg0 (n.val + 34600)))) = true := by decide
theorem m1_w42 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 34600))) (dimF (n.val + 34600)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 34600))) (densSupG (n.val + 34600))) (densSupG (arg1 (n.val + 34600)))) = true := by decide
theorem m0_w43 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 34650))) (dimF (n.val + 34650)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 34650))) (densSupG (n.val + 34650))) (densSupG (arg0 (n.val + 34650)))) = true := by decide
theorem m1_w43 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 34650))) (dimF (n.val + 34650)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 34650))) (densSupG (n.val + 34650))) (densSupG (arg1 (n.val + 34650)))) = true := by decide
theorem m0_w44 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 34700))) (dimF (n.val + 34700)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 34700))) (densSupG (n.val + 34700))) (densSupG (arg0 (n.val + 34700)))) = true := by decide
theorem m1_w44 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 34700))) (dimF (n.val + 34700)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 34700))) (densSupG (n.val + 34700))) (densSupG (arg1 (n.val + 34700)))) = true := by decide
theorem m0_w45 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 34750))) (dimF (n.val + 34750)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 34750))) (densSupG (n.val + 34750))) (densSupG (arg0 (n.val + 34750)))) = true := by decide
theorem m1_w45 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 34750))) (dimF (n.val + 34750)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 34750))) (densSupG (n.val + 34750))) (densSupG (arg1 (n.val + 34750)))) = true := by decide
theorem m0_w46 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 34800))) (dimF (n.val + 34800)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 34800))) (densSupG (n.val + 34800))) (densSupG (arg0 (n.val + 34800)))) = true := by decide
theorem m1_w46 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 34800))) (dimF (n.val + 34800)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 34800))) (densSupG (n.val + 34800))) (densSupG (arg1 (n.val + 34800)))) = true := by decide
theorem m0_w47 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 34850))) (dimF (n.val + 34850)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 34850))) (densSupG (n.val + 34850))) (densSupG (arg0 (n.val + 34850)))) = true := by decide
theorem m1_w47 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 34850))) (dimF (n.val + 34850)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 34850))) (densSupG (n.val + 34850))) (densSupG (arg1 (n.val + 34850)))) = true := by decide
theorem m0_w48 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 34900))) (dimF (n.val + 34900)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 34900))) (densSupG (n.val + 34900))) (densSupG (arg0 (n.val + 34900)))) = true := by decide
theorem m1_w48 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 34900))) (dimF (n.val + 34900)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 34900))) (densSupG (n.val + 34900))) (densSupG (arg1 (n.val + 34900)))) = true := by decide
theorem m0_w49 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg0 (n.val + 34950))) (dimF (n.val + 34950)) ||
    Nat.beq (Nat.land (densSupG (arg0 (n.val + 34950))) (densSupG (n.val + 34950))) (densSupG (arg0 (n.val + 34950)))) = true := by decide
theorem m1_w49 : ∀ n : Fin 50,
  (!Nat.blt (dimF (arg1 (n.val + 34950))) (dimF (n.val + 34950)) ||
    Nat.beq (Nat.land (densSupG (arg1 (n.val + 34950))) (densSupG (n.val + 34950))) (densSupG (arg1 (n.val + 34950)))) = true := by decide
theorem land0_range (n : ℕ) (hn0 : 32500 ≤ n) (hn1 : n < 35000) :
    (!Nat.blt (dimF (arg0 n)) (dimF n) ||
      Nat.beq (Nat.land (densSupG (arg0 n)) (densSupG n)) (densSupG (arg0 n))) = true := by
  by_cases h0 : n < 32550
  · have hoff : 32500 ≤ n := by omega
    have hnfin : n - 32500 < 50 := by omega
    simpa [Nat.sub_add_cancel hoff] using m0_w0 ⟨n - 32500, hnfin⟩
  ·
    by_cases h1 : n < 32600
    · have hoff : 32550 ≤ n := by omega
      have hnfin : n - 32550 < 50 := by omega
      simpa [Nat.sub_add_cancel hoff] using m0_w1 ⟨n - 32550, hnfin⟩
    ·
      by_cases h2 : n < 32650
      · have hoff : 32600 ≤ n := by omega
        have hnfin : n - 32600 < 50 := by omega
        simpa [Nat.sub_add_cancel hoff] using m0_w2 ⟨n - 32600, hnfin⟩
      ·
        by_cases h3 : n < 32700
        · have hoff : 32650 ≤ n := by omega
          have hnfin : n - 32650 < 50 := by omega
          simpa [Nat.sub_add_cancel hoff] using m0_w3 ⟨n - 32650, hnfin⟩
        ·
          by_cases h4 : n < 32750
          · have hoff : 32700 ≤ n := by omega
            have hnfin : n - 32700 < 50 := by omega
            simpa [Nat.sub_add_cancel hoff] using m0_w4 ⟨n - 32700, hnfin⟩
          ·
            by_cases h5 : n < 32800
            · have hoff : 32750 ≤ n := by omega
              have hnfin : n - 32750 < 50 := by omega
              simpa [Nat.sub_add_cancel hoff] using m0_w5 ⟨n - 32750, hnfin⟩
            ·
              by_cases h6 : n < 32850
              · have hoff : 32800 ≤ n := by omega
                have hnfin : n - 32800 < 50 := by omega
                simpa [Nat.sub_add_cancel hoff] using m0_w6 ⟨n - 32800, hnfin⟩
              ·
                by_cases h7 : n < 32900
                · have hoff : 32850 ≤ n := by omega
                  have hnfin : n - 32850 < 50 := by omega
                  simpa [Nat.sub_add_cancel hoff] using m0_w7 ⟨n - 32850, hnfin⟩
                ·
                  by_cases h8 : n < 32950
                  · have hoff : 32900 ≤ n := by omega
                    have hnfin : n - 32900 < 50 := by omega
                    simpa [Nat.sub_add_cancel hoff] using m0_w8 ⟨n - 32900, hnfin⟩
                  ·
                    by_cases h9 : n < 33000
                    · have hoff : 32950 ≤ n := by omega
                      have hnfin : n - 32950 < 50 := by omega
                      simpa [Nat.sub_add_cancel hoff] using m0_w9 ⟨n - 32950, hnfin⟩
                    ·
                      by_cases h10 : n < 33050
                      · have hoff : 33000 ≤ n := by omega
                        have hnfin : n - 33000 < 50 := by omega
                        simpa [Nat.sub_add_cancel hoff] using m0_w10 ⟨n - 33000, hnfin⟩
                      ·
                        by_cases h11 : n < 33100
                        · have hoff : 33050 ≤ n := by omega
                          have hnfin : n - 33050 < 50 := by omega
                          simpa [Nat.sub_add_cancel hoff] using m0_w11 ⟨n - 33050, hnfin⟩
                        ·
                          by_cases h12 : n < 33150
                          · have hoff : 33100 ≤ n := by omega
                            have hnfin : n - 33100 < 50 := by omega
                            simpa [Nat.sub_add_cancel hoff] using m0_w12 ⟨n - 33100, hnfin⟩
                          ·
                            by_cases h13 : n < 33200
                            · have hoff : 33150 ≤ n := by omega
                              have hnfin : n - 33150 < 50 := by omega
                              simpa [Nat.sub_add_cancel hoff] using m0_w13 ⟨n - 33150, hnfin⟩
                            ·
                              by_cases h14 : n < 33250
                              · have hoff : 33200 ≤ n := by omega
                                have hnfin : n - 33200 < 50 := by omega
                                simpa [Nat.sub_add_cancel hoff] using m0_w14 ⟨n - 33200, hnfin⟩
                              ·
                                by_cases h15 : n < 33300
                                · have hoff : 33250 ≤ n := by omega
                                  have hnfin : n - 33250 < 50 := by omega
                                  simpa [Nat.sub_add_cancel hoff] using m0_w15 ⟨n - 33250, hnfin⟩
                                ·
                                  by_cases h16 : n < 33350
                                  · have hoff : 33300 ≤ n := by omega
                                    have hnfin : n - 33300 < 50 := by omega
                                    simpa [Nat.sub_add_cancel hoff] using m0_w16 ⟨n - 33300, hnfin⟩
                                  ·
                                    by_cases h17 : n < 33400
                                    · have hoff : 33350 ≤ n := by omega
                                      have hnfin : n - 33350 < 50 := by omega
                                      simpa [Nat.sub_add_cancel hoff] using m0_w17 ⟨n - 33350, hnfin⟩
                                    ·
                                      by_cases h18 : n < 33450
                                      · have hoff : 33400 ≤ n := by omega
                                        have hnfin : n - 33400 < 50 := by omega
                                        simpa [Nat.sub_add_cancel hoff] using m0_w18 ⟨n - 33400, hnfin⟩
                                      ·
                                        by_cases h19 : n < 33500
                                        · have hoff : 33450 ≤ n := by omega
                                          have hnfin : n - 33450 < 50 := by omega
                                          simpa [Nat.sub_add_cancel hoff] using m0_w19 ⟨n - 33450, hnfin⟩
                                        ·
                                          by_cases h20 : n < 33550
                                          · have hoff : 33500 ≤ n := by omega
                                            have hnfin : n - 33500 < 50 := by omega
                                            simpa [Nat.sub_add_cancel hoff] using m0_w20 ⟨n - 33500, hnfin⟩
                                          ·
                                            by_cases h21 : n < 33600
                                            · have hoff : 33550 ≤ n := by omega
                                              have hnfin : n - 33550 < 50 := by omega
                                              simpa [Nat.sub_add_cancel hoff] using m0_w21 ⟨n - 33550, hnfin⟩
                                            ·
                                              by_cases h22 : n < 33650
                                              · have hoff : 33600 ≤ n := by omega
                                                have hnfin : n - 33600 < 50 := by omega
                                                simpa [Nat.sub_add_cancel hoff] using m0_w22 ⟨n - 33600, hnfin⟩
                                              ·
                                                by_cases h23 : n < 33700
                                                · have hoff : 33650 ≤ n := by omega
                                                  have hnfin : n - 33650 < 50 := by omega
                                                  simpa [Nat.sub_add_cancel hoff] using m0_w23 ⟨n - 33650, hnfin⟩
                                                ·
                                                  by_cases h24 : n < 33750
                                                  · have hoff : 33700 ≤ n := by omega
                                                    have hnfin : n - 33700 < 50 := by omega
                                                    simpa [Nat.sub_add_cancel hoff] using m0_w24 ⟨n - 33700, hnfin⟩
                                                  ·
                                                    by_cases h25 : n < 33800
                                                    · have hoff : 33750 ≤ n := by omega
                                                      have hnfin : n - 33750 < 50 := by omega
                                                      simpa [Nat.sub_add_cancel hoff] using m0_w25 ⟨n - 33750, hnfin⟩
                                                    ·
                                                      by_cases h26 : n < 33850
                                                      · have hoff : 33800 ≤ n := by omega
                                                        have hnfin : n - 33800 < 50 := by omega
                                                        simpa [Nat.sub_add_cancel hoff] using m0_w26 ⟨n - 33800, hnfin⟩
                                                      ·
                                                        by_cases h27 : n < 33900
                                                        · have hoff : 33850 ≤ n := by omega
                                                          have hnfin : n - 33850 < 50 := by omega
                                                          simpa [Nat.sub_add_cancel hoff] using m0_w27 ⟨n - 33850, hnfin⟩
                                                        ·
                                                          by_cases h28 : n < 33950
                                                          · have hoff : 33900 ≤ n := by omega
                                                            have hnfin : n - 33900 < 50 := by omega
                                                            simpa [Nat.sub_add_cancel hoff] using m0_w28 ⟨n - 33900, hnfin⟩
                                                          ·
                                                            by_cases h29 : n < 34000
                                                            · have hoff : 33950 ≤ n := by omega
                                                              have hnfin : n - 33950 < 50 := by omega
                                                              simpa [Nat.sub_add_cancel hoff] using m0_w29 ⟨n - 33950, hnfin⟩
                                                            ·
                                                              by_cases h30 : n < 34050
                                                              · have hoff : 34000 ≤ n := by omega
                                                                have hnfin : n - 34000 < 50 := by omega
                                                                simpa [Nat.sub_add_cancel hoff] using m0_w30 ⟨n - 34000, hnfin⟩
                                                              ·
                                                                by_cases h31 : n < 34100
                                                                · have hoff : 34050 ≤ n := by omega
                                                                  have hnfin : n - 34050 < 50 := by omega
                                                                  simpa [Nat.sub_add_cancel hoff] using m0_w31 ⟨n - 34050, hnfin⟩
                                                                ·
                                                                  by_cases h32 : n < 34150
                                                                  · have hoff : 34100 ≤ n := by omega
                                                                    have hnfin : n - 34100 < 50 := by omega
                                                                    simpa [Nat.sub_add_cancel hoff] using m0_w32 ⟨n - 34100, hnfin⟩
                                                                  ·
                                                                    by_cases h33 : n < 34200
                                                                    · have hoff : 34150 ≤ n := by omega
                                                                      have hnfin : n - 34150 < 50 := by omega
                                                                      simpa [Nat.sub_add_cancel hoff] using m0_w33 ⟨n - 34150, hnfin⟩
                                                                    ·
                                                                      by_cases h34 : n < 34250
                                                                      · have hoff : 34200 ≤ n := by omega
                                                                        have hnfin : n - 34200 < 50 := by omega
                                                                        simpa [Nat.sub_add_cancel hoff] using m0_w34 ⟨n - 34200, hnfin⟩
                                                                      ·
                                                                        by_cases h35 : n < 34300
                                                                        · have hoff : 34250 ≤ n := by omega
                                                                          have hnfin : n - 34250 < 50 := by omega
                                                                          simpa [Nat.sub_add_cancel hoff] using m0_w35 ⟨n - 34250, hnfin⟩
                                                                        ·
                                                                          by_cases h36 : n < 34350
                                                                          · have hoff : 34300 ≤ n := by omega
                                                                            have hnfin : n - 34300 < 50 := by omega
                                                                            simpa [Nat.sub_add_cancel hoff] using m0_w36 ⟨n - 34300, hnfin⟩
                                                                          ·
                                                                            by_cases h37 : n < 34400
                                                                            · have hoff : 34350 ≤ n := by omega
                                                                              have hnfin : n - 34350 < 50 := by omega
                                                                              simpa [Nat.sub_add_cancel hoff] using m0_w37 ⟨n - 34350, hnfin⟩
                                                                            ·
                                                                              by_cases h38 : n < 34450
                                                                              · have hoff : 34400 ≤ n := by omega
                                                                                have hnfin : n - 34400 < 50 := by omega
                                                                                simpa [Nat.sub_add_cancel hoff] using m0_w38 ⟨n - 34400, hnfin⟩
                                                                              ·
                                                                                by_cases h39 : n < 34500
                                                                                · have hoff : 34450 ≤ n := by omega
                                                                                  have hnfin : n - 34450 < 50 := by omega
                                                                                  simpa [Nat.sub_add_cancel hoff] using m0_w39 ⟨n - 34450, hnfin⟩
                                                                                ·
                                                                                  by_cases h40 : n < 34550
                                                                                  · have hoff : 34500 ≤ n := by omega
                                                                                    have hnfin : n - 34500 < 50 := by omega
                                                                                    simpa [Nat.sub_add_cancel hoff] using m0_w40 ⟨n - 34500, hnfin⟩
                                                                                  ·
                                                                                    by_cases h41 : n < 34600
                                                                                    · have hoff : 34550 ≤ n := by omega
                                                                                      have hnfin : n - 34550 < 50 := by omega
                                                                                      simpa [Nat.sub_add_cancel hoff] using m0_w41 ⟨n - 34550, hnfin⟩
                                                                                    ·
                                                                                      by_cases h42 : n < 34650
                                                                                      · have hoff : 34600 ≤ n := by omega
                                                                                        have hnfin : n - 34600 < 50 := by omega
                                                                                        simpa [Nat.sub_add_cancel hoff] using m0_w42 ⟨n - 34600, hnfin⟩
                                                                                      ·
                                                                                        by_cases h43 : n < 34700
                                                                                        · have hoff : 34650 ≤ n := by omega
                                                                                          have hnfin : n - 34650 < 50 := by omega
                                                                                          simpa [Nat.sub_add_cancel hoff] using m0_w43 ⟨n - 34650, hnfin⟩
                                                                                        ·
                                                                                          by_cases h44 : n < 34750
                                                                                          · have hoff : 34700 ≤ n := by omega
                                                                                            have hnfin : n - 34700 < 50 := by omega
                                                                                            simpa [Nat.sub_add_cancel hoff] using m0_w44 ⟨n - 34700, hnfin⟩
                                                                                          ·
                                                                                            by_cases h45 : n < 34800
                                                                                            · have hoff : 34750 ≤ n := by omega
                                                                                              have hnfin : n - 34750 < 50 := by omega
                                                                                              simpa [Nat.sub_add_cancel hoff] using m0_w45 ⟨n - 34750, hnfin⟩
                                                                                            ·
                                                                                              by_cases h46 : n < 34850
                                                                                              · have hoff : 34800 ≤ n := by omega
                                                                                                have hnfin : n - 34800 < 50 := by omega
                                                                                                simpa [Nat.sub_add_cancel hoff] using m0_w46 ⟨n - 34800, hnfin⟩
                                                                                              ·
                                                                                                by_cases h47 : n < 34900
                                                                                                · have hoff : 34850 ≤ n := by omega
                                                                                                  have hnfin : n - 34850 < 50 := by omega
                                                                                                  simpa [Nat.sub_add_cancel hoff] using m0_w47 ⟨n - 34850, hnfin⟩
                                                                                                ·
                                                                                                  by_cases h48 : n < 34950
                                                                                                  · have hoff : 34900 ≤ n := by omega
                                                                                                    have hnfin : n - 34900 < 50 := by omega
                                                                                                    simpa [Nat.sub_add_cancel hoff] using m0_w48 ⟨n - 34900, hnfin⟩
                                                                                                  ·
                                                                                                    by_cases h49 : n < 35000
                                                                                                    · have hoff : 34950 ≤ n := by omega
                                                                                                      have hnfin : n - 34950 < 50 := by omega
                                                                                                      simpa [Nat.sub_add_cancel hoff] using m0_w49 ⟨n - 34950, hnfin⟩
                                                                                                    ·
                                                                                                      omega
theorem land1_range (n : ℕ) (hn0 : 32500 ≤ n) (hn1 : n < 35000) :
    (!Nat.blt (dimF (arg1 n)) (dimF n) ||
      Nat.beq (Nat.land (densSupG (arg1 n)) (densSupG n)) (densSupG (arg1 n))) = true := by
  by_cases h0 : n < 32550
  · have hoff : 32500 ≤ n := by omega
    have hnfin : n - 32500 < 50 := by omega
    simpa [Nat.sub_add_cancel hoff] using m1_w0 ⟨n - 32500, hnfin⟩
  ·
    by_cases h1 : n < 32600
    · have hoff : 32550 ≤ n := by omega
      have hnfin : n - 32550 < 50 := by omega
      simpa [Nat.sub_add_cancel hoff] using m1_w1 ⟨n - 32550, hnfin⟩
    ·
      by_cases h2 : n < 32650
      · have hoff : 32600 ≤ n := by omega
        have hnfin : n - 32600 < 50 := by omega
        simpa [Nat.sub_add_cancel hoff] using m1_w2 ⟨n - 32600, hnfin⟩
      ·
        by_cases h3 : n < 32700
        · have hoff : 32650 ≤ n := by omega
          have hnfin : n - 32650 < 50 := by omega
          simpa [Nat.sub_add_cancel hoff] using m1_w3 ⟨n - 32650, hnfin⟩
        ·
          by_cases h4 : n < 32750
          · have hoff : 32700 ≤ n := by omega
            have hnfin : n - 32700 < 50 := by omega
            simpa [Nat.sub_add_cancel hoff] using m1_w4 ⟨n - 32700, hnfin⟩
          ·
            by_cases h5 : n < 32800
            · have hoff : 32750 ≤ n := by omega
              have hnfin : n - 32750 < 50 := by omega
              simpa [Nat.sub_add_cancel hoff] using m1_w5 ⟨n - 32750, hnfin⟩
            ·
              by_cases h6 : n < 32850
              · have hoff : 32800 ≤ n := by omega
                have hnfin : n - 32800 < 50 := by omega
                simpa [Nat.sub_add_cancel hoff] using m1_w6 ⟨n - 32800, hnfin⟩
              ·
                by_cases h7 : n < 32900
                · have hoff : 32850 ≤ n := by omega
                  have hnfin : n - 32850 < 50 := by omega
                  simpa [Nat.sub_add_cancel hoff] using m1_w7 ⟨n - 32850, hnfin⟩
                ·
                  by_cases h8 : n < 32950
                  · have hoff : 32900 ≤ n := by omega
                    have hnfin : n - 32900 < 50 := by omega
                    simpa [Nat.sub_add_cancel hoff] using m1_w8 ⟨n - 32900, hnfin⟩
                  ·
                    by_cases h9 : n < 33000
                    · have hoff : 32950 ≤ n := by omega
                      have hnfin : n - 32950 < 50 := by omega
                      simpa [Nat.sub_add_cancel hoff] using m1_w9 ⟨n - 32950, hnfin⟩
                    ·
                      by_cases h10 : n < 33050
                      · have hoff : 33000 ≤ n := by omega
                        have hnfin : n - 33000 < 50 := by omega
                        simpa [Nat.sub_add_cancel hoff] using m1_w10 ⟨n - 33000, hnfin⟩
                      ·
                        by_cases h11 : n < 33100
                        · have hoff : 33050 ≤ n := by omega
                          have hnfin : n - 33050 < 50 := by omega
                          simpa [Nat.sub_add_cancel hoff] using m1_w11 ⟨n - 33050, hnfin⟩
                        ·
                          by_cases h12 : n < 33150
                          · have hoff : 33100 ≤ n := by omega
                            have hnfin : n - 33100 < 50 := by omega
                            simpa [Nat.sub_add_cancel hoff] using m1_w12 ⟨n - 33100, hnfin⟩
                          ·
                            by_cases h13 : n < 33200
                            · have hoff : 33150 ≤ n := by omega
                              have hnfin : n - 33150 < 50 := by omega
                              simpa [Nat.sub_add_cancel hoff] using m1_w13 ⟨n - 33150, hnfin⟩
                            ·
                              by_cases h14 : n < 33250
                              · have hoff : 33200 ≤ n := by omega
                                have hnfin : n - 33200 < 50 := by omega
                                simpa [Nat.sub_add_cancel hoff] using m1_w14 ⟨n - 33200, hnfin⟩
                              ·
                                by_cases h15 : n < 33300
                                · have hoff : 33250 ≤ n := by omega
                                  have hnfin : n - 33250 < 50 := by omega
                                  simpa [Nat.sub_add_cancel hoff] using m1_w15 ⟨n - 33250, hnfin⟩
                                ·
                                  by_cases h16 : n < 33350
                                  · have hoff : 33300 ≤ n := by omega
                                    have hnfin : n - 33300 < 50 := by omega
                                    simpa [Nat.sub_add_cancel hoff] using m1_w16 ⟨n - 33300, hnfin⟩
                                  ·
                                    by_cases h17 : n < 33400
                                    · have hoff : 33350 ≤ n := by omega
                                      have hnfin : n - 33350 < 50 := by omega
                                      simpa [Nat.sub_add_cancel hoff] using m1_w17 ⟨n - 33350, hnfin⟩
                                    ·
                                      by_cases h18 : n < 33450
                                      · have hoff : 33400 ≤ n := by omega
                                        have hnfin : n - 33400 < 50 := by omega
                                        simpa [Nat.sub_add_cancel hoff] using m1_w18 ⟨n - 33400, hnfin⟩
                                      ·
                                        by_cases h19 : n < 33500
                                        · have hoff : 33450 ≤ n := by omega
                                          have hnfin : n - 33450 < 50 := by omega
                                          simpa [Nat.sub_add_cancel hoff] using m1_w19 ⟨n - 33450, hnfin⟩
                                        ·
                                          by_cases h20 : n < 33550
                                          · have hoff : 33500 ≤ n := by omega
                                            have hnfin : n - 33500 < 50 := by omega
                                            simpa [Nat.sub_add_cancel hoff] using m1_w20 ⟨n - 33500, hnfin⟩
                                          ·
                                            by_cases h21 : n < 33600
                                            · have hoff : 33550 ≤ n := by omega
                                              have hnfin : n - 33550 < 50 := by omega
                                              simpa [Nat.sub_add_cancel hoff] using m1_w21 ⟨n - 33550, hnfin⟩
                                            ·
                                              by_cases h22 : n < 33650
                                              · have hoff : 33600 ≤ n := by omega
                                                have hnfin : n - 33600 < 50 := by omega
                                                simpa [Nat.sub_add_cancel hoff] using m1_w22 ⟨n - 33600, hnfin⟩
                                              ·
                                                by_cases h23 : n < 33700
                                                · have hoff : 33650 ≤ n := by omega
                                                  have hnfin : n - 33650 < 50 := by omega
                                                  simpa [Nat.sub_add_cancel hoff] using m1_w23 ⟨n - 33650, hnfin⟩
                                                ·
                                                  by_cases h24 : n < 33750
                                                  · have hoff : 33700 ≤ n := by omega
                                                    have hnfin : n - 33700 < 50 := by omega
                                                    simpa [Nat.sub_add_cancel hoff] using m1_w24 ⟨n - 33700, hnfin⟩
                                                  ·
                                                    by_cases h25 : n < 33800
                                                    · have hoff : 33750 ≤ n := by omega
                                                      have hnfin : n - 33750 < 50 := by omega
                                                      simpa [Nat.sub_add_cancel hoff] using m1_w25 ⟨n - 33750, hnfin⟩
                                                    ·
                                                      by_cases h26 : n < 33850
                                                      · have hoff : 33800 ≤ n := by omega
                                                        have hnfin : n - 33800 < 50 := by omega
                                                        simpa [Nat.sub_add_cancel hoff] using m1_w26 ⟨n - 33800, hnfin⟩
                                                      ·
                                                        by_cases h27 : n < 33900
                                                        · have hoff : 33850 ≤ n := by omega
                                                          have hnfin : n - 33850 < 50 := by omega
                                                          simpa [Nat.sub_add_cancel hoff] using m1_w27 ⟨n - 33850, hnfin⟩
                                                        ·
                                                          by_cases h28 : n < 33950
                                                          · have hoff : 33900 ≤ n := by omega
                                                            have hnfin : n - 33900 < 50 := by omega
                                                            simpa [Nat.sub_add_cancel hoff] using m1_w28 ⟨n - 33900, hnfin⟩
                                                          ·
                                                            by_cases h29 : n < 34000
                                                            · have hoff : 33950 ≤ n := by omega
                                                              have hnfin : n - 33950 < 50 := by omega
                                                              simpa [Nat.sub_add_cancel hoff] using m1_w29 ⟨n - 33950, hnfin⟩
                                                            ·
                                                              by_cases h30 : n < 34050
                                                              · have hoff : 34000 ≤ n := by omega
                                                                have hnfin : n - 34000 < 50 := by omega
                                                                simpa [Nat.sub_add_cancel hoff] using m1_w30 ⟨n - 34000, hnfin⟩
                                                              ·
                                                                by_cases h31 : n < 34100
                                                                · have hoff : 34050 ≤ n := by omega
                                                                  have hnfin : n - 34050 < 50 := by omega
                                                                  simpa [Nat.sub_add_cancel hoff] using m1_w31 ⟨n - 34050, hnfin⟩
                                                                ·
                                                                  by_cases h32 : n < 34150
                                                                  · have hoff : 34100 ≤ n := by omega
                                                                    have hnfin : n - 34100 < 50 := by omega
                                                                    simpa [Nat.sub_add_cancel hoff] using m1_w32 ⟨n - 34100, hnfin⟩
                                                                  ·
                                                                    by_cases h33 : n < 34200
                                                                    · have hoff : 34150 ≤ n := by omega
                                                                      have hnfin : n - 34150 < 50 := by omega
                                                                      simpa [Nat.sub_add_cancel hoff] using m1_w33 ⟨n - 34150, hnfin⟩
                                                                    ·
                                                                      by_cases h34 : n < 34250
                                                                      · have hoff : 34200 ≤ n := by omega
                                                                        have hnfin : n - 34200 < 50 := by omega
                                                                        simpa [Nat.sub_add_cancel hoff] using m1_w34 ⟨n - 34200, hnfin⟩
                                                                      ·
                                                                        by_cases h35 : n < 34300
                                                                        · have hoff : 34250 ≤ n := by omega
                                                                          have hnfin : n - 34250 < 50 := by omega
                                                                          simpa [Nat.sub_add_cancel hoff] using m1_w35 ⟨n - 34250, hnfin⟩
                                                                        ·
                                                                          by_cases h36 : n < 34350
                                                                          · have hoff : 34300 ≤ n := by omega
                                                                            have hnfin : n - 34300 < 50 := by omega
                                                                            simpa [Nat.sub_add_cancel hoff] using m1_w36 ⟨n - 34300, hnfin⟩
                                                                          ·
                                                                            by_cases h37 : n < 34400
                                                                            · have hoff : 34350 ≤ n := by omega
                                                                              have hnfin : n - 34350 < 50 := by omega
                                                                              simpa [Nat.sub_add_cancel hoff] using m1_w37 ⟨n - 34350, hnfin⟩
                                                                            ·
                                                                              by_cases h38 : n < 34450
                                                                              · have hoff : 34400 ≤ n := by omega
                                                                                have hnfin : n - 34400 < 50 := by omega
                                                                                simpa [Nat.sub_add_cancel hoff] using m1_w38 ⟨n - 34400, hnfin⟩
                                                                              ·
                                                                                by_cases h39 : n < 34500
                                                                                · have hoff : 34450 ≤ n := by omega
                                                                                  have hnfin : n - 34450 < 50 := by omega
                                                                                  simpa [Nat.sub_add_cancel hoff] using m1_w39 ⟨n - 34450, hnfin⟩
                                                                                ·
                                                                                  by_cases h40 : n < 34550
                                                                                  · have hoff : 34500 ≤ n := by omega
                                                                                    have hnfin : n - 34500 < 50 := by omega
                                                                                    simpa [Nat.sub_add_cancel hoff] using m1_w40 ⟨n - 34500, hnfin⟩
                                                                                  ·
                                                                                    by_cases h41 : n < 34600
                                                                                    · have hoff : 34550 ≤ n := by omega
                                                                                      have hnfin : n - 34550 < 50 := by omega
                                                                                      simpa [Nat.sub_add_cancel hoff] using m1_w41 ⟨n - 34550, hnfin⟩
                                                                                    ·
                                                                                      by_cases h42 : n < 34650
                                                                                      · have hoff : 34600 ≤ n := by omega
                                                                                        have hnfin : n - 34600 < 50 := by omega
                                                                                        simpa [Nat.sub_add_cancel hoff] using m1_w42 ⟨n - 34600, hnfin⟩
                                                                                      ·
                                                                                        by_cases h43 : n < 34700
                                                                                        · have hoff : 34650 ≤ n := by omega
                                                                                          have hnfin : n - 34650 < 50 := by omega
                                                                                          simpa [Nat.sub_add_cancel hoff] using m1_w43 ⟨n - 34650, hnfin⟩
                                                                                        ·
                                                                                          by_cases h44 : n < 34750
                                                                                          · have hoff : 34700 ≤ n := by omega
                                                                                            have hnfin : n - 34700 < 50 := by omega
                                                                                            simpa [Nat.sub_add_cancel hoff] using m1_w44 ⟨n - 34700, hnfin⟩
                                                                                          ·
                                                                                            by_cases h45 : n < 34800
                                                                                            · have hoff : 34750 ≤ n := by omega
                                                                                              have hnfin : n - 34750 < 50 := by omega
                                                                                              simpa [Nat.sub_add_cancel hoff] using m1_w45 ⟨n - 34750, hnfin⟩
                                                                                            ·
                                                                                              by_cases h46 : n < 34850
                                                                                              · have hoff : 34800 ≤ n := by omega
                                                                                                have hnfin : n - 34800 < 50 := by omega
                                                                                                simpa [Nat.sub_add_cancel hoff] using m1_w46 ⟨n - 34800, hnfin⟩
                                                                                              ·
                                                                                                by_cases h47 : n < 34900
                                                                                                · have hoff : 34850 ≤ n := by omega
                                                                                                  have hnfin : n - 34850 < 50 := by omega
                                                                                                  simpa [Nat.sub_add_cancel hoff] using m1_w47 ⟨n - 34850, hnfin⟩
                                                                                                ·
                                                                                                  by_cases h48 : n < 34950
                                                                                                  · have hoff : 34900 ≤ n := by omega
                                                                                                    have hnfin : n - 34900 < 50 := by omega
                                                                                                    simpa [Nat.sub_add_cancel hoff] using m1_w48 ⟨n - 34900, hnfin⟩
                                                                                                  ·
                                                                                                    by_cases h49 : n < 35000
                                                                                                    · have hoff : 34950 ≤ n := by omega
                                                                                                      have hnfin : n - 34950 < 50 := by omega
                                                                                                      simpa [Nat.sub_add_cancel hoff] using m1_w49 ⟨n - 34950, hnfin⟩
                                                                                                    ·
                                                                                                      omega
end IntMul.Kappa.R8.Bit.Oppbank.LandMonoFixA13


