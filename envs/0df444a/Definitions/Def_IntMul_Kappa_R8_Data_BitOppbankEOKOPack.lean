-- Prove2me | Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankEOKOPack
-- name    : IntMul_Kappa_R8_Data_BitOppbankEOKOPack
-- status  : Definition
-- author  : @Ethan Cheung Wang
-- created : 2026-10-28T17:30:02.070084+00:00
-- url     : https://prove2.me/theorems/76603340-55a6-41a8-9179-fea7fa41396f
-- title:
--   Densified EOKO packaging (republish for theorem-module sync)
-- statement:
--   # Densified EOKO (pack republish)
--
--   Identical mathematical content to `BitOppbankEOKO` (`98d5d297`): densified edge-OK structure at `codeBound=64251` for the one-run channel.
--
--   Republished under a new definition name so theorem modules can materialize the Lean file (platform sync workaround).
--
--   **Formalization Note.** Namespace remains `IntMul.Kappa.R8.Bit.Oppbank.EOKO`.
-- source:
--   EOKO republish as EOKOPack for sync

import Mathlib
import Definitions.Def_IntMul_Kappa_R6_Defs4
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankOneRun
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankPnd
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankSupG

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 4000000
set_option linter.dupNamespace false

/-!
# Densified EOKO for one-run opp-bank channel

Retarget of R6 `EOK` from `codeBound = 38286` to densified `64251`.
-/

namespace IntMul.Kappa.R8.Bit.Oppbank.EOKO

open IntMul.Kappa.R6.Bit
open IntMul.Kappa.R6.Bit.NB
open IntMul.Kappa.R6.Bit.QHNet (FormalOK)
open IntMul.Kappa.R8.Bit.Oppbank
open IntMul.Kappa.R8.Bit.Oppbank.Pnd
open IntMul.Kappa.R8.Bit.Oppbank.OneRunNet
open Matrix

/-- Local copy of R6 Defs51 `GoodM` (avoid heavy Defs51 import). -/
def GoodM (N : ℕ) {l p : Type*} [Fintype l] [Fintype p]
    (A : Matrix l p ℚ) : Prop :=
  ∀ i j, Nat.Coprime (A i j).den N

/-- Densified edge-OK hypotheses at field size `N` (`SupG.codeBound = 64251`). -/
structure EOKO (ch : NB.Ch) (N : ℕ) : Prop where
  hS : ch.S * ch.Si = 1
  hSi : ch.Si * ch.S = 1
  gS : GoodM N ch.S
  gSi : GoodM N ch.Si
  gPc : ∀ c < SupG.codeBound, GoodM N (Pc c)
  gPl : ∀ b < 1771, GoodM N (Pl b)
  m1 : ∀ b < 1771, ∀ o < SupG.codeBound, ∀ c < SupG.codeBound, nestOK o c = true →
    edgeMat N (ch.e1 b o c) = redM N (pswQ (K ch.S ch.Si (Dm o c) (Pl b)))
  m2 : ∀ a < 1771, ∀ o < SupG.codeBound, ∀ c < SupG.codeBound, nestOK o c = true →
    edgeMat N (ch.e2 a o c) = redM N (pswQ (K ch.S ch.Si (Pl a) (Dm o c)))
  mx : ∀ b < 1771, edgeMat N (ch.ex b) = redM N (pswQ (K ch.S ch.Si 1 (1 - Pl b)))
  mn : ∀ a < 1771, ∀ t < 1771, edgeMat N (ch.en a t) =
    redM N (pswQ (K ch.S ch.Si (1 - Pl a) (1 - Pl t)))
  mi : ∀ a < 1771, edgeMat N (ch.ei a) = redM N (pswQ (K ch.S ch.Si (1 - Pl a) 1))
  mc : ∀ a < 1771, ∀ s < 1771, edgeMat N (ch.ec a s) =
    redM N (pswQ (K ch.S ch.Si (Pl a) (Pl s)))

theorem codeBound_eq : SupG.codeBound = 64251 := rfl

noncomputable def ch0NB : NB.Ch := toNB ch0O

def EOKOLargeStmt : Prop :=
  ∃ q₀ : ℕ, ∀ q, q.Prime → q₀ < q → ∀ f, EOKO ch0NB (q ^ f)

def FormalOKOfEOKOStmt : Prop :=
  ∀ N, EOKO ch0NB N → FormalOK (m := 529) net0O N

end IntMul.Kappa.R8.Bit.Oppbank.EOKO


