-- Prove2me | Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankBlock0CoreABound4a
-- name    : IntMul_Kappa_R8_Data_BitOppbankBlock0CoreABound4a
-- status  : Definition
-- author  : @Ethan Cheung Wang
-- created : 2026-11-15T17:31:08.428122+00:00
-- url     : https://prove2.me/theorems/fbf6d8a7-158a-4fe3-9242-4140f026e2fa
-- title:
--   Abstract frozen right-associated prefix bounds
-- statement:
--   # Abstract frozen right-associated prefix bounds
--
--   An abstract lemma giving right-associated `MovesV` bounds for a word `W ++ (copyoND ++ leafMix)` under the hypothesis `W = preF`. Prefix / block-0 helper only; not a full-word W1F certificate.
--
--   ## Formalization Note
--
--   Lean definition name: `IntMul_Kappa_R8_Data_BitOppbankBlock0CoreABound4a`.
-- source:
--   IntMul Kappa R8 Bit Oppbank FormalOK: IntMul_Kappa_R8_Data_BitOppbankBlock0CoreABound4a split. Prefix / block-0 helper only; not a full-word W1F certificate.

import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankGenF
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankLab1
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankQHNetRecR
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankBlock0CoreAData
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankBlock0CoreABits
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankBlock0CoreACopy
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankBlock0CoreALeaf
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankBlock0CoreAState1
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankBlock0CoreAState2
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankBlock0CoreAState3a
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankBlock0CoreABound1
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankBlock0CoreABound2
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankBlock0CoreABound3
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Max
import Mathlib.Tactic.ByCases
import Mathlib.Tactic.Ext

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

/-!
Abstract `MovesV_genF_append_bounds` specialized at `initR` but not at `preF`. Prefix / block-0 helper only; not a full-word W1F certificate.
-/

open IntMul.Kappa.R8.Bit.Oppbank
open IntMul.Kappa.R8.Bit.Oppbank.Gen (genF genStepF mvF)
open IntMul.Kappa.R8.Bit.Oppbank.Lab (ValidOn MovesV)
open IntMul.Kappa.R8.Bit.Oppbank.Pnd (nestOK argRel isND)
open IntMul.Kappa.R8.Bit.Oppbank.QHNetRecR

/-- Frozen in the prefix `W`. Applied at `W = preF` by `rfl` in the next pack. -/
theorem preF_copyoND_leafMix_bounds_right_of
    (W : List (ℕ × List ℕ × List (ℕ × ℕ)))
    (hW : W = preF)
    (h : MovesV (genF initR W).2 ∧
      ∀ x, (genF initR W).1 x < SupG.codeBound)
    (h' : MovesV (genF (genF initR W).1 (copyoND ++ leafMix)).2 ∧
      ∀ x, (genF (genF initR W).1 (copyoND ++ leafMix)).1 x < SupG.codeBound) :
    MovesV (genF initR (W ++ (copyoND ++ leafMix))).2 ∧
      ∀ x, (genF initR (W ++ (copyoND ++ leafMix))).1 x < SupG.codeBound := by
  exact MovesV_genF_append_bounds initR W (copyoND ++ leafMix) h h'


