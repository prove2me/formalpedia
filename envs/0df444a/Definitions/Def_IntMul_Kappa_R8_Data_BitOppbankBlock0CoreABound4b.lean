-- Prove2me | Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankBlock0CoreABound4b
-- name    : IntMul_Kappa_R8_Data_BitOppbankBlock0CoreABound4b
-- status  : Definition
-- author  : @Ethan Cheung Wang
-- created : 2026-11-15T17:33:48.745188+00:00
-- url     : https://prove2.me/theorems/1a302010-e1b2-4037-80c3-9d73d9fc6bdd
-- title:
--   Irreducible prefix alias and right-associated bounds
-- statement:
--   # Irreducible prefix alias and right-associated bounds
--
--   An irreducible alias `preF_ir` of the concrete prefix, together with right-associated `MovesV` bounds instantiated at that alias. Prefix / block-0 helper only; not a full-word W1F certificate.
--
--   ## Formalization Note
--
--   Lean definition name: `IntMul_Kappa_R8_Data_BitOppbankBlock0CoreABound4b`.
-- source:
--   IntMul Kappa R8 Bit Oppbank FormalOK: IntMul_Kappa_R8_Data_BitOppbankBlock0CoreABound4b split. Prefix / block-0 helper only; not a full-word W1F certificate.

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
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankBlock0CoreABound4a
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
Right-associated bounds for `preF ++ (copyoND ++ leafMix)`, by `rfl` instantiation of the frozen lemma. Prefix / block-0 helper only; not a full-word W1F certificate.
-/

open IntMul.Kappa.R8.Bit.Oppbank
open IntMul.Kappa.R8.Bit.Oppbank.Gen (genF genStepF mvF)
open IntMul.Kappa.R8.Bit.Oppbank.Lab (ValidOn MovesV)
open IntMul.Kappa.R8.Bit.Oppbank.Pnd (nestOK argRel isND)
open IntMul.Kappa.R8.Bit.Oppbank.QHNetRecR

/-- Irreducible alias of `preF` so instantiation does not unfold the concrete prefix. -/
@[irreducible] def preF_ir : List (ℕ × List ℕ × List (ℕ × ℕ)) := preF

theorem preF_ir_eq : preF_ir = preF := by
  unfold preF_ir
  rfl

theorem preF_copyoND_leafMix_bounds_right_ir :
    MovesV (genF initR (preF_ir ++ (copyoND ++ leafMix))).2 ∧
      ∀ x, (genF initR (preF_ir ++ (copyoND ++ leafMix))).1 x < SupG.codeBound :=
  preF_copyoND_leafMix_bounds_right_of preF_ir preF_ir_eq
    (by rw [preF_ir_eq]; exact preF_initR_bounds)
    (by rw [preF_ir_eq]; exact copyoND_leafMix_from_preF)


