-- Prove2me | Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankBlock0CoreABound5b
-- name    : IntMul_Kappa_R8_Data_BitOppbankBlock0CoreABound5b
-- status  : Definition
-- author  : @Ethan Cheung Wang
-- created : 2026-11-15T17:37:34.464196+00:00
-- url     : https://prove2.me/theorems/393e003c-ba5f-4bdf-ab0f-52ad8773b19d
-- title:
--   Irreducible copy-out and leaf-mix aliases with left-associated bounds
-- statement:
--   # Irreducible copy-out and leaf-mix aliases with left-associated bounds
--
--   Irreducible aliases of `copyoND` and `leafMix`, and left-associated `MovesV` bounds instantiated only at irreducible aliases. Prefix / block-0 helper only; not a full-word W1F certificate.
--
--   ## Formalization Note
--
--   Lean definition name: `IntMul_Kappa_R8_Data_BitOppbankBlock0CoreABound5b`.
-- source:
--   IntMul Kappa R8 Bit Oppbank FormalOK: IntMul_Kappa_R8_Data_BitOppbankBlock0CoreABound5b split. Prefix / block-0 helper only; not a full-word W1F certificate.

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
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankBlock0CoreABound4b
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankBlock0CoreABound5a1
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

/-- Irreducible aliases of `copyoND` and `leafMix` so associativity is not instantiated at the concrete lists. Prefix / block-0 helper only; not a full-word W1F certificate. -/

@[irreducible] def copyoND_ir : List (ℕ × List ℕ × List (ℕ × ℕ)) := copyoND
@[irreducible] def leafMix_ir : List (ℕ × List ℕ × List (ℕ × ℕ)) := leafMix

theorem copyoND_ir_eq : copyoND_ir = copyoND := by
  unfold copyoND_ir
  rfl

theorem leafMix_ir_eq : leafMix_ir = leafMix := by
  unfold leafMix_ir
  rfl

theorem preF_copyoND_leafMix_bounds_right_ir3 :
    MovesV (genF initR (preF_ir ++ (copyoND_ir ++ leafMix_ir))).2 ∧
      ∀ x, (genF initR (preF_ir ++ (copyoND_ir ++ leafMix_ir))).1 x < SupG.codeBound := by
  have e1 : copyoND_ir ++ leafMix_ir = copyoND ++ leafMix :=
    (congrArg (fun a => a ++ leafMix_ir) copyoND_ir_eq).trans
      (congrArg (fun b => copyoND ++ b) leafMix_ir_eq)
  have e : preF_ir ++ (copyoND_ir ++ leafMix_ir) = preF_ir ++ (copyoND ++ leafMix) :=
    congrArg (fun w => preF_ir ++ w) e1
  have e' :=
    congrArg
      (fun W =>
        MovesV (genF initR W).2 ∧
          ∀ x, (genF initR W).1 x < SupG.codeBound)
      e
  exact e'.mpr preF_copyoND_leafMix_bounds_right_ir

theorem MovesV_preF_copyoND_leaves_bounds_ir3 :
    MovesV (genF initR (preF_ir ++ copyoND_ir ++ leafMix_ir)).2 ∧
      ∀ x, (genF initR (preF_ir ++ copyoND_ir ++ leafMix_ir)).1 x < SupG.codeBound :=
  MovesV_genF_append_bounds_assoc initR preF_ir copyoND_ir leafMix_ir
    preF_copyoND_leafMix_bounds_right_ir3


