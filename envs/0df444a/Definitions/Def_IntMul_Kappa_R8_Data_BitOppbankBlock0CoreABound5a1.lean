-- Prove2me | Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankBlock0CoreABound5a1
-- name    : IntMul_Kappa_R8_Data_BitOppbankBlock0CoreABound5a1
-- status  : Definition
-- author  : @Ethan Cheung Wang
-- created : 2026-11-15T17:35:44.102048+00:00
-- url     : https://prove2.me/theorems/3ce3192f-f354-4534-8de2-dcb50f92dd10
-- title:
--   Abstract associativity for generator MovesV bounds
-- statement:
--   # Abstract associativity for generator MovesV bounds
--
--   Abstract associativity and three-fold state lemmas for `genF` bounds, not instantiated at the concrete prefix. Prefix / block-0 helper only; not a full-word W1F certificate.
--
--   ## Formalization Note
--
--   Lean definition name: `IntMul_Kappa_R8_Data_BitOppbankBlock0CoreABound5a1`.
-- source:
--   IntMul Kappa R8 Bit Oppbank FormalOK: IntMul_Kappa_R8_Data_BitOppbankBlock0CoreABound5a1 split. Prefix / block-0 helper only; not a full-word W1F certificate.

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
theorem MovesV_genF_append_bounds_assoc (f : ℕ → ℕ)
    (A B C : List (ℕ × List ℕ × List (ℕ × ℕ)))
    (h : MovesV (genF f (A ++ (B ++ C))).2 ∧
      ∀ x, (genF f (A ++ (B ++ C))).1 x < SupG.codeBound) :
    MovesV (genF f (A ++ B ++ C)).2 ∧
      ∀ x, (genF f (A ++ B ++ C)).1 x < SupG.codeBound := by
  have e : A ++ B ++ C = A ++ (B ++ C) := List.append_assoc A B C
  rw [e]
  exact h

theorem genF_append3_fst (f : ℕ → ℕ)
    (A B C : List (ℕ × List ℕ × List (ℕ × ℕ))) :
    (genF f (A ++ B ++ C)).1 = (genF (genF (genF f A).1 B).1 C).1 := by
  have h1 := genF_append_fst f (A ++ B) C
  have h2 := genF_append_fst f A B
  exact h1.trans (congrArg (fun s => (genF s C).1) h2)


