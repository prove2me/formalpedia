-- Prove2me | Definitions.Def_DeletionCode_FiniteWalkRules
-- name    : DeletionCode_FiniteWalkRules
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-19T06:27:18.660641+00:00
-- url     : https://prove2.me/theorems/f1206c02-1b14-48cd-b0a1-fafd64c8c086
-- title:
--   Finite Walk Rules
-- statement:
--   Definitions and structural lemmas for Finite Walk Rules, from Eyal En Gad's pinned Deletion codes: binary insertion/deletion bound development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/FiniteWalkRules.lean

import Definitions.Def_DeletionCode_WalkSelection
import Definitions.Def_DeletionCode_FiniteGenerating
import Definitions.Def_DeletionCode_CatalogueAlgebra
import Theorems.Thm_DeletionCode_BlockPartition_mem_attachedBlocks
import Theorems.Thm_DeletionCode_BlockPartition_mem_blockOf
import Theorems.Thm_DeletionCode_BlockPartition_mem_blocks
import Theorems.Thm_DeletionCode_CatalogueAlgebra_rational_neg
import Theorems.Thm_DeletionCode_CatalogueAlgebra_rational_zero
import Theorems.Thm_DeletionCode_ComponentFibers_mem_fiber
import Theorems.Thm_DeletionCode_SupportInclusion_supportComponentMap_mk
attribute [local simp] DeletionCode.BlockPartition.mem_attachedBlocks
attribute [local simp] DeletionCode.BlockPartition.mem_blockOf
attribute [local simp] DeletionCode.BlockPartition.mem_blocks
attribute [local simp] DeletionCode.CatalogueAlgebra.rational_neg
attribute [local simp] DeletionCode.CatalogueAlgebra.rational_zero
attribute [local simp] DeletionCode.ComponentFibers.mem_fiber
attribute [local simp] DeletionCode.SupportInclusion.supportComponentMap_mk


set_option autoImplicit true
namespace DeletionCode.FiniteWalkRules
open HeaderRecovery SignedSupport SignedRuleCount
open CatalogueAlgebra WalkSelection FiniteGenerating
variable {k m : ℕ}
def step (p : Fin (m + 1) → Gram (windowLength k) → ℤ) (i : Fin m) :
    Gram (windowLength k) → ℤ := p i.succ - p i.castSucc
def rationalPath (p : Fin (m + 1) → Gram (windowLength k) → ℤ) :
    Fin (m + 1) → Gram (windowLength k) → ℚ := fun j => rational (p j)
noncomputable def selectedRules
    (p : Fin (m + 1) → Gram (windowLength k) → ℤ) (S : Finset (Fin m)) :
    RuleSet k := by
  classical
  exact S.image (step p)
@[simp] theorem mem_selectedRules
    (p : Fin (m + 1) → Gram (windowLength k) → ℤ) (S : Finset (Fin m))
    (u : Gram (windowLength k) → ℤ) :
    u ∈ selectedRules p S ↔ ∃ i ∈ S, step p i = u := by
  classical
  exact Finset.mem_image
theorem step_mem_selectedRules
    (p : Fin (m + 1) → Gram (windowLength k) → ℤ) (S : Finset (Fin m))
    (i : Fin m) (hi : i ∈ S) : step p i ∈ selectedRules p S :=
  (mem_selectedRules p S _).mpr ⟨i, hi, rfl⟩
theorem selectedIndex_exists
    (p : Fin (m + 1) → Gram (windowLength k) → ℤ) (S : Finset (Fin m))
    (u : selectedRules p S) : ∃ i : S, step p i.val = u.val := by
  obtain ⟨i, hi, heq⟩ := (mem_selectedRules p S u.val).mp u.property
  exact ⟨⟨i, hi⟩, heq⟩
noncomputable def selectedIndex
    (p : Fin (m + 1) → Gram (windowLength k) → ℤ) (S : Finset (Fin m))
    (u : selectedRules p S) : S := Classical.choose (selectedIndex_exists p S u)
noncomputable def selectedRank
    (p : Fin (m + 1) → Gram (windowLength k) → ℤ) (S : Finset (Fin m))
    (u : Gram (windowLength k) → ℤ) : ℕ := by
  classical
  exact if hu : u ∈ selectedRules p S then (selectedIndex p S ⟨u, hu⟩).val.val else 0
end DeletionCode.FiniteWalkRules


