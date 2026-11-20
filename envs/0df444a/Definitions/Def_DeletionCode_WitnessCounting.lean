-- Prove2me | Definitions.Def_DeletionCode_WitnessCounting
-- name    : DeletionCode_WitnessCounting
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-19T06:27:27.732908+00:00
-- url     : https://prove2.me/theorems/d087ec53-8687-489b-bb8c-cb0314ca77d6
-- title:
--   Witness Counting
-- statement:
--   Definitions and structural lemmas for Witness Counting, from Eyal En Gad's pinned Deletion codes: binary insertion/deletion bound development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/WitnessCounting.lean

import Definitions.Def_DeletionCode_ManuscriptCounting
import Definitions.Def_DeletionCode_WitnessCases
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Finite.Sigma
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Theorems.Thm_DeletionCode_BlockPartition_mem_attachedBlocks
import Theorems.Thm_DeletionCode_BlockPartition_mem_blockOf
import Theorems.Thm_DeletionCode_BlockPartition_mem_blocks
import Theorems.Thm_DeletionCode_CatalogueAlgebra_rational_neg
import Theorems.Thm_DeletionCode_CatalogueAlgebra_rational_zero
import Theorems.Thm_DeletionCode_ComponentFibers_mem_fiber
import Theorems.Thm_DeletionCode_FiniteRelationBlocks_mem_selectedBlocks
import Theorems.Thm_DeletionCode_SupportInclusion_supportComponentMap_mk
attribute [local simp] DeletionCode.BlockPartition.mem_attachedBlocks
attribute [local simp] DeletionCode.BlockPartition.mem_blockOf
attribute [local simp] DeletionCode.BlockPartition.mem_blocks
attribute [local simp] DeletionCode.CatalogueAlgebra.rational_neg
attribute [local simp] DeletionCode.CatalogueAlgebra.rational_zero
attribute [local simp] DeletionCode.ComponentFibers.mem_fiber
attribute [local simp] DeletionCode.FiniteRelationBlocks.mem_selectedBlocks
attribute [local simp] DeletionCode.SupportInclusion.supportComponentMap_mk


set_option autoImplicit true
namespace DeletionCode.WitnessCounting
open Windows HeaderRecovery SignedRuleCount RuleSetGraph CountExponent
open ManuscriptCounting WitnessCases FiniteGenerating
open scoped BigOperators
structure Candidate (t : ℕ) (x : Letters) (n k R : ℕ) (U : RuleSet k) : Prop where
  generating : GeneratingSet t x n k R (componentCount U) U
  bounds : WitnessBounds t k U
  independent : Independent U
def AllowedComponents (t k R c : ℕ) : Prop :=
  c ≤ (2 * t - 1) * R + 1 ∧
    (R ≤ windowLength k → c ≤ (2 * t - 1) * R)
abbrev ComponentIndex (t k R : ℕ) :=
  {c : Fin (2 * t * R + 1) // AllowedComponents t k R c.val}
noncomputable instance componentIndexFintype (t k R : ℕ) :
    Fintype (ComponentIndex t k R) := by
  classical
  unfold ComponentIndex
  infer_instance
theorem allowed_of_bounds {t k R : ℕ} {U : RuleSet k}
    (hcard : U.card = R) (hb : WitnessBounds t k U) :
    AllowedComponents t k R (componentCount U) := by
  constructor
  · simpa only [hcard] using hb.components
  · intro hsmall
    have h := hb.small_components (by simpa only [hcard] using hsmall)
    simpa only [hcard] using h
theorem componentCount_lt_index_bound {t k R : ℕ} (ht : 1 ≤ t) (hR : 1 ≤ R)
    {U : RuleSet k} (hcard : U.card = R) (hb : WitnessBounds t k U) :
    componentCount U < 2 * t * R + 1 := by
  have hc := (allowed_of_bounds hcard hb).1
  have ht' : 1 ≤ 2 * t := by omega
  have hsplit : (2 * t - 1) * R + R = 2 * t * R := by
    calc
      _ = (2 * t - 1 + 1) * R := by ring
      _ = _ := by rw [Nat.sub_add_cancel ht']
  omega
noncomputable def actualComponentIndex {t k R : ℕ} (ht : 1 ≤ t) (hR : 1 ≤ R)
    (U : RuleSet k) (hcard : U.card = R) (hb : WitnessBounds t k U) :
    ComponentIndex t k R :=
  ⟨⟨componentCount U, componentCount_lt_index_bound ht hR hcard hb⟩,
    allowed_of_bounds hcard hb⟩
abbrev IndexedSets (t : ℕ) (x : Letters) (n k R : ℕ) :=
  Σ c : ComponentIndex t k R,
    {U : RuleSet k // GeneratingSet t x n k R c.val.val U}
noncomputable def partition (t : ℕ) (ht : 1 ≤ t) (x : Letters) (n k R : ℕ) (hR : 1 ≤ R) :
    {U : RuleSet k // Candidate t x n k R U} → IndexedSets t x n k R :=
  fun U => ⟨actualComponentIndex ht hR U.val U.property.generating.1 U.property.bounds,
    ⟨U.val, U.property.generating⟩⟩
end DeletionCode.WitnessCounting


