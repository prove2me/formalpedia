-- Prove2me | Definitions.Def_SharpIntermediateSubgroupBounds_Manuscript
-- name    : SharpIntermediateSubgroupBounds_Manuscript
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T05:45:39.781666+00:00
-- url     : https://prove2.me/theorems/05991590-e734-58f5-a910-73bdd2e5f0c5
-- title:
--   Manuscript
-- statement:
--   Definitions and structural lemmas for Manuscript, from Sébastien Palcoux (sebastienpalcoux/sharp-intermediate-subgroup-bounds; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Sharp bounds for intervals in finite subgroup lattices development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/sebastienpalcoux/sharp-intermediate-subgroup-bounds/blob/522d6dfcb5d25d47455375e3df0f8a561b7b780b/SharpIntermediateSubgroupBounds/Manuscript.lean

import Definitions.Def_SharpIntermediateSubgroupBounds_Gaussian
import Definitions.Def_SharpIntermediateSubgroupBounds_PrimePower
import Definitions.Def_SharpIntermediateSubgroupBounds_GroupMain
import Definitions.Def_SharpIntermediateSubgroupBounds_Escape
import Theorems.Thm_SharpIntermediateSubgroupBounds_BranchingTree_branchProduct_zero
import Theorems.Thm_SharpIntermediateSubgroupBounds_escapeBranchProduct_cons
import Theorems.Thm_SharpIntermediateSubgroupBounds_natFloor_indexLog
attribute [local simp] SharpIntermediateSubgroupBounds.BranchingTree.branchProduct_zero
attribute [local simp] SharpIntermediateSubgroupBounds.escapeBranchProduct_cons
attribute [local simp] SharpIntermediateSubgroupBounds.natFloor_indexLog


set_option autoImplicit true
namespace SharpIntermediateSubgroupBounds
open Filter
noncomputable section
noncomputable local instance manuscriptSubgroupIntervalFintype
    {G : Type*} [Group G] [Fintype G] (H : Subgroup G) :
    Fintype (Set.Ici H) :=
  Fintype.ofFinite _
abbrev ElementaryAbelianGroup (p n : ℕ) :=
  Multiplicative (Fin n → ZMod p)
abbrev elementaryAbelianInterval (p n : ℕ) :=
  Set.Ici (⊥ : Subgroup (ElementaryAbelianGroup p n))
theorem manuscript_generatedFrom_bot_eq_top_iff_addClosure
    (p r : ℕ) [Fact p.Prime]
    (x : Fin r → ElementaryAbelianGroup p r) :
    generatedFrom (⊥ : Subgroup (ElementaryAbelianGroup p r)) x = ⊤ ↔
      AddSubgroup.closure (Set.range (fun i ↦ Multiplicative.toAdd (x i))) = ⊤ := by
  rw [generatedFrom, bot_sup_eq]
  have hrange : Multiplicative.ofAdd ⁻¹' Set.range x =
      Set.range (fun i ↦ Multiplicative.toAdd (x i)) := by
    ext y
    constructor
    · rintro ⟨i, hi⟩
      exact ⟨i, congrArg Multiplicative.toAdd hi⟩
    · rintro ⟨i, rfl⟩
      exact ⟨i, rfl⟩
  constructor
  · intro h
    have h' := congrArg Subgroup.toAddSubgroup' h
    simpa [Subgroup.toAddSubgroup'_closure, hrange] using h'
  · intro h
    apply Subgroup.toAddSubgroup'.injective
    simpa [Subgroup.toAddSubgroup'_closure, hrange] using h
def manuscript_rawRelGenEquivGeneratingFrames (p r : ℕ) [Fact p.Prime] :
    RawRelGen (⊥ : Subgroup (ElementaryAbelianGroup p r)) ⊤ r ≃
      GeneratingFramesFinZMod p r where
  toFun x := ⟨fun i ↦ Multiplicative.toAdd (x.1 i),
    (manuscript_generatedFrom_bot_eq_top_iff_addClosure p r x.1).mp x.2.2⟩
  invFun s := ⟨fun i ↦ Multiplicative.ofAdd (s.1 i),
    fun _ ↦ trivial,
    (manuscript_generatedFrom_bot_eq_top_iff_addClosure p r _).mpr s.2⟩
  left_inv := by intro x; apply Subtype.ext; rfl
  right_inv := by intro s; apply Subtype.ext; rfl
end
end SharpIntermediateSubgroupBounds


