-- Prove2me | solution 1 for AME125.popcount_maskOf
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T23:17:42.380154+00:00
-- url     : https://prove2.me/submissions/5b1525c7-aee3-4d8d-8160-43fcccb96528

module
public import Definitions.Def_AME125_Data
public import Definitions.Def_AME125_GraphState
public import Definitions.Def_AME125_Certificate
public import Theorems.Thm_AME125_testBit_maskOf
public import Theorems.Thm_OpenQuantumProblem35_card_config
public import Theorems.Thm_OpenQuantumProblem35_combineFirst_leftIndex
public import Theorems.Thm_OpenQuantumProblem35_combineFirst_rightIndex
public import Theorems.Thm_OpenQuantumProblem35_diagonalState_apply
public import Theorems.Thm_OpenQuantumProblem35_mkStateVector_apply
public import Theorems.Thm_OpenQuantumProblem35_permuteState_apply
attribute [local simp] OpenQuantumProblem35.card_config
attribute [local simp] OpenQuantumProblem35.combineFirst_leftIndex
attribute [local simp] OpenQuantumProblem35.combineFirst_rightIndex
attribute [local simp] OpenQuantumProblem35.diagonalState_apply
attribute [local simp] OpenQuantumProblem35.mkStateVector_apply
attribute [local simp] OpenQuantumProblem35.permuteState_apply



set_option autoImplicit false
@[expose] public section
public section
open AME125
open scoped Matrix
namespace AME125
theorem _root_.solution (A : Finset (Fin 12)) : popcount (maskOf A) = A.card := by
  have hnd : ((List.range 12).filter fun i ↦ (maskOf A).testBit i).Nodup :=
    List.nodup_range.filter _
  rw [popcount, ← List.toFinset_card_of_nodup hnd, List.toFinset_filter, List.toFinset_range,
    ← Finset.card_map Fin.valEmbedding]
  congr 1
  ext x
  simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_map, Fin.valEmbedding_apply]
  constructor
  · rintro ⟨hx, hb⟩
    exact ⟨⟨x, hx⟩, (testBit_maskOf A ⟨x, hx⟩).mp hb, rfl⟩
  · rintro ⟨a, ha, rfl⟩
    exact ⟨a.2, (testBit_maskOf A a).mpr ha⟩
end AME125
