-- Prove2me | solution 1 for AME125.maskOf_lt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T23:17:37.893807+00:00
-- url     : https://prove2.me/submissions/8f136f7f-ec5e-45ba-952b-55088658fc74

module
public import Definitions.Def_AME125_Data
public import Definitions.Def_AME125_GraphState
public import Definitions.Def_AME125_Certificate
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
theorem _root_.solution (A : Finset (Fin 12)) : maskOf A < 4096 := by
  calc maskOf A ≤ ∑ i ∈ Finset.range 12, 2 ^ i := by
        refine Finset.sum_le_sum_of_subset fun x hx ↦ ?_
        obtain ⟨a, _, rfl⟩ := Finset.mem_map.mp hx
        simp [a.2]
    _ < 4096 := by decide
end AME125
