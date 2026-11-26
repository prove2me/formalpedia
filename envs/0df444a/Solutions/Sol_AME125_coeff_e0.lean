-- Prove2me | solution 1 for AME125.coeff_e0
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T23:18:30.039061+00:00
-- url     : https://prove2.me/submissions/2cd07426-58f8-4382-be84-3b63cf006994

module
public import Definitions.Def_AME125_Certificate
public import Definitions.Def_AME125_Control
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
open OpenQuantumProblem35
open scoped Matrix
namespace AME125
theorem _root_.solution :
    coeff (Nat.div_le_self 12 2) (controlU + controlUᵀ) (toZ e0 - toZ (0 : Config 6 5)) = 0 := by
  funext k
  simp only [coeff, Pi.zero_apply]
  refine Finset.sum_eq_zero fun i _ ↦ ?_
  by_cases hi : i.1 = 0
  · have hk : 6 ≤ (rightIndex (Nat.div_le_self 12 2) k).1 := by simp [rightIndex]
    have hne : rightIndex (Nat.div_le_self 12 2) k ≠ 0 := fun h ↦ by simp [h] at hk
    simp [controlU, U, hi, hk, hne, Matrix.add_apply, Matrix.transpose_apply]
  · have : lift (n := 12) (toZ e0 - toZ (0 : Config 6 5)) i = 0 := by
      simp only [lift]
      split_ifs with h
      · rw [Pi.sub_apply]
        have h1 : toZ e0 ⟨i.1, h⟩ = 0 := by
          simp only [toZ, e0, hi, ite_false]
          rfl
        have h2 : toZ (0 : Config 6 5) ⟨i.1, h⟩ = 0 := rfl
        rw [h1, h2, sub_zero]
      · rfl
    simp [this]
end AME125
