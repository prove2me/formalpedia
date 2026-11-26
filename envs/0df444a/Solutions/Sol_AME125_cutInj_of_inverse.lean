-- Prove2me | solution 1 for AME125.cutInj_of_inverse
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T23:17:32.462037+00:00
-- url     : https://prove2.me/submissions/e97fb1bd-0b94-417c-98d1-5e26cece6ff9

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
theorem _root_.solution {n : ℕ} (S : Matrix (Fin n) (Fin n) (ZMod 5)) (A : Finset (Fin n))
    (R : Fin n → Fin n → ZMod 5)
    (h : ∀ i ∈ A, ∀ k ∈ A, ∑ j, (if j ∈ A then 0 else S i j * R j k) = if i = k then 1 else 0) :
    CutInj S A := by
  intro w hw hcol
  funext k
  by_cases hk : k ∈ A
  · calc w k = ∑ i, w i * (if i = k then 1 else 0) := by simp
      _ = ∑ i, w i * ∑ j, (if j ∈ A then 0 else S i j * R j k) := by
        refine Finset.sum_congr rfl fun i _ ↦ ?_
        by_cases hi : i ∈ A
        · rw [h i hi k hk]
        · simp [hw i hi]
      _ = ∑ j, (if j ∈ A then 0 else (∑ i, w i * S i j) * R j k) := by
        simp_rw [Finset.mul_sum]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun j _ ↦ ?_
        split_ifs <;> simp [Finset.sum_mul, mul_assoc]
      _ = 0 := by
        refine Finset.sum_eq_zero fun j _ ↦ ?_
        split_ifs with hj
        · rfl
        · simp [hcol j hj]
  · exact hw k hk
end AME125
