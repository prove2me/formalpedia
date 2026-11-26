-- Prove2me | solution 1 for AME125.controlState_not_isAME
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T23:21:40.8843+00:00
-- url     : https://prove2.me/submissions/f6fe96db-eac8-4de2-8daf-3e4aed608af9

module
public import Definitions.Def_AME125_Certificate
public import Definitions.Def_AME125_Control
public import Theorems.Thm_AME125_coeff_e0
public import Theorems.Thm_AME125_reduced_graphState
public import Theorems.Thm_OpenQuantumProblem35_card_config
public import Theorems.Thm_OpenQuantumProblem35_combineFirst_leftIndex
public import Theorems.Thm_OpenQuantumProblem35_combineFirst_rightIndex
public import Theorems.Thm_OpenQuantumProblem35_diagonalState_apply
public import Theorems.Thm_OpenQuantumProblem35_maximallyMixed_apply
public import Theorems.Thm_OpenQuantumProblem35_mkStateVector_apply
public import Theorems.Thm_OpenQuantumProblem35_permuteState_apply
public import Theorems.Thm_OpenQuantumProblem35_permuteState_refl
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
theorem _root_.solution : ¬ IsAME controlState := by
  intro h
  have hred := h.2 (Equiv.refl _)
  rw [permuteState_refl] at hred
  have hentry := congrFun (congrFun hred e0) 0
  obtain ⟨K, -, hK⟩ := reduced_graphState (Nat.div_le_self 12 2) controlU e0 0
  have hne : e0 ≠ 0 := fun h0 ↦ by simpa [e0] using congrFun h0 ⟨0, by norm_num⟩
  rw [maximallyMixed_apply, if_neg hne] at hentry
  rw [controlState, hK, coeff_e0, if_pos rfl] at hentry
  have hχ : χ K ≠ 0 := fun h0 ↦ by simpa [h0] using AddChar.norm_apply χ K
  simp [hχ] at hentry
end AME125
