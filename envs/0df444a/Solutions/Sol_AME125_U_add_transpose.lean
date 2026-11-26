-- Prove2me | solution 1 for AME125.U_add_transpose
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T23:16:22.785875+00:00
-- url     : https://prove2.me/submissions/d6ecbcfb-7d7b-4b80-942e-30e5c0424ecb

module
public import Definitions.Def_AME125_Data
public import Definitions.Def_AME125_GraphState
public import Definitions.Def_AME125_Certificate
public import Theorems.Thm_AME125_thetaN_symm
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
theorem _root_.solution (i j : Fin 12) (h : i ≠ j) : (U + Uᵀ) i j = theta i j := by
  simp only [Matrix.add_apply, Matrix.transpose_apply, U]
  rcases lt_or_gt_of_ne (Fin.val_ne_of_ne h) with hij | hij
  · simp [hij.le, not_le.mpr hij]
  · simp [hij.le, not_le.mpr hij, theta, thetaN_symm i.1 i.2 j.1 j.2]
end AME125
