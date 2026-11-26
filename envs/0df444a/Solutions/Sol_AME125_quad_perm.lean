-- Prove2me | solution 1 for AME125.quad_perm
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T23:08:10.305514+00:00
-- url     : https://prove2.me/submissions/2580911b-27e9-49d5-acc8-b7ae2a748ce1

module
public import Definitions.Def_AME125_Defs
public import Definitions.Def_AME125_GraphState
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
theorem _root_.solution {n : ℕ} (U : Matrix (Fin n) (Fin n) (ZMod 5)) (π : Equiv.Perm (Fin n))
    (x : Fin n → ZMod 5) : quad U (fun i ↦ x (π i)) = quad (U.submatrix π.symm π.symm) x := by
  symm
  unfold quad
  rw [← Equiv.sum_comp π]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [← Equiv.sum_comp π]
  simp
end AME125
