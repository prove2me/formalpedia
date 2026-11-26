-- Prove2me | solution 1 for AME125.quad_add
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T23:07:50.627729+00:00
-- url     : https://prove2.me/submissions/8a20db83-3f88-49f1-9947-57bcc32e9c79

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
theorem _root_.solution {n : ℕ} (U : Matrix (Fin n) (Fin n) (ZMod 5)) (y w : Fin n → ZMod 5) :
    quad U (y + w) = quad U y + quad U w + ∑ j, (∑ i, w i * (U + Uᵀ) i j) * y j := by
  simp only [quad, Pi.add_apply, Matrix.add_apply, Matrix.transpose_apply]
  have h1 : ∑ j, (∑ i, w i * (U i j + U j i)) * y j =
      ∑ i, ∑ j, U i j * w i * y j + ∑ i, ∑ j, U i j * y i * w j := by
    simp_rw [Finset.sum_mul, mul_add, add_mul, Finset.sum_add_distrib]
    rw [Finset.sum_comm]
    congr 1
    · exact Finset.sum_congr rfl fun _ _ ↦ Finset.sum_congr rfl fun _ _ ↦ by ring
    · exact Finset.sum_congr rfl fun _ _ ↦ Finset.sum_congr rfl fun _ _ ↦ by ring
  rw [h1]
  simp_rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun _ _ ↦ Finset.sum_congr rfl fun _ _ ↦ by ring
end AME125
