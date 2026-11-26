-- Prove2me | solution 1 for AME125.permuteState_graphState
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T23:10:09.379624+00:00
-- url     : https://prove2.me/submissions/74f27e5b-5e3c-40c1-afce-76c7e231cfa2

module
public import Definitions.Def_AME125_Defs
public import Definitions.Def_AME125_GraphState
public import Theorems.Thm_AME125_quad_perm
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
theorem _root_.solution {n : ℕ} (π : Equiv.Perm (Fin n))
    (U : Matrix (Fin n) (Fin n) (ZMod 5)) :
    permuteState π (graphState U) = graphState (U.submatrix π.symm π.symm) := by
  ext x
  rw [permuteState_apply]
  simp only [graphState, mkStateVector_apply]
  rw [show toZ (permuteConfig π x) = fun i ↦ toZ x (π i) from rfl, quad_perm]
end AME125
