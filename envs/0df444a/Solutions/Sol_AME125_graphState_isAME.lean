-- Prove2me | solution 1 for AME125.graphState_isAME
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T23:16:37.680251+00:00
-- url     : https://prove2.me/submissions/a0e52401-1d94-46a0-a783-fd03154f4592

module
public import Definitions.Def_AME125_Defs
public import Definitions.Def_AME125_GraphState
public import Theorems.Thm_AME125_graphState_isNormalized
public import Theorems.Thm_AME125_permuteState_graphState
public import Theorems.Thm_AME125_CutInj_submatrix
public import Theorems.Thm_AME125_card_firstHalf
public import Theorems.Thm_AME125_graphState_firstHalf
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
theorem _root_.solution {n : ℕ} (hn : Even n) (U : Matrix (Fin n) (Fin n) (ZMod 5))
    (h : ∀ A : Finset (Fin n), A.card = n / 2 → CutInj (U + Uᵀ) A) : IsAME (graphState U) := by
  refine ⟨graphState_isNormalized hn U, fun π ↦ ?_⟩
  rw [permuteState_graphState]
  apply graphState_firstHalf hn
  have e : U.submatrix π.symm π.symm + (U.submatrix π.symm π.symm)ᵀ =
      (U + Uᵀ).submatrix π.symm π.symm := by
    ext i j
    simp
  rw [e]
  exact CutInj.submatrix π (h _ (by rw [Finset.card_map, card_firstHalf (Nat.div_le_self n 2)]))
end AME125
