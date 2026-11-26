-- Prove2me | solution 1 for AME125.CutInj.submatrix
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T23:08:46.015794+00:00
-- url     : https://prove2.me/submissions/830c92c8-6cb5-4690-a14a-a5d814b2a0db

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
namespace CutInj
theorem _root_.solution {n : ℕ} {S : Matrix (Fin n) (Fin n) (ZMod 5)} (π : Equiv.Perm (Fin n))
    {A : Finset (Fin n)} (h : CutInj S (A.map π.symm.toEmbedding)) :
    CutInj (S.submatrix π.symm π.symm) A := by
  intro w hw hcol
  have hz := h (fun k ↦ w (π k)) (fun k hk ↦ hw (π k) fun h' ↦ hk (by
      simpa using Finset.mem_map_of_mem π.symm.toEmbedding h')) (fun j hj ↦ by
      have hj' : π j ∉ A := fun h' ↦ hj (by
        simpa using Finset.mem_map_of_mem π.symm.toEmbedding h')
      have hc := hcol (π j) hj'
      simp only [Matrix.submatrix_apply, Equiv.symm_apply_apply] at hc
      rw [← hc, ← Equiv.sum_comp π (fun i ↦ w i * S (π.symm i) j)]
      simp)
  funext i
  simpa using congrFun hz (π.symm i)
end CutInj
end AME125
