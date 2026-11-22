-- Prove2me | Definitions.Def_LeanPool_PebblingLean_Paper
-- name    : LeanPool_PebblingLean_Paper
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T05:55:34.839224+00:00
-- url     : https://prove2.me/theorems/96ad7099-66ee-4ca3-abf0-d1d52bfe059d
-- title:
--   Paper
-- statement:
--   Definitions and structural lemmas for Paper, from Lior Pachter; LeanPool contributors's pinned Optimal Pebbling Number of the Hypercube development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/Paper.lean

module
public import Definitions.Def_LeanPool_PebblingLean_UpperBoundParameters
public import Definitions.Def_LeanPool_PebblingLean_LowerBound
public import Mathlib.Algebra.Order.Algebra
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Mathlib.Tactic.Positivity.Finset
public import Theorems.Thm_PebblingLean_Graph_Walk_length_append
public import Theorems.Thm_PebblingLean_Graph_Walk_length_reverse
public import Theorems.Thm_PebblingLean_Hypercube_fromDiffSet_empty
public import Theorems.Thm_PebblingLean_Hypercube_mem_annulus
public import Theorems.Thm_PebblingLean_Hypercube_size_constantDistribution
public import Theorems.Thm_PebblingLean_Hypercube_solvableAtLeast_constantDistribution
public import Theorems.Thm_PebblingLean_Pebbling_fibersDistribution_apply
public import Theorems.Thm_PebblingLean_Pebbling_moveDistribution_apply_from
public import Theorems.Thm_PebblingLean_Pebbling_moveDistribution_apply_of_ne
public import Theorems.Thm_PebblingLean_Pebbling_moveDistribution_apply_to
public import Theorems.Thm_PebblingLean_Pebbling_single_apply_ne
public import Theorems.Thm_PebblingLean_Pebbling_single_apply_self
public import Theorems.Thm_PebblingLean_Pebbling_size_single
public import Theorems.Thm_PebblingLean_Pebbling_size_zero
public import Theorems.Thm_PebblingLean_Pebbling_sliceDistribution_apply_off
public import Theorems.Thm_PebblingLean_Pebbling_sliceDistribution_apply_on
public import Theorems.Thm_PebblingLean_Pebbling_twoPoint_apply_left
public import Theorems.Thm_PebblingLean_Pebbling_twoPoint_apply_ne
public import Theorems.Thm_PebblingLean_Pebbling_twoPoint_apply_right
public import Theorems.Thm_PebblingLean_Pebbling_weight_zero
attribute [local simp] PebblingLean.Graph.Walk.length_append
attribute [local simp] PebblingLean.Graph.Walk.length_reverse
attribute [local simp] PebblingLean.Hypercube.fromDiffSet_empty
attribute [local simp] PebblingLean.Hypercube.mem_annulus
attribute [local simp] PebblingLean.Pebbling.fibersDistribution_apply
attribute [local simp] PebblingLean.Pebbling.moveDistribution_apply_from
attribute [local simp] PebblingLean.Pebbling.moveDistribution_apply_of_ne
attribute [local simp] PebblingLean.Pebbling.moveDistribution_apply_to
attribute [local simp] PebblingLean.Pebbling.single_apply_ne
attribute [local simp] PebblingLean.Pebbling.single_apply_self
attribute [local simp] PebblingLean.Pebbling.size_single
attribute [local simp] PebblingLean.Pebbling.size_zero
attribute [local simp] PebblingLean.Pebbling.sliceDistribution_apply_off
attribute [local simp] PebblingLean.Pebbling.sliceDistribution_apply_on
attribute [local simp] PebblingLean.Pebbling.twoPoint_apply_left
attribute [local simp] PebblingLean.Pebbling.twoPoint_apply_ne
attribute [local simp] PebblingLean.Pebbling.twoPoint_apply_right
attribute [local simp] PebblingLean.Pebbling.weight_zero


set_option autoImplicit true
@[expose] public section
@[expose] public section
namespace PebblingLean
namespace Hypercube
namespace Paper
open Pebbling
def N0 : ℕ :=
  PaperParameters.explicitCutoff
noncomputable def CLean : ℝ :=
  Real.exp (4 * PaperParameters.loss N0) *
    finiteBaseNormalizedBound
      (PaperParameters.recursiveCostBound (217 : ℝ) N0) N0
theorem exists_solvable_size (n : ℕ) :
    ∃ k : ℕ, HasSolvableSize (graph n) k := by
  refine ⟨2 ^ n, ?_⟩
  refine ⟨constantDistribution n 1, ?_, ?_⟩
  · simpa using size_constantDistribution n 1
  · simpa [Solvable] using solvableAtLeast_constantDistribution n 1
noncomputable def optimalPebblingNumber (n : ℕ) : ℕ :=
  by
    classical
    exact Nat.find (exists_solvable_size n)
end Paper
end Hypercube
end PebblingLean


