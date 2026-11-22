-- Prove2me | Definitions.Def_LeanPool_FormalLearningTheory_PureMath_FiniteVCApprox
-- name    : LeanPool_FormalLearningTheory_PureMath_FiniteVCApprox
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T05:31:55.518708+00:00
-- url     : https://prove2.me/theorems/7ff44a6d-72c5-4d1e-a50b-680fc995d2c7
-- title:
--   Finite VCApprox
-- statement:
--   Definitions and structural lemmas for Finite VCApprox, from Dhruv Gupta; LeanPool contributors's pinned Formal Learning Theory Kernel development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/FormalLearningTheory/PureMath/FiniteVCApprox.lean

module
public import Definitions.Def_LeanPool_FormalLearningTheory_PureMath_ApproxMinimax
public import Mathlib.Combinatorics.SetFamily.Shatter
public import Mathlib.Algebra.BigOperators.Field
set_option autoImplicit true
@[expose] public section
@[expose] public section
open Finset
noncomputable section
def trueExpectation {H : Type*} [Fintype H]
    (μ : FinitePMF H) (f : H → ℝ) : ℝ :=
  ∑ h : H, μ.prob h * f h
def boolTestExpectation {H : Type*} [Fintype H]
    (μ : FinitePMF H) (f : H → Bool) : ℝ :=
  trueExpectation μ (fun h => if f h then (1 : ℝ) else 0)
def tvDistance {H : Type*} [Fintype H]
    (μ ν : FinitePMF H) : ℝ :=
  ∑ h : H, |μ.prob h - ν.prob h|
def boolFamilyToFinsetFamily {H : Type*} [Fintype H] [DecidableEq H]
    (A : Finset (H → Bool)) : Finset (Finset H) :=
  A.image (fun f => Finset.univ.filter (fun h => f h = true))
noncomputable def Finset.boolVCDim {H : Type*} [Fintype H] [DecidableEq H]
    (A : Finset (H → Bool)) : ℕ :=
  (boolFamilyToFinsetFamily A).vcDim
end


