-- Prove2me | Definitions.Def_Operator_Crouzeix_SmoothJordanSimilarity
-- name    : Operator_Crouzeix_SmoothJordanSimilarity
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T13:55:26.953801+00:00
-- url     : https://prove2.me/theorems/1271781c-ef27-5583-b59f-c53603f4cd78
-- title:
--   Smooth Jordan Similarity
-- statement:
--   Definitions and structural lemmas for Smooth Jordan Similarity, from Ezzeri Esa (savarin/lean-operator-theory; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Crouzeix-Palencia theorem, von Neumann inequality, and unitary power dilation development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/SmoothJordanSimilarity.lean

import Definitions.Def_Operator_Crouzeix_SmoothJordanAffine
import Definitions.Def_Operator_Crouzeix_SmoothJordanPolytopeReduction
set_option autoImplicit false
open Complex Metric Set
open scoped InnerProductSpace
noncomputable def complexMulRealEquiv (a : ℂ) (ha : a ≠ 0) :
    ℂ ≃L[ℝ] ℂ :=
  ContinuousLinearEquiv.smulLeft (R₁ := ℝ) (M₁ := ℂ) (Units.mk0 a ha)
def HasSmoothJordanOuterApproximationForUnitBallPolytopes : Prop :=
  ∀ (u : Finset ℂ) (c : ℂ),
    Metric.closedBall c 1 ⊆ convexHull ℝ (u : Set ℂ) →
      HasSmoothJordanOuterApproximation (convexHull ℝ (u : Set ℂ))
universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E] [Nontrivial E]


