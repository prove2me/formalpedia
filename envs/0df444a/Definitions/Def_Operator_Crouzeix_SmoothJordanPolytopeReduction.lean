-- Prove2me | Definitions.Def_Operator_Crouzeix_SmoothJordanPolytopeReduction
-- name    : Operator_Crouzeix_SmoothJordanPolytopeReduction
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T13:53:51.287346+00:00
-- url     : https://prove2.me/theorems/565921c2-c04c-5e44-96d2-82dd51fc50af
-- title:
--   Smooth Jordan Polytope Reduction
-- statement:
--   Definitions and structural lemmas for Smooth Jordan Polytope Reduction, from Ezzeri Esa (savarin/lean-operator-theory; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Crouzeix-Palencia theorem, von Neumann inequality, and unitary power dilation development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/SmoothJordanPolytopeReduction.lean

import Definitions.Def_Operator_Crouzeix_SmoothJordanOuterApproximationReduction
import Mathlib.Analysis.Normed.Affine.Convex
set_option autoImplicit false
open Complex Metric Set
open scoped InnerProductSpace
def HasSmoothJordanOuterApproximationForPolytopes : Prop :=
  ∀ u : Finset ℂ,
    (interior (convexHull ℝ (u : Set ℂ))).Nonempty →
      HasSmoothJordanOuterApproximation (convexHull ℝ (u : Set ℂ))
universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E] [Nontrivial E]


