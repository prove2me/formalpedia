-- Prove2me | Definitions.Def_Operator_Crouzeix_PolytopeSoftSupport
-- name    : Operator_Crouzeix_PolytopeSoftSupport
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T13:55:47.590014+00:00
-- url     : https://prove2.me/theorems/9fdfa28d-7b8b-5457-9cc8-5ec0529b1653
-- title:
--   Polytope Soft Support
-- statement:
--   Definitions and structural lemmas for Polytope Soft Support, from Ezzeri Esa (savarin/lean-operator-theory; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Crouzeix-Palencia theorem, von Neumann inequality, and unitary power dilation development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/PolytopeSoftSupport.lean

import Definitions.Def_Operator_Crouzeix_SmoothJordanPolytopeReduction
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
set_option autoImplicit false
open Complex Set
open scoped ContDiff
noncomputable def polytopeDirectionalValue (z : ℂ) (theta : ℝ) : ℝ :=
  z.re * Real.cos theta + z.im * Real.sin theta
noncomputable def polytopeSoftPartition
    (u : Finset ℂ) (delta theta : ℝ) : ℝ :=
  ∑ z ∈ u, Real.exp (polytopeDirectionalValue z theta / delta)
noncomputable def polytopeSoftSupport
    (u : Finset ℂ) (delta theta : ℝ) : ℝ :=
  delta * Real.log (polytopeSoftPartition u delta theta)


