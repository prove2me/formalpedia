-- Prove2me | Definitions.Def_Operator_NumericalRange_RadiusAffine
-- name    : Operator_NumericalRange_RadiusAffine
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T13:24:41.084247+00:00
-- url     : https://prove2.me/theorems/47e99e77-ad14-4eb6-a186-2317766cb6a5
-- title:
--   Radius Affine
-- statement:
--   Definitions and structural lemmas for Radius Affine, from Ezzeri Esa (savarin/lean-operator-theory; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Crouzeix-Palencia theorem, von Neumann inequality, and unitary power dilation development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/NumericalRange/RadiusAffine.lean

import Mathlib.Analysis.Convex.Function
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Topology.MetricSpace.Bounded
import Mathlib.Topology.Order.Compact
import Definitions.Def_Operator_NumericalRange_Affine
import Definitions.Def_Operator_NumericalRange_RadiusAdjoint
set_option autoImplicit false
open Filter
open ContinuousLinearMap
open scoped InnerProductSpace InnerProduct
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [Nontrivial E]
omit [Nontrivial E] in
/-- The set of scalar centers that globally minimize `w(A-cI)`. -/
def centeredNumericalRadiusMinimizers (A : E →L[ℂ] E) : Set ℂ :=
  {c | ∀ d : ℂ,
    numericalRadius (A - c • 1) ≤ numericalRadius (A - d • 1)}


