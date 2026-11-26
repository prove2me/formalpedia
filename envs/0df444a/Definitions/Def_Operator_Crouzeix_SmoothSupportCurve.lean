-- Prove2me | Definitions.Def_Operator_Crouzeix_SmoothSupportCurve
-- name    : Operator_Crouzeix_SmoothSupportCurve
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T14:03:20.954891+00:00
-- url     : https://prove2.me/theorems/ec3edf94-bbae-4287-863e-3a6ce9c8d65d
-- title:
--   Smooth Support Curve
-- statement:
--   Definitions and structural lemmas for Smooth Support Curve, from Ezzeri Esa (savarin/lean-operator-theory; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Crouzeix-Palencia theorem, von Neumann inequality, and unitary power dilation development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/SmoothSupportCurve.lean

import Definitions.Def_Operator_Crouzeix_PolytopeSoftSupportCurvature
set_option autoImplicit false
open Complex Set
open scoped ContDiff
noncomputable def smoothSupportUnitNormal (theta : ℝ) : ℂ :=
  circleMap 0 1 theta
noncomputable def smoothSupportUnitTangent (theta : ℝ) : ℂ :=
  smoothSupportUnitNormal theta * I
noncomputable def smoothSupportCurve (h : ℝ → ℝ) (theta : ℝ) : ℂ :=
  h theta • smoothSupportUnitNormal theta +
    deriv h theta • smoothSupportUnitTangent theta
noncomputable def smoothSupportCurvatureRadius
    (h : ℝ → ℝ) (theta : ℝ) : ℝ :=
  h theta + deriv (deriv h) theta
noncomputable def polytopeRoundedSupportCurve
    (u : Finset ℂ) (delta rho : ℝ) : ℝ → ℂ :=
  smoothSupportCurve (polytopeRoundedSupport u delta rho)


