-- Prove2me | Definitions.Def_Operator_Crouzeix_ScalarCompanionBoundaryMeasure
-- name    : Operator_Crouzeix_ScalarCompanionBoundaryMeasure
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T13:06:52.071732+00:00
-- url     : https://prove2.me/theorems/adbaaf98-7404-4009-b33c-073c756de430
-- title:
--   Scalar Companion Boundary Measure
-- statement:
--   Definitions and structural lemmas for Scalar Companion Boundary Measure, from Ezzeri Esa (savarin/lean-operator-theory; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Crouzeix-Palencia theorem, von Neumann inequality, and unitary power dilation development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/ScalarCompanionBoundaryMeasure.lean

import Definitions.Def_Operator_Crouzeix_ScalarCompanionPhaseInduction
import Definitions.Def_Operator_Crouzeix_ScalarCompanionRadial
set_option autoImplicit false
open Complex MeasureTheory Polynomial Set
open scoped ComplexConjugate Interval Real
noncomputable def crouzeixBoundaryDoubleLayerDensity
    (Omega : SmoothJordanDomain) (xi : ℂ) (t : ℝ) : ℝ :=
  (deriv Omega.boundaryParam t *
    (Omega.boundaryParam t - xi)⁻¹).im / Real.pi


