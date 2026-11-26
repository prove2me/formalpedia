-- Prove2me | Definitions.Def_Operator_Crouzeix_ScalarCompanion
-- name    : Operator_Crouzeix_ScalarCompanion
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T12:34:29.069795+00:00
-- url     : https://prove2.me/theorems/86e3bf1b-1976-4bd2-82ba-f2a865336e4f
-- title:
--   Scalar Companion
-- statement:
--   Definitions and structural lemmas for Scalar Companion, from Ezzeri Esa (savarin/lean-operator-theory; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Crouzeix-Palencia theorem, von Neumann inequality, and unitary power dilation development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/ScalarCompanion.lean

import Definitions.Def_Operator_Crouzeix_AuxOperator
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
set_option autoImplicit false
open Complex Filter MeasureTheory Set spectrum
open scoped Interval Real
noncomputable def crouzeixPolynomialScalarCompanion
    (Omega : SmoothJordanDomain) (p : Polynomial ℂ) (z : ℂ) : ℂ :=
  (2 * (Real.pi : ℂ) * I)⁻¹ *
    contourIntegral
      (fun σ ↦ star (Polynomial.eval σ p) * (σ - z)⁻¹)
      Omega.boundaryParam
noncomputable def crouzeixPolynomialScalarCompanionDeriv
    (Omega : SmoothJordanDomain) (p : Polynomial ℂ) (z : ℂ) : ℂ :=
  (2 * (Real.pi : ℂ) * I)⁻¹ *
    ∫ t in (0 : ℝ)..(2 * Real.pi),
      deriv Omega.boundaryParam t *
        star (Polynomial.eval (Omega.boundaryParam t) p) *
          (Omega.boundaryParam t - z)⁻¹ ^ 2


