-- Prove2me | Definitions.Def_Operator_Crouzeix_ScalarCompanionPlemelj
-- name    : Operator_Crouzeix_ScalarCompanionPlemelj
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T12:38:38.336597+00:00
-- url     : https://prove2.me/theorems/1f297ad1-ec10-473a-afb0-795192be6ae4
-- title:
--   Scalar Companion Plemelj
-- statement:
--   Definitions and structural lemmas for Scalar Companion Plemelj, from Ezzeri Esa (savarin/lean-operator-theory; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Crouzeix-Palencia theorem, von Neumann inequality, and unitary power dilation development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/ScalarCompanionPlemelj.lean

import Definitions.Def_Operator_Crouzeix_ScalarCompanionBoundary
import Mathlib.Algebra.Polynomial.FieldDivision
set_option autoImplicit false
open Complex Filter MeasureTheory Set
open scoped Interval Real
noncomputable def crouzeixScalarCauchyKernel
    (Omega : SmoothJordanDomain) (z : ℂ) : ℂ :=
  (2 * (Real.pi : ℂ) * I)⁻¹ *
    contourIntegral (fun sigma ↦ (sigma - z)⁻¹) Omega.boundaryParam
noncomputable def crouzeixPolynomialScalarCompanionRegularized
    (Omega : SmoothJordanDomain) (p : Polynomial ℂ) (xi z : ℂ) : ℂ :=
  (2 * (Real.pi : ℂ) * I)⁻¹ *
    contourIntegral
      (fun sigma ↦
        (star (Polynomial.eval sigma p) - star (Polynomial.eval xi p)) *
          (sigma - z)⁻¹)
      Omega.boundaryParam
noncomputable def crouzeixPolynomialScalarCompanionBoundaryValue
    (Omega : SmoothJordanDomain) (p : Polynomial ℂ) (xi : ℂ) : ℂ :=
  star (Polynomial.eval xi p) +
    crouzeixPolynomialScalarCompanionRegularized Omega p xi xi


