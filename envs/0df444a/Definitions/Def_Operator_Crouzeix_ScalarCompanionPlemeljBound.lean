-- Prove2me | Definitions.Def_Operator_Crouzeix_ScalarCompanionPlemeljBound
-- name    : Operator_Crouzeix_ScalarCompanionPlemeljBound
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T12:54:56.800847+00:00
-- url     : https://prove2.me/theorems/5780a6a6-1eec-42e8-98ba-d82f5c60ec37
-- title:
--   Scalar Companion Plemelj Bound
-- statement:
--   Definitions and structural lemmas for Scalar Companion Plemelj Bound, from Ezzeri Esa (savarin/lean-operator-theory; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Crouzeix-Palencia theorem, von Neumann inequality, and unitary power dilation development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/ScalarCompanionPlemeljBound.lean

import Definitions.Def_Operator_Crouzeix_ProductBase
import Definitions.Def_Operator_Crouzeix_ScalarCompanionDecay
import Definitions.Def_Operator_Crouzeix_ScalarCompanionPlemelj
set_option autoImplicit false
open Complex Set
open scoped Interval Real
noncomputable def crouzeixPolynomialBoundaryPhaseTransform
    (Omega : SmoothJordanDomain) (xi : ℂ) (q : Polynomial ℂ) : ℂ :=
  (2 * (Real.pi : ℂ) * I)⁻¹ *
    contourIntegral
      (fun sigma ↦
        star (sigma - xi) * star (Polynomial.eval sigma q) *
          (sigma - xi)⁻¹)
      Omega.boundaryParam


