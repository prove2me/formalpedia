-- Prove2me | Definitions.Def_Operator_Crouzeix_ScalarCompanionBoundary
-- name    : Operator_Crouzeix_ScalarCompanionBoundary
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T12:35:22.600518+00:00
-- url     : https://prove2.me/theorems/68f2b4f4-fe02-5d9f-9d0e-6dc4a75866dd
-- title:
--   Scalar Companion Boundary
-- statement:
--   Definitions and structural lemmas for Scalar Companion Boundary, from Ezzeri Esa (savarin/lean-operator-theory; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Crouzeix-Palencia theorem, von Neumann inequality, and unitary power dilation development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/ScalarCompanionBoundary.lean

import Definitions.Def_Operator_Crouzeix_ScalarCompanion
import Mathlib.Analysis.Complex.AbsMax
import Mathlib.Topology.ExtendFrom
set_option autoImplicit false
open Complex Filter Set
noncomputable def crouzeixPolynomialScalarCompanionClosedExtension
    (Omega : SmoothJordanDomain) (p : Polynomial ℂ) : ℂ → ℂ :=
  extendFrom Omega.carrier (crouzeixPolynomialScalarCompanion Omega p)


