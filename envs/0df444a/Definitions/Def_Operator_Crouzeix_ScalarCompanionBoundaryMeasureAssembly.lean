-- Prove2me | Definitions.Def_Operator_Crouzeix_ScalarCompanionBoundaryMeasureAssembly
-- name    : Operator_Crouzeix_ScalarCompanionBoundaryMeasureAssembly
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T13:18:26.812104+00:00
-- url     : https://prove2.me/theorems/61dff0ab-18bf-4642-88e0-99810408344c
-- title:
--   Scalar Companion Boundary Measure Assembly
-- statement:
--   Definitions and structural lemmas for Scalar Companion Boundary Measure Assembly, from Ezzeri Esa (savarin/lean-operator-theory; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Crouzeix-Palencia theorem, von Neumann inequality, and unitary power dilation development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/ScalarCompanionBoundaryMeasureAssembly.lean

import Definitions.Def_Operator_Crouzeix_PolynomialCauchyFromResolventMass
import Definitions.Def_Operator_Crouzeix_ResolventContourHomotopy
import Definitions.Def_Operator_Crouzeix_ScalarCompanionBoundaryMeasureMass
import Definitions.Def_Operator_Crouzeix_ScalarCompanionRadialAssembly
set_option autoImplicit false
open Complex MeasureTheory Set
open scoped InnerProductSpace Interval Real
universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]


