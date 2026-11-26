-- Prove2me | Definitions.Def_Operator_Crouzeix_ScalarCompanionBoundaryMeasureMass
-- name    : Operator_Crouzeix_ScalarCompanionBoundaryMeasureMass
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T13:07:56.423843+00:00
-- url     : https://prove2.me/theorems/67569cce-e6a4-402e-8104-a7209f342568
-- title:
--   Scalar Companion Boundary Measure Mass
-- statement:
--   Definitions and structural lemmas for Scalar Companion Boundary Measure Mass, from Ezzeri Esa (savarin/lean-operator-theory; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Crouzeix-Palencia theorem, von Neumann inequality, and unitary power dilation development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/ScalarCompanionBoundaryMeasureMass.lean

import Definitions.Def_Operator_Crouzeix_ScalarCompanionBoundaryMeasure
import Definitions.Def_Operator_Crouzeix_SmoothJordanSupport
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.DerivIntegrable
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
set_option autoImplicit false
open Complex Filter MeasureTheory Set
open scoped Interval Real


