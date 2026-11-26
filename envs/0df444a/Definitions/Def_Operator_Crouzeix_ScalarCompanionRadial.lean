-- Prove2me | Definitions.Def_Operator_Crouzeix_ScalarCompanionRadial
-- name    : Operator_Crouzeix_ScalarCompanionRadial
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T13:05:39.920825+00:00
-- url     : https://prove2.me/theorems/df498e35-2aff-4639-8d68-2dd97b43214d
-- title:
--   Scalar Companion Radial
-- statement:
--   Definitions and structural lemmas for Scalar Companion Radial, from Ezzeri Esa (savarin/lean-operator-theory; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Crouzeix-Palencia theorem, von Neumann inequality, and unitary power dilation development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/ScalarCompanionRadial.lean

import Definitions.Def_Operator_Crouzeix_ScalarCompanionPlemeljBound
import Definitions.Def_Operator_Crouzeix_ScalarCompanionDecay
import Mathlib.Analysis.Convex.Topology
set_option autoImplicit false
open Complex Filter MeasureTheory Set
open scoped Interval Real
noncomputable def smoothJordanInwardPoint (c xi : ℂ) (r : ℝ) : ℂ :=
  (1 - r) • xi + r • c


