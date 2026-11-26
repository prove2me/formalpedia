-- Prove2me | Definitions.Def_Operator_Crouzeix_SmoothJordanCauchy
-- name    : Operator_Crouzeix_SmoothJordanCauchy
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T12:34:34.563541+00:00
-- url     : https://prove2.me/theorems/0d21bd5e-21d9-42d1-9649-aa6987bd17e2
-- title:
--   Smooth Jordan Cauchy
-- statement:
--   Definitions and structural lemmas for Smooth Jordan Cauchy, from Ezzeri Esa (savarin/lean-operator-theory; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Crouzeix-Palencia theorem, von Neumann inequality, and unitary power dilation development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/SmoothJordanCauchy.lean

import Definitions.Def_Operator_Crouzeix_ContourIntegral
import Definitions.Def_Operator_Crouzeix_SmoothJordanSupport
import Mathlib.MeasureTheory.Integral.CurveIntegral.Poincare
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Topology.Sets.Compacts
import Mathlib.Analysis.SpecificLimits.Basic
set_option autoImplicit false
open Complex Filter MeasureTheory Set
open scoped Interval Topology


