-- Prove2me | Definitions.Def_Operator_Crouzeix_ConvexRungeIntegral
-- name    : Operator_Crouzeix_ConvexRungeIntegral
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T12:30:49.34479+00:00
-- url     : https://prove2.me/theorems/5f0b0332-2776-4b62-9d7a-3cb3269db404
-- title:
--   Convex Runge Integral
-- statement:
--   Definitions and structural lemmas for Convex Runge Integral, from Ezzeri Esa (savarin/lean-operator-theory; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Crouzeix-Palencia theorem, von Neumann inequality, and unitary power dilation development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/ConvexRungeIntegral.lean

import Definitions.Def_Operator_Crouzeix_ConvexRungeClosure
import Mathlib.Analysis.Convex.Integral
import Mathlib.Analysis.Convex.Combination
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Topology.Sequences
import Mathlib.Topology.Sets.Compacts
set_option autoImplicit false
open Complex Filter MeasureTheory Set
open scoped Topology Interval


