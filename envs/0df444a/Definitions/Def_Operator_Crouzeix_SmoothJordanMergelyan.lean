-- Prove2me | Definitions.Def_Operator_Crouzeix_SmoothJordanMergelyan
-- name    : Operator_Crouzeix_SmoothJordanMergelyan
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T13:51:21.142736+00:00
-- url     : https://prove2.me/theorems/da3821ae-4d96-4b55-8583-ad5f17bee5e9
-- title:
--   Smooth Jordan Mergelyan
-- statement:
--   Definitions and structural lemmas for Smooth Jordan Mergelyan, from Ezzeri Esa (savarin/lean-operator-theory; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Crouzeix-Palencia theorem, von Neumann inequality, and unitary power dilation development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/SmoothJordanMergelyan.lean

import Definitions.Def_Operator_Crouzeix_ConvexRungeIntegral
import Definitions.Def_Operator_Crouzeix_SmoothJordanCauchyFormula
import Definitions.Def_Operator_Crouzeix_SmoothJordanExhaustion
import Mathlib.Topology.UniformSpace.UniformConvergenceTopology
set_option autoImplicit false
open Complex Filter Metric Set
open scoped Interval Real Topology
noncomputable def smoothJordanRadialPoint (c z : ℂ) (r : ℝ) : ℂ :=
  (1 - r) • c + r • z
noncomputable def smoothJordanOutwardPoint (c xi : ℂ) (r : ℝ) : ℂ :=
  c + r⁻¹ • (xi - c)
noncomputable def smoothMergelyanRadialFactor (n : ℕ) : ℝ :=
  ((n : ℝ) + 1) / ((n : ℝ) + 2)


