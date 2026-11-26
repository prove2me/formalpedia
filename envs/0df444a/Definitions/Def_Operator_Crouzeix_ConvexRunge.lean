-- Prove2me | Definitions.Def_Operator_Crouzeix_ConvexRunge
-- name    : Operator_Crouzeix_ConvexRunge
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T12:29:23.851701+00:00
-- url     : https://prove2.me/theorems/2298339d-47e1-4114-9fc4-a3a36fb771ad
-- title:
--   Convex Runge
-- statement:
--   Definitions and structural lemmas for Convex Runge, from Ezzeri Esa (savarin/lean-operator-theory; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Crouzeix-Palencia theorem, von Neumann inequality, and unitary power dilation development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/ConvexRunge.lean

import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Topology.UniformSpace.UniformConvergence
set_option autoImplicit false
open Complex Filter Metric Set
open scoped Topology


