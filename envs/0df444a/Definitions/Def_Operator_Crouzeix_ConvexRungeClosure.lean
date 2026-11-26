-- Prove2me | Definitions.Def_Operator_Crouzeix_ConvexRungeClosure
-- name    : Operator_Crouzeix_ConvexRungeClosure
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T12:30:10.955666+00:00
-- url     : https://prove2.me/theorems/73eeefb2-ff77-4d9c-9c56-4c7739037ed0
-- title:
--   Convex Runge Closure
-- statement:
--   Definitions and structural lemmas for Convex Runge Closure, from Ezzeri Esa (savarin/lean-operator-theory; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Crouzeix-Palencia theorem, von Neumann inequality, and unitary power dilation development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/ConvexRungeClosure.lean

import Definitions.Def_Operator_Crouzeix_ConvexRungeFinite
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.UniformSpace.UniformConvergence
set_option autoImplicit false
open Filter Polynomial Set
open scoped Topology


