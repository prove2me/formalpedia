-- Prove2me | Definitions.Def_Operator_Crouzeix_ConvexRungeFinite
-- name    : Operator_Crouzeix_ConvexRungeFinite
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T12:29:44.811571+00:00
-- url     : https://prove2.me/theorems/f7e7ba36-2df9-4bcb-9b4a-89081ba57601
-- title:
--   Convex Runge Finite
-- statement:
--   Definitions and structural lemmas for Convex Runge Finite, from Ezzeri Esa (savarin/lean-operator-theory; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Crouzeix-Palencia theorem, von Neumann inequality, and unitary power dilation development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/ConvexRungeFinite.lean

import Definitions.Def_Operator_Crouzeix_ConvexRunge
import Mathlib.Topology.Algebra.IsUniformGroup.Basic
set_option autoImplicit false
open Complex Filter Set
open scoped Topology


