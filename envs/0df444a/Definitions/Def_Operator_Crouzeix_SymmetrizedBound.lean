-- Prove2me | Definitions.Def_Operator_Crouzeix_SymmetrizedBound
-- name    : Operator_Crouzeix_SymmetrizedBound
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T12:44:12.819223+00:00
-- url     : https://prove2.me/theorems/7798d1cf-90bf-4aa0-a8ae-1b7ae64769ea
-- title:
--   Symmetrized Bound
-- statement:
--   Definitions and structural lemmas for Symmetrized Bound, from Ezzeri Esa (savarin/lean-operator-theory; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Crouzeix-Palencia theorem, von Neumann inequality, and unitary power dilation development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/SymmetrizedBound.lean

import Definitions.Def_Operator_Crouzeix_DoubleLayerBound
set_option autoImplicit false
open MeasureTheory
open scoped InnerProductSpace Interval Real
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]


