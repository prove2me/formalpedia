-- Prove2me | Definitions.Def_Operator_Crouzeix_SymmetrizedAuxiliary
-- name    : Operator_Crouzeix_SymmetrizedAuxiliary
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T12:43:36.327796+00:00
-- url     : https://prove2.me/theorems/edf24677-f482-558c-8e89-2dfc1710865e
-- title:
--   Symmetrized Auxiliary
-- statement:
--   Definitions and structural lemmas for Symmetrized Auxiliary, from Ezzeri Esa (savarin/lean-operator-theory; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Crouzeix-Palencia theorem, von Neumann inequality, and unitary power dilation development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/SymmetrizedAuxiliary.lean

import Definitions.Def_Operator_Crouzeix_AdjointIntegral
import Definitions.Def_Operator_Crouzeix_AuxOperator
set_option autoImplicit false
open Complex MeasureTheory Set
open scoped InnerProductSpace Interval Real
universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]


