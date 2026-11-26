-- Prove2me | Definitions.Def_Operator_Crouzeix_CircleAuxiliary
-- name    : Operator_Crouzeix_CircleAuxiliary
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T12:53:45.641807+00:00
-- url     : https://prove2.me/theorems/8be833e1-0e56-5121-91d5-e5cf894b8b39
-- title:
--   Circle Auxiliary
-- statement:
--   Definitions and structural lemmas for Circle Auxiliary, from Ezzeri Esa (savarin/lean-operator-theory; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Crouzeix-Palencia theorem, von Neumann inequality, and unitary power dilation development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/CircleAuxiliary.lean

import Definitions.Def_Operator_Crouzeix_AuxOperator
import Definitions.Def_Operator_Crouzeix_CircleCauchy
set_option autoImplicit false
open Complex ComplexConjugate Polynomial Set
open scoped InnerProductSpace Interval Real
universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]


