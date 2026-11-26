-- Prove2me | Definitions.Def_Operator_Crouzeix_AffineAuxiliary
-- name    : Operator_Crouzeix_AffineAuxiliary
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T12:55:58.835949+00:00
-- url     : https://prove2.me/theorems/ee2287d9-1cc5-418e-8b79-5d8effa36ee3
-- title:
--   Affine Auxiliary
-- statement:
--   Definitions and structural lemmas for Affine Auxiliary, from Ezzeri Esa (savarin/lean-operator-theory; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Crouzeix-Palencia theorem, von Neumann inequality, and unitary power dilation development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/AffineAuxiliary.lean

import Definitions.Def_Operator_Crouzeix_AffinePolynomial
import Definitions.Def_Operator_Crouzeix_AuxOperator
import Definitions.Def_Operator_Crouzeix_CircleAuxiliary
import Definitions.Def_Operator_Crouzeix_CircleCauchy
set_option autoImplicit false
open Complex MeasureTheory
open scoped InnerProductSpace Interval Real
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
variable [CompleteSpace E]


