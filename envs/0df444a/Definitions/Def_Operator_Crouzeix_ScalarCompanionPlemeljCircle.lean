-- Prove2me | Definitions.Def_Operator_Crouzeix_ScalarCompanionPlemeljCircle
-- name    : Operator_Crouzeix_ScalarCompanionPlemeljCircle
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T13:13:26.97051+00:00
-- url     : https://prove2.me/theorems/9459c4e6-3933-57f6-8032-c9e2de9ee66a
-- title:
--   Scalar Companion Plemelj Circle
-- statement:
--   Definitions and structural lemmas for Scalar Companion Plemelj Circle, from Ezzeri Esa (savarin/lean-operator-theory; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Crouzeix-Palencia theorem, von Neumann inequality, and unitary power dilation development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/ScalarCompanionPlemeljCircle.lean

import Definitions.Def_Operator_Crouzeix_PalenciaSupport
import Definitions.Def_Operator_Crouzeix_ProductBase
import Definitions.Def_Operator_Crouzeix_ScalarCompanionCircle
import Definitions.Def_Operator_Crouzeix_ScalarCompanionPlemelj
set_option autoImplicit false
open Complex ComplexConjugate Filter Polynomial Set
open scoped Interval Real
section AuxiliaryOperator
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]
end AuxiliaryOperator


