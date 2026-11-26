-- Prove2me | Definitions.Def_Operator_Crouzeix_ScalarCompanionAssembly
-- name    : Operator_Crouzeix_ScalarCompanionAssembly
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T12:55:54.587927+00:00
-- url     : https://prove2.me/theorems/1878ceec-70af-5001-bb7e-7235eb64d5c5
-- title:
--   Scalar Companion Assembly
-- statement:
--   Definitions and structural lemmas for Scalar Companion Assembly, from Ezzeri Esa (savarin/lean-operator-theory; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Crouzeix-Palencia theorem, von Neumann inequality, and unitary power dilation development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/ScalarCompanionAssembly.lean

import Definitions.Def_Operator_Crouzeix_BoundaryApproximation
import Definitions.Def_Operator_Crouzeix_PalenciaSmoothApproximation
import Definitions.Def_Operator_Crouzeix_ScalarCompanionPlemeljBound
set_option autoImplicit false
open Complex Filter Set
open scoped InnerProductSpace Interval Real
universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]


