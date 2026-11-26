-- Prove2me | Definitions.Def_Operator_Crouzeix_ScalarCompanionRadialAssembly
-- name    : Operator_Crouzeix_ScalarCompanionRadialAssembly
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T13:08:44.803121+00:00
-- url     : https://prove2.me/theorems/683ffe55-dfd7-5f86-aa2e-7841d76b0e7b
-- title:
--   Scalar Companion Radial Assembly
-- statement:
--   Definitions and structural lemmas for Scalar Companion Radial Assembly, from Ezzeri Esa (savarin/lean-operator-theory; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Crouzeix-Palencia theorem, von Neumann inequality, and unitary power dilation development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/ScalarCompanionRadialAssembly.lean

import Definitions.Def_Operator_Crouzeix_ScalarCompanionAssembly
import Definitions.Def_Operator_Crouzeix_ScalarCompanionPhaseInduction
import Definitions.Def_Operator_Crouzeix_ScalarCompanionRadial
set_option autoImplicit false
open Complex Filter Set
open scoped InnerProductSpace Interval Real
universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]


