-- Prove2me | Definitions.Def_Operator_Crouzeix_ScalarCompanionDecay
-- name    : Operator_Crouzeix_ScalarCompanionDecay
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T12:53:35.664328+00:00
-- url     : https://prove2.me/theorems/6d2db24b-f494-4702-8001-59a622cd3624
-- title:
--   Scalar Companion Decay
-- statement:
--   Definitions and structural lemmas for Scalar Companion Decay, from Ezzeri Esa (savarin/lean-operator-theory; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Crouzeix-Palencia theorem, von Neumann inequality, and unitary power dilation development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/ScalarCompanionDecay.lean

import Definitions.Def_Operator_Crouzeix_GeneralSymmetrized
import Definitions.Def_Operator_Crouzeix_ScalarCompanion
set_option autoImplicit false
open Complex Filter Set
open scoped Interval Real


