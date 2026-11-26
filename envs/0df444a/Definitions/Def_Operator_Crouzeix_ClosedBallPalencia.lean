-- Prove2me | Definitions.Def_Operator_Crouzeix_ClosedBallPalencia
-- name    : Operator_Crouzeix_ClosedBallPalencia
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T13:55:54.675688+00:00
-- url     : https://prove2.me/theorems/ecdc567f-5bd8-4fa1-b866-4340c37526ed
-- title:
--   Closed Ball Palencia
-- statement:
--   Definitions and structural lemmas for Closed Ball Palencia, from Ezzeri Esa (savarin/lean-operator-theory; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Crouzeix-Palencia theorem, von Neumann inequality, and unitary power dilation development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/ClosedBallPalencia.lean

import Definitions.Def_Operator_Crouzeix_SmoothJordanExhaustion
import Definitions.Def_Operator_Crouzeix_ScalarCompanionPlemeljCircle
set_option autoImplicit false
open Complex Filter MeasureTheory Metric Set
open scoped InnerProductSpace Interval Real
universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]


