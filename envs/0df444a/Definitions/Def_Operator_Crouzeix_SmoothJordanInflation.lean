-- Prove2me | Definitions.Def_Operator_Crouzeix_SmoothJordanInflation
-- name    : Operator_Crouzeix_SmoothJordanInflation
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T13:54:10.94648+00:00
-- url     : https://prove2.me/theorems/f6a88942-f195-477f-94a0-3c01eac19a0b
-- title:
--   Smooth Jordan Inflation
-- statement:
--   Definitions and structural lemmas for Smooth Jordan Inflation, from Ezzeri Esa (savarin/lean-operator-theory; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Crouzeix-Palencia theorem, von Neumann inequality, and unitary power dilation development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/SmoothJordanInflation.lean

import Definitions.Def_Operator_Crouzeix_ScalarCompanionBoundaryMeasureAffine
import Definitions.Def_Operator_Crouzeix_SmoothJordanCompact
import Definitions.Def_Operator_Crouzeix_SmoothJordanOuterApproximation
set_option autoImplicit false
open Complex Metric Set
universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]


