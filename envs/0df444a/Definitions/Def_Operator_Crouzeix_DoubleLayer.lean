-- Prove2me | Definitions.Def_Operator_Crouzeix_DoubleLayer
-- name    : Operator_Crouzeix_DoubleLayer
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T12:33:17.479652+00:00
-- url     : https://prove2.me/theorems/1b7ef463-6a10-4257-b53e-b805e7ce0391
-- title:
--   Double Layer
-- statement:
--   Definitions and structural lemmas for Double Layer, from Ezzeri Esa (savarin/lean-operator-theory; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Crouzeix-Palencia theorem, von Neumann inequality, and unitary power dilation development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/DoubleLayer.lean

import Mathlib.MeasureTheory.Integral.CircleIntegral
import Mathlib.Analysis.InnerProductSpace.Positive
import Definitions.Def_Operator_NumericalRange_Helpers
set_option autoImplicit false
open Complex
open scoped InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]


