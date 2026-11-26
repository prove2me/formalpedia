-- Prove2me | Definitions.Def_Operator_Crouzeix_PolynomialCompanionConvergence
-- name    : Operator_Crouzeix_PolynomialCompanionConvergence
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T12:45:43.49348+00:00
-- url     : https://prove2.me/theorems/4f732c10-a1b8-58af-8a6c-8947169b29d5
-- title:
--   Polynomial Companion Convergence
-- statement:
--   Definitions and structural lemmas for Polynomial Companion Convergence, from Ezzeri Esa (savarin/lean-operator-theory; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Crouzeix-Palencia theorem, von Neumann inequality, and unitary power dilation development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/PolynomialCompanionConvergence.lean

import Definitions.Def_Operator_Crouzeix_AuxOperator
set_option autoImplicit false
open Complex Filter MeasureTheory Set
open scoped InnerProductSpace Interval Real
universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]


