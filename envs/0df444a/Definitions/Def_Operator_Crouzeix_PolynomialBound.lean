-- Prove2me | Definitions.Def_Operator_Crouzeix_PolynomialBound
-- name    : Operator_Crouzeix_PolynomialBound
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T14:42:33.064697+00:00
-- url     : https://prove2.me/theorems/ec90cb23-2bf8-52d0-9f87-a8bc4333c5fc
-- title:
--   Polynomial Bound
-- statement:
--   Definitions and structural lemmas for Polynomial Bound, from Ezzeri Esa (savarin/lean-operator-theory; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Crouzeix-Palencia theorem, von Neumann inequality, and unitary power dilation development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/PolynomialBound.lean

import Mathlib.Analysis.SpecificLimits.Normed
import Definitions.Def_Operator_Crouzeix_BoundaryMaximum
import Definitions.Def_Operator_Crouzeix_SmoothSupportDomain
set_option autoImplicit false
open Complex Set
open scoped InnerProductSpace Polynomial
universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
variable [CompleteSpace E]


