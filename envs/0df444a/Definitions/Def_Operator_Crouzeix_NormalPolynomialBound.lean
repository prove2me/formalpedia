-- Prove2me | Definitions.Def_Operator_Crouzeix_NormalPolynomialBound
-- name    : Operator_Crouzeix_NormalPolynomialBound
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T14:43:12.513819+00:00
-- url     : https://prove2.me/theorems/d0861d55-5365-5e90-8acb-1f11961f7215
-- title:
--   Normal Polynomial Bound
-- statement:
--   Definitions and structural lemmas for Normal Polynomial Bound, from Ezzeri Esa (savarin/lean-operator-theory; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Crouzeix-Palencia theorem, von Neumann inequality, and unitary power dilation development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/NormalPolynomialBound.lean

import Definitions.Def_Operator_Crouzeix_PolynomialBound
import Definitions.Def_Operator_NumericalRange_RadiusNormal
import Definitions.Def_Operator_SpectralSet_Normal
set_option autoImplicit false
open Complex Set
open scoped InnerProductSpace Polynomial
universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]


