-- Prove2me | Definitions.Def_Operator_Crouzeix_CircleProduct
-- name    : Operator_Crouzeix_CircleProduct
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T12:59:00.188229+00:00
-- url     : https://prove2.me/theorems/03b84abb-c949-4e31-bc02-625b2dabbabc
-- title:
--   Circle Product
-- statement:
--   Definitions and structural lemmas for Circle Product, from Ezzeri Esa (savarin/lean-operator-theory; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Crouzeix-Palencia theorem, von Neumann inequality, and unitary power dilation development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/CircleProduct.lean

import Definitions.Def_Operator_Crouzeix_AffinePolynomial
import Definitions.Def_Operator_Crouzeix_CircleAuxiliary
import Definitions.Def_Operator_Crouzeix_VonNeumann
import Mathlib.Analysis.Normed.Module.Ball.Pointwise
set_option autoImplicit false
open Complex Polynomial Set
open scoped InnerProductSpace Pointwise
universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]


