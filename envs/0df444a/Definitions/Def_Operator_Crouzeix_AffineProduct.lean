-- Prove2me | Definitions.Def_Operator_Crouzeix_AffineProduct
-- name    : Operator_Crouzeix_AffineProduct
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T13:01:49.060537+00:00
-- url     : https://prove2.me/theorems/05c7a81f-5aa0-519a-b14e-b11dff7d9130
-- title:
--   Affine Product
-- statement:
--   Definitions and structural lemmas for Affine Product, from Ezzeri Esa (savarin/lean-operator-theory; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Crouzeix-Palencia theorem, von Neumann inequality, and unitary power dilation development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/AffineProduct.lean

import Definitions.Def_Operator_Crouzeix_AffineAuxiliary
import Definitions.Def_Operator_Crouzeix_AffineDisk
set_option autoImplicit false
open Complex Polynomial Set
open scoped InnerProductSpace
universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]


