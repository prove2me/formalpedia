-- Prove2me | Definitions.Def_Operator_Crouzeix_ProductSymmetrizedAlignment
-- name    : Operator_Crouzeix_ProductSymmetrizedAlignment
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T13:15:46.68398+00:00
-- url     : https://prove2.me/theorems/8bdda919-bb03-49a8-ac9a-f6a926f76665
-- title:
--   Product Symmetrized Alignment
-- statement:
--   Definitions and structural lemmas for Product Symmetrized Alignment, from Ezzeri Esa (savarin/lean-operator-theory; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Crouzeix-Palencia theorem, von Neumann inequality, and unitary power dilation development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/ProductSymmetrizedAlignment.lean

import Definitions.Def_Operator_Crouzeix_NormalProduct
set_option autoImplicit false
open Complex Polynomial Set
open scoped InnerProductSpace
universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E] [Nontrivial E]


