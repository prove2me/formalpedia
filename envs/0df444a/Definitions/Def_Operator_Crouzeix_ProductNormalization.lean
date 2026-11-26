-- Prove2me | Definitions.Def_Operator_Crouzeix_ProductNormalization
-- name    : Operator_Crouzeix_ProductNormalization
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T13:22:52.265801+00:00
-- url     : https://prove2.me/theorems/be62a63a-ca06-591e-bc7b-6b091c3b22d0
-- title:
--   Product Normalization
-- statement:
--   Definitions and structural lemmas for Product Normalization, from Ezzeri Esa (savarin/lean-operator-theory; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Crouzeix-Palencia theorem, von Neumann inequality, and unitary power dilation development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/ProductNormalization.lean

import Definitions.Def_Operator_Crouzeix_PolynomialSupNormZero
set_option autoImplicit false
open scoped InnerProductSpace
universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E]


