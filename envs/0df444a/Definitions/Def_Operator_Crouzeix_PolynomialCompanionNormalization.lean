-- Prove2me | Definitions.Def_Operator_Crouzeix_PolynomialCompanionNormalization
-- name    : Operator_Crouzeix_PolynomialCompanionNormalization
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T12:49:17.87181+00:00
-- url     : https://prove2.me/theorems/882fde80-3bb0-40d9-8044-3d110e3c89e0
-- title:
--   Polynomial Companion Normalization
-- statement:
--   Definitions and structural lemmas for Polynomial Companion Normalization, from Ezzeri Esa (savarin/lean-operator-theory; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Crouzeix-Palencia theorem, von Neumann inequality, and unitary power dilation development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/PolynomialCompanionNormalization.lean

import Definitions.Def_Operator_Crouzeix_PolynomialSupNormZero
set_option autoImplicit false
open Filter
universe u
variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℂ E]


