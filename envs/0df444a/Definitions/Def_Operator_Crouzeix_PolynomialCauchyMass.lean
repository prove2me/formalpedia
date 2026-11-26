-- Prove2me | Definitions.Def_Operator_Crouzeix_PolynomialCauchyMass
-- name    : Operator_Crouzeix_PolynomialCauchyMass
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T12:45:20.702831+00:00
-- url     : https://prove2.me/theorems/d0c5ba3f-81d7-4784-b375-64f18ce8e313
-- title:
--   Polynomial Cauchy Mass
-- statement:
--   Definitions and structural lemmas for Polynomial Cauchy Mass, from Ezzeri Esa (savarin/lean-operator-theory; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Crouzeix-Palencia theorem, von Neumann inequality, and unitary power dilation development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/PolynomialCauchyMass.lean

import Definitions.Def_Operator_Crouzeix_AuxOperator
set_option autoImplicit false
open Complex
open scoped InnerProductSpace
universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E]


