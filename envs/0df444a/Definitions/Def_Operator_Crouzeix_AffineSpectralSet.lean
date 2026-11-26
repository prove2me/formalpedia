-- Prove2me | Definitions.Def_Operator_Crouzeix_AffineSpectralSet
-- name    : Operator_Crouzeix_AffineSpectralSet
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T13:00:40.387118+00:00
-- url     : https://prove2.me/theorems/d894df9c-464f-5755-bef2-5fe7723d20c1
-- title:
--   Affine Spectral Set
-- statement:
--   Definitions and structural lemmas for Affine Spectral Set, from Ezzeri Esa (savarin/lean-operator-theory; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Crouzeix-Palencia theorem, von Neumann inequality, and unitary power dilation development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/AffineSpectralSet.lean

import Definitions.Def_Operator_Crouzeix_AffinePolynomial
set_option autoImplicit false
open Set
open scoped InnerProductSpace Pointwise Polynomial
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]


