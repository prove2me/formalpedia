-- Prove2me | Definitions.Def_Operator_Crouzeix_PolynomialCauchyFromResolventMass
-- name    : Operator_Crouzeix_PolynomialCauchyFromResolventMass
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T12:48:16.655324+00:00
-- url     : https://prove2.me/theorems/b2d151a9-16d6-54cd-9dc0-65d1ee4763d2
-- title:
--   Polynomial Cauchy From Resolvent Mass
-- statement:
--   Definitions and structural lemmas for Polynomial Cauchy From Resolvent Mass, from Ezzeri Esa (savarin/lean-operator-theory; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Crouzeix-Palencia theorem, von Neumann inequality, and unitary power dilation development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/PolynomialCauchyFromResolventMass.lean

import Definitions.Def_Operator_Crouzeix_ProductContour
set_option autoImplicit false
open Complex Polynomial Set
open scoped InnerProductSpace Interval Real
universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]


