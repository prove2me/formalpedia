-- Prove2me | Definitions.Def_Operator_Crouzeix_PolynomialSupNormZero
-- name    : Operator_Crouzeix_PolynomialSupNormZero
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T12:47:14.892639+00:00
-- url     : https://prove2.me/theorems/21992e8e-6554-4286-9a6d-1384ca19ec2b
-- title:
--   Polynomial Sup Norm Zero
-- statement:
--   Definitions and structural lemmas for Polynomial Sup Norm Zero, from Ezzeri Esa (savarin/lean-operator-theory; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Crouzeix-Palencia theorem, von Neumann inequality, and unitary power dilation development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/PolynomialSupNormZero.lean

import Definitions.Def_Operator_Crouzeix_PalenciaSupport
import Definitions.Def_Operator_Crouzeix_VonNeumann
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Topology.DiscreteSubset
set_option autoImplicit false
open Polynomial ContinuousLinearMap
universe u
section AuxiliaryBounds
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]
end AuxiliaryBounds


