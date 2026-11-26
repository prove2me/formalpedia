-- Prove2me | Definitions.Def_Operator_NumericalRange_RadiusAdjoint
-- name    : Operator_NumericalRange_RadiusAdjoint
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T13:20:43.149162+00:00
-- url     : https://prove2.me/theorems/8420eaae-df2b-49ba-93ee-3874c433c0b6
-- title:
--   Radius Adjoint
-- statement:
--   Definitions and structural lemmas for Radius Adjoint, from Ezzeri Esa (savarin/lean-operator-theory; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Crouzeix-Palencia theorem, von Neumann inequality, and unitary power dilation development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/NumericalRange/RadiusAdjoint.lean

import Definitions.Def_Operator_NumericalRange_Adjoint
import Definitions.Def_Operator_NumericalRange_Radius
set_option autoImplicit false
open Complex
open ContinuousLinearMap
open scoped InnerProductSpace InnerProduct
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]


