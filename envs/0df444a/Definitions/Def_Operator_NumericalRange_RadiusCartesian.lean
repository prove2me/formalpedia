-- Prove2me | Definitions.Def_Operator_NumericalRange_RadiusCartesian
-- name    : Operator_NumericalRange_RadiusCartesian
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T13:23:51.572629+00:00
-- url     : https://prove2.me/theorems/063dc50f-1afc-4191-a1b3-405eeb42ea75
-- title:
--   Radius Cartesian
-- statement:
--   Definitions and structural lemmas for Radius Cartesian, from Ezzeri Esa (savarin/lean-operator-theory; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Crouzeix-Palencia theorem, von Neumann inequality, and unitary power dilation development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/NumericalRange/RadiusCartesian.lean

import Definitions.Def_Operator_NumericalRange_RadiusAdjoint
import Definitions.Def_Operator_NumericalRange_RadiusNormal
set_option autoImplicit false
open Complex ContinuousLinearMap
open scoped InnerProductSpace InnerProduct
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]


