-- Prove2me | Definitions.Def_Operator_NumericalRange_RadiusNormal
-- name    : Operator_NumericalRange_RadiusNormal
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T13:17:26.279682+00:00
-- url     : https://prove2.me/theorems/409b4ce5-afa0-563b-9e54-0931e76c32b2
-- title:
--   Radius Normal
-- statement:
--   Definitions and structural lemmas for Radius Normal, from Ezzeri Esa (savarin/lean-operator-theory; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Crouzeix-Palencia theorem, von Neumann inequality, and unitary power dilation development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/NumericalRange/RadiusNormal.lean

import Mathlib.Analysis.CStarAlgebra.Spectrum
import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
import Definitions.Def_Operator_NumericalRange_RadiusSpectrum
set_option autoImplicit false
open scoped InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]


