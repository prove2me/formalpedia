-- Prove2me | Definitions.Def_Operator_NumericalRange_RadiusSpectrum
-- name    : Operator_NumericalRange_RadiusSpectrum
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T13:16:46.538202+00:00
-- url     : https://prove2.me/theorems/8b6de7dc-ff16-4085-9dd2-1b1635e109e1
-- title:
--   Radius Spectrum
-- statement:
--   Definitions and structural lemmas for Radius Spectrum, from Ezzeri Esa (savarin/lean-operator-theory; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Crouzeix-Palencia theorem, von Neumann inequality, and unitary power dilation development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/NumericalRange/RadiusSpectrum.lean

import Mathlib.Analysis.Normed.Algebra.Spectrum
import Definitions.Def_Operator_NumericalRange_Affine
import Definitions.Def_Operator_NumericalRange_Radius
import Definitions.Def_Operator_SpectralSet_SpectrumInNR
set_option autoImplicit false
open Set
open scoped ENNReal InnerProductSpace NNReal
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
variable [CompleteSpace E]


