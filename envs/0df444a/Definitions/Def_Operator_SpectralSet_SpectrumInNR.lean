-- Prove2me | Definitions.Def_Operator_SpectralSet_SpectrumInNR
-- name    : Operator_SpectralSet_SpectrumInNR
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T12:32:24.034532+00:00
-- url     : https://prove2.me/theorems/612ee08e-ca83-4842-bd9f-e4478b9d73c6
-- title:
--   Spectrum In NR
-- statement:
--   Definitions and structural lemmas for Spectrum In NR, from Ezzeri Esa (savarin/lean-operator-theory; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Crouzeix-Palencia theorem, von Neumann inequality, and unitary power dilation development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/SpectralSet/SpectrumInNR.lean

import Mathlib.Algebra.Algebra.Spectrum.Basic
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Projection.Submodule
import Mathlib.Analysis.Normed.Operator.Banach
import Definitions.Def_Operator_NumericalRange_Helpers
set_option autoImplicit false
open scoped InnerProductSpace
open ContinuousLinearMap
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
variable [CompleteSpace E]


