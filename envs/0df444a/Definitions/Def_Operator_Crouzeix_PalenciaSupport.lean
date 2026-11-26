-- Prove2me | Definitions.Def_Operator_Crouzeix_PalenciaSupport
-- name    : Operator_Crouzeix_PalenciaSupport
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T12:36:54.486303+00:00
-- url     : https://prove2.me/theorems/9cb41c42-34e9-4616-8386-c31d15e16a6a
-- title:
--   Palencia Support
-- statement:
--   Definitions and structural lemmas for Palencia Support, from Ezzeri Esa (savarin/lean-operator-theory; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Crouzeix-Palencia theorem, von Neumann inequality, and unitary power dilation development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/PalenciaSupport.lean

import Definitions.Def_Operator_Crouzeix_AuxOperator
import Definitions.Def_Operator_SpectralSet_Basic
import Mathlib.Algebra.Algebra.Spectrum.Basic
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Normed.Operator.Basic
set_option autoImplicit false
open Polynomial
universe u
variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℂ E]
section AuxiliaryContour
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]
end AuxiliaryContour
section AuxiliaryHomogeneity
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
variable [CompleteSpace H]
end AuxiliaryHomogeneity


