-- Prove2me | Definitions.Def_Operator_SpectralSet_Basic
-- name    : Operator_SpectralSet_Basic
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T12:29:20.93134+00:00
-- url     : https://prove2.me/theorems/745e3101-d7e0-4d05-8e8b-8b45cc6c6460
-- title:
--   Basic
-- statement:
--   Definitions and structural lemmas for Basic, from Ezzeri Esa (savarin/lean-operator-theory; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Crouzeix-Palencia theorem, von Neumann inequality, and unitary power dilation development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/SpectralSet/Basic.lean

import Mathlib.Algebra.Algebra.Spectrum.Basic
import Mathlib.Analysis.Normed.Algebra.Spectrum
import Mathlib.Analysis.InnerProductSpace.Basic
set_option autoImplicit false
open scoped Polynomial
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
noncomputable def polynomialSupNorm (p : Polynomial ℂ) (X : Set ℂ) : ℝ :=
  ⨆ z ∈ X, ‖Polynomial.eval z p‖
def IsKPolynomialSpectralSet (A : E →L[ℂ] E) (K : ℝ) (X : Set ℂ) : Prop :=
  spectrum ℂ (A : E →L[ℂ] E) ⊆ X ∧
  ∀ p : Polynomial ℂ, ‖Polynomial.aeval A p‖ ≤ K * polynomialSupNorm p X
def IsPolynomialSpectralSet (A : E →L[ℂ] E) (X : Set ℂ) : Prop :=
  IsKPolynomialSpectralSet A 1 X


