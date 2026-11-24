-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PIntNumBaseChange
-- name    : GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PIntNumBaseChange
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T23:27:46.263029+00:00
-- url     : https://prove2.me/theorems/4322ac10-bd40-431f-ab65-a3c18fce7dee
-- title:
--   PInt Num Base Change
-- statement:
--   Definitions and structural lemmas for PInt Num Base Change, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/PIntNumBaseChange.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PGradedFinite
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights.FieldNumbers
open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR
noncomputable section
section Descent
variable {σ : Type*} {F : Type*} [Field F] {F' : Type*} [Field F'] [Algebra F F']
def coeffFormFun (φ : F' →ₗ[F] F) (f : MvPolynomial σ F') : MvPolynomial σ F :=
  ∑ μ ∈ f.support, monomial μ (φ (coeff μ f))
theorem coeff_coeffFormFun (φ : F' →ₗ[F] F) (f : MvPolynomial σ F') (ν : σ →₀ ℕ) :
    coeff ν (coeffFormFun φ f) = φ (coeff ν f) := by
  classical
  simp only [coeffFormFun, coeff_sum, coeff_monomial, Finset.sum_ite_eq']
  split_ifs with h
  · rfl
  · rw [MvPolynomial.notMem_support_iff.mp h, map_zero]
def coeffForm (φ : F' →ₗ[F] F) : MvPolynomial σ F' →+ MvPolynomial σ F where
  toFun := coeffFormFun φ
  map_zero' := by ext ν; simp [coeff_coeffFormFun]
  map_add' f g := by ext ν; simp [coeff_coeffFormFun]
variable {K : Type*} {ι : K → Type*}
end Descent
section Hilbert
variable {K : Type*} [Fintype K] [DecidableEq K] {ι : K → Type*} [∀ k, Fintype (ι k)]
variable {F : Type*} [Field F] {F' : Type*} [Field F'] [Algebra F F']
end Hilbert
section Transcendental
variable {σ : Type*} {F : Type*} [Field F]
end Transcendental
end
end GroundTheory.Heights₂.Heights.FieldNumbers


