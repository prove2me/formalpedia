-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_IntegrableMonomialMulConjComplexGaussian
-- name    : Development_AbelianVarietyTheory_Proofs_CovolumeBounds_IntegrableMonomialMulConjComplexGaussian
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T08:50:32.19788+00:00
-- url     : https://prove2.me/theorems/13fcac62-c990-4e61-a5fc-4d803c42a76d
-- title:
--   Integrable Monomial Mul Conj Complex Gaussian
-- statement:
--   Definitions and structural lemmas for Integrable Monomial Mul Conj Complex Gaussian, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/IntegrableMonomialMulConjComplexGaussian.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Set Real
open scoped Nat ComplexConjugate
namespace GlobalTheory
section General
variable (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
noncomputable def complexGaussian (g : ℕ) : Measure E :=
  volume.withDensity fun z => ENNReal.ofReal ((π ^ g)⁻¹ * exp (-‖z‖ ^ 2))
variable {E}
theorem integrable_exp_neg_mul_norm_sq {b : ℝ} (hb : 0 < b) :
    Integrable fun z : E => exp (-b * ‖z‖ ^ 2) := by
  by_contra h
  have h1 := GaussianFourier.integral_rexp_neg_mul_sq_norm (V := E) hb
  rw [integral_undef h] at h1
  exact absurd h1 (by positivity)
theorem integral_exp_neg_mul_norm_sq {g : ℕ} (hE : Module.finrank ℝ E = 2 * g) {b : ℝ}
    (hb : 0 < b) : ∫ z : E, exp (-b * ‖z‖ ^ 2) = (π / b) ^ g := by
  rw [GaussianFourier.integral_rexp_neg_mul_sq_norm hb, hE, ← rpow_natCast]
  congr 1
  push_cast
  ring
theorem isProbabilityMeasure_complexGaussian {g : ℕ} (hE : Module.finrank ℝ E = 2 * g) :
    IsProbabilityMeasure (complexGaussian E g) := by
  constructor
  have h := integral_exp_neg_mul_norm_sq hE one_pos
  have hi := integrable_exp_neg_mul_norm_sq (E := E) one_pos
  simp only [neg_mul, one_mul, div_one] at h hi
  rw [complexGaussian, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    ← ofReal_integral_eq_lintegral_ofReal (hi.const_mul _) (.of_forall fun z => by positivity),
    integral_const_mul, h, inv_mul_cancel₀ (by positivity), ENNReal.ofReal_one]
end General
section Combinatorics
end Combinatorics
section Kernel
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
end Kernel
section Monomials
theorem finrank_real_euclideanSpace_complex (ι : Type*) [Fintype ι] :
    Module.finrank ℝ (EuclideanSpace ℂ ι) = 2 * Fintype.card ι := by
  rw [finrank_real_of_complex, finrank_euclideanSpace]
end Monomials
section Fin
noncomputable abbrev fockMeasure (g : ℕ) : Measure (EuclideanSpace ℂ (Fin g)) :=
  complexGaussian (EuclideanSpace ℂ (Fin g)) g
theorem finrank_real_euclideanSpace_complex_fin (g : ℕ) :
    Module.finrank ℝ (EuclideanSpace ℂ (Fin g)) = 2 * g := by
  rw [finrank_real_euclideanSpace_complex, Fintype.card_fin]
instance (g : ℕ) : IsProbabilityMeasure (fockMeasure g) :=
  isProbabilityMeasure_complexGaussian (finrank_real_euclideanSpace_complex_fin g)
end Fin
end GlobalTheory


