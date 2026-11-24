-- Prove2me | Definitions.Def_ReciprocityTheory_GeometryOfNumbers_SphericalMonomials_GaussSt
-- name    : ReciprocityTheory_GeometryOfNumbers_SphericalMonomials_GaussSt
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T01:02:11.725801+00:00
-- url     : https://prove2.me/theorems/bdadddd9-eba6-4c42-aa49-88614a97c52c
-- title:
--   Gauss St
-- statement:
--   Definitions and structural lemmas for Gauss St, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GeometryOfNumbers/SphericalMonomials/GaussSt.lean

import Definitions.Def_ReciprocityTheory_GeometryOfNumbers_SphericalMonomials_MonoNormSq
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace ReciprocityTheory.GeometryOfNumbersTheory
open MeasureTheory
section helpers
open Set Complex
theorem conj_pow_mul_pow_polar (r θ : ℝ) (a b : ℕ) :
    starRingEnd ℂ (((r : ℂ) * Complex.exp (θ * I)) ^ a) * ((r : ℂ) * Complex.exp (θ * I)) ^ b =
      ((r ^ (a + b) : ℝ) : ℂ) * Complex.exp ((((b : ℂ) - a) * I) * θ) := by
  rw [map_pow, map_mul, Complex.conj_ofReal, ← Complex.exp_conj, map_mul, Complex.conj_ofReal,
    Complex.conj_I, mul_pow, mul_pow, ← Complex.exp_nat_mul, ← Complex.exp_nat_mul]
  have : Complex.exp (((b : ℂ) - a) * I * θ) =
      Complex.exp (a * (θ * -I)) * Complex.exp (b * (θ * I)) := by
    rw [← Complex.exp_add]; congr 1; ring
  rw [this]; push_cast; ring
theorem integral_conj_pow_mul_pow_mul_exp_eq_polar (a b : ℕ) (t : ℝ) :
    ∫ z : ℂ, starRingEnd ℂ (z ^ a) * z ^ b * (Real.exp (-(t * ‖z‖ ^ 2)) : ℂ) =
      ((∫ r in Ioi (0 : ℝ), r ^ (a + b + 1) * Real.exp (-(t * r ^ 2)) : ℝ) : ℂ) *
        ∫ θ in Ioo (-Real.pi) Real.pi, Complex.exp ((((b : ℂ) - a) * I) * θ) := by
  rw [← Complex.integral_comp_polarCoord_symm, polarCoord_target]
  have hm : MeasurableSet (Ioi (0 : ℝ) ×ˢ Ioo (-Real.pi) Real.pi) :=
    measurableSet_Ioi.prod measurableSet_Ioo
  rw [setIntegral_congr_fun hm (g := fun p : ℝ × ℝ =>
      ((p.1 ^ (a + b + 1) * Real.exp (-(t * p.1 ^ 2)) : ℝ) : ℂ) *
        Complex.exp ((((b : ℂ) - a) * I) * p.2))]
  · rw [Measure.volume_eq_prod]
    refine (setIntegral_prod_mul (μ := volume) (ν := volume)
      (fun r : ℝ => ((r ^ (a + b + 1) * Real.exp (-(t * r ^ 2)) : ℝ) : ℂ))
      (fun θ : ℝ => Complex.exp ((((b : ℂ) - a) * I) * θ)) _ _).trans ?_
    rw [integral_complex_ofReal]
  · rintro ⟨r, θ⟩ ⟨hr, -⟩
    have hr : 0 < r := hr
    have hw : Complex.polarCoord.symm (r, θ) = (r : ℂ) * Complex.exp (θ * I) := by
      rw [Complex.polarCoord_symm_apply, Complex.exp_mul_I, ← Complex.ofReal_cos,
        ← Complex.ofReal_sin]
    have hn : ‖Complex.polarCoord.symm (r, θ)‖ = r := by
      rw [norm_polarCoord_symm, abs_of_pos hr]
    simp only
    rw [hn, hw, conj_pow_mul_pow_polar, Complex.real_smul]
    push_cast; ring
theorem integral_exp_mul_I_self (a : ℕ) :
    ∫ θ in Ioo (-Real.pi) Real.pi, Complex.exp ((((a : ℂ) - a) * I) * θ) = 2 * Real.pi := by
  simp only [sub_self, zero_mul, Complex.exp_zero]
  rw [setIntegral_const, Real.volume_real_Ioo_of_le (by linarith [Real.pi_pos])]
  simp; ring
theorem integral_Ioi_pow_mul_exp_neg_mul_sq (a : ℕ) {t : ℝ} (ht : 0 < t) :
    ∫ r in Ioi (0 : ℝ), r ^ (a + a + 1) * Real.exp (-(t * r ^ 2)) =
      (a.factorial : ℝ) / (2 * t ^ (a + 1)) := by
  have h := _root_.integral_rpow_mul_exp_neg_mul_rpow (p := 2) (q := ((a + a + 1 : ℕ) : ℝ)) (b := t)
    two_pos (by have := (Nat.cast_nonneg (a + a + 1) : (0 : ℝ) ≤ _); linarith) ht
  have e : ∫ r in Ioi (0 : ℝ), r ^ (a + a + 1) * Real.exp (-(t * r ^ 2)) =
      ∫ r in Ioi (0 : ℝ), r ^ (((a + a + 1 : ℕ) : ℝ)) * Real.exp (-t * r ^ (2 : ℝ)) := by
    refine setIntegral_congr_fun measurableSet_Ioi (fun r _ => ?_)
    rw [Real.rpow_natCast, Real.rpow_two, neg_mul]
  rw [e, h]
  have g : ((((a + a + 1 : ℕ) : ℝ)) + 1) / 2 = (a : ℝ) + 1 := by push_cast; ring
  have g2 : -((((a + a + 1 : ℕ) : ℝ)) + 1) / 2 = -(((a + 1 : ℕ) : ℝ)) := by push_cast; ring
  rw [g, g2, Real.Gamma_nat_eq_factorial, Real.rpow_neg ht.le, Real.rpow_natCast]
  field_simp
theorem integrable_conj_pow_mul_pow_mul_exp (a b : ℕ) {t : ℝ} (ht : 0 < t) :
    Integrable fun z : ℂ => starRingEnd ℂ (z ^ a) * z ^ b * (Real.exp (-(t * ‖z‖ ^ 2)) : ℂ) := by
  have hf : Integrable (fun z : ℂ => (fun y : ℝ => y ^ (a + b) * Real.exp (-(t * y ^ 2))) ‖z‖)
      volume := by
    refine (integrable_fun_norm_addHaar (volume : Measure ℂ)
      (f := fun y : ℝ => y ^ (a + b) * Real.exp (-(t * y ^ 2)))).mpr ?_
    have h := integrableOn_rpow_mul_exp_neg_mul_sq ht (s := ((a + b + 1 : ℕ) : ℝ))
      (by have := (Nat.cast_nonneg (a + b + 1) : (0 : ℝ) ≤ _); linarith)
    refine h.congr_fun (fun y hy => ?_) measurableSet_Ioi
    have hy : 0 < y := hy
    simp only [Complex.finrank_real_complex, smul_eq_mul]
    rw [Real.rpow_natCast]; ring_nf
  refine hf.mono' (by fun_prop) (Filter.Eventually.of_forall fun z => ?_)
  simp only [norm_mul, norm_pow, Complex.norm_conj, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos _)]
  rw [pow_add]
theorem integral_norm_pow_mul_exp (a : ℕ) {t : ℝ} (ht : 0 < t) :
    ∫ z : ℂ, ‖z‖ ^ (a + a) * Real.exp (-(t * ‖z‖ ^ 2)) =
      Real.pi * (a.factorial : ℝ) / t ^ (a + 1) := by
  apply Complex.ofReal_injective
  rw [← integral_complex_ofReal]
  have e : (fun z : ℂ => ((‖z‖ ^ (a + a) * Real.exp (-(t * ‖z‖ ^ 2)) : ℝ) : ℂ)) =
      fun z : ℂ => starRingEnd ℂ (z ^ a) * z ^ a * (Real.exp (-(t * ‖z‖ ^ 2)) : ℂ) := by
    funext z
    rw [Complex.conj_mul', norm_pow]
    push_cast; ring
  rw [e, integral_conj_pow_mul_pow_mul_exp_eq_polar, integral_Ioi_pow_mul_exp_neg_mul_sq a ht, integral_exp_mul_I_self]
  have : t ^ (a + 1) ≠ 0 := by positivity
  push_cast
  field_simp
theorem gs_prod {N : ℕ} (a b : Fin N → ℕ) (t : ℝ) (z : Fin N → ℂ) :
    starRingEnd ℂ (monoC a z) * monoC b z * (Real.exp (-(t * sqN z)) : ℂ) =
      ∏ i, (starRingEnd ℂ (z i ^ a i) * z i ^ b i * (Real.exp (-(t * ‖z i‖ ^ 2)) : ℂ)) := by
  rw [monoC, monoC, sqN, map_prod, Finset.mul_sum, ← Finset.sum_neg_distrib, Real.exp_sum,
    Complex.ofReal_prod, ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
theorem gs_prod_sq {N : ℕ} (a : Fin N → ℕ) (t : ℝ) (z : Fin N → ℂ) :
    ‖monoC a z‖ ^ 2 * Real.exp (-(t * sqN z)) =
      ∏ i, (‖z i‖ ^ (a i + a i) * Real.exp (-(t * ‖z i‖ ^ 2))) := by
  rw [monoC, sqN, norm_prod, ← Finset.prod_pow, Finset.mul_sum, ← Finset.sum_neg_distrib,
    Real.exp_sum, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [norm_pow, ← pow_mul, mul_two]
end helpers
theorem integrable_mono_mul_exp {N : ℕ} (a b : Fin N → ℕ) {t : ℝ} (ht : 0 < t) :
    Integrable fun z : Fin N → ℂ =>
      starRingEnd ℂ (monoC a z) * monoC b z * (Real.exp (-(t * sqN z)) : ℂ) := by
  simp_rw [gs_prod]
  exact Integrable.fintype_prod (f := fun i (w : ℂ) =>
    starRingEnd ℂ (w ^ a i) * w ^ b i * (Real.exp (-(t * ‖w‖ ^ 2)) : ℂ))
    (μ := fun _ => volume) fun i => integrable_conj_pow_mul_pow_mul_exp (a i) (b i) ht
theorem integral_mono_sq_mul_exp {N : ℕ} (a : Fin N → ℕ) {t : ℝ} (ht : 0 < t) :
    ∫ z : Fin N → ℂ, ‖monoC a z‖ ^ 2 * Real.exp (-(t * sqN z)) =
      Real.pi ^ N * ((∏ i, (a i).factorial : ℕ) : ℝ) / t ^ ((∑ i, a i) + N) := by
  simp_rw [gs_prod_sq]
  rw [integral_fintype_prod_volume_eq_prod (fun i (w : ℂ) =>
    ‖w‖ ^ (a i + a i) * Real.exp (-(t * ‖w‖ ^ 2)))]
  simp_rw [integral_norm_pow_mul_exp _ ht]
  rw [Finset.prod_div_distrib, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ,
    Fintype.card_fin, Nat.cast_prod, Finset.prod_pow_eq_pow_sum, Finset.sum_add_distrib,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, mul_one]
instance isProbabilityMeasure_gaussC (N : ℕ) : IsProbabilityMeasure (gaussC N) := by
  have e1 : (fun z : Fin N → ℂ => ‖monoC (0 : Fin N → ℕ) z‖ ^ 2 * Real.exp (-(1 * sqN z))) =
      fun z => Real.exp (-sqN z) := by
    funext z; simp [monoC]
  have hval := integral_mono_sq_mul_exp (N := N) 0 one_pos
  rw [e1] at hval
  simp only [Pi.zero_apply, Nat.factorial_zero, Finset.prod_const_one, Nat.cast_one, mul_one,
    Finset.sum_const_zero, zero_add, one_pow, div_one] at hval
  have hint : Integrable fun z : Fin N → ℂ => Real.exp (-sqN z) := by
    refine (integrable_mono_mul_exp (N := N) 0 0 one_pos).norm.congr
      (Filter.Eventually.of_forall fun z => ?_)
    simp [monoC, Complex.norm_exp]
  constructor
  rw [gaussC, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    ← ofReal_integral_eq_lintegral_ofReal (hint.const_mul _)
      (Filter.Eventually.of_forall fun z => by positivity),
    integral_const_mul, hval, inv_mul_cancel₀ (by positivity), ENNReal.ofReal_one]
end ReciprocityTheory.GeometryOfNumbersTheory


