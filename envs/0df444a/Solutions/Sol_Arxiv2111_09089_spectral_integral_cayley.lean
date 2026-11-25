-- Prove2me | solution 1 for Arxiv2111_09089.spectral_integral_cayley
-- status  : ACCEPTED   (prove)
-- author  : @terra-mathbot
-- created : 2026-11-25T20:35:31.873956+00:00
-- url     : https://prove2.me/submissions/793cd304-64c9-4947-a40a-ad2835ee6859

import Mathlib
import Definitions.Def_Arxiv2111_09089_Basic

open Complex MeasureTheory Filter Topology Asymptotics
open Arxiv2111_09089

lemma sin_half_pos {φ : ℝ} (h : φ ∈ Set.Ioo 0 (2 * Real.pi)) : 0 < Real.sin (φ / 2) :=
  Real.sin_pos_of_pos_of_lt_pi (by linarith [h.1]) (by linarith [h.2])

lemma cayley_circle {φ : ℝ} (h : φ ∈ Set.Ioo 0 (2 * Real.pi)) :
    cayley (exp ((φ : ℂ) * I)) = (Real.cot (φ / 2) : ℂ) := by
  have hs := sin_half_pos h
  set u := exp (((φ / 2 : ℝ) : ℂ) * I) with hu
  have hu0 : u ≠ 0 := Complex.exp_ne_zero _
  have he : exp ((φ : ℂ) * I) = u * u := by
    rw [hu, ← Complex.exp_add]; congr 1; push_cast; ring
  have hinv : exp (-(((φ / 2 : ℝ) : ℂ) * I)) = u⁻¹ := by rw [Complex.exp_neg]
  have hcos : Complex.cos ((φ / 2 : ℝ) : ℂ) = (u + u⁻¹) / 2 := by
    rw [Complex.cos, ← hu, ← hinv]; ring_nf
  have hsin : Complex.sin ((φ / 2 : ℝ) : ℂ) = (u⁻¹ - u) * I / 2 := by
    rw [Complex.sin, ← hu, ← hinv]; ring_nf
  have hsC : Complex.sin ((φ / 2 : ℝ) : ℂ) ≠ 0 := by
    rw [← Complex.ofReal_sin]; exact_mod_cast hs.ne'
  have hd : u⁻¹ - u ≠ 0 := by
    intro h0; apply hsC; rw [hsin, h0]; ring
  have h1 : 1 - u * u ≠ 0 := by
    intro h0; apply hd
    have : u⁻¹ = u := by
      field_simp; linear_combination h0
    rw [this, sub_self]
  rw [Complex.ofReal_cot, Complex.cot_eq_cos_div_sin, hcos, hsin, he]
  unfold cayley
  rw [div_eq_div_iff h1 (by
    intro h0; apply hsC; rw [hsin]; linear_combination h0)]
  field_simp
  ring_nf
  rw [Complex.I_sq]
  ring

lemma hasDeriv_cot_half {φ : ℝ} (h : φ ∈ Set.Ioo 0 (2 * Real.pi)) :
    HasDerivAt (fun ψ : ℝ => Real.cot (ψ / 2)) (-(1 + Real.cot (φ / 2) ^ 2) / 2) φ := by
  have hs := (sin_half_pos h).ne'
  have hc : HasDerivAt (fun ψ : ℝ => Real.cos (ψ / 2)) (-Real.sin (φ / 2) * (1 / 2)) φ := by
    have := ((hasDerivAt_id φ).div_const 2).cos
    simpa using this
  have hsn : HasDerivAt (fun ψ : ℝ => Real.sin (ψ / 2)) (Real.cos (φ / 2) * (1 / 2)) φ := by
    have := ((hasDerivAt_id φ).div_const 2).sin
    simpa using this
  have hq := hc.div hsn hs
  have hfun : (fun ψ : ℝ => Real.cot (ψ / 2)) = fun ψ => Real.cos (ψ / 2) / Real.sin (ψ / 2) := by
    funext ψ; rw [Real.cot_eq_cos_div_sin]
  rw [hfun]
  refine hq.congr_deriv ?_
  rw [Real.cot_eq_cos_div_sin]
  field_simp
  ring

theorem cay_props :
    (∀ φ ∈ Set.Ioo 0 (2 * Real.pi), cayley (exp ((φ : ℂ) * I)) = (Real.cot (φ / 2) : ℂ)) ∧
    StrictAntiOn (fun φ : ℝ => Real.cot (φ / 2)) (Set.Ioo 0 (2 * Real.pi)) ∧
    Tendsto (fun φ : ℝ => Real.cot (φ / 2)) (𝓝[>] 0) atTop ∧
    Tendsto (fun φ : ℝ => Real.cot (φ / 2)) (𝓝[<] (2 * Real.pi)) atBot ∧
    ∀ φ ∈ Set.Ioo 0 (2 * Real.pi),
      HasDerivAt (fun ψ : ℝ => Real.cot (ψ / 2)) (-(1 + Real.cot (φ / 2) ^ 2) / 2) φ := by
  have hpi := Real.pi_pos
  have hfun : (fun ψ : ℝ => Real.cot (ψ / 2)) = fun ψ => Real.cos (ψ / 2) * (Real.sin (ψ / 2))⁻¹ := by
    funext ψ; rw [Real.cot_eq_cos_div_sin, div_eq_mul_inv]
  refine ⟨fun φ h => cayley_circle h, ?_, ?_, ?_, fun φ h => hasDeriv_cot_half h⟩
  · apply strictAntiOn_of_deriv_neg (convex_Ioo 0 (2 * Real.pi))
    · exact fun φ h => (hasDeriv_cot_half h).continuousAt.continuousWithinAt
    · intro φ h
      rw [interior_Ioo] at h
      rw [(hasDeriv_cot_half h).deriv]
      have := sq_nonneg (Real.cot (φ / 2))
      linarith
  · rw [hfun]
    have hsin : Tendsto (fun ψ : ℝ => Real.sin (ψ / 2)) (𝓝[>] 0) (𝓝[>] 0) := by
      apply tendsto_nhdsWithin_iff.mpr
      constructor
      · apply tendsto_nhdsWithin_of_tendsto_nhds
        have : Continuous (fun ψ : ℝ => Real.sin (ψ / 2)) := by fun_prop
        simpa using this.tendsto 0
      · filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 2 * Real.pi by positivity)] with ψ hψ
        exact sin_half_pos hψ
    have hcos : Tendsto (fun ψ : ℝ => Real.cos (ψ / 2)) (𝓝[>] 0) (𝓝 1) := by
      apply tendsto_nhdsWithin_of_tendsto_nhds
      have : Continuous (fun ψ : ℝ => Real.cos (ψ / 2)) := by fun_prop
      simpa using this.tendsto 0
    exact hcos.pos_mul_atTop one_pos (tendsto_inv_nhdsGT_zero.comp hsin)
  · rw [hfun]
    have hsin : Tendsto (fun ψ : ℝ => Real.sin (ψ / 2)) (𝓝[<] (2 * Real.pi)) (𝓝[>] 0) := by
      apply tendsto_nhdsWithin_iff.mpr
      constructor
      · apply tendsto_nhdsWithin_of_tendsto_nhds
        have : Continuous (fun ψ : ℝ => Real.sin (ψ / 2)) := by fun_prop
        have h2 := this.tendsto (2 * Real.pi)
        simpa [mul_div_cancel_left₀] using h2
      · filter_upwards [Ioo_mem_nhdsLT (show (0 : ℝ) < 2 * Real.pi by positivity)] with ψ hψ
        exact sin_half_pos hψ
    have hcos : Tendsto (fun ψ : ℝ => Real.cos (ψ / 2)) (𝓝[<] (2 * Real.pi)) (𝓝 (-1)) := by
      apply tendsto_nhdsWithin_of_tendsto_nhds
      have : Continuous (fun ψ : ℝ => Real.cos (ψ / 2)) := by fun_prop
      have h2 := this.tendsto (2 * Real.pi)
      simpa [mul_div_cancel_left₀] using h2
    exact hcos.neg_mul_atTop (by norm_num) (tendsto_inv_nhdsGT_zero.comp hsin)



lemma si_scalar {θ : ℝ} (h : θ ∈ Set.Ioo 0 (2 * Real.pi)) :
    exp ((θ : ℂ) * I) * I * (2 * I / (1 - exp ((θ : ℂ) * I)) ^ 2) =
      (((1 + Real.cot (θ / 2) ^ 2) / 2 : ℝ) : ℂ) := by
  have hs := (sin_half_pos h).ne'
  set C : ℂ := (Real.cos (θ / 2) : ℂ) with hC
  set S : ℂ := (Real.sin (θ / 2) : ℂ) with hSd
  have hS0 : S ≠ 0 := by rw [hSd]; exact_mod_cast hs
  have pyth : C ^ 2 + S ^ 2 = 1 := by
    rw [hC, hSd]; exact_mod_cast Real.cos_sq_add_sin_sq (θ / 2)
  have he : exp ((θ : ℂ) * I) = (C + S * I) ^ 2 := by
    have : exp ((θ : ℂ) * I) = exp (((θ / 2 : ℝ) : ℂ) * I) ^ 2 := by
      rw [← Complex.exp_nat_mul]; congr 1; push_cast; ring
    rw [this, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
  set D : ℂ := S - C * I with hD
  have hD0 : D ≠ 0 := by
    intro h0
    have := congrArg Complex.re h0
    rw [hD, Complex.sub_re, Complex.mul_re, Complex.I_re, Complex.I_im, hC, hSd,
      Complex.ofReal_re, Complex.ofReal_im, Complex.zero_re] at this
    apply hs; linarith
  have hID : C + S * I = I * D := by
    rw [hD]; linear_combination C * Complex.I_sq
  have h1 : 1 - (C + S * I) ^ 2 = 2 * S * D := by
    rw [hD]; linear_combination (-1 : ℂ) * pyth + (-S ^ 2) * Complex.I_sq
  have hR : (((1 + Real.cot (θ / 2) ^ 2) / 2 : ℝ) : ℂ) = 1 / (2 * S ^ 2) := by
    have hr : (1 + Real.cot (θ / 2) ^ 2) / 2 = 1 / (2 * Real.sin (θ / 2) ^ 2) := by
      rw [Real.cot_eq_cos_div_sin]
      field_simp
      linarith [Real.cos_sq_add_sin_sq (θ / 2)]
    rw [hr]
    simp only [Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_mul, Complex.ofReal_pow,
      Complex.ofReal_ofNat]
    rw [hSd]
  rw [hR, he, h1, hID]
  have : (I * D) ^ 2 * I * (2 * I / (2 * S * D) ^ 2) = 1 / (2 * S ^ 2) := by
    have hI4 : I ^ 4 = 1 := by
      rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, Complex.I_sq]; norm_num
    field_simp
    ring_nf
    first | exact hI4 | (rw [hI4]; ring) | simp [hI4]
  exact this

theorem solution (α : ℝ) (hα : 0 < α) (F : ℂ → ℂ)
    (hF : Integrable (fun μ : ℝ => F (xiOfMu α μ))) :
    ∫ μ : ℝ, (1 + α * I) * F (xiOfMu α μ) =
      ∮ η in C(0, 1), (1 + α * I) * (2 * I / (1 - η) ^ 2) * F (xiOfMu α (cayley η)) := by
  obtain ⟨_, hanti, hlim0, hlim2, _⟩ := cay_props
  have hpi := Real.pi_pos
  have h02 : (0 : ℝ) < 2 * Real.pi := by positivity
  set f : ℝ → ℝ := fun θ => Real.cot (θ / 2) with hf
  have hcont : ContinuousOn f (Set.Ioo 0 (2 * Real.pi)) :=
    fun x hx => (hasDeriv_cot_half hx).continuousAt.continuousWithinAt
  have hsurj : f '' Set.Ioo 0 (2 * Real.pi) = Set.univ := by
    apply Set.eq_univ_of_univ_subset
    exact ContinuousOn.surjOn_of_tendsto' ⟨Real.pi, by constructor <;> linarith⟩ hcont
      ((tendsto_comp_coe_Ioo_atBot h02).mpr hlim0) ((tendsto_comp_coe_Ioo_atTop h02).mpr hlim2)
  have hcov := integral_image_eq_integral_abs_deriv_smul measurableSet_Ioo
    (fun x hx => (hasDeriv_cot_half hx).hasDerivWithinAt) hanti.injOn
    (fun μ : ℝ => (1 + α * I) * F (xiOfMu α μ))
  rw [hsurj, Measure.restrict_univ] at hcov
  rw [hcov, circleIntegral, intervalIntegral.integral_of_le h02.le, integral_Ioc_eq_integral_Ioo]
  refine setIntegral_congr_fun measurableSet_Ioo (fun θ hθ => ?_)
  simp only [deriv_circleMap, circleMap, zero_add, Complex.ofReal_one, one_mul]
  rw [cayley_circle hθ]
  have hab : |(-(1 + Real.cot (θ / 2) ^ 2) / 2)| = (1 + Real.cot (θ / 2) ^ 2) / 2 := by
    rw [abs_of_nonpos]; · ring
    have := sq_nonneg (Real.cot (θ / 2)); linarith
  rw [hab, Complex.real_smul, smul_eq_mul, ← si_scalar hθ]
  ring

