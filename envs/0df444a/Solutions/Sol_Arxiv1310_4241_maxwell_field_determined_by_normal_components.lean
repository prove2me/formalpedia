-- Prove2me | solution 1 for Arxiv1310_4241.maxwell_field_determined_by_normal_components
-- status  : ACCEPTED   (prove)
-- author  : @fl-39
-- created : 2026-11-25T19:42:43.256072+00:00
-- url     : https://prove2.me/submissions/267bb04a-f7c3-40d9-a964-b26823adee86

import Mathlib
import Definitions.Def_Arxiv1310_4241_Basic

open MeasureTheory Filter Topology Arxiv1310_4241

private lemma isOpen_upperHalfSpace : IsOpen upperHalfSpace :=
  isOpen_lt continuous_const (EuclideanSpace.proj (𝕜 := ℝ) (2 : Fin 3)).continuous

private lemma norm_mul_exp_I_mul (R : ℝ) (hR : 0 ≤ R) (θ : ℝ) :
    ‖(R : ℂ) * Complex.exp (Complex.I * θ)‖ = R := by
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hR,
    mul_comm Complex.I (θ : ℂ), Complex.norm_exp_ofReal_mul_I, mul_one]

/-- Schwarz-type Liouville lemma: an entire function `F` with `F 0 = 0` and
`Im F(R e^{iθ}) = o(R)` uniformly in `θ` as `R → ∞` vanishes identically. -/
private lemma entire_eq_zero_of_im_littleO (F : ℂ → ℂ) (hF : Differentiable ℂ F) (hF0 : F 0 = 0)
    (him : ∀ ε > 0, ∃ R₀ > (0 : ℝ), ∀ R ≥ R₀, ∀ θ : ℝ,
      |(F ((R : ℂ) * Complex.exp (Complex.I * θ))).im| ≤ ε * R) :
    ∀ w : ℂ, F w = 0 := by
  intro w
  suffices hnorm : ‖F w‖ ≤ 0 from norm_le_zero_iff.mp hnorm
  apply le_of_forall_pos_le_add
  intro δ hδ
  rw [zero_add]
  by_cases hw : w = 0
  · rw [hw, hF0, norm_zero]; exact hδ.le
  have hw_pos : 0 < ‖w‖ := norm_pos_iff.mpr hw
  set ε : ℝ := δ / (4 * ‖w‖)
  have hε : 0 < ε := div_pos hδ (by positivity)
  obtain ⟨R₀, hR₀, hbound⟩ := him ε hε
  set R : ℝ := max R₀ (2 * ‖w‖ + 1)
  have hR_ge_R₀ : R₀ ≤ R := le_max_left _ _
  have hR_gt : 2 * ‖w‖ < R := by linarith [le_max_right R₀ (2 * ‖w‖ + 1)]
  have hR_pos : 0 < R := by linarith
  have hw_ball : w ∈ Metric.ball (0 : ℂ) R := by
    simp only [Metric.mem_ball, dist_zero_right]; linarith
  have h0_ball : (0 : ℂ) ∈ Metric.ball (0 : ℂ) R := by
    simp only [Metric.mem_ball, dist_zero_right, norm_zero]; exact hR_pos
  have hcauchy_w : (∮ z in C(0, R), (z - w)⁻¹ • F z) = (2 * Real.pi * Complex.I) • F w :=
    Complex.circleIntegral_sub_inv_smul_of_differentiable_on_off_countable
      Set.countable_empty hw_ball hF.continuous.continuousOn
      (fun z _ => hF.differentiableAt)
  have hcauchy_0 : (∮ z in C(0, R), (z - 0)⁻¹ • F z) = 0 := by
    have h := Complex.circleIntegral_sub_inv_smul_of_differentiable_on_off_countable
      Set.countable_empty h0_ball hF.continuous.continuousOn
      (fun z _ => hF.differentiableAt)
    rw [hF0, smul_zero] at h
    exact h
  have hzw_ne : ∀ θ : ℝ, (R : ℂ) * Complex.exp (Complex.I * θ) - w ≠ 0 := by
    intro θ h
    have h1 : (R : ℂ) * Complex.exp (Complex.I * θ) = w := sub_eq_zero.mp h
    have h2 : ‖(R : ℂ) * Complex.exp (Complex.I * θ)‖ = R := norm_mul_exp_I_mul R hR_pos.le θ
    rw [h1] at h2
    linarith
  have hI_ne : (Complex.I : ℂ) ≠ 0 := Complex.I_ne_zero
  have hint_w : (∫ θ in (0 : ℝ)..(2 * Real.pi),
      ((R : ℂ) * Complex.exp (Complex.I * θ) / ((R : ℂ) * Complex.exp (Complex.I * θ) - w)) *
        F ((R : ℂ) * Complex.exp (Complex.I * θ))) = 2 * Real.pi * F w := by
    have h1 := hcauchy_w
    simp only [circleIntegral, deriv_circleMap, circleMap, zero_add, smul_eq_mul] at h1
    have hpull : (∫ θ in (0 : ℝ)..(2 * Real.pi),
        ((R : ℂ) * Complex.exp (Complex.I * θ) * Complex.I) *
          (((R : ℂ) * Complex.exp (Complex.I * θ) - w)⁻¹ * F ((R : ℂ) * Complex.exp (Complex.I * θ)))) =
        Complex.I * (∫ θ in (0 : ℝ)..(2 * Real.pi),
          ((R : ℂ) * Complex.exp (Complex.I * θ) / ((R : ℂ) * Complex.exp (Complex.I * θ) - w)) *
            F ((R : ℂ) * Complex.exp (Complex.I * θ))) := by
      rw [← intervalIntegral.integral_const_mul]
      congr 1; ext θ; ring
    have h1' : (∫ θ in (0 : ℝ)..(2 * Real.pi),
        ((R : ℂ) * Complex.exp (Complex.I * θ) * Complex.I) *
          (((R : ℂ) * Complex.exp (Complex.I * θ) - w)⁻¹ * F ((R : ℂ) * Complex.exp (Complex.I * θ)))) =
        Complex.I * (2 * Real.pi * F w) := by
      have heq : (fun θ : ℝ => ((R : ℂ) * Complex.exp (Complex.I * θ) * Complex.I) *
            (((R : ℂ) * Complex.exp (Complex.I * θ) - w)⁻¹ * F ((R : ℂ) * Complex.exp (Complex.I * θ)))) =
          (fun θ : ℝ => ((R : ℂ) * Complex.exp ((θ : ℂ) * Complex.I) * Complex.I) *
            (((R : ℂ) * Complex.exp ((θ : ℂ) * Complex.I) - w)⁻¹ * F ((R : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)))) := by
        ext θ; rw [mul_comm Complex.I (θ : ℂ)]
      rw [heq, h1]; ring
    rw [hpull] at h1'
    exact mul_left_cancel₀ hI_ne h1'
  have hint_0 : (∫ θ in (0 : ℝ)..(2 * Real.pi),
      F ((R : ℂ) * Complex.exp (Complex.I * θ))) = 0 := by
    have h1 := hcauchy_0
    simp only [circleIntegral, deriv_circleMap, circleMap, zero_add, sub_zero, smul_eq_mul] at h1
    have hpull : (∫ θ in (0 : ℝ)..(2 * Real.pi),
        ((R : ℂ) * Complex.exp (Complex.I * θ) * Complex.I) *
          (((R : ℂ) * Complex.exp (Complex.I * θ))⁻¹ * F ((R : ℂ) * Complex.exp (Complex.I * θ)))) =
        Complex.I * (∫ θ in (0 : ℝ)..(2 * Real.pi),
          F ((R : ℂ) * Complex.exp (Complex.I * θ))) := by
      rw [← intervalIntegral.integral_const_mul]
      congr 1; ext θ
      have hRne : (R : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hR_pos.ne'
      have hene : Complex.exp (Complex.I * θ) ≠ 0 := Complex.exp_ne_zero _
      field_simp [hRne, hene]
    have h1' : (∫ θ in (0 : ℝ)..(2 * Real.pi),
        ((R : ℂ) * Complex.exp (Complex.I * θ) * Complex.I) *
          (((R : ℂ) * Complex.exp (Complex.I * θ))⁻¹ * F ((R : ℂ) * Complex.exp (Complex.I * θ)))) = 0 := by
      have heq : (fun θ : ℝ => ((R : ℂ) * Complex.exp (Complex.I * θ) * Complex.I) *
            (((R : ℂ) * Complex.exp (Complex.I * θ))⁻¹ * F ((R : ℂ) * Complex.exp (Complex.I * θ)))) =
          (fun θ : ℝ => ((R : ℂ) * Complex.exp ((θ : ℂ) * Complex.I) * Complex.I) *
            (((R : ℂ) * Complex.exp ((θ : ℂ) * Complex.I))⁻¹ * F ((R : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)))) := by
        ext θ; rw [mul_comm Complex.I (θ : ℂ)]
      rw [heq, h1]
    rw [hpull] at h1'
    exact (mul_eq_zero.mp h1').resolve_left hI_ne
  have hcont_w : Continuous (fun θ : ℝ =>
      ((R : ℂ) * Complex.exp (Complex.I * θ) / ((R : ℂ) * Complex.exp (Complex.I * θ) - w)) *
        F ((R : ℂ) * Complex.exp (Complex.I * θ))) := by
    refine Continuous.mul ?_ (hF.continuous.comp (by fun_prop))
    exact Continuous.div (by fun_prop) (by fun_prop) hzw_ne
  have hcont_0 : Continuous (fun θ : ℝ => F ((R : ℂ) * Complex.exp (Complex.I * θ))) :=
    hF.continuous.comp (by fun_prop)
  have hcont_f : Continuous (fun θ : ℝ =>
      (w / ((R : ℂ) * Complex.exp (Complex.I * θ) - w)) *
        F ((R : ℂ) * Complex.exp (Complex.I * θ))) :=
    (Continuous.div continuous_const (by fun_prop) hzw_ne).mul hcont_0
  have hcont_fc : Continuous (fun θ : ℝ =>
      (w / ((R : ℂ) * Complex.exp (Complex.I * θ) - w)) *
        star (F ((R : ℂ) * Complex.exp (Complex.I * θ)))) :=
    (Continuous.div continuous_const (by fun_prop) hzw_ne).mul (Complex.continuous_conj.comp hcont_0)
  have hint_diff : (∫ θ in (0 : ℝ)..(2 * Real.pi),
      (w / ((R : ℂ) * Complex.exp (Complex.I * θ) - w)) *
        F ((R : ℂ) * Complex.exp (Complex.I * θ))) = 2 * Real.pi * F w := by
    have hsub := intervalIntegral.integral_sub
      (hcont_w.intervalIntegrable (μ := volume) 0 (2 * Real.pi))
      (hcont_0.intervalIntegrable (μ := volume) 0 (2 * Real.pi))
    rw [hint_w, hint_0, sub_zero] at hsub
    rw [← hsub]
    congr 1; ext θ
    have hne := hzw_ne θ
    field_simp [hne]; ring
  have hden_refl : ∀ z ∈ Metric.closedBall (0 : ℂ) R, (R : ℂ) ^ 2 - star w * z ≠ 0 := by
    intro z hz h
    have h1 : (R : ℂ) ^ 2 = star w * z := sub_eq_zero.mp h
    have h2 : ‖(R : ℂ) ^ 2‖ = R ^ 2 := by
      rw [norm_pow, Complex.norm_real, Real.norm_of_nonneg hR_pos.le]
    have h3 : ‖star w * z‖ ≤ ‖w‖ * R := by
      rw [norm_mul, norm_star]
      have hz' : ‖z‖ ≤ R := by simpa [Metric.mem_closedBall, dist_zero_right] using hz
      exact mul_le_mul_of_nonneg_left hz' (norm_nonneg w)
    rw [h1] at h2
    nlinarith
  have hrefl_holo : ∀ z ∈ Metric.closedBall (0 : ℂ) R,
      DifferentiableAt ℂ (fun z => ((R : ℂ) ^ 2 - star w * z)⁻¹ * F z) z := by
    intro z hz
    have hd : DifferentiableAt ℂ (fun z => (R : ℂ) ^ 2 - star w * z) z := by fun_prop
    exact (hd.inv (hden_refl z hz)).mul hF.differentiableAt
  have hcauchy_refl : (∮ z in C(0, R), ((R : ℂ) ^ 2 - star w * z)⁻¹ * F z) = 0 := by
    apply Complex.circleIntegral_eq_zero_of_differentiable_on_off_countable
      hR_pos.le Set.countable_empty
    · exact fun z hz => (hrefl_holo z hz).continuousAt.continuousWithinAt
    · exact fun z hz => hrefl_holo z (Metric.ball_subset_closedBall hz.1)
  have hint_refl : (∫ θ in (0 : ℝ)..(2 * Real.pi),
      (w / ((R : ℂ) * Complex.exp (Complex.I * θ) - w)) *
        star (F ((R : ℂ) * Complex.exp (Complex.I * θ)))) = 0 := by
    have h1 := hcauchy_refl
    simp only [circleIntegral, deriv_circleMap, circleMap, zero_add, smul_eq_mul] at h1
    have hpull : (∫ θ in (0 : ℝ)..(2 * Real.pi),
        ((R : ℂ) * Complex.exp (Complex.I * θ) * Complex.I) *
          (((R : ℂ) ^ 2 - star w * ((R : ℂ) * Complex.exp (Complex.I * θ)))⁻¹ *
            F ((R : ℂ) * Complex.exp (Complex.I * θ)))) =
        Complex.I * (∫ θ in (0 : ℝ)..(2 * Real.pi),
          ((R : ℂ) * Complex.exp (Complex.I * θ) /
            ((R : ℂ) ^ 2 - star w * ((R : ℂ) * Complex.exp (Complex.I * θ)))) *
            F ((R : ℂ) * Complex.exp (Complex.I * θ))) := by
      rw [← intervalIntegral.integral_const_mul]
      congr 1; ext θ; ring
    have h1' : (∫ θ in (0 : ℝ)..(2 * Real.pi),
        ((R : ℂ) * Complex.exp (Complex.I * θ) * Complex.I) *
          (((R : ℂ) ^ 2 - star w * ((R : ℂ) * Complex.exp (Complex.I * θ)))⁻¹ *
            F ((R : ℂ) * Complex.exp (Complex.I * θ)))) = 0 := by
      have heq : (fun θ : ℝ => ((R : ℂ) * Complex.exp (Complex.I * θ) * Complex.I) *
            (((R : ℂ) ^ 2 - star w * ((R : ℂ) * Complex.exp (Complex.I * θ)))⁻¹ *
              F ((R : ℂ) * Complex.exp (Complex.I * θ)))) =
          (fun θ : ℝ => ((R : ℂ) * Complex.exp ((θ : ℂ) * Complex.I) * Complex.I) *
            (((R : ℂ) ^ 2 - star w * ((R : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)))⁻¹ *
              F ((R : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)))) := by
        ext θ; rw [mul_comm Complex.I (θ : ℂ)]
      rw [heq, h1]
    rw [hpull] at h1'
    have h2 := (mul_eq_zero.mp h1').resolve_left hI_ne
    have h3 : (∫ θ in (0 : ℝ)..(2 * Real.pi),
        star (w / ((R : ℂ) * Complex.exp (Complex.I * θ) - w)) *
          F ((R : ℂ) * Complex.exp (Complex.I * θ))) = 0 := by
      have hmul : star w * (∫ θ in (0 : ℝ)..(2 * Real.pi),
          ((R : ℂ) * Complex.exp (Complex.I * θ) /
            ((R : ℂ) ^ 2 - star w * ((R : ℂ) * Complex.exp (Complex.I * θ)))) *
            F ((R : ℂ) * Complex.exp (Complex.I * θ))) = 0 := by rw [h2, mul_zero]
      rw [← intervalIntegral.integral_const_mul] at hmul
      rw [← hmul]
      congr 1; ext θ
      set z : ℂ := (R : ℂ) * Complex.exp (Complex.I * θ)
      have hz_mul_star : z * star z = (R : ℂ) ^ 2 := by
        have hsz : star z = (R : ℂ) * Complex.exp (-Complex.I * (θ : ℂ)) := by
          simp only [z, Complex.star_def, map_mul, Complex.conj_ofReal, ← Complex.exp_conj,
            Complex.conj_I]
        rw [hsz]
        have hexp : Complex.exp (Complex.I * (θ : ℂ)) * Complex.exp (-Complex.I * (θ : ℂ)) = 1 := by
          rw [← Complex.exp_add]; simp
        calc (R : ℂ) * Complex.exp (Complex.I * (θ : ℂ)) * ((R : ℂ) * Complex.exp (-Complex.I * (θ : ℂ)))
            = (R : ℂ) ^ 2 * (Complex.exp (Complex.I * (θ : ℂ)) * Complex.exp (-Complex.I * (θ : ℂ))) := by ring
          _ = (R : ℂ) ^ 2 := by rw [hexp, mul_one]
      have hden1 : star z - star w ≠ 0 := by
        intro h; apply hzw_ne θ
        have := congrArg star h
        simpa using this
      have hden2 : (R : ℂ) ^ 2 - star w * z ≠ 0 := by
        apply hden_refl z
        simp only [Metric.mem_closedBall, dist_zero_right, z, norm_mul_exp_I_mul R hR_pos.le θ, le_refl]
      have hfrac : star (w / (z - w)) = star w * (z / ((R : ℂ) ^ 2 - star w * z)) := by
        rw [star_div₀, star_sub]
        field_simp [hden1, hden2]
        linear_combination -star w * hz_mul_star
      rw [hfrac]; ring
    have hconj : star (∫ θ in (0 : ℝ)..(2 * Real.pi),
        (w / ((R : ℂ) * Complex.exp (Complex.I * θ) - w)) *
          star (F ((R : ℂ) * Complex.exp (Complex.I * θ)))) = 0 := by
      have hsc : Complex.conjCLE.toContinuousLinearMap (∫ θ in (0 : ℝ)..(2 * Real.pi),
          (w / ((R : ℂ) * Complex.exp (Complex.I * θ) - w)) *
            star (F ((R : ℂ) * Complex.exp (Complex.I * θ)))) =
        ∫ θ in (0 : ℝ)..(2 * Real.pi),
          Complex.conjCLE.toContinuousLinearMap ((w / ((R : ℂ) * Complex.exp (Complex.I * θ) - w)) *
            star (F ((R : ℂ) * Complex.exp (Complex.I * θ)))) :=
        (Complex.conjCLE.toContinuousLinearMap.intervalIntegral_comp_comm
          (hcont_fc.intervalIntegrable 0 (2 * Real.pi))).symm
      change Complex.conjCLE.toContinuousLinearMap _ = 0
      rw [hsc]
      convert h3 using 2
      ext θ
      simp [Complex.star_def, mul_comm]
    exact star_eq_zero.mp hconj
  have hint_im : (∫ θ in (0 : ℝ)..(2 * Real.pi),
      (w / ((R : ℂ) * Complex.exp (Complex.I * θ) - w)) *
        (2 * Complex.I * ((F ((R : ℂ) * Complex.exp (Complex.I * θ))).im : ℂ))) =
      2 * Real.pi * F w := by
    have hsub := intervalIntegral.integral_sub
      (hcont_f.intervalIntegrable (μ := volume) 0 (2 * Real.pi))
      (hcont_fc.intervalIntegrable (μ := volume) 0 (2 * Real.pi))
    rw [hint_diff, hint_refl, sub_zero] at hsub
    rw [← hsub]
    congr 1; ext θ
    have hsub_conj : F ((R : ℂ) * Complex.exp (Complex.I * θ)) -
        star (F ((R : ℂ) * Complex.exp (Complex.I * θ))) =
        2 * Complex.I * ((F ((R : ℂ) * Complex.exp (Complex.I * θ))).im : ℂ) := by
      apply Complex.ext <;> simp <;> ring
    rw [← mul_sub, hsub_conj]
  have hnorm_est : ‖2 * (Real.pi : ℂ) * F w‖ ≤ (4 * ε * ‖w‖) * |2 * Real.pi - 0| := by
    rw [← hint_im]
    apply intervalIntegral.norm_integral_le_of_norm_le_const
    intro θ _
    rw [norm_mul, norm_div, norm_mul, norm_mul, Complex.norm_ofNat, Complex.norm_I, mul_one,
      Complex.norm_real, Real.norm_eq_abs]
    have hden_lb : R / 2 ≤ ‖(R : ℂ) * Complex.exp (Complex.I * θ) - w‖ := by
      have htri := norm_sub_norm_le ((R : ℂ) * Complex.exp (Complex.I * θ)) w
      rw [norm_mul_exp_I_mul R hR_pos.le θ] at htri
      linarith
    have hden_pos : 0 < R / 2 := by linarith
    have him_le := hbound R hR_ge_R₀ θ
    have hdiv_le : ‖w‖ / ‖(R : ℂ) * Complex.exp (Complex.I * θ) - w‖ ≤ ‖w‖ / (R / 2) :=
      div_le_div_of_nonneg_left (norm_nonneg w) hden_pos hden_lb
    calc ‖w‖ / ‖(R : ℂ) * Complex.exp (Complex.I * θ) - w‖ *
            (2 * |(F ((R : ℂ) * Complex.exp (Complex.I * θ))).im|)
        ≤ (‖w‖ / (R / 2)) * (2 * (ε * R)) := by gcongr
      _ = 4 * ε * ‖w‖ := by field_simp [hR_pos.ne']; ring
  have h2pi_pos : 0 < 2 * Real.pi := by positivity
  have hnorm_lhs : ‖2 * (Real.pi : ℂ) * F w‖ = 2 * Real.pi * ‖F w‖ := by
    rw [norm_mul, norm_mul, Complex.norm_ofNat, Complex.norm_real,
      Real.norm_of_nonneg Real.pi_pos.le]
  rw [hnorm_lhs, sub_zero, abs_of_pos h2pi_pos] at hnorm_est
  have hle : ‖F w‖ ≤ 4 * ε * ‖w‖ := by nlinarith
  have h4 : 4 * ε * ‖w‖ = δ := by
    simp only [ε]; field_simp [hw_pos.ne']
  linarith

/-- If a real-differentiable function `g : ℂ → ℂ` satisfies the Cauchy-Riemann equation
`fderiv ℝ g w I = I * fderiv ℝ g w 1`, then `g` is complex-differentiable at `w`. -/
private lemma differentiableAt_complex_of_cauchyRiemann {g : ℂ → ℂ} {w : ℂ}
    (hg : DifferentiableAt ℝ g w)
    (hcr : fderiv ℝ g w Complex.I = Complex.I * fderiv ℝ g w 1) :
    DifferentiableAt ℂ g w := by
  set c : ℂ := fderiv ℝ g w 1
  have hlin : ∀ h : ℂ, fderiv ℝ g w h = h * c := by
    intro h
    have hdecomp : h = h.re • (1 : ℂ) + h.im • Complex.I := by
      apply Complex.ext <;> simp
    conv_lhs => rw [hdecomp]
    rw [map_add, map_smul, map_smul, hcr]
    simp only [Complex.real_smul, c]
    apply Complex.ext
    · simp; ring
    · simp
  have hderiv : HasDerivAt g c w := by
    rw [hasDerivAt_iff_isLittleO]
    have hfd := hg.hasFDerivAt.isLittleO
    refine hfd.congr' (Eventually.of_forall fun h => ?_) (Eventually.of_forall fun _ => rfl)
    simp only [hlin, smul_eq_mul]
  exact hderiv.differentiableAt

theorem solution (ω : ℝ) (ε μ : ℂ)
    (hk : IsCausalWavenumber (wavenumber ω ε μ)) (E₁ H₁ E₂ H₂ : Space → Fin 3 → ℂ)
    (h₁ : IsSourceFreeMaxwellOn ω ε μ upperHalfSpace E₁ H₁)
    (h₂ : IsSourceFreeMaxwellOn ω ε μ upperHalfSpace E₂ H₂)
    (hr₁ : SilverMullerAsPrinted ε μ upperHalfSpace E₁ H₁)
    (hr₂ : SilverMullerAsPrinted ε μ upperHalfSpace E₂ H₂)
    (hEz : ∀ p ∈ upperHalfSpace, E₁ p 2 = E₂ p 2) (hHz : ∀ p ∈ upperHalfSpace, H₁ p 2 = H₂ p 2) :
    ∀ p ∈ upperHalfSpace, E₁ p = E₂ p ∧ H₁ p = H₂ p := by
  let E : Space → Fin 3 → ℂ := fun p => E₁ p - E₂ p
  let H : Space → Fin 3 → ℂ := fun p => H₁ p - H₂ p
  have hEz0 : ∀ p ∈ upperHalfSpace, E p 2 = 0 := fun p hp => sub_eq_zero.mpr (hEz p hp)
  have hHz0 : ∀ p ∈ upperHalfSpace, H p 2 = 0 := fun p hp => sub_eq_zero.mpr (hHz p hp)
  have hMax : IsSourceFreeMaxwellOn ω ε μ upperHalfSpace E H := by
    intro p hp
    rcases h₁ p hp with ⟨hE1d, hH1d, hcurlE1, hcurlH1, hdivE1, hdivH1⟩
    rcases h₂ p hp with ⟨hE2d, hH2d, hcurlE2, hcurlH2, hdivE2, hdivH2⟩
    have hE1c : ∀ i, DifferentiableAt ℝ (fun q => E₁ q i) p := differentiableAt_pi.mp hE1d
    have hE2c : ∀ i, DifferentiableAt ℝ (fun q => E₂ q i) p := differentiableAt_pi.mp hE2d
    have hH1c : ∀ i, DifferentiableAt ℝ (fun q => H₁ q i) p := differentiableAt_pi.mp hH1d
    have hH2c : ∀ i, DifferentiableAt ℝ (fun q => H₂ q i) p := differentiableAt_pi.mp hH2d
    have hpd_sub : ∀ {f g : Space → ℂ} (i : Fin 3),
        DifferentiableAt ℝ f p → DifferentiableAt ℝ g p →
        pd i (fun q => f q - g q) p = pd i f p - pd i g p := fun i hf hg => by
      simp [pd, fderiv_fun_sub hf hg]
    refine ⟨hE1d.fun_sub hE2d, hH1d.fun_sub hH2d, ?_, ?_, ?_, ?_⟩
    · ext i
      have hce1 := congrFun hcurlE1 i
      have hce2 := congrFun hcurlE2 i
      fin_cases i <;> simp [E, H, curl, hpd_sub _ (hE1c _) (hE2c _)] at hce1 hce2 ⊢ <;>
        linear_combination hce1 - hce2
    · ext i
      have hch1 := congrFun hcurlH1 i
      have hch2 := congrFun hcurlH2 i
      fin_cases i <;> simp [E, H, curl, hpd_sub _ (hH1c _) (hH2c _)] at hch1 hch2 ⊢ <;>
        linear_combination hch1 - hch2
    · simp only [E, divergence, Pi.sub_apply, hpd_sub _ (hE1c _) (hE2c _)] at hdivE1 hdivE2 ⊢
      linear_combination hdivE1 - hdivE2
    · simp only [H, divergence, Pi.sub_apply, hpd_sub _ (hH1c _) (hH2c _)] at hdivH1 hdivH2 ⊢
      linear_combination hdivH1 - hdivH2
  have hSM : SilverMullerAsPrinted ε μ upperHalfSpace E H := by
    have hsub := hr₁.sub hr₂
    rw [sub_zero] at hsub
    refine hsub.congr (fun p => ?_)
    ext i
    fin_cases i <;> simp [E, H, crossProduct, Matrix.vecHead, Matrix.vecTail] <;> ring
  have hSM2 : Tendsto (fun p => H p 0 * radialUnit p 1 - H p 1 * radialUnit p 0)
      (Bornology.cobounded Space ⊓ Filter.principal upperHalfSpace) (𝓝 0) := by
    have hcomp : Tendsto (fun p => (crossProduct (H p) (radialUnit p) - (μ / ε) • E p) 2)
        (Bornology.cobounded Space ⊓ Filter.principal upperHalfSpace) (𝓝 0) := by
      have h := ((continuous_apply (2 : Fin 3)).continuousAt.tendsto).comp hSM
      simpa only [Function.comp_def, Pi.zero_apply] using h
    refine hcomp.congr' ?_
    filter_upwards [Filter.mem_inf_of_right (Filter.mem_principal_self upperHalfSpace)] with p hp
    simp [crossProduct, hEz0 p hp]
  have hH_zero : ∀ p ∈ upperHalfSpace, H p = 0 := by
    intro p hp
    set z0 : ℝ := p 2
    have hz0 : 0 < z0 := hp
    let φ : ℂ → Space := fun w => pt w.re w.im z0
    have hφ_mem : ∀ w : ℂ, φ w ∈ upperHalfSpace := fun w => by
      simp [φ, pt, upperHalfSpace, hz0]
    let Lφ : ℂ →L[ℝ] Space :=
      (Complex.reCLM.smulRight (EuclideanSpace.single (0 : Fin 3) (1 : ℝ))) +
      (Complex.imCLM.smulRight (EuclideanSpace.single (1 : Fin 3) (1 : ℝ)))
    have hφ_fderiv : ∀ w : ℂ, HasFDerivAt φ Lφ w := by
      intro w
      have hφ_eq : φ = fun z : ℂ => Lφ z + pt 0 0 z0 := by
        ext z i
        fin_cases i <;> simp [φ, Lφ, pt]
      rw [hφ_eq]
      exact Lφ.hasFDerivAt.add_const (pt 0 0 z0)
    have hH_lin : ∀ (ℓ : ℂ →L[ℝ] ℝ) (w : ℂ), ℓ (H (φ w) 0) = 0 ∧ ℓ (H (φ w) 1) = 0 := by
      intro ℓ
      let g : ℂ → ℂ := fun w => (ℓ (H (φ w) 0) : ℂ) - Complex.I * (ℓ (H (φ w) 1) : ℂ)
      have hg_holo : Differentiable ℂ g := by
        intro w
        have hHw := hMax (φ w) (hφ_mem w)
        rcases hHw with ⟨_, hHd, _, hcurlH, _, hdivH⟩
        have hH0d : DifferentiableAt ℝ (fun q => H q 0) (φ w) := (differentiableAt_pi.mp hHd) 0
        have hH1d : DifferentiableAt ℝ (fun q => H q 1) (φ w) := (differentiableAt_pi.mp hHd) 1
        have hg0 : HasFDerivAt (fun z => (ℓ (H (φ z) 0) : ℂ))
            (Complex.ofRealCLM.comp (ℓ.comp ((fderiv ℝ (fun q => H q 0) (φ w)).comp Lφ))) w :=
          Complex.ofRealCLM.hasFDerivAt.comp w
            (ℓ.hasFDerivAt.comp w (hH0d.hasFDerivAt.comp w (hφ_fderiv w)))
        have hg1 : HasFDerivAt (fun z => Complex.I * (ℓ (H (φ z) 1) : ℂ))
            (Complex.I • (Complex.ofRealCLM.comp (ℓ.comp ((fderiv ℝ (fun q => H q 1) (φ w)).comp Lφ)))) w :=
          (Complex.ofRealCLM.hasFDerivAt.comp w
            (ℓ.hasFDerivAt.comp w (hH1d.hasFDerivAt.comp w (hφ_fderiv w)))).const_mul Complex.I
        have hgd := hg0.sub hg1
        have hL1 : Lφ 1 = EuclideanSpace.single (0 : Fin 3) (1 : ℝ) := by
          ext i; fin_cases i <;> simp [Lφ]
        have hLI : Lφ Complex.I = EuclideanSpace.single (1 : Fin 3) (1 : ℝ) := by
          ext i; fin_cases i <;> simp [Lφ]
        have hcurl2 : pd 0 (fun q => H q 1) (φ w) = pd 1 (fun q => H q 0) (φ w) := by
          have hc := congrFun hcurlH 2
          simp only [curl, Pi.smul_apply, smul_eq_mul, hEz0 (φ w) (hφ_mem w), mul_zero,
            Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons] at hc
          exact sub_eq_zero.mp hc
        have hpd2H2 : pd 2 (fun q => H q 2) (φ w) = 0 := by
          have hev : (fun q => H q 2) =ᶠ[𝓝 (φ w)] fun _ => (0 : ℂ) := by
            filter_upwards [isOpen_upperHalfSpace.mem_nhds (hφ_mem w)] with q hq
            exact hHz0 q hq
          simp [pd, hev.fderiv_eq]
        have hdiv0 : pd 0 (fun q => H q 0) (φ w) = -pd 1 (fun q => H q 1) (φ w) := by
          rw [divergence, hpd2H2, add_zero] at hdivH
          exact eq_neg_of_add_eq_zero_left hdivH
        apply differentiableAt_complex_of_cauchyRiemann hgd.differentiableAt
        rw [hgd.fderiv]
        simp only [sub_apply, smul_apply, ContinuousLinearMap.comp_apply, Complex.ofRealCLM_apply,
          hL1, hLI]
        change (ℓ (pd 1 (fun q => H q 0) (φ w)) : ℂ) -
            Complex.I * (ℓ (pd 1 (fun q => H q 1) (φ w)) : ℂ) =
          Complex.I * ((ℓ (pd 0 (fun q => H q 0) (φ w)) : ℂ) -
            Complex.I * (ℓ (pd 0 (fun q => H q 1) (φ w)) : ℂ))
        rw [hcurl2, hdiv0, map_neg, Complex.ofReal_neg]
        ring_nf; simp [Complex.I_sq]
      let F : ℂ → ℂ := fun w => w * g w
      have hF_holo : Differentiable ℂ F := differentiable_id.mul hg_holo
      have hF0 : F 0 = 0 := by simp [F]
      have hF_im : ∀ ε > 0, ∃ R₀ > (0 : ℝ), ∀ R ≥ R₀, ∀ θ : ℝ,
          |(F ((R : ℂ) * Complex.exp (Complex.I * θ))).im| ≤ ε * R := by
        intro ε hε
        set C : ℝ := 2 * (‖ℓ‖ + 1)
        have hC : 0 < C := by positivity
        have hev_sm : ∀ᶠ q in Bornology.cobounded Space ⊓ Filter.principal upperHalfSpace,
            ‖H q 0 * radialUnit q 1 - H q 1 * radialUnit q 0‖ ≤ ε / C :=
          (Metric.tendsto_nhds.mp hSM2 (ε / C) (div_pos hε hC)).mono fun q hq => by
            simpa [dist_zero_right] using hq.le
        rw [Filter.eventually_inf_principal] at hev_sm
        set S : Set Space := {q | q ∈ upperHalfSpace → ‖H q 0 * radialUnit q 1 - H q 1 * radialUnit q 0‖ ≤ ε / C}
        have hs_bdd : Bornology.IsBounded Sᶜ := by
          exact Bornology.isBounded_compl_iff.mpr hev_sm
        obtain ⟨M, hM⟩ := hs_bdd.subset_closedBall (0 : Space)
        refine ⟨max (max M 0 + 1) z0, by positivity, fun R hR θ => ?_⟩
        have hR_pos : 0 < R := lt_of_lt_of_le (by positivity) hR
        have hR_ge_z0 : z0 ≤ R := le_trans (le_max_right _ _) hR
        have hR_gt_M : M < R := by linarith [le_max_left (max M 0 + 1) z0, le_max_left M 0]
        set w : ℂ := (R : ℂ) * Complex.exp (Complex.I * θ)
        have hw_re : w.re = R * Real.cos θ := by
          simp only [w, mul_comm Complex.I (θ : ℂ), Complex.exp_ofReal_mul_I_re,
            Complex.exp_ofReal_mul_I_im, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
            zero_mul, sub_zero]
        have hw_im : w.im = R * Real.sin θ := by
          simp only [w, mul_comm Complex.I (θ : ℂ), Complex.exp_ofReal_mul_I_re,
            Complex.exp_ofReal_mul_I_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
            zero_mul, add_zero]
        have hnorm_φ : ‖φ w‖ = Real.sqrt (R ^ 2 + z0 ^ 2) := by
          rw [EuclideanSpace.norm_eq]
          simp only [Fin.sum_univ_three, φ, pt, Real.norm_eq_abs, sq_abs, hw_re, hw_im,
            Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.tail_cons,
            Matrix.head_cons]
          congr 1
          have hcs := Real.cos_sq_add_sin_sq θ
          nlinarith
        have hnorm_ge : R ≤ ‖φ w‖ := by
          rw [hnorm_φ]
          exact Real.le_sqrt_of_sq_le (by nlinarith [sq_nonneg z0])
        have hnorm_le : ‖φ w‖ ≤ 2 * R := by
          rw [hnorm_φ]
          exact Real.sqrt_le_iff.mpr ⟨by linarith, by nlinarith⟩
        have hφ_mem_S : φ w ∈ S := by
          by_contra hnot
          have hmem : φ w ∈ Sᶜ := hnot
          have := hM hmem
          simp only [Metric.mem_closedBall, dist_zero_right] at this
          linarith
        have hsm_le : ‖H (φ w) 0 * radialUnit (φ w) 1 - H (φ w) 1 * radialUnit (φ w) 0‖ ≤ ε / C :=
          hφ_mem_S (hφ_mem w)
        have hnorm_pos : 0 < ‖φ w‖ := lt_of_lt_of_le hR_pos hnorm_ge
        have him_eq : (F w).im = ‖φ w‖ * ℓ (H (φ w) 0 * radialUnit (φ w) 1 - H (φ w) 1 * radialUnit (φ w) 0) := by
          have hru0 : radialUnit (φ w) 0 = ((R * Real.cos θ / ‖φ w‖ : ℝ) : ℂ) := by
            simp [radialUnit, φ, pt, hw_re]
          have hru1 : radialUnit (φ w) 1 = ((R * Real.sin θ / ‖φ w‖ : ℝ) : ℂ) := by
            simp [radialUnit, φ, pt, hw_im]
          rw [hru0, hru1, map_sub,
            show H (φ w) 0 * ((R * Real.sin θ / ‖φ w‖ : ℝ) : ℂ) = (R * Real.sin θ / ‖φ w‖) • H (φ w) 0 by
              rw [Complex.real_smul, mul_comm],
            show H (φ w) 1 * ((R * Real.cos θ / ‖φ w‖ : ℝ) : ℂ) = (R * Real.cos θ / ‖φ w‖) • H (φ w) 1 by
              rw [Complex.real_smul, mul_comm],
            map_smul, map_smul]
          simp only [F, g, Complex.mul_im, Complex.sub_re, Complex.sub_im, Complex.mul_re,
            Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im, hw_re, hw_im,
            smul_eq_mul]
          field_simp [hnorm_pos.ne']
          ring
        rw [him_eq, abs_mul, abs_of_pos hnorm_pos]
        have hℓ_le : |ℓ (H (φ w) 0 * radialUnit (φ w) 1 - H (φ w) 1 * radialUnit (φ w) 0)| ≤
            ‖ℓ‖ * ‖H (φ w) 0 * radialUnit (φ w) 1 - H (φ w) 1 * radialUnit (φ w) 0‖ :=
          ℓ.le_opNorm _
        calc ‖φ w‖ * |ℓ (H (φ w) 0 * radialUnit (φ w) 1 - H (φ w) 1 * radialUnit (φ w) 0)|
            ≤ (2 * R) * (‖ℓ‖ * (ε / C)) := by
              have h1 : ‖ℓ‖ * ‖H (φ w) 0 * radialUnit (φ w) 1 - H (φ w) 1 * radialUnit (φ w) 0‖ ≤
                  ‖ℓ‖ * (ε / C) := mul_le_mul_of_nonneg_left hsm_le (norm_nonneg ℓ)
              have h2 := le_trans hℓ_le h1
              exact mul_le_mul hnorm_le h2 (abs_nonneg _) (by linarith)
          _ ≤ (2 * R) * ((‖ℓ‖ + 1) * (ε / C)) := by gcongr; linarith
          _ = ε * R := by simp only [C]; field_simp [hC.ne']
      have hF_zero := entire_eq_zero_of_im_littleO F hF_holo hF0 hF_im
      intro w
      have hgw : g w = 0 := by
        by_cases hw : w = 0
        · have hlim : Tendsto g (𝓝[≠] 0) (𝓝 (g 0)) :=
            hg_holo.continuous.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
          have hlim0 : Tendsto g (𝓝[≠] 0) (𝓝 0) := by
            refine tendsto_const_nhds.congr' ?_
            filter_upwards [self_mem_nhdsWithin] with z hz
            exact ((mul_eq_zero.mp (hF_zero z)).resolve_left hz).symm
          rw [hw]
          exact tendsto_nhds_unique hlim hlim0
        · exact (mul_eq_zero.mp (hF_zero w)).resolve_left hw
      have hre := congrArg Complex.re hgw
      have him := congrArg Complex.im hgw
      simp only [g, Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im,
        Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im, Complex.zero_re,
        Complex.zero_im] at hre him
      exact ⟨by linarith, by linarith⟩
    let wp : ℂ := ⟨p 0, p 1⟩
    have hφp : φ wp = p := by
      ext i; fin_cases i <;> simp [φ, wp, pt, z0]
    have hre := hH_lin Complex.reCLM wp
    have him := hH_lin Complex.imCLM wp
    rw [hφp] at hre him
    ext i
    fin_cases i
    · apply Complex.ext
      · exact hre.1
      · exact him.1
    · apply Complex.ext
      · exact hre.2
      · exact him.2
    · exact hHz0 p hp
  have hk0 : wavenumber ω ε μ ≠ 0 := by
    intro h; have := hk.1; rw [h] at this; simp at this
  have hω : (ω : ℂ) ≠ 0 := by
    intro h; apply hk0; rw [wavenumber, h, zero_mul]
  have hε : ε ≠ 0 := by
    intro h; apply hk0; rw [wavenumber, h, zero_mul, Complex.zero_cpow (by norm_num), mul_zero]
  have hc_ne : -(Complex.I * (ω : ℂ) * ε) ≠ 0 :=
    neg_ne_zero.mpr (mul_ne_zero (mul_ne_zero Complex.I_ne_zero hω) hε)
  intro p hp
  have hHp : H p = 0 := hH_zero p hp
  have hEp : E p = 0 := by
    have hcurlH := (hMax p hp).2.2.2.1
    have hcurl0 : curl H p = 0 := by
      have hev : ∀ i : Fin 3, (fun q => H q i) =ᶠ[𝓝 p] fun _ => (0 : ℂ) := by
        intro i
        filter_upwards [isOpen_upperHalfSpace.mem_nhds hp] with q hq
        simp [hH_zero q hq]
      ext i
      fin_cases i <;> simp [curl, pd, (hev _).fderiv_eq]
    rw [hcurl0] at hcurlH
    exact (smul_eq_zero.mp hcurlH.symm).resolve_left hc_ne
  exact ⟨sub_eq_zero.mp hEp, sub_eq_zero.mp hHp⟩
