-- Prove2me | Definitions.Def_RPLib_S3_Bergman
-- name    : RPLib_S3_Bergman
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-13T20:51:26.871355+00:00
-- url     : https://prove2.me/theorems/bb524492-7421-4042-a1c6-ddf397cf7605
-- title:
--   The weighted Bergman reproducing formula on the upper half plane
-- statement:
--   For $k \ge 3$ and $f$ holomorphic on the upper half plane $\mathbb{H}$ with $|f(z)| \le C (\operatorname{Im} z)^{-k/2}$,
--   $$\int_{\mathbb{H}} f(z)\, \overline{(z - \bar w)^{-k}}\, (\operatorname{Im} z)^{k}\, \frac{dx\,dy}{y^2} = \frac{4\pi\, i^{k}}{(k-1)\,2^{k}}\, f(w),$$
--   proved via weighted integrals over the unit disc and the Cayley transform.
--
--   **Formalization note.** Library module of a formalization of the Ramanujan-Petersson conjecture (trace-formula layer: the Eichler-Selberg trace formula on $S_k(\Gamma_1(M))$ for $k \ge 3$, proved by Zagier's kernel method). It contains definitions together with proved lemmas (no `sorry`), so that later solution files can import them.
-- source:
--   H. Hedenmalm, B. Korenblum and K. Zhu, Theory of Bergman Spaces, GTM 199, Springer 2000, Chapter 1; D. Zagier, The Eichler-Selberg trace formula on SL2(Z), appendix to S. Lang, Introduction to Modular Forms, Grundlehren 222, Springer 1976 (with the Correction in later printings)

import Mathlib

open MeasureTheory Metric Set Filter Complex UpperHalfPlane
open scoped Real ComplexConjugate NNReal Manifold

set_option autoImplicit false

noncomputable section

namespace RamanujanPetersson.Bergman

/-! ## Part 1: weighted integrals over the unit disc -/


lemma polarCoord_symm_eq_circleMap (p : ℝ × ℝ) :
    Complex.polarCoord.symm p = circleMap 0 p.1 p.2 := by
  simp [circleMap, Complex.exp_mul_I]

lemma continuous_polarCoord_symm : Continuous (fun p : ℝ × ℝ => Complex.polarCoord.symm p) := by
  simp only [Complex.polarCoord_symm_apply]
  fun_prop

/-- Mean value property, integrated over `(-π, π)`. -/
lemma integral_Ioo_circleMap {G : ℂ → ℂ} (hG : DifferentiableOn ℂ G (ball 0 1)) {r : ℝ}
    (hr0 : 0 < r) (hr1 : r < 1) :
    ∫ θ in Ioo (-π) π, G (circleMap 0 r θ) = (2 * π) • G 0 := by
  have hdc : DiffContOnCl ℂ G (ball (0:ℂ) |r|) := by
    apply DifferentiableOn.diffContOnCl
    rw [closure_ball _ (abs_pos.mpr hr0.ne').ne']
    exact hG.mono (closedBall_subset_ball (by rwa [abs_of_pos hr0]))
  have hmv := hdc.circleAverage
  rw [Real.circleAverage_def] at hmv
  rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le (by linarith [Real.pi_pos])]
  have hper := ((periodic_circleMap (0:ℂ) r).comp G).intervalIntegral_add_eq (-π) 0
  have e : -π + 2 * π = π := by ring
  rw [e, zero_add] at hper
  simp only [Function.comp_apply] at hper
  rw [hper, ← hmv, smul_smul, mul_inv_cancel₀ (by positivity), one_smul]

/-- `∫_0^1 r (1 - r^2)^s dr = 1 / (2 (s + 1))` for `s > -1`, with integrability. -/
lemma hasDerivAt_weight_prim {s : ℝ} (hs : -1 < s) {x : ℝ} (hx : x ∈ Ioo (0:ℝ) 1) :
    HasDerivAt (fun r : ℝ => -(1 - r ^ 2) ^ (s + 1) / (2 * (s + 1))) (x * (1 - x ^ 2) ^ s) x := by
  have hpos : 0 < 1 - x ^ 2 := by nlinarith [hx.1, hx.2]
  have h1 : HasDerivAt (fun r : ℝ => 1 - r ^ 2) (-(2 * x)) x := by
    simpa using ((hasDerivAt_pow 2 x).const_sub 1)
  have h2 := (h1.rpow_const (p := s + 1) (Or.inl hpos.ne')).neg.div_const (2 * (s + 1))
  have h3 : HasDerivAt (fun r : ℝ => -(1 - r ^ 2) ^ (s + 1) / (2 * (s + 1)))
      (-(-(2 * x) * (s + 1) * (1 - x ^ 2) ^ (s + 1 - 1)) / (2 * (s + 1))) x := h2
  convert h3 using 1
  have hs1 : s + 1 ≠ 0 := by linarith
  rw [show s + 1 - 1 = s by ring]
  field_simp

lemma continuousOn_weight_prim {s : ℝ} (hs : -1 < s) :
    ContinuousOn (fun r : ℝ => -(1 - r ^ 2) ^ (s + 1) / (2 * (s + 1))) (Icc 0 1) := by
  apply ContinuousOn.div_const
  apply ContinuousOn.neg
  apply ContinuousOn.rpow_const (by fun_prop)
  intro x _
  right; linarith

lemma weight_nonneg {s : ℝ} {x : ℝ} (hx : x ∈ Ioo (0:ℝ) 1) : 0 ≤ x * (1 - x ^ 2) ^ s := by
  have hpos : 0 < 1 - x ^ 2 := by nlinarith [hx.1, hx.2]
  exact mul_nonneg hx.1.le (Real.rpow_nonneg hpos.le _)

lemma intervalIntegrable_weight {s : ℝ} (hs : -1 < s) :
    IntervalIntegrable (fun x : ℝ => x * (1 - x ^ 2) ^ s) volume 0 1 := by
  apply intervalIntegral.intervalIntegrable_deriv_of_nonneg (g := fun r : ℝ => -(1 - r ^ 2) ^ (s + 1) / (2 * (s + 1)))
  · rw [uIcc_of_le zero_le_one]; exact continuousOn_weight_prim hs
  · intro x hx
    rw [min_eq_left zero_le_one, max_eq_right zero_le_one] at hx
    exact hasDerivAt_weight_prim hs hx
  · intro x hx
    rw [min_eq_left zero_le_one, max_eq_right zero_le_one] at hx
    exact weight_nonneg hx

lemma integrableOn_weight {s : ℝ} (hs : -1 < s) :
    IntegrableOn (fun x : ℝ => x * (1 - x ^ 2) ^ s) (Ioo 0 1) :=
  ((intervalIntegrable_weight hs).1).mono_set Ioo_subset_Ioc_self

lemma integral_weight {s : ℝ} (hs : -1 < s) :
    ∫ x in Ioo (0:ℝ) 1, x * (1 - x ^ 2) ^ s = 1 / (2 * (s + 1)) := by
  rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le zero_le_one,
    intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le zero_le_one (continuousOn_weight_prim hs)
      (fun x hx => hasDerivAt_weight_prim hs hx) (intervalIntegrable_weight hs)]
  have hs1 : s + 1 ≠ 0 := by linarith
  have : (0:ℝ) ^ (s + 1) = 0 := Real.zero_rpow hs1
  simp [this]
  field_simp

/-- **Disc lemma.** For `G` holomorphic on the unit disc and `s > -1`, if
`(1 - |ζ|^2)^s G(ζ)` is integrable on the disc then its integral is `π/(s+1) G(0)`. -/
theorem integral_ball_smul {s : ℝ} (hs : -1 < s) {G : ℂ → ℂ} (hG : DifferentiableOn ℂ G (ball 0 1))
    (hint : IntegrableOn (fun ζ : ℂ => (1 - ‖ζ‖ ^ 2) ^ s • G ζ) (ball 0 1)) :
    ∫ ζ in ball (0:ℂ) 1, (1 - ‖ζ‖ ^ 2) ^ s • G ζ = (π / (s + 1)) • G 0 := by
  classical
  set h : ℂ → ℂ := fun ζ => (1 - ‖ζ‖ ^ 2) ^ s • G ζ with hh
  set F : ℂ → ℂ := (ball (0:ℂ) 1).indicator h with hF
  have hhc : ContinuousOn h (ball 0 1) := by
    rw [hh]
    apply ContinuousOn.fun_smul _ hG.continuousOn
    apply ContinuousOn.rpow_const (by fun_prop)
    intro ζ hζ
    left
    have : ‖ζ‖ < 1 := by simpa using hζ
    have : ‖ζ‖ ^ 2 < 1 := by nlinarith [norm_nonneg ζ]
    linarith
  have hFmeas : Measurable F := by
    rw [hF, ← Set.piecewise_eq_indicator]
    exact ContinuousOn.measurable_piecewise hhc continuousOn_const measurableSet_ball
  have hFint : Integrable F := (integrable_indicator_iff measurableSet_ball).2 hint
  rw [← integral_indicator measurableSet_ball, ← Complex.integral_comp_polarCoord_symm]
  -- integrability in polar coordinates
  have hpint : IntegrableOn (fun p : ℝ × ℝ => p.1 • F (Complex.polarCoord.symm p))
      polarCoord.target := by
    refine ⟨?_, ?_⟩
    · exact (measurable_fst.smul (hFmeas.comp continuous_polarCoord_symm.measurable)).aestronglyMeasurable
    · show ∫⁻ p in polarCoord.target, ‖p.1 • F (Complex.polarCoord.symm p)‖ₑ < ⊤
      calc ∫⁻ p in polarCoord.target, ‖p.1 • F (Complex.polarCoord.symm p)‖ₑ
          = ∫⁻ p in polarCoord.target, ENNReal.ofReal p.1 • ‖F (Complex.polarCoord.symm p)‖ₑ := by
            apply setLIntegral_congr_fun polarCoord.open_target.measurableSet
            intro p hp
            have : 0 < p.1 := hp.1
            dsimp only
            rw [enorm_smul, Real.enorm_of_nonneg this.le, smul_eq_mul]
        _ = ∫⁻ ζ, ‖F ζ‖ₑ := Complex.lintegral_comp_polarCoord_symm (fun ζ => ‖F ζ‖ₑ)
        _ < ⊤ := hFint.2
  set S : Set (ℝ × ℝ) := Ioo (0:ℝ) 1 ×ˢ Ioo (-π) π with hS
  have hSsub : S ⊆ polarCoord.target := by
    rintro ⟨r, θ⟩ ⟨hr, hθ⟩
    exact ⟨hr.1, hθ⟩
  have hnorm : ∀ p ∈ polarCoord.target, ‖Complex.polarCoord.symm p‖ = p.1 := by
    intro p hp
    rw [Complex.norm_polarCoord_symm, abs_of_pos hp.1]
  rw [setIntegral_eq_of_subset_of_forall_sdiff_eq_zero polarCoord.open_target.measurableSet hSsub]
  swap
  · rintro p ⟨hp, hpS⟩
    have h1 : ¬ p.1 < 1 := by
      intro h1
      exact hpS ⟨⟨hp.1, h1⟩, hp.2⟩
    have : Complex.polarCoord.symm p ∉ ball (0:ℂ) 1 := by
      simp only [mem_ball_zero_iff, hnorm p hp]
      exact h1
    show p.1 • F _ = 0
    rw [hF, Set.indicator_of_notMem this, smul_zero]
  have hSF : ∀ p ∈ S, p.1 • F (Complex.polarCoord.symm p)
      = (p.1 * (1 - p.1 ^ 2) ^ s) • G (circleMap 0 p.1 p.2) := by
    intro p hp
    have hpt := hSsub hp
    have hmem : Complex.polarCoord.symm p ∈ ball (0:ℂ) 1 := by
      simp only [mem_ball_zero_iff, hnorm p hpt]
      exact hp.1.2
    rw [hF, Set.indicator_of_mem hmem, hh]
    simp only [smul_smul, polarCoord_symm_eq_circleMap, norm_circleMap_zero, abs_of_pos (show (0:ℝ) < p.1 from hpt.1)]
  rw [setIntegral_congr_fun (measurableSet_Ioo.prod measurableSet_Ioo) hSF]
  have hSint : IntegrableOn (fun p : ℝ × ℝ => (p.1 * (1 - p.1 ^ 2) ^ s) • G (circleMap 0 p.1 p.2)) S :=
    ((hpint.mono_set hSsub).congr_fun hSF (measurableSet_Ioo.prod measurableSet_Ioo))
  rw [Measure.volume_eq_prod, setIntegral_prod _ hSint]
  have hinner : ∀ r ∈ Ioo (0:ℝ) 1,
      ∫ θ in Ioo (-π) π, (r * (1 - r ^ 2) ^ s) • G (circleMap 0 r θ)
        = (r * (1 - r ^ 2) ^ s * (2 * π)) • G 0 := by
    intro r hr
    rw [integral_smul, integral_Ioo_circleMap hG hr.1 hr.2, smul_smul]
  rw [setIntegral_congr_fun measurableSet_Ioo hinner, integral_smul_const]
  congr 1
  rw [integral_mul_const, integral_weight hs]
  have hs1 : s + 1 ≠ 0 := by linarith
  field_simp


/-! ## Part 2: the Cayley parametrisation of `ℍ` by the unit disc -/

/-- Cayley parametrisation of the upper half plane by the unit disc, centred at `w`:
`ζ ↦ conj w + (w - conj w) / (1 - ζ)`; it sends `0` to `w`. -/
def cay (w ζ : ℂ) : ℂ := conj w + (w - conj w) / (1 - ζ)

lemma one_sub_ne_zero_of_mem_ball {ζ : ℂ} (hζ : ζ ∈ ball (0:ℂ) 1) : 1 - ζ ≠ 0 := by
  intro h
  have : ζ = 1 := by linear_combination -h
  rw [this] at hζ
  simp at hζ

lemma cay_zero (w : ℂ) : cay w 0 = w := by simp [cay]

lemma cay_sub_conj (w ζ : ℂ) : cay w ζ - conj w = (w - conj w) / (1 - ζ) := by simp [cay]

lemma sub_conj_ne_zero {w : ℂ} (hw : 0 < w.im) : w - conj w ≠ 0 := by
  rw [Complex.sub_conj]
  exact mul_ne_zero (ofReal_ne_zero.mpr (by positivity)) I_ne_zero

lemma im_cay (w ζ : ℂ) (hA : 1 - ζ ≠ 0) :
    (cay w ζ).im = w.im * (1 - ‖ζ‖ ^ 2) / ‖1 - ζ‖ ^ 2 := by
  have hN : normSq (1 - ζ) ≠ 0 := by rwa [Ne, Complex.normSq_eq_zero]
  rw [Complex.sq_norm, Complex.sq_norm]
  simp only [cay, add_im, conj_im, div_im, Complex.sub_conj]
  have h1 : normSq (1 - ζ) = (1 - ζ.re) ^ 2 + ζ.im ^ 2 := by
    rw [normSq_apply]; simp; ring
  rw [h1] at hN ⊢
  rw [normSq_apply]
  simp
  field_simp
  ring

lemma cay_im_pos {w : ℂ} (hw : 0 < w.im) {ζ : ℂ} (hζ : ζ ∈ ball (0:ℂ) 1) : 0 < (cay w ζ).im := by
  have hA := one_sub_ne_zero_of_mem_ball hζ
  rw [im_cay w ζ hA]
  have h1 : ‖ζ‖ < 1 := mem_ball_zero_iff.mp hζ
  have h2 : 0 < 1 - ‖ζ‖ ^ 2 := by nlinarith [norm_nonneg ζ]
  have h3 : 0 < ‖1 - ζ‖ ^ 2 := by positivity
  exact div_pos (mul_pos hw h2) h3

lemma cay_image {w : ℂ} (hw : 0 < w.im) : cay w '' ball 0 1 = {z : ℂ | 0 < z.im} := by
  ext z
  constructor
  · rintro ⟨ζ, hζ, rfl⟩
    exact cay_im_pos hw hζ
  · intro hz
    have hz' : 0 < z.im := hz
    have hden : z - conj w ≠ 0 := by
      intro h
      have := congrArg Complex.im h
      simp at this
      linarith
    have hc := sub_conj_ne_zero hw
    refine ⟨(z - w) / (z - conj w), ?_, ?_⟩
    · rw [mem_ball_zero_iff, norm_div, div_lt_one (norm_pos_iff.mpr hden)]
      rw [← sq_lt_sq₀ (norm_nonneg _) (norm_nonneg _), Complex.sq_norm, Complex.sq_norm,
        normSq_apply, normSq_apply]
      simp
      nlinarith
    · simp only [cay]
      have : 1 - (z - w) / (z - conj w) = (w - conj w) / (z - conj w) := by
        field_simp
        ring
      rw [this, div_div_cancel₀ hc]
      ring

lemma cay_injOn {w : ℂ} (hw : 0 < w.im) : InjOn (cay w) (ball 0 1) := by
  intro ζ₁ h₁ ζ₂ h₂ heq
  have hc := sub_conj_ne_zero hw
  have e₁ := one_sub_ne_zero_of_mem_ball h₁
  have e₂ := one_sub_ne_zero_of_mem_ball h₂
  simp only [cay, add_right_inj] at heq
  rw [div_eq_div_iff e₁ e₂] at heq
  have := mul_left_cancel₀ hc heq
  linear_combination this

lemma hasDerivAt_cay (w : ℂ) {ζ : ℂ} (hA : 1 - ζ ≠ 0) :
    HasDerivAt (cay w) ((w - conj w) / (1 - ζ) ^ 2) ζ := by
  have h := ((hasDerivAt_const ζ (w - conj w)).div ((hasDerivAt_id' ζ).const_sub 1) hA).const_add
    (conj w)
  have h' : HasDerivAt (cay w) ((0 * (1 - ζ) - (w - conj w) * -1) / (1 - ζ) ^ 2) ζ := h
  convert h' using 1
  ring

/-- The real derivative of `cay w` at `ζ`. -/
def cayD (w ζ : ℂ) : ℂ →L[ℝ] ℂ :=
  (ContinuousLinearMap.toSpanSingleton ℂ ((w - conj w) / (1 - ζ) ^ 2)).restrictScalars ℝ

lemma hasFDerivAt_cay (w : ℂ) {ζ : ℂ} (hA : 1 - ζ ≠ 0) : HasFDerivAt (cay w) (cayD w ζ) ζ := by
  exact (hasDerivAt_cay w hA).hasFDerivAt.restrictScalars ℝ

lemma det_cayD (w ζ : ℂ) : (cayD w ζ).det = normSq ((w - conj w) / (1 - ζ) ^ 2) := by
  simp [cayD, ContinuousLinearMap.det, LinearMap.det_restrictScalars, Algebra.norm_complex_eq]

lemma abs_det_cayD (w ζ : ℂ) : |(cayD w ζ).det| = ‖(w - conj w) / (1 - ζ) ^ 2‖ ^ 2 := by
  rw [det_cayD, abs_of_nonneg (normSq_nonneg _), Complex.normSq_eq_norm_sq]

lemma norm_cayDeriv_sq {w : ℂ} (hw : 0 < w.im) (ζ : ℂ) :
    ‖(w - conj w) / (1 - ζ) ^ 2‖ ^ 2 = 4 * w.im ^ 2 / (‖1 - ζ‖ ^ 2) ^ 2 := by
  rw [norm_div, norm_pow, Complex.sub_conj, norm_mul, norm_I, mul_one, Complex.norm_real,
    Real.norm_of_nonneg (by positivity)]
  ring

/-- Change of variables from the upper half plane (Lebesgue measure) to the unit disc. -/
theorem setIntegral_upper_eq_ball {w : ℂ} (hw : 0 < w.im) (g : ℂ → ℂ) :
    ∫ z in {z : ℂ | 0 < z.im}, g z
      = ∫ ζ in ball (0:ℂ) 1, ‖(w - conj w) / (1 - ζ) ^ 2‖ ^ 2 • g (cay w ζ) := by
  rw [← cay_image hw, integral_image_eq_integral_abs_det_fderiv_smul volume measurableSet_ball
    (f' := cayD w) (fun ζ hζ => (hasFDerivAt_cay w (one_sub_ne_zero_of_mem_ball hζ)).hasFDerivWithinAt)
    (cay_injOn hw) g]
  simp_rw [abs_det_cayD]

theorem integrableOn_upper_iff_ball {w : ℂ} (hw : 0 < w.im) (g : ℂ → ℂ) :
    IntegrableOn g {z : ℂ | 0 < z.im}
      ↔ IntegrableOn (fun ζ => ‖(w - conj w) / (1 - ζ) ^ 2‖ ^ 2 • g (cay w ζ)) (ball (0:ℂ) 1) := by
  rw [← cay_image hw, integrableOn_image_iff_integrableOn_abs_det_fderiv_smul volume
    measurableSet_ball (f' := cayD w)
    (fun ζ hζ => (hasFDerivAt_cay w (one_sub_ne_zero_of_mem_ball hζ)).hasFDerivWithinAt)
    (cay_injOn hw) g]
  simp_rw [abs_det_cayD]

/-! ## Part 3: integrals on `ℍ` (hyperbolic measure) as Lebesgue integrals -/

lemma measurable_density :
    Measurable (fun z : ℍ => ((1 / NNReal.mk z.im z.im_pos.le : ℝ≥0) ^ 2)) := by
  refine Continuous.measurable ?_
  refine .pow (.div₀ continuous_const ?_ ?_) _
  · exact UpperHalfPlane.continuous_im.subtype_mk _
  · exact fun x ↦ NNReal.ne_iff.mp x.im_ne_zero

lemma density_smul (F : ℍ → ℂ) (x : ℍ) :
    ((1 / NNReal.mk x.im x.im_pos.le : ℝ≥0) ^ 2) • F x
      = ((((x : ℂ)).im) ^ 2)⁻¹ • F (ofComplex (x : ℂ)) := by
  rw [ofComplex_apply, NNReal.smul_def]
  congr 1
  simp

theorem integral_eq_setIntegral (F : ℍ → ℂ) :
    ∫ z : ℍ, F z = ∫ z in {z : ℂ | 0 < z.im}, ((z.im) ^ 2)⁻¹ • F (ofComplex z) := by
  have hr : Set.range UpperHalfPlane.coe = {z : ℂ | 0 < z.im} := UpperHalfPlane.range_coe
  rw [volume_def, integral_withDensity_eq_integral_smul measurable_density,
    ← hr, ← measurableEmbedding_coe.map_comap volume,
    measurableEmbedding_coe.integral_map]
  simp_rw [density_smul]

theorem integrable_iff_integrableOn (F : ℍ → ℂ) :
    Integrable F ↔ IntegrableOn (fun z : ℂ => ((z.im) ^ 2)⁻¹ • F (ofComplex z)) {z : ℂ | 0 < z.im} := by
  have hr : Set.range UpperHalfPlane.coe = {z : ℂ | 0 < z.im} := UpperHalfPlane.range_coe
  rw [volume_def, integrable_withDensity_iff_integrable_smul measurable_density, IntegrableOn,
    ← hr, ← measurableEmbedding_coe.map_comap volume,
    measurableEmbedding_coe.integrable_map_iff]
  have : ((fun z : ℂ => ((z.im) ^ 2)⁻¹ • F (ofComplex z)) ∘ UpperHalfPlane.coe)
      = fun x => ((1 / NNReal.mk x.im x.im_pos.le : ℝ≥0) ^ 2) • F x := by
    funext x
    rw [Function.comp_apply, density_smul]
  rw [this]

/-! ## Part 4: the integrand in disc coordinates -/

lemma integrand_cay {w : ℂ} (hw : 0 < w.im) {ζ : ℂ} (hζ : ζ ∈ ball (0:ℂ) 1) (n : ℕ) (a : ℂ) :
    ‖(w - conj w) / (1 - ζ) ^ 2‖ ^ 2 • (((cay w ζ).im ^ 2)⁻¹ •
      (a * conj (((cay w ζ - conj w) ^ (n + 2))⁻¹) * ((cay w ζ).im : ℂ) ^ (n + 2)))
    = (4 * (Complex.I / 2) ^ (n + 2)) * ((1 - ‖ζ‖ ^ 2) ^ (n:ℝ) • (a / (1 - ζ) ^ (n + 2))) := by
  have hA : 1 - ζ ≠ 0 := one_sub_ne_zero_of_mem_ball hζ
  have hB : conj (1 - ζ) ≠ 0 := (map_ne_zero _).mpr hA
  have h1 : ‖ζ‖ < 1 := mem_ball_zero_iff.mp hζ
  have hs : 0 < 1 - ‖ζ‖ ^ 2 := by nlinarith [norm_nonneg ζ]
  have hAB : ((‖1 - ζ‖ : ℝ) : ℂ) ^ 2 = (1 - ζ) * conj (1 - ζ) := (Complex.mul_conj' _).symm
  have hI : (-2 * Complex.I) * (Complex.I / 2) = 1 := by
    ring_nf
    rw [Complex.I_sq]
    ring
  have hI' : Complex.I / 2 = (-2 * Complex.I)⁻¹ := eq_inv_of_mul_eq_one_right hI
  have h2Complex.I : (-2 * Complex.I) ≠ 0 := by
    intro h
    rw [h, zero_mul] at hI
    exact zero_ne_one hI
  rw [norm_cayDeriv_sq hw, im_cay w ζ hA, cay_sub_conj, Real.rpow_natCast, hI']
  have hconj : conj ((w - conj w) / (1 - ζ)) = (-2 * Complex.I) * (w.im : ℂ) / conj (1 - ζ) := by
    rw [map_div₀, map_sub, Complex.conj_conj, ← neg_sub, Complex.sub_conj]
    push_cast
    ring
  rw [map_inv₀, map_pow, hconj]
  set v := w.im with hv
  set s := 1 - ‖ζ‖ ^ 2 with hs_def
  have hv0 : (v : ℂ) ≠ 0 := ofReal_ne_zero.mpr hw.ne'
  have hs0 : (s : ℂ) ≠ 0 := ofReal_ne_zero.mpr hs.ne'
  simp only [Complex.real_smul]
  push_cast
  rw [hAB]
  generalize hB' : conj (1 - ζ) = B at *
  generalize hA' : 1 - ζ = A at *
  have key : ((-2 * Complex.I * (v:ℂ) / B) ^ (n + 2))⁻¹ * ((v:ℂ) * s / (A * B)) ^ (n + 2)
      = ((s:ℂ) / (-2 * Complex.I * A)) ^ (n + 2) := by
    rw [← inv_pow, ← mul_pow]
    congr 1
    field_simp
  rw [mul_assoc a, key, div_pow (s:ℂ) (-2 * Complex.I * A) (n + 2),
    mul_pow (-2 * Complex.I) A (n + 2), pow_add (s:ℂ) n 2, inv_pow]
  field_simp


/-! ## Part 5: the reproducing formula -/

/-- The Bergman-Petersson constant `C_k = 4 π i^k / ((k - 1) 2^k) = π i^k / ((k - 1) 2^(k-2))`. -/
def bergmanConst (k : ℕ) : ℂ := 4 * π * Complex.I ^ k / (((k:ℂ) - 1) * 2 ^ k)

/-- **Reproducing formula.** For `k ≥ 2`, `f` holomorphic on `ℍ` and `w ∈ ℍ`, if the integrand is
integrable for the invariant measure `dx dy / y^2` then
`∫_ℍ f(z) conj((z - conj w)^(-k)) y^k dμ(z) = C_k f(w)`. -/
theorem bergman_reproducing {k : ℕ} (hk : 2 ≤ k) {f : ℍ → ℂ}
    (hf : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f) (w : ℍ)
    (hint : Integrable (fun z : ℍ => f z * conj ((((z:ℂ) - conj (w:ℂ)) ^ k)⁻¹) * ((z.im : ℂ)) ^ k)) :
    ∫ z : ℍ, f z * conj ((((z:ℂ) - conj (w:ℂ)) ^ k)⁻¹) * ((z.im : ℂ)) ^ k = bergmanConst k * f w := by
  obtain ⟨n, rfl⟩ : ∃ n, k = n + 2 := ⟨k - 2, by omega⟩
  have hw : 0 < (w:ℂ).im := w.im_pos
  set F : ℍ → ℂ := fun z => f z * conj ((((z:ℂ) - conj (w:ℂ)) ^ (n + 2))⁻¹) * ((z.im : ℂ)) ^ (n + 2)
    with hF
  set G : ℂ → ℂ := fun ζ => f (ofComplex (cay w ζ)) / (1 - ζ) ^ (n + 2) with hG
  have hGd : DifferentiableOn ℂ G (ball 0 1) := by
    have h1 : DifferentiableOn ℂ (f ∘ ofComplex) {z : ℂ | 0 < z.im} :=
      UpperHalfPlane.mdifferentiable_iff.mp hf
    have h2 : DifferentiableOn ℂ (cay w) (ball 0 1) := fun ζ hζ =>
      (hasDerivAt_cay w (one_sub_ne_zero_of_mem_ball hζ)).differentiableAt.differentiableWithinAt
    have h3 : DifferentiableOn ℂ (fun ζ => (f ∘ ofComplex) (cay w ζ)) (ball 0 1) :=
      h1.comp h2 (fun ζ hζ => cay_im_pos hw hζ)
    exact h3.div (by fun_prop) (fun ζ hζ => pow_ne_zero _ (one_sub_ne_zero_of_mem_ball hζ))
  have hpt : ∀ ζ ∈ ball (0:ℂ) 1, ‖((w:ℂ) - conj (w:ℂ)) / (1 - ζ) ^ 2‖ ^ 2 •
      (((cay w ζ).im ^ 2)⁻¹ • F (ofComplex (cay w ζ)))
      = (4 * (Complex.I / 2) ^ (n + 2)) * ((1 - ‖ζ‖ ^ 2) ^ (n:ℝ) • G ζ) := by
    intro ζ hζ
    simp only [hF, hG]
    rw [ofComplex_apply_of_im_pos (cay_im_pos hw hζ)]
    exact integrand_cay hw hζ n _
  have hc0 : (4 * (Complex.I / 2) ^ (n + 2)) ≠ 0 :=
    mul_ne_zero (by norm_num : (4:ℂ) ≠ 0) (pow_ne_zero _ (div_ne_zero Complex.I_ne_zero two_ne_zero))
  have hint' : IntegrableOn (fun ζ => (1 - ‖ζ‖ ^ 2) ^ (n:ℝ) • G ζ) (ball 0 1) := by
    have h1 := (integrableOn_upper_iff_ball hw _).mp ((integrable_iff_integrableOn F).mp hint)
    have h2 := h1.congr_fun hpt measurableSet_ball
    refine IntegrableOn.congr_fun (Integrable.const_mul h2 (4 * (Complex.I / 2) ^ (n + 2))⁻¹)
      (fun ζ _ => ?_) measurableSet_ball
    rw [← mul_assoc, inv_mul_cancel₀ hc0, one_mul]
  rw [integral_eq_setIntegral, setIntegral_upper_eq_ball hw,
    setIntegral_congr_fun measurableSet_ball hpt, integral_const_mul,
    integral_ball_smul (by linarith [(Nat.cast_nonneg n : (0:ℝ) ≤ n)]) hGd hint']
  have hG0 : G 0 = f w := by simp [hG, cay_zero, ofComplex_apply]
  rw [hG0, bergmanConst, Complex.real_smul, div_pow]
  have hn1 : ((n:ℂ) + 1) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
  rw [show (((n + 2 : ℕ) : ℂ) - 1) = (n:ℂ) + 1 by push_cast; ring]
  push_cast
  field_simp

/-! ## Part 6: the absolutely integrable kernel `y^σ / |z - conj w|^(2σ)` (`σ > 1`) -/

lemma integrableOn_ball_weight {s : ℝ} (hs : -1 < s) :
    IntegrableOn (fun ζ : ℂ => (1 - ‖ζ‖ ^ 2) ^ s) (ball (0:ℂ) 1) := by
  refine (integrableOn_fun_norm_addHaar (volume : Measure ℂ) (f := fun y : ℝ => (1 - y ^ 2) ^ s)).2 ?_
  rw [Complex.finrank_real_complex]
  simpa using integrableOn_weight hs

/-- `∫_{|ζ|<1} (1 - |ζ|^2)^s = π / (s + 1)` for `s > -1`. -/
lemma integral_ball_weight {s : ℝ} (hs : -1 < s) :
    ∫ ζ in ball (0:ℂ) 1, (1 - ‖ζ‖ ^ 2) ^ s = π / (s + 1) := by
  have hint : IntegrableOn (fun ζ : ℂ => (1 - ‖ζ‖ ^ 2) ^ s • (fun _ : ℂ => (1:ℂ)) ζ) (ball 0 1) := by
    have h0 : IntegrableOn (fun ζ : ℂ => (((1 - ‖ζ‖ ^ 2) ^ s : ℝ) : ℂ)) (ball 0 1) :=
      Integrable.ofReal (integrableOn_ball_weight hs)
    refine h0.congr_fun (fun ζ _ => ?_) measurableSet_ball
    simp [Complex.real_smul]
  have h := integral_ball_smul hs (differentiableOn_const (1:ℂ)) hint
  simp only [Complex.real_smul, mul_one] at h
  rw [integral_complex_ofReal] at h
  exact_mod_cast h

/-- The kernel `y^σ / |z - conj w|^(2σ)` on `ℂ` (used on `ℍ` through `kernel`). -/
def kernelC (w : ℂ) (σ : ℝ) (z : ℂ) : ℝ := z.im ^ σ / ‖z - conj w‖ ^ (2 * σ)

/-- The kernel `y^σ / |z - conj w|^(2σ)` on `ℍ`. For `σ = k/2` it dominates the reproducing
integrand of any `f` with `|f(z)| y^(k/2)` bounded (cusp forms). -/
def kernel (w : ℍ) (σ : ℝ) (z : ℍ) : ℝ := kernelC (w:ℂ) σ (z:ℂ)

lemma kernel_apply (w : ℍ) (σ : ℝ) (z : ℍ) :
    kernel w σ z = z.im ^ σ / ‖(z:ℂ) - conj (w:ℂ)‖ ^ (2 * σ) := rfl

lemma kernel_disc_real {v s A σ : ℝ} (hv : 0 < v) (hs : 0 < s) (hA : 0 < A) :
    4 * v ^ 2 / (A ^ 2) ^ 2 * (((v * s / A ^ 2) ^ 2)⁻¹ * ((v * s / A ^ 2) ^ σ / (2 * v / A) ^ (2 * σ)))
      = 4 * ((4 * v) ^ σ)⁻¹ * (s ^ σ / s ^ 2) := by
  rw [Real.rpow_mul (x := 2 * v / A) (by positivity) 2 σ, Real.rpow_two,
    ← Real.div_rpow (x := v * s / A ^ 2) (y := (2 * v / A) ^ 2) (by positivity) (by positivity)]
  have e : v * s / A ^ 2 / (2 * v / A) ^ 2 = s / (4 * v) := by
    field_simp
    ring
  rw [e, Real.div_rpow hs.le (by positivity)]
  have h1 : 0 < (4 * v) ^ σ := Real.rpow_pos_of_pos (by positivity) σ
  have h2 : 0 < s ^ σ := Real.rpow_pos_of_pos hs σ
  field_simp

lemma kernel_cay {w : ℂ} (hw : 0 < w.im) {ζ : ℂ} (hζ : ζ ∈ ball (0:ℂ) 1) (σ : ℝ) :
    ‖(w - conj w) / (1 - ζ) ^ 2‖ ^ 2 * (((cay w ζ).im ^ 2)⁻¹ * kernelC w σ (cay w ζ))
      = 4 * ((4 * w.im) ^ σ)⁻¹ * (1 - ‖ζ‖ ^ 2) ^ (σ - 2) := by
  have hA : 1 - ζ ≠ 0 := one_sub_ne_zero_of_mem_ball hζ
  have h1 : ‖ζ‖ < 1 := mem_ball_zero_iff.mp hζ
  have hs : 0 < 1 - ‖ζ‖ ^ 2 := by nlinarith [norm_nonneg ζ]
  have hA' : 0 < ‖1 - ζ‖ := norm_pos_iff.mpr hA
  have hn : ‖cay w ζ - conj w‖ = 2 * w.im / ‖1 - ζ‖ := by
    rw [cay_sub_conj, norm_div, Complex.sub_conj, norm_mul, norm_I, mul_one, Complex.norm_real,
      Real.norm_of_nonneg (by positivity)]
  rw [kernelC, hn, im_cay w ζ hA, norm_cayDeriv_sq hw, Real.rpow_sub hs, Real.rpow_two]
  exact kernel_disc_real hw hs hA'

lemma kernel_pt (w : ℍ) (σ : ℝ) {ζ : ℂ} (hζ : ζ ∈ ball (0:ℂ) 1) :
    ‖((w:ℂ) - conj (w:ℂ)) / (1 - ζ) ^ 2‖ ^ 2 •
      (((cay w ζ).im ^ 2)⁻¹ • ((kernel w σ (ofComplex (cay w ζ)) : ℝ) : ℂ))
    = ((4 * ((4 * (w:ℂ).im) ^ σ)⁻¹ * (1 - ‖ζ‖ ^ 2) ^ (σ - 2) : ℝ) : ℂ) := by
  have hw : 0 < (w:ℂ).im := w.im_pos
  rw [ofComplex_apply_of_im_pos (cay_im_pos hw hζ), ← kernel_cay hw hζ σ, Complex.real_smul,
    Complex.real_smul, ← Complex.ofReal_mul, ← Complex.ofReal_mul]
  rfl

/-- **Kernel integrability.** For `σ > 1`, `y^σ / |z - conj w|^(2σ)` is integrable on `ℍ` for the
invariant measure `dx dy / y^2`. -/
theorem integrable_kernel (w : ℍ) {σ : ℝ} (hσ : 1 < σ) : Integrable (kernel w σ) := by
  have hw : 0 < (w:ℂ).im := w.im_pos
  have hC : Integrable (fun z : ℍ => ((kernel w σ z : ℝ) : ℂ)) := by
    rw [integrable_iff_integrableOn, integrableOn_upper_iff_ball hw]
    refine IntegrableOn.congr_fun ?_ (fun ζ hζ => (kernel_pt w σ hζ).symm) measurableSet_ball
    exact Integrable.ofReal ((integrableOn_ball_weight (s := σ - 2) (by linarith)).const_mul _)
  simpa using hC.re

/-- **Kernel integral.** For `σ > 1`,
`∫_ℍ y^σ / |z - conj w|^(2σ) dμ(z) = 4 π / ((σ - 1) (4 Im w)^σ)`. -/
theorem integral_kernel (w : ℍ) {σ : ℝ} (hσ : 1 < σ) :
    ∫ z : ℍ, kernel w σ z = 4 * π / ((σ - 1) * (4 * w.im) ^ σ) := by
  have hw : 0 < (w:ℂ).im := w.im_pos
  have h : ∫ z : ℍ, ((kernel w σ z : ℝ) : ℂ) = ((4 * π / ((σ - 1) * (4 * w.im) ^ σ) : ℝ) : ℂ) := by
    rw [integral_eq_setIntegral, setIntegral_upper_eq_ball hw,
      setIntegral_congr_fun measurableSet_ball (fun ζ hζ => kernel_pt w σ hζ), integral_complex_ofReal,
      integral_const_mul, integral_ball_weight (by linarith)]
    congr 1
    have e : (w:ℂ).im = w.im := rfl
    rw [e, show σ - 2 + 1 = σ - 1 by ring]
    have h1 : 0 < (4 * w.im) ^ σ := Real.rpow_pos_of_pos (by linarith [w.im_pos]) σ
    have h2 : σ - 1 ≠ 0 := by linarith
    field_simp
  rw [integral_complex_ofReal] at h
  exact_mod_cast h

/-- The kernel for `σ = k/2`, `k ∈ ℕ`: `y^(k/2) / |z - conj w|^k`. -/
lemma kernel_half_nat (w : ℍ) (k : ℕ) (z : ℍ) :
    kernel w ((k:ℝ) / 2) z = z.im ^ ((k:ℝ) / 2) / ‖(z:ℂ) - conj (w:ℂ)‖ ^ k := by
  rw [kernel_apply, show 2 * ((k:ℝ) / 2) = (k:ℝ) by ring, Real.rpow_natCast]

/-- For `k ≥ 3`, `y^(k/2) / |z - conj w|^k` is integrable on `ℍ` for `dx dy / y^2`. -/
theorem integrable_kernel_nat (w : ℍ) {k : ℕ} (hk : 3 ≤ k) :
    Integrable (fun z : ℍ => z.im ^ ((k:ℝ) / 2) / ‖(z:ℂ) - conj (w:ℂ)‖ ^ k) := by
  have hk' : (3:ℝ) ≤ k := by exact_mod_cast hk
  have h := integrable_kernel w (σ := (k:ℝ) / 2) (by linarith)
  refine h.congr (Eventually.of_forall fun z => ?_)
  exact kernel_half_nat w k z

/-- For `k ≥ 3`, `∫_ℍ y^(k/2) / |z - conj w|^k dμ(z) = 8 π / ((k - 2) 2^k (Im w)^(k/2))`. -/
theorem integral_kernel_nat (w : ℍ) {k : ℕ} (hk : 3 ≤ k) :
    ∫ z : ℍ, z.im ^ ((k:ℝ) / 2) / ‖(z:ℂ) - conj (w:ℂ)‖ ^ k
      = 8 * π / (((k:ℝ) - 2) * 2 ^ k * w.im ^ ((k:ℝ) / 2)) := by
  have hk' : (3:ℝ) ≤ k := by exact_mod_cast hk
  have hv : 0 < w.im := w.im_pos
  simp_rw [← kernel_half_nat w k]
  rw [integral_kernel w (by linarith)]
  have e4 : (4 * w.im) ^ ((k:ℝ) / 2) = 2 ^ k * w.im ^ ((k:ℝ) / 2) := by
    rw [Real.mul_rpow (by norm_num) hv.le]
    congr 1
    rw [show (4:ℝ) = 2 ^ (2:ℝ) by norm_num, ← Real.rpow_mul (by norm_num),
      show (2:ℝ) * ((k:ℝ) / 2) = (k:ℝ) by ring, Real.rpow_natCast]
  rw [e4]
  have h1 : 0 < w.im ^ ((k:ℝ) / 2) := Real.rpow_pos_of_pos hv _
  have h2 : (k:ℝ) - 2 ≠ 0 := by linarith
  have h3 : (k:ℝ) / 2 - 1 ≠ 0 := by linarith
  field_simp
  ring

lemma coe_sub_conj_ne_zero (z w : ℍ) : (z:ℂ) - conj (w:ℂ) ≠ 0 := by
  intro h
  have h' := congrArg Complex.im h
  have hz : 0 < (z:ℂ).im := z.im_pos
  have hw : 0 < (w:ℂ).im := w.im_pos
  simp only [sub_im, conj_im, sub_neg_eq_add, zero_im] at h'
  linarith

/-- **Integrability for bounded weight-`k` functions.** If `k ≥ 3` and `|f(z)| ≤ C / y^(k/2)`
(the form of Mathlib's `CuspFormClass.exists_bound`) then the reproducing integrand is integrable. -/
theorem integrable_reproducing_of_bound {k : ℕ} (hk : 3 ≤ k) {f : ℍ → ℂ}
    (hf : Continuous f) (w : ℍ) {C : ℝ} (hC : ∀ z : ℍ, ‖f z‖ ≤ C / z.im ^ ((k:ℝ) / 2)) :
    Integrable (fun z : ℍ => f z * conj ((((z:ℂ) - conj (w:ℂ)) ^ k)⁻¹) * ((z.im : ℂ)) ^ k) := by
  refine Integrable.mono' ((integrable_kernel_nat w hk).const_mul C) ?_ (Eventually.of_forall fun z => ?_)
  · have h1 : Continuous (fun z : ℍ => (z : ℂ)) := UpperHalfPlane.continuous_coe
    have h2 : Continuous (fun z : ℍ => ((z.im : ℝ) : ℂ)) :=
      Complex.continuous_ofReal.comp UpperHalfPlane.continuous_im
    have h3 : Continuous (fun z : ℍ => conj ((((z:ℂ) - conj (w:ℂ)) ^ k)⁻¹)) :=
      Complex.continuous_conj.comp (((h1.sub continuous_const).pow k).inv₀
        (fun z => pow_ne_zero _ (coe_sub_conj_ne_zero z w)))
    exact ((hf.mul h3).mul (h2.pow k)).aestronglyMeasurable
  · have hy : 0 < z.im := z.im_pos
    have hY : 0 < z.im ^ ((k:ℝ) / 2) := Real.rpow_pos_of_pos hy _
    have hfz : ‖f z‖ * z.im ^ ((k:ℝ) / 2) ≤ C := (le_div_iff₀ hY).mp (hC z)
    have hYY : z.im ^ k = z.im ^ ((k:ℝ) / 2) * z.im ^ ((k:ℝ) / 2) := by
      rw [← Real.rpow_add hy, ← Real.rpow_natCast]
      congr 1
      ring
    rw [norm_mul, norm_mul, Complex.norm_conj, norm_inv, norm_pow, norm_pow, Complex.norm_real,
      Real.norm_of_nonneg hy.le, hYY]
    calc ‖f z‖ * (‖(z:ℂ) - conj (w:ℂ)‖ ^ k)⁻¹ * (z.im ^ ((k:ℝ) / 2) * z.im ^ ((k:ℝ) / 2))
        = (‖f z‖ * z.im ^ ((k:ℝ) / 2)) * (z.im ^ ((k:ℝ) / 2) / ‖(z:ℂ) - conj (w:ℂ)‖ ^ k) := by ring
      _ ≤ C * (z.im ^ ((k:ℝ) / 2) / ‖(z:ℂ) - conj (w:ℂ)‖ ^ k) :=
        mul_le_mul_of_nonneg_right hfz (div_nonneg hY.le (pow_nonneg (norm_nonneg _) _))

/-- **Reproducing formula for bounded weight-`k` functions** (`k ≥ 3`, e.g. cusp forms via
`CuspFormClass.exists_bound`): `∫_ℍ f(z) conj((z - conj w)^(-k)) y^k dμ(z) = C_k f(w)`. -/
theorem bergman_reproducing_of_bound {k : ℕ} (hk : 3 ≤ k) {f : ℍ → ℂ}
    (hf : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f) (w : ℍ) {C : ℝ}
    (hC : ∀ z : ℍ, ‖f z‖ ≤ C / z.im ^ ((k:ℝ) / 2)) :
    ∫ z : ℍ, f z * conj ((((z:ℂ) - conj (w:ℂ)) ^ k)⁻¹) * ((z.im : ℂ)) ^ k = bergmanConst k * f w :=
  bergman_reproducing (by omega) hf w (integrable_reproducing_of_bound hk hf.continuous w hC)

end RamanujanPetersson.Bergman


