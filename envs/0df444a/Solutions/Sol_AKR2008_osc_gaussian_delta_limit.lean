-- Prove2me | solution 1 for AKR2008.osc_gaussian_delta_limit
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-04T14:41:32.588291+00:00
-- url     : https://prove2.me/submissions/6e73d46c-8e3c-4097-8a1b-f3816c84f55f

import Mathlib
import Definitions.Def_AKR2008_HybridDefs

open ProbabilityTheory MeasureTheory NNReal in
lemma osc2434_pdf (ω τ w x t : ℝ) (v : ℝ≥0) (hv : (v : ℝ) = Real.cos (ω * t) ^ 2 / τ)
    (hτ : 0 < τ) (hcos : Real.cos (ω * t) ≠ 0) :
    AKR2008.oscP ω τ w x t = gaussianPDFReal (w * Real.cos (ω * t)) v x := by
  have hc2 : 0 < Real.cos (ω * t) ^ 2 := by positivity
  unfold AKR2008.oscP gaussianPDFReal
  rw [hv]
  congr 1
  · rw [← Real.sqrt_inv]
    congr 1
    field_simp
  · congr 1
    field_simp

open ProbabilityTheory MeasureTheory NNReal in
lemma osc2434_rewrite (ω τ w t : ℝ) (hτ : 0 < τ) (hcos : Real.cos (ω * t) ≠ 0)
    (φ : BoundedContinuousFunction ℝ ℝ) (v0 : ℝ≥0) (hv0 : (v0 : ℝ) = τ⁻¹) :
    ∫ x, AKR2008.oscP ω τ w x t * φ x
      = ∫ y, φ (Real.cos (ω * t) * y) ∂(gaussianReal w v0) := by
  set c := Real.cos (ω * t) with hc
  set V : ℝ≥0 := NNReal.mk (c ^ 2) (sq_nonneg _) * v0 with hV
  have hVr : (V : ℝ) = c ^ 2 / τ := by
    rw [hV, NNReal.coe_mul, hv0]
    simp [div_eq_mul_inv]
  have hc2 : 0 < c ^ 2 := by positivity
  have hVne : V ≠ 0 := by
    intro h
    have : (V : ℝ) = 0 := by rw [h]; rfl
    rw [hVr] at this
    have : 0 < c ^ 2 / τ := by positivity
    linarith
  have key : ∀ x, AKR2008.oscP ω τ w x t * φ x = gaussianPDFReal (c * w) V x • φ x := by
    intro x
    rw [osc2434_pdf ω τ w x t V hVr hτ hcos, smul_eq_mul, mul_comm w c]
  simp_rw [key]
  rw [← integral_gaussianReal_eq_integral_smul hVne, hV, ← gaussianReal_map_const_mul c]
  rw [integral_map (measurable_const_mul c).aemeasurable
    φ.continuous.aestronglyMeasurable]

open ProbabilityTheory MeasureTheory NNReal in
lemma osc2434_lim (w : ℝ) (v0 : ℝ≥0) (φ : BoundedContinuousFunction ℝ ℝ) :
    Filter.Tendsto (fun c : ℝ => ∫ y, φ (c * y) ∂(gaussianReal w v0))
      (nhds 0) (nhds (φ 0)) := by
  have h0 : ∫ _y, φ 0 ∂(gaussianReal w v0) = φ 0 := by
    simp
  rw [← h0]
  refine tendsto_integral_filter_of_dominated_convergence (fun _ => ‖φ‖) ?_ ?_ ?_ ?_
  · exact Filter.Eventually.of_forall fun c =>
      (φ.continuous.comp (continuous_const_mul c)).aestronglyMeasurable
  · exact Filter.Eventually.of_forall fun c =>
      Filter.Eventually.of_forall fun y => φ.norm_coe_le_norm _
  · exact integrable_const _
  · refine Filter.Eventually.of_forall fun y => ?_
    have : Filter.Tendsto (fun c : ℝ => c * y) (nhds 0) (nhds 0) := by
      have := (continuous_mul_const y).tendsto 0
      simpa using this
    exact (φ.continuous.tendsto 0).comp this

open AKR2008 in
theorem solution (ω τ w : ℝ) (hω : 0 < ω) (hτ : 0 < τ) (n : ℤ)
    (φ : BoundedContinuousFunction ℝ ℝ) :
    Filter.Tendsto (fun t => ∫ x, oscP ω τ w x t * φ x)
      (nhdsWithin ((2 * n + 1) * Real.pi / (2 * ω)) {((2 * n + 1) * Real.pi / (2 * ω))}ᶜ)
      (nhds (φ 0)) := by
  set t0 := (2 * n + 1) * Real.pi / (2 * ω) with ht0
  have hcos0 : Real.cos (ω * t0) = 0 := by
    rw [Real.cos_eq_zero_iff]
    refine ⟨n, ?_⟩
    rw [ht0]
    field_simp
  have hsin : Real.sin (ω * t0) ≠ 0 := by
    intro h
    have := Real.sin_sq_add_cos_sq (ω * t0)
    rw [h, hcos0] at this
    norm_num at this
  have hder : HasDerivAt (fun t => Real.cos (ω * t)) (-Real.sin (ω * t0) * ω) t0 := by
    have h1 : HasDerivAt (fun s => ω * s) ω t0 := by
      simpa using (hasDerivAt_id t0).const_mul ω
    exact (Real.hasDerivAt_cos (ω * t0)).comp t0 h1
  have hne : ∀ᶠ t in nhdsWithin t0 {t0}ᶜ, Real.cos (ω * t) ≠ 0 :=
    hder.eventually_ne (c := 0) (by
      apply mul_ne_zero (neg_ne_zero.mpr hsin) hω.ne')
  have hc : Filter.Tendsto (fun t => Real.cos (ω * t)) (nhdsWithin t0 {t0}ᶜ) (nhds 0) := by
    have := (hder.continuousAt.tendsto)
    rw [hcos0] at this
    exact this.mono_left nhdsWithin_le_nhds
  have hlim := (osc2434_lim w τ⁻¹.toNNReal φ).comp hc
  refine hlim.congr' ?_
  filter_upwards [hne] with t ht
  exact (osc2434_rewrite ω τ w t hτ ht φ τ⁻¹.toNNReal
    (Real.coe_toNNReal _ (inv_nonneg.mpr hτ.le))).symm
