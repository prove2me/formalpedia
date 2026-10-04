-- Prove2me | solution 1 for AKR2008.osc_gaussian_energy
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-03T12:46:23.716196+00:00
-- url     : https://prove2.me/submissions/14737456-e202-413e-8918-5e3fec38bc66

import Mathlib
import Definitions.Def_AKR2008_HybridDefs

open ProbabilityTheory MeasureTheory NNReal in
lemma osc0573_second_moment (μ : ℝ) (v : ℝ≥0) :
    ∫ x, x ^ 2 ∂(gaussianReal μ v) = (v : ℝ) + μ ^ 2 := by
  have h := variance_eq_sub (memLp_id_gaussianReal (μ := μ) (v := v) 2)
  rw [variance_id_gaussianReal] at h
  have hm : ∫ x, id x ∂(gaussianReal μ v) = μ := integral_id_gaussianReal
  have h2 : ∫ x, (id ^ 2 : ℝ → ℝ) x ∂(gaussianReal μ v) = ∫ x, x ^ 2 ∂(gaussianReal μ v) := by
    rfl
  rw [hm, h2] at h
  linarith

lemma osc0573_deriv (ω x t : ℝ) (hcos : Real.cos (ω * t) ≠ 0) :
    deriv (fun s => AKR2008.oscS ω x s) t = -(ω * x ^ 2 / 2) * (ω * (1 / Real.cos (ω * t) ^ 2)) := by
  have h1 : HasDerivAt (fun s => ω * s) ω t := by
    simpa using (hasDerivAt_id t).const_mul ω
  have h2 : HasDerivAt (fun s => Real.tan (ω * s)) (1 / Real.cos (ω * t) ^ 2 * ω) t :=
    (Real.hasDerivAt_tan hcos).comp t h1
  have h3 := h2.const_mul (-(ω * x ^ 2 / 2))
  unfold AKR2008.oscS
  rw [h3.deriv]
  ring

open ProbabilityTheory MeasureTheory NNReal in
lemma osc0573_pdf (ω τ w x t : ℝ) (v : ℝ≥0) (hv : (v : ℝ) = Real.cos (ω * t) ^ 2 / τ)
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
theorem solution (ω τ w t : ℝ) (hτ : 0 < τ) (hcos : Real.cos (ω * t) ≠ 0) :
    ∫ x, AKR2008.oscP ω τ w x t * (-deriv (fun s => AKR2008.oscS ω x s) t) = ω ^ 2 * (τ⁻¹ + w ^ 2) / 2 := by
  have hc2 : 0 < Real.cos (ω * t) ^ 2 := by positivity
  have hpos : 0 < Real.cos (ω * t) ^ 2 / τ := by positivity
  have hvr : ((Real.cos (ω * t) ^ 2 / τ).toNNReal : ℝ) = Real.cos (ω * t) ^ 2 / τ :=
    Real.coe_toNNReal _ hpos.le
  have hv0 : (Real.cos (ω * t) ^ 2 / τ).toNNReal ≠ 0 := by
    intro h
    rw [h] at hvr
    simp at hvr
    linarith
  have key : ∀ x, AKR2008.oscP ω τ w x t * (-deriv (fun s => AKR2008.oscS ω x s) t)
      = gaussianPDFReal (w * Real.cos (ω * t)) (Real.cos (ω * t) ^ 2 / τ).toNNReal x •
          ((ω ^ 2 / (2 * Real.cos (ω * t) ^ 2)) * x ^ 2) := by
    intro x
    rw [osc0573_pdf ω τ w x t _ hvr hτ hcos, osc0573_deriv ω x t hcos, smul_eq_mul]
    field_simp
  simp_rw [key]
  rw [← integral_gaussianReal_eq_integral_smul hv0, integral_const_mul, osc0573_second_moment, hvr]
  field_simp
