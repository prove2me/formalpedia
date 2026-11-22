-- Prove2me | solution 1 for ApproxIdentity.norm_haarConv_sub_le_of_leftUniformContinuous
-- status  : ACCEPTED   (prove)
-- author  : @RSoulat
-- created : 2026-11-22T19:03:05.372819+00:00
-- url     : https://prove2.me/submissions/63bfb09f-29b4-461d-8fdb-471cb78d9e3a

import Mathlib

open MeasureTheory Topology
open scoped ENNReal

set_option autoImplicit false

theorem solution {G : Type*} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [LocallyCompactSpace G] [T2Space G] [MeasurableSpace G] [BorelSpace G]
    (μ : Measure G) [μ.IsHaarMeasure] (f : G → ℂ)
    (hf : ∀ δ : ℝ, 0 < δ → ∃ V ∈ 𝓝 (1 : G), ∀ y ∈ V, ∀ x : G, ‖f (y⁻¹ * x) - f x‖ ≤ δ)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ U ∈ 𝓝 (1 : G), ∀ ψ : G → ℝ, Continuous ψ → HasCompactSupport ψ → (∀ x, 0 ≤ ψ x) →
      tsupport ψ ⊆ U → ∫ x, ψ x ∂μ = 1 →
      ∀ x : G, ‖(∫ y, (ψ y : ℂ) * f (y⁻¹ * x) ∂μ) - f x‖ ≤ ε := by
  have hcf : Continuous f := by
    refine continuous_iff_continuousAt.mpr fun x => Metric.tendsto_nhds.mpr fun r hr => ?_
    obtain ⟨V, hV, hcontrol⟩ := hf (r / 2) (half_pos hr)
    have hTranslate : Filter.Tendsto (fun z : G => x * z⁻¹) (𝓝 x) (𝓝 (1 : G)) :=
      (continuous_const.mul continuous_inv).tendsto' x 1 (by simp)
    filter_upwards [hTranslate hV] with z hz
    have h := hcontrol (x * z⁻¹) hz x
    rw [mul_inv_rev, inv_inv, mul_assoc, inv_mul_cancel, mul_one] at h
    rw [dist_eq_norm]
    exact h.trans_lt (half_lt_self hr)
  obtain ⟨U, hU, hcontrol⟩ := hf ε hε
  refine ⟨U, hU, ?_⟩
  intro ψ hψ hcψ hnψ hsupport hmass x
  have hψC : Continuous (fun y => (ψ y : ℂ)) := Complex.continuous_ofReal.comp hψ
  have hcψC : HasCompactSupport (fun y => (ψ y : ℂ)) := hcψ.comp_left Complex.ofReal_zero
  have hconv : Integrable (fun y => (ψ y : ℂ) * f (y⁻¹ * x)) μ :=
    (hψC.mul (hcf.comp (continuous_inv.mul continuous_const))).integrable_of_hasCompactSupport
      hcψC.mul_right
  have hconst : Integrable (fun y => (ψ y : ℂ) * f x) μ :=
    (hψC.integrable_of_hasCompactSupport hcψC).mul_const _
  have hsub : (∫ y, (ψ y : ℂ) * (f (y⁻¹ * x) - f x) ∂μ) =
      (∫ y, (ψ y : ℂ) * f (y⁻¹ * x) ∂μ) - f x := by
    simp only [mul_sub]
    rw [integral_sub hconv hconst, integral_mul_const, integral_complex_ofReal, hmass,
      Complex.ofReal_one, one_mul]
  rw [← hsub]
  calc
    ‖∫ y, (ψ y : ℂ) * (f (y⁻¹ * x) - f x) ∂μ‖ ≤ ∫ y, ψ y * ε ∂μ := by
      apply norm_integral_le_of_norm_le ((hψ.integrable_of_hasCompactSupport hcψ).mul_const ε)
      exact Filter.Eventually.of_forall fun y => by
        rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (hnψ y)]
        by_cases hy : ψ y = 0
        · simp [hy]
        · exact mul_le_mul_of_nonneg_left
            (hcontrol y (hsupport (subset_closure hy)) x) (hnψ y)
    _ = ε := by rw [integral_mul_const, hmass, one_mul]
