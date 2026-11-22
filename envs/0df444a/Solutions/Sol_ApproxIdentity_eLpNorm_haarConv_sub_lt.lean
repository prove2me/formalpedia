-- Prove2me | solution 1 for ApproxIdentity.eLpNorm_haarConv_sub_lt
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @emmgaml
-- created : 2026-11-22T20:12:03.881808+00:00
-- url     : https://prove2.me/submissions/7ff9c820-0632-4d76-aa82-94be03607aca
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Theorems.Thm_HaarConvolution_haarConv_ae_eq_integral_smul_compMeasurePreserving

open MeasureTheory Topology
open scoped ENNReal

set_option autoImplicit false

theorem solution {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [LocallyCompactSpace G] [T2Space G] [MeasurableSpace G] [BorelSpace G]
    (μ : Measure G) [μ.IsHaarMeasure] [μ.Regular] (p : ℝ≥0∞) (hp1 : 1 ≤ p) (hp : p ≠ ⊤)
    (f : G → ℂ) (hf : MemLp f p μ) (ε : ℝ) (hε : 0 < ε) :
    ∃ U ∈ 𝓝 (1 : G), ∀ ψ : G → ℝ, Continuous ψ → HasCompactSupport ψ → (∀ x, 0 ≤ ψ x) →
      tsupport ψ ⊆ U → ∫ x, ψ x ∂μ = 1 →
      eLpNorm (fun x : G => (∫ y, (ψ y : ℂ) * f (y⁻¹ * x) ∂μ) - f x) p μ < ENNReal.ofReal ε := by
  have : Fact (1 ≤ p) := ⟨hp1⟩
  set F : Lp ℂ p μ := hf.toLp f with hF
  -- the left translates `y ↦ f (y⁻¹ * ·)` as elements of `L^p`
  let T : G → Lp ℂ p μ := fun y => Lp.compMeasurePreserving (fun x : G => y⁻¹ * x)
      (measurePreserving_mul_left μ y⁻¹) F
  let g : C(G, C(G, G)) :=
    (ContinuousMap.mk (fun q : G × G => q.1⁻¹ * q.2) (by fun_prop)).curry
  have hT : Continuous T :=
    Continuous.compMeasurePreservingLp (μ := μ) (ν := μ) (f := fun _ : G => F)
      (g := fun y => g y) continuous_const g.continuous
      (fun y => measurePreserving_mul_left μ y⁻¹) hp
  have hT1 : T 1 = F := by
    apply Lp.ext
    filter_upwards [Lp.coeFn_compMeasurePreserving F (measurePreserving_mul_left μ (1 : G)⁻¹)]
      with x hx
    refine hx.trans ?_
    simp
  have hδ : (0 : ℝ) < ε / 2 := by linarith
  have hev : ∀ᶠ y in 𝓝 (1 : G), dist (T y) F < ε / 2 := by
    have h := hT.tendsto 1
    rw [hT1] at h
    exact (Metric.tendsto_nhds.1 h) _ hδ
  refine ⟨{y | dist (T y) F < ε / 2}, hev, ?_⟩
  intro ψ hψ hψc hψ0 hψU hψ1
  have hψC : Continuous (fun y => (ψ y : ℂ)) := Complex.continuous_ofReal.comp hψ
  have hψCc : HasCompactSupport (fun y => (ψ y : ℂ)) := hψc.comp_left Complex.ofReal_zero
  have key := HaarConvolution.haarConv_ae_eq_integral_smul_compMeasurePreserving μ p hp
    (fun y => (ψ y : ℂ)) hψC hψCc f hf
  set I : Lp ℂ p μ := ∫ y, (ψ y : ℂ) • T y ∂μ with hI
  have hae : (fun x : G => (∫ y, (ψ y : ℂ) * f (y⁻¹ * x) ∂μ) - f x) =ᵐ[μ] ⇑(I - F) := by
    filter_upwards [key, Lp.coeFn_sub I F, hf.coeFn_toLp] with x h1 h2 h3
    rw [h2, Pi.sub_apply, ← h1, hF, h3]
  rw [eLpNorm_congr_ae hae, ← Lp.enorm_def]
  have hint1 : Integrable (fun y => (ψ y : ℂ) • T y) μ :=
    (hψC.smul hT).integrable_of_hasCompactSupport hψCc.smul_right
  have hint2 : Integrable (fun y => (ψ y : ℂ) • F) μ :=
    (hψC.integrable_of_hasCompactSupport hψCc).smul_const F
  have hψ1C : ∫ y, (ψ y : ℂ) ∂μ = 1 := by
    rw [integral_complex_ofReal, hψ1]; simp
  have hIF : I - F = ∫ y, (ψ y : ℂ) • (T y - F) ∂μ := by
    simp_rw [smul_sub]
    rw [integral_sub hint1 hint2, integral_smul_const, hψ1C, one_smul]
  have hnorm : ‖I - F‖ ≤ ε / 2 := by
    rw [hIF]
    have hb : Integrable (fun y => ψ y * (ε / 2)) μ :=
      (hψ.integrable_of_hasCompactSupport hψc).mul_const _
    calc ‖∫ y, (ψ y : ℂ) • (T y - F) ∂μ‖ ≤ ∫ y, ψ y * (ε / 2) ∂μ := by
          apply norm_integral_le_of_norm_le hb
          refine Filter.Eventually.of_forall (fun y => ?_)
          rw [norm_smul, Complex.norm_real, Real.norm_of_nonneg (hψ0 y)]
          by_cases hy : ψ y = 0
          · simp [hy]
          · apply mul_le_mul_of_nonneg_left _ (hψ0 y)
            have hyU : y ∈ {y | dist (T y) F < ε / 2} := hψU (subset_tsupport _ hy)
            rw [← dist_eq_norm]
            exact le_of_lt hyU
      _ = ε / 2 := by rw [integral_mul_const, hψ1, one_mul]
  rw [← ofReal_norm]
  exact (ENNReal.ofReal_lt_ofReal_iff hε).2 (by linarith)
