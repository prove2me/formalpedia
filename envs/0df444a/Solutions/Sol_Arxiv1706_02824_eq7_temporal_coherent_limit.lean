-- Prove2me | solution 1 for Arxiv1706_02824.eq7_temporal_coherent_limit
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-26T04:47:53.687393+00:00
-- url     : https://prove2.me/submissions/0fc4060e-841e-4529-af69-00ba60acfec4

import Mathlib
import Definitions.Def_Arxiv1706_02824_Basic

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Filter Topology Real
open scoped ComplexConjugate

namespace S78E7
open Arxiv1706_02824

lemma main (W : ℝ → ℂ) (hW : Integrable W) :
    Tendsto (fun T : ℝ => sincSqIntegral W T) (𝓝[>] 0) (𝓝 ((‖∫ ν : ℝ, W ν‖ ^ 2 : ℝ) : ℂ)) := by
  set F : ℝ → ℝ × ℝ → ℂ := fun T p =>
    W p.1 * conj (W p.2) * ((Real.sinc (π * (p.1 - p.2) * T) ^ 2 : ℝ) : ℂ) with hF
  have hm1 : AEStronglyMeasurable (fun p : ℝ × ℝ => W p.1) (volume.prod volume) :=
    hW.aestronglyMeasurable.comp_quasiMeasurePreserving Measure.quasiMeasurePreserving_fst
  have hm2 : AEStronglyMeasurable (fun p : ℝ × ℝ => conj (W p.2)) (volume.prod volume) :=
    (hW.aestronglyMeasurable.comp_quasiMeasurePreserving
      Measure.quasiMeasurePreserving_snd).star
  have hmF : ∀ T, AEStronglyMeasurable (F T) (volume.prod volume) := by
    intro T
    refine (hm1.mul hm2).mul ?_
    exact (Continuous.aestronglyMeasurable (by fun_prop [Real.continuous_sinc]))
  have hbound : Integrable (fun p : ℝ × ℝ => ‖W p.1‖ * ‖W p.2‖) (volume.prod volume) :=
    hW.norm.mul_prod hW.norm
  have hle : ∀ T p, ‖F T p‖ ≤ ‖W p.1‖ * ‖W p.2‖ := by
    intro T p
    simp only [hF, norm_mul, Complex.norm_real, RCLike.norm_conj, Real.norm_eq_abs]
    have h1 : |Real.sinc (π * (p.1 - p.2) * T) ^ 2| ≤ 1 := by
      rw [abs_pow]; exact pow_le_one₀ (abs_nonneg _) (Real.abs_sinc_le_one _)
    calc ‖W p.1‖ * ‖W p.2‖ * |Real.sinc (π * (p.1 - p.2) * T) ^ 2|
        ≤ ‖W p.1‖ * ‖W p.2‖ * 1 := mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = _ := mul_one _
  have hint : ∀ T, Integrable (F T) (volume.prod volume) := fun T =>
    hbound.mono' (hmF T) (Eventually.of_forall (hle T))
  have heq : ∀ T, sincSqIntegral W T = ∫ p, F T p ∂(volume.prod volume) := by
    intro T; rw [integral_prod _ (hint T)]; rfl
  simp_rw [heq]
  have hlim : ∫ p, W p.1 * conj (W p.2) ∂(volume.prod volume) = ((‖∫ ν : ℝ, W ν‖ ^ 2 : ℝ) : ℂ) := by
    rw [integral_prod_mul (fun x => W x) (fun y => conj (W y)), integral_conj, Complex.mul_conj']
    push_cast; rfl
  rw [← hlim]
  refine tendsto_integral_filter_of_dominated_convergence _ (Eventually.of_forall hmF) 
    (Eventually.of_forall (fun T => Eventually.of_forall (hle T))) hbound ?_
  refine Eventually.of_forall (fun p => ?_)
  have hc : Continuous (fun T : ℝ => ((Real.sinc (π * (p.1 - p.2) * T) ^ 2 : ℝ) : ℂ)) := by
    fun_prop [Real.continuous_sinc]
  have := (hc.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Set.Ioi (0:ℝ)))
  simp only [mul_zero, Real.sinc_zero, one_pow, Complex.ofReal_one] at this
  simpa [hF] using (tendsto_const_nhds (x := W p.1 * conj (W p.2))).mul this

end S78E7

open Arxiv1706_02824 in
theorem solution (W : ℝ → ℂ) (hW : Integrable W) :
    Tendsto (fun T : ℝ => sincSqIntegral W T) (𝓝[>] 0) (𝓝 ((‖∫ ν : ℝ, W ν‖ ^ 2 : ℝ) : ℂ)) ∧
    ∀ (J : ℂ) (s : ℝ → ℝ), (∀ ν, 0 ≤ s ν) → Integrable s → ∫ ν : ℝ, s ν = 1 →
      (∀ ν, W ν = J * (s ν : ℂ)) →
      Tendsto (fun T : ℝ => sincSqIntegral W T) (𝓝[>] 0) (𝓝 ((‖J‖ ^ 2 : ℝ) : ℂ)) := by
  refine ⟨S78E7.main W hW, fun J s _ _ h1 hWs => ?_⟩
  have : ∫ ν : ℝ, W ν = J := by
    simp_rw [hWs]
    rw [integral_const_mul, integral_complex_ofReal, h1, Complex.ofReal_one, mul_one]
  have h := S78E7.main W hW
  rwa [this] at h
