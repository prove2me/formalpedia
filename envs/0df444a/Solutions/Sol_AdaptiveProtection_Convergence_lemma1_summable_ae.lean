-- Prove2me | solution 1 for AdaptiveProtection.Convergence.lemma1_summable_ae
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T15:30:13.823763+00:00
-- url     : https://prove2.me/submissions/61fd7537-e231-4e84-bada-71052eea7bbf

import Mathlib

set_option autoImplicit false
open MeasureTheory Filter Topology

theorem solution
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Y : ℕ → Ω → ℝ) (hY : ∀ n, Integrable (Y n) μ)
    (hsum : Summable fun n => ∫ ω, |Y n ω| ∂μ) :
    ∀ᵐ ω ∂μ, Summable fun n => |Y n ω| := by
  have hmeas : ∀ n, AEMeasurable (fun ω => ENNReal.ofReal |Y n ω|) μ := fun n =>
    ((hY n).aestronglyMeasurable.norm.aemeasurable).ennreal_ofReal.congr
      (Filter.Eventually.of_forall (fun ω => by simp [Real.norm_eq_abs]))
  have hint : ∀ n, ∫⁻ ω, ENNReal.ofReal |Y n ω| ∂μ = ENNReal.ofReal (∫ ω, |Y n ω| ∂μ) := by
    intro n
    rw [ofReal_integral_eq_lintegral_ofReal (hY n).abs (Filter.Eventually.of_forall (fun ω => abs_nonneg _))]
  have htot : ∫⁻ ω, ∑' n, ENNReal.ofReal |Y n ω| ∂μ ≠ ⊤ := by
    rw [lintegral_tsum hmeas]
    simp_rw [hint]
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun n => integral_nonneg (fun ω => abs_nonneg _)) hsum]
    exact ENNReal.ofReal_ne_top
  have hae := ae_lt_top' (AEMeasurable.ennreal_tsum hmeas) htot
  filter_upwards [hae] with ω hω
  have := ENNReal.summable_toReal hω.ne
  simpa [ENNReal.toReal_ofReal (abs_nonneg _)] using this
