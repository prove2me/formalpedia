-- Prove2me | solution 1 for ArapostathisAC.VanishingDiscount.remark_5_1_a
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-05T22:33:29.425641+00:00
-- url     : https://prove2.me/submissions/8c73450d-64bd-4b16-8a12-a24de05c2276

import Mathlib
import Definitions.Def_ArapostathisAC_VanishingDiscount_CMP

set_option autoImplicit false

open MeasureTheory Filter Topology

open ArapostathisAC.VanishingDiscount in
theorem ArapostathisAC.VanishingDiscount.pathMeasure_isProb_0546e9ec {A : Type*} [MetricSpace A]
    [MeasurableSpace A] [BorelSpace A] (M : CMP A) (π : Policy M) (i : ℕ) :
    IsProbabilityMeasure (pathMeasure M π i) := by
  have : IsProbabilityMeasure (initMeasure π i) := by
    unfold initMeasure
    exact Measure.isProbabilityMeasure_map (measurable_prodMk_left).aemeasurable
  unfold pathMeasure
  infer_instance

open MeasureTheory Filter Topology ArapostathisAC.VanishingDiscount in
theorem solution {A : Type*} [MetricSpace A] [MeasurableSpace A] [BorelSpace A]
    (M : CMP A) (ρ : ℝ) (h : ℕ → ℝ) (hsol : ACOE M ρ h) (hbdd : ∃ C, ∀ i, |h i| ≤ C) :
    ∀ π : Policy M, ∀ i,
      (∀ t, Integrable (fun ω : ℕ → ℕ × A => h (ω t).1) (pathMeasure M π i)) ∧
      Tendsto (fun t : ℕ => (∫ ω, h (ω t).1 ∂(pathMeasure M π i)) / t) atTop (𝓝 0) := by
  intro π i
  obtain ⟨C, hC⟩ := hbdd
  have := pathMeasure_isProb_0546e9ec M π i
  have hmeas : ∀ t, Measurable (fun ω : ℕ → ℕ × A => h (ω t).1) := fun t =>
    (measurable_of_countable h).comp (measurable_fst.comp (measurable_pi_apply t))
  have hint : ∀ t, Integrable (fun ω : ℕ → ℕ × A => h (ω t).1) (pathMeasure M π i) := fun t =>
    Integrable.of_bound (hmeas t).aestronglyMeasurable C
      (Eventually.of_forall fun ω => by rw [Real.norm_eq_abs]; exact hC _)
  refine ⟨hint, ?_⟩
  have hbd : ∀ t, |∫ ω, h (ω t).1 ∂(pathMeasure M π i)| ≤ C := by
    intro t
    have := norm_integral_le_of_norm_le_const (μ := pathMeasure M π i)
      (f := fun ω : ℕ → ℕ × A => h (ω t).1) (C := C)
      (Eventually.of_forall fun ω => by rw [Real.norm_eq_abs]; exact hC _)
    simpa [Real.norm_eq_abs, probReal_univ] using this
  have hlim : Tendsto (fun t : ℕ => C / (t : ℝ)) atTop (𝓝 0) :=
    tendsto_const_div_atTop_nhds_zero_nat C
  refine squeeze_zero_norm' ?_ hlim
  filter_upwards [eventually_gt_atTop 0] with t ht
  have htpos : (0 : ℝ) < t := by exact_mod_cast ht
  rw [Real.norm_eq_abs, abs_div, abs_of_pos htpos]
  exact div_le_div_of_nonneg_right (hbd t) htpos.le
