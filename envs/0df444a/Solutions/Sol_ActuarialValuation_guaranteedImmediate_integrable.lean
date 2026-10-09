-- Prove2me | solution 1 for ActuarialValuation.guaranteedImmediate_integrable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-09T06:39:30.571982+00:00
-- url     : https://prove2.me/submissions/bba39ba2-e8f2-4a1d-9619-663091baf024

import Mathlib
import Definitions.Def_actuarial_guaranteedAnnuityDuePV
import Definitions.Def_actuarial_guaranteedAnnuityImmediatePV
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory
open ActuarialValuation

private theorem integrable_partial_geometric
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (K : Ω → ℕ) (hK : Measurable K)
    (v : ℝ) (hv0 : 0 ≤ v) (hv1 : v < 1)
    (bound : ℕ → ℕ) (f : ℕ → ℝ)
    (hf0 : ∀ k, 0 ≤ f k)
    (hf_le : ∀ k, f k ≤ v ^ k) :
    Integrable (fun ω => ∑ k ∈ Finset.range (bound (K ω)), f k) P := by
  have hv : v ≠ 1 := ne_of_lt hv1
  have hden : 0 < 1 - v := sub_pos.mpr hv1
  have hmeas : Measurable (fun ω : Ω =>
      ∑ k ∈ Finset.range (bound (K ω)), f k) := by
    have hdisc : Measurable (fun m : ℕ =>
        ∑ k ∈ Finset.range (bound m), f k) :=
      measurable_of_countable _
    simpa only [Function.comp_def] using hdisc.comp hK
  have hgeom (m : ℕ) :
      (∑ k ∈ Finset.range m, v ^ k) = (1 - v ^ m) / (1 - v) := by
    rw [geom_sum_eq hv]
    have hneg : v - 1 = -(1 - v) := by ring
    rw [hneg]
    simp only [div_neg, neg_div]
    ring
  have hbound : ∀ ω, ‖(∑ k ∈ Finset.range (bound (K ω)), f k)‖ ≤
      1 / (1 - v) := by
    intro ω
    have hp : 0 ≤ (∑ k ∈ Finset.range (bound (K ω)), f k) := by
      apply Finset.sum_nonneg
      intro k hk
      exact hf0 k
    have hle : (∑ k ∈ Finset.range (bound (K ω)), f k) ≤
        (∑ k ∈ Finset.range (bound (K ω)), v ^ k) := by
      apply Finset.sum_le_sum
      intro k hk
      exact hf_le k
    have hpow : 0 ≤ v ^ (bound (K ω)) := pow_nonneg hv0 _
    have hnum : 1 - v ^ (bound (K ω)) ≤ 1 := by linarith
    have hratio :
        (1 - v ^ (bound (K ω))) / (1 - v) ≤ 1 / (1 - v) :=
      div_le_div_of_nonneg_right hnum (le_of_lt hden)
    rw [Real.norm_eq_abs, abs_of_nonneg hp]
    exact le_trans hle (by rw [hgeom]; exact hratio)
  exact Integrable.of_bound hmeas.aestronglyMeasurable
    (1 / (1 - v)) (Filter.Eventually.of_forall hbound)

theorem solution {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (K : Ω → ℕ) (hK : Measurable K)
    (v : ℝ) (hv0 : 0 ≤ v) (hv1 : v < 1) (n : ℕ)
    :
    Integrable (guaranteedAnnuityImmediatePV K v n) P := by
  change Integrable (fun ω => ∑ k ∈ Finset.range (max (K ω) n), v ^ (k + 1)) P
  apply integrable_partial_geometric P K hK v hv0 hv1
    (fun m => max m n) (fun k => v ^ (k + 1))
  · intro k
    exact pow_nonneg hv0 _
  · intro k
    have hvle : v ≤ 1 := le_of_lt hv1
    rw [pow_succ]
    nlinarith [mul_nonneg (pow_nonneg hv0 k) (sub_nonneg.mpr hvle)]
