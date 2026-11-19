-- Prove2me | Definitions.Def_LevyStochCalc_Probability_ProgressiveCadlag_F000
-- name    : LevyStochCalc_Probability_ProgressiveCadlag_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-18T22:29:51.545205+00:00
-- url     : https://prove2.me/theorems/06d90127-d9db-4de8-8805-a4b536b33578
-- title:
--   Source declarations: LevyStochCalc.Probability.ProgressiveCadlag
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.Probability.ProgressiveCadlag. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Probability_Progressive_F002
import Mathlib.MeasureTheory.Function.Floor

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Right-continuous adapted processes are progressively measurable

An adapted process with right-continuous paths is progressively measurable: on `(-∞, i] × Ω` it
is the pointwise limit of the dyadic right-staircases `t ↦ X_{⌈2ⁿt⌉/2ⁿ ∧ i}`, each of which
takes countably many values, all at times bounded by `i`.

## Main statements

* `Probability.dyadicCeil` — the dyadic right-staircase, capped at a horizon.
* `LevyStochCalc.Probability.progressivelyMeasurable_of_rightContinuous` — a right-continuous
  adapted process is progressively measurable.
* `LevyStochCalc.Probability.ProgressivelyMeasurable.measurable_uncurry` — a progressively
  measurable process is jointly measurable.
* `LevyStochCalc.Probability.exists_everywhere_cadlag_modification` — under the usual
  conditions, an almost-surely càdlàg adapted process has an everywhere-càdlàg modification.
* `LevyStochCalc.Probability.ProgressivelyMeasurable.measurable_setIntegral_Icc` — the integral
  of a progressively measurable process over `[0, t]` is measurable for `ℱ t`.
-/

open MeasureTheory Filter Topology

namespace LevyStochCalc.Probability

universe u

variable {Ω : Type u} [MeasurableSpace Ω]

/-- Right-continuity along `𝓝[>] t` upgrades to `𝓝[≥] t`. -/
theorem tendsto_nhdsGE_of_nhdsGT {f : ℝ → ℝ} {t : ℝ}
    (h : Tendsto f (𝓝[>] t) (𝓝 (f t))) : Tendsto f (𝓝[≥] t) (𝓝 (f t)) := by
  have hset : Set.Ici t = Set.Ioi t ∪ {t} := by
    ext x
    simp [le_iff_lt_or_eq]
  rw [hset, nhdsWithin_union, nhdsWithin_singleton]
  exact h.sup (tendsto_pure_nhds f t)
/-- The dyadic right-staircase at scale `2⁻ⁿ`, capped at the horizon `i`. -/
noncomputable def dyadicCeil (n : ℕ) (i t : ℝ) : ℝ :=
  min ((⌈(2 : ℝ) ^ n * t⌉ : ℝ) / 2 ^ n) i
theorem dyadicCeil_le (n : ℕ) (i t : ℝ) : dyadicCeil n i t ≤ i := min_le_right _ _
theorem le_dyadicCeil (n : ℕ) {i t : ℝ} (ht : t ≤ i) : t ≤ dyadicCeil n i t := by
  refine le_min ?_ ht
  rw [le_div_iff₀ (by positivity : (0 : ℝ) < 2 ^ n)]
  calc t * 2 ^ n = (2 : ℝ) ^ n * t := by ring
    _ ≤ (⌈(2 : ℝ) ^ n * t⌉ : ℝ) := Int.le_ceil _
theorem measurable_dyadicCeil (n : ℕ) (i : ℝ) : Measurable (dyadicCeil n i) := by
  have hcast : Measurable ((↑) : ℤ → ℝ) := measurable_of_countable _
  exact (((hcast.comp
    (Int.measurable_ceil.comp (measurable_const.mul measurable_id))).div
    measurable_const).min measurable_const)
theorem tendsto_dyadicCeil {i t : ℝ} (ht : t ≤ i) :
    Tendsto (fun n => dyadicCeil n i t) atTop (𝓝 t) := by
  have hupper : ∀ n : ℕ, (⌈(2 : ℝ) ^ n * t⌉ : ℝ) / 2 ^ n ≤ t + (1 / 2 : ℝ) ^ n := by
    intro n
    have hpos : (0 : ℝ) < 2 ^ n := by positivity
    rw [div_le_iff₀ hpos]
    have h1 : (⌈(2 : ℝ) ^ n * t⌉ : ℝ) ≤ (2 : ℝ) ^ n * t + 1 := (Int.ceil_lt_add_one _).le
    have h2 : ((1 : ℝ) / 2) ^ n * 2 ^ n = 1 := by
      rw [div_pow, one_pow, div_mul_cancel₀ _ (by positivity : ((2 : ℝ) ^ n) ≠ 0)]
    nlinarith [h1, h2]
  have hzero : Tendsto (fun n : ℕ => ((1 : ℝ) / 2) ^ n) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  have htop : Tendsto (fun n : ℕ => t + ((1 : ℝ) / 2) ^ n) atTop (𝓝 t) := by
    simpa using tendsto_const_nhds.add hzero
  have hmid : Tendsto (fun n : ℕ => (⌈(2 : ℝ) ^ n * t⌉ : ℝ) / 2 ^ n) atTop (𝓝 t) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds htop
      (Filter.Eventually.of_forall fun n => ?_)
      (Filter.Eventually.of_forall fun n => hupper n)
    rw [le_div_iff₀ (by positivity : (0 : ℝ) < 2 ^ n)]
    calc t * 2 ^ n = (2 : ℝ) ^ n * t := by ring
      _ ≤ (⌈(2 : ℝ) ^ n * t⌉ : ℝ) := Int.le_ceil _
  have := hmid.min (tendsto_const_nhds (x := i))
  rwa [min_eq_left ht] at this
end LevyStochCalc.Probability


