-- Prove2me | Definitions.Def_LevyStochCalc_Probability_ProgressiveCadlag_F001
-- name    : LevyStochCalc_Probability_ProgressiveCadlag_F001
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-18T23:36:01.59921+00:00
-- url     : https://prove2.me/theorems/eb7b5d48-d3ff-41cc-9957-dd709a5023d0
-- title:
--   Source declarations: LevyStochCalc.Probability.ProgressiveCadlag
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.Probability.ProgressiveCadlag. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Probability_Progressive_F002
import Definitions.Def_SourceProof_845c55972b82cdb43dfb6421
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

/-- A progressively measurable real process is jointly measurable. -/
theorem ProgressivelyMeasurable.measurable_uncurry
    {ℱ : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›} {H : Ω → ℝ → ℝ}
    (h : ProgressivelyMeasurable ℱ H) : Measurable (Function.uncurry H) := by
  have hmono : ∀ t : ℝ, @Prod.instMeasurableSpace Ω ℝ (ℱ t) inferInstance
      ≤ @Prod.instMeasurableSpace Ω ℝ ‹MeasurableSpace Ω› inferInstance :=
    fun t => sup_le_sup (MeasurableSpace.comap_mono (ℱ.le t)) le_rfl
  have hf : ∀ n : ℕ, Measurable fun p : Ω × ℝ =>
      (Set.Iic ((n : ℕ) : ℝ)).indicator (H p.1) p.2 :=
    fun n => ((h ((n : ℕ) : ℝ)).mono (hmono _)).measurable
  have hconv : ∀ p : Ω × ℝ,
      Tendsto (fun n : ℕ => (Set.Iic ((n : ℕ) : ℝ)).indicator (H p.1) p.2) atTop
        (𝓝 (Function.uncurry H p)) := by
    intro p
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [Filter.eventually_ge_atTop ⌈p.2⌉₊] with n hn
    have hle : p.2 ≤ ((n : ℕ) : ℝ) :=
      le_trans (Nat.le_ceil p.2) (by exact_mod_cast hn)
    exact (Set.indicator_of_mem (Set.mem_Iic.mpr hle) _).symm
  exact measurable_of_tendsto_metrizable hf (tendsto_pi_nhds.mpr hconv)
/-- **A right-continuous adapted process is jointly measurable.** -/
theorem measurable_uncurry_of_rightContinuous
    {ℱ : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›} {X : ℝ → Ω → ℝ}
    (hadapt : ∀ t : ℝ, Measurable[ℱ t] (X t))
    (hright : ∀ (ω : Ω) (t : ℝ), Tendsto (fun s => X s ω) (𝓝[>] t) (𝓝 (X t ω))) :
    Measurable (Function.uncurry X) :=
  ((_root_.Prove2MeSourceProof.h_845c55972b82cdb43dfb6421 hadapt hright).measurable_uncurry).comp
    measurable_swap
end LevyStochCalc.Probability


