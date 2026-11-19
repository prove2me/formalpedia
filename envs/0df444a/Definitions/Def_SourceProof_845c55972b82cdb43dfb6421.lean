-- Prove2me | Definitions.Def_SourceProof_845c55972b82cdb43dfb6421
-- name    : SourceProof_845c55972b82cdb43dfb6421
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-18T22:30:31.187952+00:00
-- url     : https://prove2.me/theorems/c383a052-6ade-43b0-8acb-89069aefff4f
-- title:
--   LevyStochCalc source proof: LevyStochCalc.Probability.progressivelyMeasurable_of_rightContinuous
-- statement:
--   Auxiliary theorem proved in the original LevyStochCalc source. Its proof and dependencies are retained verbatim from the certified extraction.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Probability_ProgressiveCadlag_F000
import Definitions.Def_SourceProof_35d8365844de2771203e553f

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


theorem _root_.Prove2MeSourceProof.h_845c55972b82cdb43dfb6421
    {ℱ : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›} {X : ℝ → Ω → ℝ}
    (hadapt : ∀ t : ℝ, Measurable[ℱ t] (X t))
    (hright : ∀ (ω : Ω) (t : ℝ), Tendsto (fun s => X s ω) (𝓝[>] t) (𝓝 (X t ω))) :
    ProgressivelyMeasurable ℱ (fun ω s => X s ω) := by
  refine _root_.Prove2MeSourceProof.h_35d8365844de2771203e553f ?_
  intro i
  letI : MeasurableSpace Ω := ℱ i
  -- the staircase, as a function of a dyadic index and the sample point
  have hslice : ∀ (n : ℕ) (k : ℤ),
      Measurable fun ω : Ω => X (min ((k : ℝ) / 2 ^ n) i) ω := by
    intro n k
    exact (hadapt _).mono (ℱ.mono (min_le_right _ _)) le_rfl
  have hF : ∀ n : ℕ, Measurable fun p : ℤ × Ω => X (min ((p.1 : ℝ) / 2 ^ n) i) p.2 := fun n =>
    measurable_from_prod_countable_right (fun k => hslice n k)
  have hg : ∀ n : ℕ, Measurable fun q : Set.Iic i × Ω => X (LevyStochCalc.Probability.dyadicCeil n i (q.1 : ℝ)) q.2 := by
    intro n
    have he : Measurable fun q : Set.Iic i × Ω =>
        ((⌈(2 : ℝ) ^ n * (q.1 : ℝ)⌉ : ℤ), q.2) :=
      (Int.measurable_ceil.comp (measurable_const.mul
        (measurable_subtype_coe.comp measurable_fst))).prodMk measurable_snd
    exact (hF n).comp he
  have hconv : ∀ q : Set.Iic i × Ω,
      Tendsto (fun n => X (LevyStochCalc.Probability.dyadicCeil n i (q.1 : ℝ)) q.2) atTop (𝓝 (X (q.1 : ℝ) q.2)) := by
    rintro ⟨⟨t, ht⟩, ω⟩
    have hge : Tendsto (fun n => LevyStochCalc.Probability.dyadicCeil n i t) atTop (𝓝[≥] t) :=
      tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
        (LevyStochCalc.Probability.tendsto_dyadicCeil (Set.mem_Iic.mp ht))
        (Filter.Eventually.of_forall fun n => LevyStochCalc.Probability.le_dyadicCeil n (Set.mem_Iic.mp ht))
    exact (LevyStochCalc.Probability.tendsto_nhdsGE_of_nhdsGT (hright ω t)).comp hge
  exact (measurable_of_tendsto_metrizable hg (tendsto_pi_nhds.mpr hconv)).stronglyMeasurable
end LevyStochCalc.Probability


