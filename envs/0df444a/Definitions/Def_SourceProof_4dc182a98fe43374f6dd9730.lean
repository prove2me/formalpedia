-- Prove2me | Definitions.Def_SourceProof_4dc182a98fe43374f6dd9730
-- name    : SourceProof_4dc182a98fe43374f6dd9730
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-18T22:26:27.061262+00:00
-- url     : https://prove2.me/theorems/6befecc1-6846-44ef-8a7d-819ee69d88d7
-- title:
--   LevyStochCalc source proof: LevyStochCalc.Probability.ProgressivelyMeasurable.measurable_setIntegral_Icc
-- statement:
--   Auxiliary theorem proved in the original LevyStochCalc source. Its proof and dependencies are retained verbatim from the certified extraction.
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


theorem _root_.Prove2MeSourceProof.h_4dc182a98fe43374f6dd9730
    {ℱ : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›} {H : Ω → ℝ → ℝ}
    (h : ProgressivelyMeasurable ℱ H) (t : ℝ) :
    Measurable[ℱ t] fun ω => ∫ s in Set.Icc (0 : ℝ) t, H ω s ∂volume := by
  letI : MeasurableSpace Ω := ℱ t
  haveI : MeasureTheory.IsFiniteMeasure (volume.restrict (Set.Icc (0 : ℝ) t)) :=
    ⟨by rw [MeasureTheory.Measure.restrict_apply_univ, Real.volume_Icc]
        exact ENNReal.ofReal_lt_top⟩
  have hind : Measurable fun ω : Ω =>
      ∫ s in Set.Icc (0 : ℝ) t, (Set.Iic t).indicator (H ω) s ∂volume :=
    ((h t).integral_prod_right'
      (ν := volume.restrict (Set.Icc (0 : ℝ) t))).measurable
  have heq : (fun ω : Ω => ∫ s in Set.Icc (0 : ℝ) t, H ω s ∂volume)
      = fun ω : Ω => ∫ s in Set.Icc (0 : ℝ) t, (Set.Iic t).indicator (H ω) s ∂volume := by
    funext ω
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Icc fun s hs => ?_
    exact (Set.indicator_of_mem (Set.mem_Iic.mpr hs.2) (H ω)).symm
  rw [heq]
  exact hind
end LevyStochCalc.Probability


