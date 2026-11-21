-- Prove2me | Definitions.Def_SourceProof_98598376fa8eb2edcffbba89
-- name    : SourceProof_98598376fa8eb2edcffbba89
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T10:55:54.212327+00:00
-- url     : https://prove2.me/theorems/7a683307-ad22-43bd-827a-7b3ec4721990
-- title:
--   LevyStochCalc source module: SourceProof_98598376fa8eb2edcffbba89
-- statement:
--   The original source theorem `LevyStochCalc.BSDEJ.Generator.measurable_uncurry_leftAverageLimit` comes from the `LevyStochCalc.BSDEJ.DriftModification` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_BSDEJ_DriftModification_F000

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# A progressive modification of a drift progressive for the right-continuous filtration

A real process that is progressively measurable for the right-continuous filtration `ℱ₊` has a
modification, equal to it almost everywhere on `Ω × [0, T]`, that is progressively measurable for
`ℱ` itself. The modification is the pointwise `limsup` of the moving averages of the process over
the windows `[s - 2c, s - c]` lying strictly to the left of `s`: each such average is
`ℱ`-progressive because it reads the process only before `s`, and Lebesgue's differentiation
theorem identifies the limit with the process at almost every time.
-/

open MeasureTheory Filter Metric
open scoped NNReal ENNReal Topology

namespace LevyStochCalc.BSDEJ.Generator

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {ℱ : Filtration ℝ mΩ}
  {b : Ω → ℝ → ℝ} {T : ℝ}

/-! ### Moving averages over a window strictly to the left -/

/-! ### Lebesgue differentiation along the left windows -/

/-! ### The modification -/


theorem _root_.Prove2MeSourceProof.h_98598376fa8eb2edcffbba89 (hbm : Measurable (Function.uncurry b)) (T : ℝ) :
    Measurable (Function.uncurry (leftAverageLimit b T)) := by
  have hM : Measurable fun p : Ω × ℝ =>
      limsup (fun n : ℕ => LevyStochCalc.BSDEJ.Generator.leftAverage b (1 / ((n : ℝ) + 1)) p.1 p.2) atTop :=
    Measurable.limsup fun n => LevyStochCalc.BSDEJ.Generator.measurable_uncurry_leftAverage hbm (1 / ((n : ℝ) + 1))
  have hrw : (fun p : Ω × ℝ => LevyStochCalc.BSDEJ.Generator.leftAverageLimit b T p.1 p.2)
      = Set.indicator ((fun p : Ω × ℝ => p.2) ⁻¹' Set.Icc (0 : ℝ) T)
        fun p : Ω × ℝ => limsup (fun n : ℕ => LevyStochCalc.BSDEJ.Generator.leftAverage b (1 / ((n : ℝ) + 1)) p.1 p.2) atTop := by
    funext p
    by_cases hp : p.2 ∈ Set.Icc (0 : ℝ) T
    · rw [Set.indicator_of_mem (s := (fun p : Ω × ℝ => p.2) ⁻¹' Set.Icc (0 : ℝ) T) hp]
      exact Set.indicator_of_mem (s := Set.Icc (0 : ℝ) T) hp _
    · rw [Set.indicator_of_notMem (s := (fun p : Ω × ℝ => p.2) ⁻¹' Set.Icc (0 : ℝ) T) hp]
      exact Set.indicator_of_notMem (s := Set.Icc (0 : ℝ) T) hp _
  change Measurable fun p : Ω × ℝ => LevyStochCalc.BSDEJ.Generator.leftAverageLimit b T p.1 p.2
  rw [hrw]
  exact hM.indicator (measurable_snd measurableSet_Icc)
end LevyStochCalc.BSDEJ.Generator


