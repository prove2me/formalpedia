-- Prove2me | Definitions.Def_ProbabilityTheory_chapter_07_def_7_2_F000
-- name    : ProbabilityTheory_chapter_07_def_7_2_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-12T15:26:22.780533+00:00
-- url     : https://prove2.me/theorems/228aef05-bc64-401b-ab63-2b44373fc31a
-- title:
--   Chapter 7, def_7_2: supporting Lean bundle F000
-- statement:
--   Supporting Lean declarations for Chapter 7, source module `def_7_2`: `PushForwardMeasure`, `ImageMeasure`, `InducedMeasure`, `RandomVariableDistribution`, `distribution_isProbabilityMeasure`, and 1 others. The mathematical interpretation of this bundle needs review.
-- source:
--   https://github.com/wkshum/ProbabilityTheory/blob/e6387d4fd8005d627d2aec40d10f039ddb4e4b40/ProbabilityTheory/chapter_07/def_7_2.lean

import Definitions.Def_ProbabilityTheory_chapter_07_thm_7_10_F000
import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
import Mathlib.MeasureTheory.Measure.Map
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.Tactic

open MeasureTheory

noncomputable def PushForwardMeasure {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (X : Ω → ℝ) : Measure ℝ :=
  pushForwardRealMeasure μ X

noncomputable def ImageMeasure {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (X : Ω → ℝ) : Measure ℝ :=
  PushForwardMeasure μ X

noncomputable def InducedMeasure {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (X : Ω → ℝ) : Measure ℝ :=
  PushForwardMeasure μ X

noncomputable def RandomVariableDistribution {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [MeasureTheory.IsProbabilityMeasure μ]
    (X : Ω → ℝ) : Measure ℝ :=
  PushForwardMeasure μ X



noncomputable def def_7_2 {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (X : Ω → ℝ) : Measure ℝ :=
  PushForwardMeasure μ X


