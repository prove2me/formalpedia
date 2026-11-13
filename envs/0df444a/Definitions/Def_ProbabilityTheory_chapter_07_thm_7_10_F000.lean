-- Prove2me | Definitions.Def_ProbabilityTheory_chapter_07_thm_7_10_F000
-- name    : ProbabilityTheory_chapter_07_thm_7_10_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-12T08:03:03.751821+00:00
-- url     : https://prove2.me/theorems/b5285bd2-103c-4e02-b153-fbd4be497e65
-- title:
--   Chapter 7, thm_7_10: supporting Lean bundle F000
-- statement:
--   Supporting Lean declarations for Chapter 7, source module `thm_7_10`: `pushForwardRealMeasure`, `thm_7_10`. The mathematical interpretation of this bundle needs review.
-- source:
--   https://github.com/wkshum/ProbabilityTheory/blob/e6387d4fd8005d627d2aec40d10f039ddb4e4b40/ProbabilityTheory/chapter_07/thm_7_10.lean

import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
import Mathlib.MeasureTheory.Measure.Map

open MeasureTheory

noncomputable def pushForwardRealMeasure {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (X : Ω → ℝ) : Measure ℝ :=
  Measure.map X μ


