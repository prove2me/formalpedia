-- Prove2me | Definitions.Def_ProbabilityTheory_chapter_03_def_3_2_F000
-- name    : ProbabilityTheory_chapter_03_def_3_2_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-12T16:24:44.512584+00:00
-- url     : https://prove2.me/theorems/e6e3d6eb-a083-4f95-9535-4d7860109f69
-- title:
--   Chapter 3, def_3_2: supporting Lean bundle F000
-- statement:
--   Supporting Lean declarations for Chapter 3, source module `def_3_2`: `IsExtension`. The mathematical interpretation of this bundle needs review.
-- source:
--   https://github.com/wkshum/ProbabilityTheory/blob/e6387d4fd8005d627d2aec40d10f039ddb4e4b40/ProbabilityTheory/chapter_03/def_3_2.lean

import Definitions.Def_ProbabilityTheory_chapter_03_def_3_1_F001
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.MeasureTheory.OuterMeasure.OfAddContent
import Mathlib.Tactic

open MeasureTheory ENNReal

def IsExtension {X : Type*} (F₀ : Set (Set X)) (μ₀ : Set X → ℝ≥0∞)
    (μ : @Measure X (MeasurableSpace.generateFrom F₀)) : Prop :=
  ∀ E ∈ F₀, μ E = μ₀ E


