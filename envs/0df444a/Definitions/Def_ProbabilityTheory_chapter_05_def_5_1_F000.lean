-- Prove2me | Definitions.Def_ProbabilityTheory_chapter_05_def_5_1_F000
-- name    : ProbabilityTheory_chapter_05_def_5_1_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-12T08:00:30.744067+00:00
-- url     : https://prove2.me/theorems/85972996-ab43-4e34-8a7b-122729e8477c
-- title:
--   Chapter 5, def_5_1: supporting Lean bundle F000
-- statement:
--   Supporting Lean declarations for Chapter 5, source module `def_5_1`: `def_5_1`. The mathematical interpretation of this bundle needs review.
-- source:
--   https://github.com/wkshum/ProbabilityTheory/blob/e6387d4fd8005d627d2aec40d10f039ddb4e4b40/ProbabilityTheory/chapter_05/def_5_1.lean

import Mathlib.Probability.Independence.Basic

def def_5_1 {Ω : Type _} [MeasurableSpace Ω]
  (μ : MeasureTheory.Measure Ω) (A B : Set Ω) : Prop :=
  ProbabilityTheory.IndepSet A B μ

example {Ω : Type _} [MeasurableSpace Ω]
    (μ : MeasureTheory.Measure Ω) [MeasureTheory.IsProbabilityMeasure μ]
    (A B : Set Ω) (hA : MeasurableSet A) (hB : MeasurableSet B) :
    def_5_1 μ A B ↔ μ (A ∩ B) = μ A * μ B := by
  simpa [def_5_1] using
    (ProbabilityTheory.indepSet_iff_measure_inter_eq_mul hA hB μ)


