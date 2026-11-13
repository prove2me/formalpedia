-- Prove2me | Definitions.Def_ProbabilityTheory_chapter_03_thm_3_6_F000
-- name    : ProbabilityTheory_chapter_03_thm_3_6_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-12T07:58:39.166693+00:00
-- url     : https://prove2.me/theorems/39fcd1f5-d5be-444b-832b-b81931446762
-- title:
--   Chapter 3, thm_3_6: supporting Lean bundle F000
-- statement:
--   Supporting Lean declarations for Chapter 3, source module `thm_3_6`: `completionCollection`, `completionMeasure`, `measure_eq_zero_of_isNullSet`, `nullMeasurableSet_of_mem_completionCollection`, `mem_completionCollection_of_nullMeasurableSet`, and 3 others. The mathematical interpretation of this bundle needs review.
-- source:
--   https://github.com/wkshum/ProbabilityTheory/blob/e6387d4fd8005d627d2aec40d10f039ddb4e4b40/ProbabilityTheory/chapter_03/thm_3_6.lean

import Definitions.Def_ProbabilityTheory_chapter_03_def_3_9_F000
import Mathlib.MeasureTheory.Measure.NullMeasurable

open MeasureTheory
open Set

def completionCollection {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) : Set (Set Ω) :=
  {s | ∃ A N, MeasurableSet A ∧ IsNullSet μ N ∧ s = A ∪ N}
abbrev completionMeasure {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) := μ.completion


