-- Prove2me | Definitions.Def_ProbabilityTheory_chapter_02_thm_2_5_F000
-- name    : ProbabilityTheory_chapter_02_thm_2_5_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-12T20:21:12.284983+00:00
-- url     : https://prove2.me/theorems/ef96dca6-5ebc-42e5-a2da-7bd38aca9cef
-- title:
--   Chapter 2, thm_2_5: supporting Lean bundle F000
-- statement:
--   Supporting Lean declarations for Chapter 2, source module `thm_2_5`: `thm_2_5_gap`, `thm_2_5_gap_increasing`, `thm_2_5_gap_measurable`, `thm_2_5_gap_iUnion_eq`, `thm_2_5_gap_measure`, and 3 others. The mathematical interpretation of this bundle needs review.
-- source:
--   https://github.com/wkshum/ProbabilityTheory/blob/e6387d4fd8005d627d2aec40d10f039ddb4e4b40/ProbabilityTheory/chapter_02/thm_2_5.lean

import Definitions.Def_ProbabilityTheory_chapter_02_def_2_6_F000
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.Tactic

open MeasureTheory Set

def thm_2_5_gap {Ω : Type*} (A : ℕ → Set Ω) (i : ℕ) : Set Ω :=
  A 0 \ A i


