-- Prove2me | Definitions.Def_ProbabilityTheory_chapter_02_thm_2_4_F000
-- name    : ProbabilityTheory_chapter_02_thm_2_4_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-12T07:56:35.680355+00:00
-- url     : https://prove2.me/theorems/ec272383-a3f0-4ded-b433-784c3c4587e1
-- title:
--   Chapter 2, thm_2_4: supporting Lean bundle F000
-- statement:
--   Supporting Lean declarations for Chapter 2, source module `thm_2_4`: `thm_2_4_increment`, `thm_2_4_increment_subset`, `thm_2_4_increment_pairwise_disjoint`, `thm_2_4_increment_measurable`. The mathematical interpretation of this bundle needs review.
-- source:
--   https://github.com/wkshum/ProbabilityTheory/blob/e6387d4fd8005d627d2aec40d10f039ddb4e4b40/ProbabilityTheory/chapter_02/thm_2_4.lean

import Definitions.Def_ProbabilityTheory_chapter_02_def_2_6_F000
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.Tactic

open MeasureTheory Set
open scoped BigOperators

def thm_2_4_increment {Ω : Type*} (A : ℕ → Set Ω) : ℕ → Set Ω
  | 0 => A 0
  | n + 1 => A (n + 1) \ A n


