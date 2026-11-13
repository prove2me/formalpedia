-- Prove2me | Definitions.Def_ProbabilityTheory_chapter_03_def_3_4_F000
-- name    : ProbabilityTheory_chapter_03_def_3_4_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-12T07:57:26.368508+00:00
-- url     : https://prove2.me/theorems/f65e8941-6fbe-4de3-92cc-c0e842143704
-- title:
--   Chapter 3, def_3_4: supporting Lean bundle F000
-- statement:
--   Supporting Lean declarations for Chapter 3, source module `def_3_4`: `distributionFunction`. The mathematical interpretation of this bundle needs review.
-- source:
--   https://github.com/wkshum/ProbabilityTheory/blob/e6387d4fd8005d627d2aec40d10f039ddb4e4b40/ProbabilityTheory/chapter_03/def_3_4.lean

import Mathlib.Probability.CDF

open MeasureTheory Set

noncomputable def distributionFunction (P : Measure ℝ) [IsProbabilityMeasure P]
    (x : ℝ) : ℝ :=
  (P (Iic x)).toReal


