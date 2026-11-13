-- Prove2me | Definitions.Def_ProbabilityTheory_chapter_03_def_3_6_F000
-- name    : ProbabilityTheory_chapter_03_def_3_6_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-12T07:57:43.763412+00:00
-- url     : https://prove2.me/theorems/3ceed192-ccb6-437a-b5cd-86ca3870a0e1
-- title:
--   Chapter 3, def_3_6: supporting Lean bundle F000
-- statement:
--   Supporting Lean declarations for Chapter 3, source module `def_3_6`: `IsCompactIntervalSet`. The mathematical interpretation of this bundle needs review.
-- source:
--   https://github.com/wkshum/ProbabilityTheory/blob/e6387d4fd8005d627d2aec40d10f039ddb4e4b40/ProbabilityTheory/chapter_03/def_3_6.lean

import Mathlib.Data.Real.Basic

def IsCompactIntervalSet (s : Set ℝ) : Prop :=
  ∃ a b : ℝ, s = Set.Icc a b


