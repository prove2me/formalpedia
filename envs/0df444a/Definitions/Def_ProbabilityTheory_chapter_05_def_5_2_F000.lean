-- Prove2me | Definitions.Def_ProbabilityTheory_chapter_05_def_5_2_F000
-- name    : ProbabilityTheory_chapter_05_def_5_2_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-12T08:00:46.760141+00:00
-- url     : https://prove2.me/theorems/f3b6d460-4926-4c11-a1be-3c48c5de2fce
-- title:
--   Chapter 5, def_5_2: supporting Lean bundle F000
-- statement:
--   Supporting Lean declarations for Chapter 5, source module `def_5_2`: `def_5_2`. The mathematical interpretation of this bundle needs review.
-- source:
--   https://github.com/wkshum/ProbabilityTheory/blob/e6387d4fd8005d627d2aec40d10f039ddb4e4b40/ProbabilityTheory/chapter_05/def_5_2.lean

import Definitions.Def_ProbabilityTheory_chapter_05_def_5_1_F000
import Mathlib.Probability.Independence.Basic

def def_5_2 {Ω β γ : Type _}
    [MeasurableSpace Ω] [MeasurableSpace β] [MeasurableSpace γ]
    (μ : MeasureTheory.Measure Ω) (X : Ω → β) (Y : Ω → γ) : Prop :=
  ProbabilityTheory.IndepFun X Y μ


