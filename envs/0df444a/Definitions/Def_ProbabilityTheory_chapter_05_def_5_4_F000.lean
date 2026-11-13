-- Prove2me | Definitions.Def_ProbabilityTheory_chapter_05_def_5_4_F000
-- name    : ProbabilityTheory_chapter_05_def_5_4_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-12T08:01:15.634089+00:00
-- url     : https://prove2.me/theorems/50b4a199-e128-47fc-8c5a-4bf74abc4445
-- title:
--   Chapter 5, def_5_4: supporting Lean bundle F000
-- statement:
--   Supporting Lean declarations for Chapter 5, source module `def_5_4`: `def_5_4`. The mathematical interpretation of this bundle needs review.
-- source:
--   https://github.com/wkshum/ProbabilityTheory/blob/e6387d4fd8005d627d2aec40d10f039ddb4e4b40/ProbabilityTheory/chapter_05/def_5_4.lean

import Definitions.Def_ProbabilityTheory_chapter_05_def_5_1_F000
import Mathlib.Probability.Independence.Basic
import Mathlib.Tactic

def def_5_4 {Ω : Type _} [MeasurableSpace Ω] (μ : MeasureTheory.Measure Ω)
    (F₁ F₂ : Set (Set Ω)) : Prop :=
  ProbabilityTheory.IndepSets F₁ F₂ μ


