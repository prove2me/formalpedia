-- Prove2me | Definitions.Def_ProbabilityTheory_chapter_05_def_5_3_F000
-- name    : ProbabilityTheory_chapter_05_def_5_3_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-12T08:00:55.147761+00:00
-- url     : https://prove2.me/theorems/5daaa784-5ba6-4c93-ab38-1d994c84aa38
-- title:
--   Chapter 5, def_5_3: supporting Lean bundle F000
-- statement:
--   Supporting Lean declarations for Chapter 5, source module `def_5_3`: `def_5_3`. The mathematical interpretation of this bundle needs review.
-- source:
--   https://github.com/wkshum/ProbabilityTheory/blob/e6387d4fd8005d627d2aec40d10f039ddb4e4b40/ProbabilityTheory/chapter_05/def_5_3.lean

import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
import Mathlib.Tactic

@[reducible]
def def_5_3 {Ω β : Type _}
  [MeasurableSpace Ω] [MeasurableSpace β] (X : Ω → β) :
    MeasurableSpace Ω :=
  MeasurableSpace.comap X inferInstance


