-- Prove2me | Definitions.Def_ProbabilityTheory_chapter_02_def_2_8_F001
-- name    : ProbabilityTheory_chapter_02_def_2_8_F001
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-12T15:29:11.725289+00:00
-- url     : https://prove2.me/theorems/b581aab6-8366-4baa-af8b-42ecf079b161
-- title:
--   Chapter 2, def_2_8: supporting Lean bundle F001
-- statement:
--   Supporting Lean declarations for Chapter 2, source module `def_2_8`: `closedInterval_mem_borelAlgebraReal`, `leftClosedInfinite_mem_borelAlgebraReal`, `rightClosedInfinite_mem_borelAlgebraReal`, `rightOpenInfinite_mem_borelAlgebraReal`, `leftOpenInfinite_mem_borelAlgebraReal`, and 3 others. The mathematical interpretation of this bundle needs review.
-- source:
--   https://github.com/wkshum/ProbabilityTheory/blob/e6387d4fd8005d627d2aec40d10f039ddb4e4b40/ProbabilityTheory/chapter_02/def_2_8.lean

import Definitions.Def_ProbabilityTheory_chapter_02_def_2_8_F000
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.Tactic

open Set MeasureTheory









@[reducible]
def def_2_8 : MeasurableSpace ℝ :=
  borelAlgebraReal


