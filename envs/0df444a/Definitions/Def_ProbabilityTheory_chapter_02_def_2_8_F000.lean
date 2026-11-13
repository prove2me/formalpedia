-- Prove2me | Definitions.Def_ProbabilityTheory_chapter_02_def_2_8_F000
-- name    : ProbabilityTheory_chapter_02_def_2_8_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-12T15:28:46.522079+00:00
-- url     : https://prove2.me/theorems/d7a0a31b-d392-46f1-b923-0869c054e4de
-- title:
--   Chapter 2, def_2_8: supporting Lean bundle F000
-- statement:
--   Supporting Lean declarations for Chapter 2, source module `def_2_8`: `realOpenIntervals`, `borelAlgebraReal`, `euclideanOpenBalls`, `borelAlgebraEuclidean`. The mathematical interpretation of this bundle needs review.
-- source:
--   https://github.com/wkshum/ProbabilityTheory/blob/e6387d4fd8005d627d2aec40d10f039ddb4e4b40/ProbabilityTheory/chapter_02/def_2_8.lean

import Definitions.Def_ProbabilityTheory_chapter_02_def_2_7_F000
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.Tactic

open Set MeasureTheory

def realOpenIntervals : Set (Set ℝ) :=
  {S | ∃ a b : ℝ, a < b ∧ S = Set.Ioo a b}

@[reducible]
def borelAlgebraReal : MeasurableSpace ℝ :=
  generatedSigmaField realOpenIntervals

def euclideanOpenBalls (d : ℕ) : Set (Set (EuclideanSpace ℝ (Fin d))) :=
  {S | ∃ c : EuclideanSpace ℝ (Fin d), ∃ r : ℝ, 0 < r ∧ S = Metric.ball c r}

@[reducible]
def borelAlgebraEuclidean (d : ℕ) : MeasurableSpace (EuclideanSpace ℝ (Fin d)) :=
  generatedSigmaField (euclideanOpenBalls d)


