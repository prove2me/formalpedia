-- Prove2me | Definitions.Def_ProbabilityTheory_chapter_02_thm_2_8_F001
-- name    : ProbabilityTheory_chapter_02_thm_2_8_F001
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-12T15:30:00.865933+00:00
-- url     : https://prove2.me/theorems/d03ed2a1-b3b3-4934-9af2-449912516450
-- title:
--   Chapter 2, thm_2_8: supporting Lean bundle F001
-- statement:
--   Supporting Lean declarations for Chapter 2, source module `thm_2_8`: `euclideanOpenBoxes`, `metricOpenBalls_isTopologicalBasis`. The mathematical interpretation of this bundle needs review.
-- source:
--   https://github.com/wkshum/ProbabilityTheory/blob/e6387d4fd8005d627d2aec40d10f039ddb4e4b40/ProbabilityTheory/chapter_02/thm_2_8.lean

import Definitions.Def_ProbabilityTheory_chapter_02_thm_2_8_F000
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
import Mathlib.MeasureTheory.MeasurableSpace.Pi
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.Tactic

open Set MeasureTheory MeasurableSpace

open scoped Pointwise

def euclideanOpenBoxes (d : ℕ) :
    Set (Set (EuclideanSpace ℝ (Fin d))) :=
  Set.preimage (fun x : EuclideanSpace ℝ (Fin d) => fun i : Fin d => x i) ''
    openBoxes d


