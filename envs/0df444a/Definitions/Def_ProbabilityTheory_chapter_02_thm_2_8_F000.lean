-- Prove2me | Definitions.Def_ProbabilityTheory_chapter_02_thm_2_8_F000
-- name    : ProbabilityTheory_chapter_02_thm_2_8_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-12T15:29:35.293778+00:00
-- url     : https://prove2.me/theorems/f9172181-e4e6-4083-835f-63beb3854f7a
-- title:
--   Chapter 2, thm_2_8: supporting Lean bundle F000
-- statement:
--   Supporting Lean declarations for Chapter 2, source module `thm_2_8`: `openBoxes`. The mathematical interpretation of this bundle needs review.
-- source:
--   https://github.com/wkshum/ProbabilityTheory/blob/e6387d4fd8005d627d2aec40d10f039ddb4e4b40/ProbabilityTheory/chapter_02/thm_2_8.lean

import Definitions.Def_ProbabilityTheory_chapter_02_def_2_8_F001
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
import Mathlib.MeasureTheory.MeasurableSpace.Pi
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.Tactic

open Set MeasureTheory MeasurableSpace

open scoped Pointwise

def openBoxes (d : ℕ) : Set (Set (Fin d → ℝ)) :=
  {s | ∃ a b : Fin d → ℝ,
    (∀ i, a i < b i) ∧ s = Set.pi Set.univ (fun i => Ioo (a i) (b i))}


