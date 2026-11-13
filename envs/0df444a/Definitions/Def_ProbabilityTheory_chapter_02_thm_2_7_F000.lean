-- Prove2me | Definitions.Def_ProbabilityTheory_chapter_02_thm_2_7_F000
-- name    : ProbabilityTheory_chapter_02_thm_2_7_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-12T15:30:27.254353+00:00
-- url     : https://prove2.me/theorems/26bf7382-71a3-4968-a1dc-c1a9638f3794
-- title:
--   Chapter 2, thm_2_7: supporting Lean bundle F000
-- statement:
--   Supporting Lean declarations for Chapter 2, source module `thm_2_7`: `realStrictClosedIntervals`, `thm_2_7_closedApprox`, `thm_2_7_closedApprox_mem_generateFrom_strictClosed`, `thm_2_7_iUnion_closedApprox_eq_Ioo`, `thm_2_7_closedIntervals_borel_inclusion`, and 4 others. The mathematical interpretation of this bundle needs review.
-- source:
--   https://github.com/wkshum/ProbabilityTheory/blob/e6387d4fd8005d627d2aec40d10f039ddb4e4b40/ProbabilityTheory/chapter_02/thm_2_7.lean

import Definitions.Def_ProbabilityTheory_chapter_02_def_2_8_F000
import Definitions.Def_ProbabilityTheory_chapter_02_def_2_8_F001
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.Tactic

open Set MeasureTheory

def realStrictClosedIntervals : Set (Set ℝ) :=
  {S | ∃ a b : ℝ, a < b ∧ Set.Icc a b = S}

def thm_2_7_closedApprox (a b : ℝ) (n : ℕ) : Set ℝ :=
  let δ : ℝ := 1 / ((n : ℝ) + 1)
  if _h : a + δ < b - δ then Set.Icc (a + δ) (b - δ) else ∅


