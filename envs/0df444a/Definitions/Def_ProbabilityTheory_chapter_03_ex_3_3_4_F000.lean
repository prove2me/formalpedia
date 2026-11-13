-- Prove2me | Definitions.Def_ProbabilityTheory_chapter_03_ex_3_3_4_F000
-- name    : ProbabilityTheory_chapter_03_ex_3_3_4_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-12T07:58:22.51299+00:00
-- url     : https://prove2.me/theorems/18941efa-1a8a-4726-8e07-f47871032bb5
-- title:
--   Chapter 3, ex_3_3_4: supporting Lean bundle F000
-- statement:
--   Supporting Lean declarations for Chapter 3, source module `ex_3_3_4`: `dirac_step_fun`, `monotone_dirac_step_fun`, `dirac_step_function`. The mathematical interpretation of this bundle needs review.
-- source:
--   https://github.com/wkshum/ProbabilityTheory/blob/e6387d4fd8005d627d2aec40d10f039ddb4e4b40/ProbabilityTheory/chapter_03/ex_3_3_4.lean

import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.MeasureTheory.Measure.Dirac
import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
import Mathlib.MeasureTheory.Measure.Stieltjes
import Mathlib.Tactic

open MeasureTheory Set Function Filter

noncomputable def dirac_step_fun (x₀ x : ℝ) : ℝ :=
  if x < x₀ then 0 else 1

theorem monotone_dirac_step_fun (x₀ : ℝ) : Monotone (dirac_step_fun x₀) := by
  intro x y hxy
  by_cases hy : y < x₀
  · have hx : x < x₀ := lt_of_le_of_lt hxy hy
    simp [dirac_step_fun, hx, hy]
  · by_cases hx : x < x₀
    · simp [dirac_step_fun, hx, hy]
    · simp [dirac_step_fun, hx, hy]

noncomputable def dirac_step_function (x₀ : ℝ) : StieltjesFunction ℝ :=
  (monotone_dirac_step_fun x₀).stieltjesFunction


