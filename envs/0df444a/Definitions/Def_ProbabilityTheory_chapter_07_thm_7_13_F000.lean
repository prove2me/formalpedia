-- Prove2me | Definitions.Def_ProbabilityTheory_chapter_07_thm_7_13_F000
-- name    : ProbabilityTheory_chapter_07_thm_7_13_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-12T15:26:42.215124+00:00
-- url     : https://prove2.me/theorems/f2b83846-932b-4f5c-9e81-fb894b8b06a4
-- title:
--   Chapter 7, thm_7_13: supporting Lean bundle F000
-- statement:
--   Supporting Lean declarations for Chapter 7, source module `thm_7_13`: `thm_7_13`. The mathematical interpretation of this bundle needs review.
-- source:
--   https://github.com/wkshum/ProbabilityTheory/blob/e6387d4fd8005d627d2aec40d10f039ddb4e4b40/ProbabilityTheory/chapter_07/thm_7_13.lean

import Definitions.Def_ProbabilityTheory_chapter_05_def_5_2_F000
import Definitions.Def_ProbabilityTheory_chapter_06_def_6_3_F000
import Mathlib.MeasureTheory.Function.SimpleFunc
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.Probability.Independence.Basic
import Mathlib.Probability.Independence.Integration
import Mathlib.Tactic

open MeasureTheory

theorem thm_7_13 {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {X Y : Ω → ℝ} (hXY : def_5_2 μ X Y) (hX : Integrable X μ) (hY : Integrable Y μ)
    (_hXY_int : Integrable (fun ω => X ω * Y ω) μ) :
    ∫ ω, X ω * Y ω ∂μ = (∫ ω, X ω ∂μ) * ∫ ω, Y ω ∂μ := by
  simpa [def_5_2] using
    (ProbabilityTheory.IndepFun.integral_fun_mul_eq_mul_integral
      (μ := μ) (X := X) (Y := Y) hXY hX.1 hY.1)


