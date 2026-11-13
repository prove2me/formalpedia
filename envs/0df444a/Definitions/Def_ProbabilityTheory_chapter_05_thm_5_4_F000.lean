-- Prove2me | Definitions.Def_ProbabilityTheory_chapter_05_thm_5_4_F000
-- name    : ProbabilityTheory_chapter_05_thm_5_4_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-12T15:26:06.223206+00:00
-- url     : https://prove2.me/theorems/eef106e6-a931-4edb-b58b-c65dc4721195
-- title:
--   Chapter 5, thm_5_4: supporting Lean bundle F000
-- statement:
--   Supporting Lean declarations for Chapter 5, source module `thm_5_4`: `jointCDF`, `marginalCDF`. The mathematical interpretation of this bundle needs review.
-- source:
--   https://github.com/wkshum/ProbabilityTheory/blob/e6387d4fd8005d627d2aec40d10f039ddb4e4b40/ProbabilityTheory/chapter_05/thm_5_4.lean

import Mathlib.Data.Set.Lattice
import Mathlib.Data.Set.Pairwise.Basic
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.MeasureTheory.PiSystem
import Mathlib.Probability.Independence.Basic
import Mathlib.Tactic

open MeasureTheory Set

noncomputable def jointCDF {Ω : Type _} [MeasurableSpace Ω]
    (μ : Measure Ω) (X Y : Ω → ℝ) (x y : ℝ) : ENNReal :=
  μ (X ⁻¹' Set.Iic x ∩ Y ⁻¹' Set.Iic y)
noncomputable def marginalCDF {Ω : Type _} [MeasurableSpace Ω]
    (μ : Measure Ω) (X : Ω → ℝ) (x : ℝ) : ENNReal :=
  μ (X ⁻¹' Set.Iic x)


