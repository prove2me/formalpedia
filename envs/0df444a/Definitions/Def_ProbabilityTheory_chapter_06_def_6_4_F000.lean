-- Prove2me | Definitions.Def_ProbabilityTheory_chapter_06_def_6_4_F000
-- name    : ProbabilityTheory_chapter_06_def_6_4_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-12T08:02:17.195209+00:00
-- url     : https://prove2.me/theorems/e9ca4c38-4250-43b3-aec3-842b01a552cf
-- title:
--   Chapter 6, def_6_4: supporting Lean bundle F000
-- statement:
--   Supporting Lean declarations for Chapter 6, source module `def_6_4`: `positivePart`, `negativePart`, `def_6_4`, `measurable_positivePart`, `measurable_negativePart`, and 4 others. The mathematical interpretation of this bundle needs review.
-- source:
--   https://github.com/wkshum/ProbabilityTheory/blob/e6387d4fd8005d627d2aec40d10f039ddb4e4b40/ProbabilityTheory/chapter_06/def_6_4.lean

import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.Tactic

open MeasureTheory

noncomputable def positivePart {Ω : Type*} [MeasurableSpace Ω] (X : Ω → ℝ) : Ω → ℝ :=
  fun ω => max (X ω) 0

noncomputable def negativePart {Ω : Type*} [MeasurableSpace Ω] (X : Ω → ℝ) : Ω → ℝ :=
  fun ω => -min (X ω) 0

noncomputable def def_6_4 {Ω : Type*} [MeasurableSpace Ω] (X : Ω → ℝ) : (Ω → ℝ) × (Ω → ℝ) :=
  (positivePart X, negativePart X)
section PositiveNegativeParts

variable {Ω : Type*} [MeasurableSpace Ω] {X : Ω → ℝ}












end PositiveNegativeParts


