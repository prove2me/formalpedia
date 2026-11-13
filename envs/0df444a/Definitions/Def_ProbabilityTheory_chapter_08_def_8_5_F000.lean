-- Prove2me | Definitions.Def_ProbabilityTheory_chapter_08_def_8_5_F000
-- name    : ProbabilityTheory_chapter_08_def_8_5_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-12T07:39:14.363909+00:00
-- url     : https://prove2.me/theorems/b447efd4-d0ab-4451-8796-142ed3b5e083
-- title:
--   Definition 8.5: Total variation distance
-- statement:
--   The total variation distance of two measures is the supremum, over measurable sets, of the absolute difference of their real-valued masses.
-- source:
--   Kenneth W. Shum (2023), Definition 8.5: Total variation distance, Lean source: https://github.com/wkshum/ProbabilityTheory/blob/e6387d4fd8005d627d2aec40d10f039ddb4e4b40/ProbabilityTheory/chapter_08/def_8_5.lean

import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.MeasureTheory.Measure.MeasureSpaceDef

open MeasureTheory Set

noncomputable def totalVariationDistance
    {Ω : Type*} [MeasurableSpace Ω] (P Q : Measure Ω) : ℝ :=
  sSup {d : ℝ | ∃ A : Set Ω, MeasurableSet A ∧ d = |P.real A - Q.real A|}

noncomputable def def_8_5
    {Ω : Type*} [MeasurableSpace Ω] (P Q : Measure Ω) : ℝ :=
  totalVariationDistance P Q


