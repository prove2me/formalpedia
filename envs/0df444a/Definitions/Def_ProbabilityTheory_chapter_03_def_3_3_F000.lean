-- Prove2me | Definitions.Def_ProbabilityTheory_chapter_03_def_3_3_F000
-- name    : ProbabilityTheory_chapter_03_def_3_3_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-12T16:25:06.780223+00:00
-- url     : https://prove2.me/theorems/04ccd483-947d-4baa-8da2-65818fcb4a45
-- title:
--   Chapter 3, def_3_3: supporting Lean bundle F000
-- statement:
--   Supporting Lean declarations for Chapter 3, source module `def_3_3`: `IsSigmaFinite`. The mathematical interpretation of this bundle needs review.
-- source:
--   https://github.com/wkshum/ProbabilityTheory/blob/e6387d4fd8005d627d2aec40d10f039ddb4e4b40/ProbabilityTheory/chapter_03/def_3_3.lean

import Definitions.Def_ProbabilityTheory_chapter_03_def_3_1_F000
import Definitions.Def_ProbabilityTheory_chapter_03_def_3_1_F001
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.MeasureTheory.OuterMeasure.OfAddContent
import Mathlib.Tactic

open Set ENNReal Function

def IsSigmaFinite {Ω : Type*}
    {F₀ : FieldOfSets Ω}
    (μ : Premeasure F₀) : Prop :=
  ∃ (A : ℕ → Set Ω) (hA : ∀ i, A i ∈ F₀.carrier),
    (⋃ i, A i = univ) ∧ (∀ i, μ.μ₀ ⟨A i, hA i⟩ < ∞)


