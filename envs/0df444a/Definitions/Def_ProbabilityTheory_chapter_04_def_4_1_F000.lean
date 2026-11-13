-- Prove2me | Definitions.Def_ProbabilityTheory_chapter_04_def_4_1_F000
-- name    : ProbabilityTheory_chapter_04_def_4_1_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-12T07:58:49.221882+00:00
-- url     : https://prove2.me/theorems/060ab0cf-cd4b-4886-a036-6780fcd508f0
-- title:
--   Chapter 4, def_4_1: supporting Lean bundle F000
-- statement:
--   Supporting Lean declarations for Chapter 4, source module `def_4_1`: `IsRealMeasurable`. The mathematical interpretation of this bundle needs review.
-- source:
--   https://github.com/wkshum/ProbabilityTheory/blob/e6387d4fd8005d627d2aec40d10f039ddb4e4b40/ProbabilityTheory/chapter_04/def_4_1.lean

import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.MeasureTheory.MeasurableSpace.Basic

open MeasureTheory Set

def IsRealMeasurable {Ω : Type*} [MeasurableSpace Ω] (X : Ω → ℝ) : Prop :=
  ∀ B : Set ℝ, MeasurableSet B → MeasurableSet (X ⁻¹' B)

example {Ω : Type*} [MeasurableSpace Ω] (X : Ω → ℝ) :
    IsRealMeasurable X ↔ Measurable X :=
  Iff.rfl


