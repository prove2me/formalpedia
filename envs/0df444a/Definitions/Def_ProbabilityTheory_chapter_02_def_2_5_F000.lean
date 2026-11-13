-- Prove2me | Definitions.Def_ProbabilityTheory_chapter_02_def_2_5_F000
-- name    : ProbabilityTheory_chapter_02_def_2_5_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-12T07:55:42.05734+00:00
-- url     : https://prove2.me/theorems/fce104c9-b471-490c-846d-c84fee50d91a
-- title:
--   Chapter 2, def_2_5: supporting Lean bundle F000
-- statement:
--   Supporting Lean declarations for Chapter 2, source module `def_2_5`: `MeasureOn`, `IsFiniteMeasureOn`, `IsProbabilityMeasureOn`, `MeasureSpaceData`, `ProbabilitySpaceData`, and 1 others. The mathematical interpretation of this bundle needs review.
-- source:
--   https://github.com/wkshum/ProbabilityTheory/blob/e6387d4fd8005d627d2aec40d10f039ddb4e4b40/ProbabilityTheory/chapter_02/def_2_5.lean

import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.Tactic

open MeasureTheory Set

abbrev MeasureOn (Ω : Type*) [MeasurableSpace Ω] := Measure Ω

def IsFiniteMeasureOn {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) : Prop :=
  μ Set.univ < ⊤

def IsProbabilityMeasureOn {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) : Prop :=
  IsProbabilityMeasure μ

structure MeasureSpaceData (Ω : Type*) [MeasurableSpace Ω] where
  measure : Measure Ω

structure ProbabilitySpaceData (Ω : Type*) [MeasurableSpace Ω]
  extends MeasureSpaceData Ω where
  (is_probability : IsProbabilityMeasure measure)

def def_2_5 {Ω : Type*} [MeasurableSpace Ω] := Measure Ω

section checking_ENNReal

open ENNReal

example (c : ENNReal) : c + ∞ = ∞ := by
  exact add_top c

example : ∞ * ∞ = ∞ := by
  exact top_mul_top
end checking_ENNReal


