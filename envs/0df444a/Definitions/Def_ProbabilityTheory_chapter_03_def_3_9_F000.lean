-- Prove2me | Definitions.Def_ProbabilityTheory_chapter_03_def_3_9_F000
-- name    : ProbabilityTheory_chapter_03_def_3_9_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-12T07:58:09.288069+00:00
-- url     : https://prove2.me/theorems/fe4bd8f8-6a7d-4679-9071-8d90884efef9
-- title:
--   Chapter 3, def_3_9: supporting Lean bundle F000
-- statement:
--   Supporting Lean declarations for Chapter 3, source module `def_3_9`: `IsNullSet`, `IsCompleteSpace`. The mathematical interpretation of this bundle needs review.
-- source:
--   https://github.com/wkshum/ProbabilityTheory/blob/e6387d4fd8005d627d2aec40d10f039ddb4e4b40/ProbabilityTheory/chapter_03/def_3_9.lean

import Mathlib.MeasureTheory.Measure.NullMeasurable

open MeasureTheory Set

def IsNullSet {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (N : Set Ω) : Prop :=
  ∃ E, MeasurableSet E ∧ N ⊆ E ∧ μ E = 0

def IsCompleteSpace {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) : Prop :=
  ∀ N, IsNullSet μ N → MeasurableSet N


