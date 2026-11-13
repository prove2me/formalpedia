-- Prove2me | Definitions.Def_ProbabilityTheory_chapter_02_def_2_7_F000
-- name    : ProbabilityTheory_chapter_02_def_2_7_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-12T15:28:30.691881+00:00
-- url     : https://prove2.me/theorems/6d4d9a1e-d670-4bf2-b5a3-bc77d785f67d
-- title:
--   Chapter 2, def_2_7: supporting Lean bundle F000
-- statement:
--   Supporting Lean declarations for Chapter 2, source module `def_2_7`: `generatedSigmaField`, `generatedSigmaFieldSeq`, `generatedSigmaField_contains`, `generatedSigmaFieldSeq_contains`, `def_2_7`. The mathematical interpretation of this bundle needs review.
-- source:
--   https://github.com/wkshum/ProbabilityTheory/blob/e6387d4fd8005d627d2aec40d10f039ddb4e4b40/ProbabilityTheory/chapter_02/def_2_7.lean

import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.Tactic

open Set MeasureTheory

@[reducible]
def generatedSigmaField {Ω : Type*} (C : Set (Set Ω)) : MeasurableSpace Ω :=
  MeasurableSpace.generateFrom C

@[reducible]
def generatedSigmaFieldSeq {Ω : Type*} (B : ℕ → Set Ω) : MeasurableSpace Ω :=
  generatedSigmaField (Set.range B)



@[reducible]
def def_2_7 {Ω : Type*} (C : Set (Set Ω)) : MeasurableSpace Ω :=
  generatedSigmaField C


