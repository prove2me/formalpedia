-- Prove2me | Definitions.Def_ProbabilityTheory_chapter_02_def_2_3_F000
-- name    : ProbabilityTheory_chapter_02_def_2_3_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-12T07:55:18.227793+00:00
-- url     : https://prove2.me/theorems/7ebdf0ef-b974-4fc9-af64-aea52d25d61b
-- title:
--   Chapter 2, def_2_3: supporting Lean bundle F000
-- statement:
--   Supporting Lean declarations for Chapter 2, source module `def_2_3`: `SigmaField`, `IsMeasurableIn`, `IsSubSigmaField`, `def_2_3`. The mathematical interpretation of this bundle needs review.
-- source:
--   https://github.com/wkshum/ProbabilityTheory/blob/e6387d4fd8005d627d2aec40d10f039ddb4e4b40/ProbabilityTheory/chapter_02/def_2_3.lean

import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.Tactic

open Set

abbrev SigmaField (Ω : Type*) := MeasurableSpace Ω

def IsMeasurableIn {Ω : Type*} (𝓕 : SigmaField Ω) (A : Set Ω) : Prop :=
  @MeasurableSet Ω 𝓕 A

def IsSubSigmaField {Ω : Type*} (𝓖 𝓕 : SigmaField Ω) : Prop :=
  ∀ ⦃A : Set Ω⦄, IsMeasurableIn 𝓖 A → IsMeasurableIn 𝓕 A

def def_2_3 (Ω : Type*) : Type _ :=
  SigmaField Ω


