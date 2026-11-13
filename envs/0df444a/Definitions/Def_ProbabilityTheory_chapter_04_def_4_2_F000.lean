-- Prove2me | Definitions.Def_ProbabilityTheory_chapter_04_def_4_2_F000
-- name    : ProbabilityTheory_chapter_04_def_4_2_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-12T07:58:56.640982+00:00
-- url     : https://prove2.me/theorems/e9caf222-2329-4420-a550-2656fe8a8284
-- title:
--   Chapter 4, def_4_2: supporting Lean bundle F000
-- statement:
--   Supporting Lean declarations for Chapter 4, source module `def_4_2`: `IsMeasurable`. The mathematical interpretation of this bundle needs review.
-- source:
--   https://github.com/wkshum/ProbabilityTheory/blob/e6387d4fd8005d627d2aec40d10f039ddb4e4b40/ProbabilityTheory/chapter_04/def_4_2.lean

import Mathlib.MeasureTheory.MeasurableSpace.Basic

open Set

def IsMeasurable {Ω Ω' : Type*} (F : MeasurableSpace Ω) (G : MeasurableSpace Ω')
    (f : Ω → Ω') : Prop :=
  ∀ B : Set Ω', @MeasurableSet Ω' G B → @MeasurableSet Ω F (f ⁻¹' B)


