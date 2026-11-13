-- Prove2me | Definitions.Def_ProbabilityTheory_chapter_06_thm_6_3_F000
-- name    : ProbabilityTheory_chapter_06_thm_6_3_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-12T08:02:43.833381+00:00
-- url     : https://prove2.me/theorems/d0299bb3-af78-4126-94d7-6e3087b01317
-- title:
--   Chapter 6, thm_6_3: supporting Lean bundle F000
-- statement:
--   Supporting Lean declarations for Chapter 6, source module `thm_6_3`: `sourceSimpleApproximationSet`, `sourceSimpleApproximationIntegral`, `sourceSupIntegral`, `sourceSimpleApproximationSet_mono`, `sourceSupIntegral_mono`, and 2 others. The mathematical interpretation of this bundle needs review.
-- source:
--   https://github.com/wkshum/ProbabilityTheory/blob/e6387d4fd8005d627d2aec40d10f039ddb4e4b40/ProbabilityTheory/chapter_06/thm_6_3.lean

import Mathlib.MeasureTheory.Integral.Lebesgue.Basic

open MeasureTheory
open scoped ENNReal

variable {Ω : Type*} [MeasurableSpace Ω]

def sourceSimpleApproximationSet (X : Ω → ENNReal) : Set (SimpleFunc Ω ENNReal) :=
  {f | ∀ ω, f ω ≤ X ω}
noncomputable def sourceSimpleApproximationIntegral
    (μ : Measure Ω) (f : SimpleFunc Ω ENNReal) : ENNReal :=
  f.lintegral μ
noncomputable def sourceSupIntegral (μ : Measure Ω) (X : Ω → ENNReal) : ENNReal :=
  ⨆ f : sourceSimpleApproximationSet X, sourceSimpleApproximationIntegral μ f.1


