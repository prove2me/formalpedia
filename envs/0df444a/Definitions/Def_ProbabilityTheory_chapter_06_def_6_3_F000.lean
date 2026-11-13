-- Prove2me | Definitions.Def_ProbabilityTheory_chapter_06_def_6_3_F000
-- name    : ProbabilityTheory_chapter_06_def_6_3_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-12T08:02:04.788947+00:00
-- url     : https://prove2.me/theorems/ad245fce-6a06-4db4-9dfe-4bfbb00e74b7
-- title:
--   Chapter 6, def_6_3: supporting Lean bundle F000
-- statement:
--   Supporting Lean declarations for Chapter 6, source module `def_6_3`: `simpleApproximationSet`, `textbookIntegralNonnegative`, `textbookIntegralNonnegative_eq_top_of_unbounded`, `textbookIntegralNonnegative_eq_lintegral`, `def_6_3`. The mathematical interpretation of this bundle needs review.
-- source:
--   https://github.com/wkshum/ProbabilityTheory/blob/e6387d4fd8005d627d2aec40d10f039ddb4e4b40/ProbabilityTheory/chapter_06/def_6_3.lean

import Mathlib.MeasureTheory.Function.SimpleFunc
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic

open MeasureTheory

variable {Ω : Type*} [MeasurableSpace Ω]

def simpleApproximationSet (X : Ω → ENNReal)
    : Set (SimpleFunc Ω ENNReal) :=
  {f | ∀ ω, f ω ≤ X ω}

noncomputable def textbookIntegralNonnegative
    (μ : Measure Ω) (X : Ω → ENNReal) : ENNReal :=
  ⨆ (f : SimpleFunc Ω ENNReal) (_hf : f ∈ simpleApproximationSet X),
    f.lintegral μ





noncomputable def def_6_3 (μ : Measure Ω) (X : Ω → ENNReal)
    : ENNReal :=
  ∫⁻ ω, X ω ∂μ


