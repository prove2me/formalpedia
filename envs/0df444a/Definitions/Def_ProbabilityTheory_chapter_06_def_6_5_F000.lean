-- Prove2me | Definitions.Def_ProbabilityTheory_chapter_06_def_6_5_F000
-- name    : ProbabilityTheory_chapter_06_def_6_5_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-12T08:02:32.501221+00:00
-- url     : https://prove2.me/theorems/b6909dcc-58f2-42c7-90ae-267617475f6e
-- title:
--   Chapter 6, def_6_5: supporting Lean bundle F000
-- statement:
--   Supporting Lean declarations for Chapter 6, source module `def_6_5`: `posPart`, `negPart`, `posLIntegral`, `negLIntegral`, `textbookIntegral`, and 8 others. The mathematical interpretation of this bundle needs review.
-- source:
--   https://github.com/wkshum/ProbabilityTheory/blob/e6387d4fd8005d627d2aec40d10f039ddb4e4b40/ProbabilityTheory/chapter_06/def_6_5.lean

import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.Tactic

open MeasureTheory

namespace Def65Support

noncomputable def posPart {Ω : Type*} [MeasurableSpace Ω] (X : Ω → EReal)
  : Ω → ENNReal :=
  fun ω => (X ω).toENNReal

noncomputable def negPart {Ω : Type*} [MeasurableSpace Ω] (X : Ω → EReal)
  : Ω → ENNReal :=
  fun ω => (-X ω).toENNReal

noncomputable def posLIntegral {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω)
    (X : Ω → EReal) : ENNReal :=
  ∫⁻ ω, posPart X ω ∂μ

noncomputable def negLIntegral {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω)
    (X : Ω → EReal) : ENNReal :=
  ∫⁻ ω, negPart X ω ∂μ
end Def65Support

noncomputable def textbookIntegral {Ω : Type*} [MeasurableSpace Ω]
  (μ : Measure Ω) (X : Ω → EReal) : Option EReal :=
  if _hUndefined :
      Def65Support.posLIntegral μ X = ⊤ ∧ Def65Support.negLIntegral μ X = ⊤ then
    none
  else
    let p := Def65Support.posLIntegral μ X
    let n := Def65Support.negLIntegral μ X
    some ((p : EReal) - (n : EReal))

def textbookIntegrable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (X : Ω → EReal) :
    Prop :=
  Def65Support.posLIntegral μ X < ⊤ ∧ Def65Support.negLIntegral μ X < ⊤

noncomputable def def_6_5 {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (X : Ω → EReal) :
    Option EReal :=
  textbookIntegral μ X

noncomputable def textbookIntegralOn {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (s : Set Ω) (X : Ω → EReal) : Option EReal :=
  textbookIntegral μ (s.indicator X)
section TextbookIntegralLemmas

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {X : Ω → EReal}






end TextbookIntegralLemmas


