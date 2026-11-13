-- Prove2me | Definitions.Def_ProbabilityTheory_chapter_06_def_6_2_F000
-- name    : ProbabilityTheory_chapter_06_def_6_2_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-12T08:01:55.449189+00:00
-- url     : https://prove2.me/theorems/03107462-c1ea-4fc2-9742-c38637d5fe7e
-- title:
--   Chapter 6, def_6_2: supporting Lean bundle F000
-- statement:
--   Supporting Lean declarations for Chapter 6, source module `def_6_2`: `simpleFunctionIntegralTerm`, `simpleFunctionHasPosInf`, `simpleFunctionHasNegInf`, `simpleFunctionIntegralDefined`, `simpleFunctionIntegralValue`, and 2 others. The mathematical interpretation of this bundle needs review.
-- source:
--   https://github.com/wkshum/ProbabilityTheory/blob/e6387d4fd8005d627d2aec40d10f039ddb4e4b40/ProbabilityTheory/chapter_06/def_6_2.lean

import Mathlib.MeasureTheory.Function.SimpleFunc
import Mathlib.Tactic

open MeasureTheory
open scoped BigOperators

variable {Ω : Type*} [MeasurableSpace Ω]

noncomputable def simpleFunctionIntegralTerm
    (μ : Measure Ω) (X : SimpleFunc Ω EReal) (x : EReal) : EReal :=
  x * (μ (X ⁻¹' {x}) : EReal)

def simpleFunctionHasPosInf (μ : Measure Ω) (X : SimpleFunc Ω EReal)
  : Prop :=
  ∃ x ∈ X.range, simpleFunctionIntegralTerm μ X x = ⊤

def simpleFunctionHasNegInf (μ : Measure Ω) (X : SimpleFunc Ω EReal) : Prop :=
  ∃ x ∈ X.range, simpleFunctionIntegralTerm μ X x = ⊥

def simpleFunctionIntegralDefined (μ : Measure Ω) (X : SimpleFunc Ω EReal) : Prop :=
  ¬ (simpleFunctionHasPosInf μ X ∧ simpleFunctionHasNegInf μ X)

noncomputable def simpleFunctionIntegralValue
  (μ : Measure Ω) (X : SimpleFunc Ω EReal) : EReal :=
  Finset.sum X.range fun x => simpleFunctionIntegralTerm μ X x

noncomputable def def_6_2 (μ : Measure Ω) (X : SimpleFunc Ω EReal) : Option EReal :=
  by
    classical
    exact
      if h : simpleFunctionIntegralDefined μ X then
        some (simpleFunctionIntegralValue μ X)
      else
        none


