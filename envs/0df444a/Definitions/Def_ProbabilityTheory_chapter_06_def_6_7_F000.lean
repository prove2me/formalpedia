-- Prove2me | Definitions.Def_ProbabilityTheory_chapter_06_def_6_7_F000
-- name    : ProbabilityTheory_chapter_06_def_6_7_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-12T15:27:35.958819+00:00
-- url     : https://prove2.me/theorems/5970ef9f-b1ca-4fef-bf67-0d91600da950
-- title:
--   Chapter 6, def_6_7: supporting Lean bundle F000
-- statement:
--   Supporting Lean declarations for Chapter 6, source module `def_6_7`: `textbookIntegral`, `expectation`, `def_6_7`. The mathematical interpretation of this bundle needs review.
-- source:
--   https://github.com/wkshum/ProbabilityTheory/blob/e6387d4fd8005d627d2aec40d10f039ddb4e4b40/ProbabilityTheory/chapter_06/def_6_7.lean

import Definitions.Def_ProbabilityTheory_chapter_06_def_6_6_F000
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.Tactic

open MeasureTheory

namespace Def67Support

open Def66RealSupport

noncomputable def textbookIntegral {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (X : Ω → EReal) : Option EReal :=
  if posLIntegral P X = ⊤ ∧ negLIntegral P X = ⊤ then
    none
  else
    some ((posLIntegral P X : EReal) - (negLIntegral P X : EReal))
end Def67Support

noncomputable def expectation {Ω : Type*}
  [MeasurableSpace Ω] (P : Measure Ω)
    (X : Ω → EReal) : Option EReal :=
  Def67Support.textbookIntegral P X

noncomputable def def_6_7 {Ω : Type*}
  [MeasurableSpace Ω] (P : Measure Ω) (X : Ω → EReal) :
    Option EReal :=
  expectation P X


