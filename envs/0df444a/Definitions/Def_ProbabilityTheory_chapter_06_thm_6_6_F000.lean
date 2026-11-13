-- Prove2me | Definitions.Def_ProbabilityTheory_chapter_06_thm_6_6_F000
-- name    : ProbabilityTheory_chapter_06_thm_6_6_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-12T15:27:56.045002+00:00
-- url     : https://prove2.me/theorems/8f8dc55d-bc9a-45f3-a71d-4a52a6dcba14
-- title:
--   Chapter 6, thm_6_6: supporting Lean bundle F000
-- statement:
--   Supporting Lean declarations for Chapter 6, source module `thm_6_6`: `textbookIntegrable`, `realAbsIntegral`, `realPartAbsIntegral`, `imagPartAbsIntegral`, `complexTextbookIntegrable`, and 5 others. The mathematical interpretation of this bundle needs review.
-- source:
--   https://github.com/wkshum/ProbabilityTheory/blob/e6387d4fd8005d627d2aec40d10f039ddb4e4b40/ProbabilityTheory/chapter_06/thm_6_6.lean

import Definitions.Def_ProbabilityTheory_chapter_06_def_6_6_F000
import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex
import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.Tactic

open MeasureTheory

namespace Thm66Support

open Def66RealSupport

def textbookIntegrable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (X : Ω → EReal) : Prop :=
  posLIntegral μ X < ⊤ ∧ negLIntegral μ X < ⊤
noncomputable def realAbsIntegral {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (X : Ω → EReal) : ENNReal :=
  posLIntegral μ X + negLIntegral μ X
noncomputable def realPartAbsIntegral {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (Z : Ω → ℂ) : ENNReal :=
  ∫⁻ ω, ENNReal.ofReal |(Z ω).re| ∂μ
noncomputable def imagPartAbsIntegral {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (Z : Ω → ℂ) : ENNReal :=
  ∫⁻ ω, ENNReal.ofReal |(Z ω).im| ∂μ
def complexTextbookIntegrable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (Z : Ω → ℂ) : Prop :=
  realPartAbsIntegral μ Z < ⊤ ∧ imagPartAbsIntegral μ Z < ⊤
noncomputable def complexAbsIntegral {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (Z : Ω → ℂ) : ENNReal :=
  ∫⁻ ω, ENNReal.ofReal ‖Z ω‖ ∂μ


end Thm66Support


