-- Prove2me | Definitions.Def_ProbabilityTheory_chapter_06_def_6_6_F000
-- name    : ProbabilityTheory_chapter_06_def_6_6_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-12T15:27:15.710736+00:00
-- url     : https://prove2.me/theorems/f682b641-4566-4213-a58f-59fe716a0d03
-- title:
--   Chapter 6, def_6_6: supporting Lean bundle F000
-- statement:
--   Supporting Lean declarations for Chapter 6, source module `def_6_6`: `posPart`, `negPart`, `posLIntegral`, `negLIntegral`, `textbookIntegrable`, and 6 others. The mathematical interpretation of this bundle needs review.
-- source:
--   https://github.com/wkshum/ProbabilityTheory/blob/e6387d4fd8005d627d2aec40d10f039ddb4e4b40/ProbabilityTheory/chapter_06/def_6_6.lean

import Definitions.Def_ProbabilityTheory_chapter_06_def_6_5_F000
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.Tactic

open MeasureTheory

namespace Def66RealSupport

noncomputable def posPart {Ω : Type*} [MeasurableSpace Ω] (X : Ω → EReal) : Ω → ENNReal :=
  fun ω => (X ω).toENNReal
noncomputable def negPart {Ω : Type*} [MeasurableSpace Ω] (X : Ω → EReal) : Ω → ENNReal :=
  fun ω => (-X ω).toENNReal
noncomputable def posLIntegral {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (X : Ω → EReal) : ENNReal :=
  ∫⁻ ω, posPart X ω ∂μ
noncomputable def negLIntegral {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (X : Ω → EReal) : ENNReal :=
  ∫⁻ ω, negPart X ω ∂μ
def textbookIntegrable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (X : Ω → EReal) : Prop :=
  posLIntegral μ X < ⊤ ∧ negLIntegral μ X < ⊤
noncomputable def textbookValue {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (X : Ω → EReal) : ℝ :=
  (((posLIntegral μ X : EReal) - (negLIntegral μ X : EReal)).toReal)
end Def66RealSupport

def complexTextbookIntegrable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (Z : Ω → ℂ) : Prop :=
  Def66RealSupport.textbookIntegrable μ (fun ω => ((Z ω).re : EReal)) ∧
    Def66RealSupport.textbookIntegrable μ (fun ω => ((Z ω).im : EReal))

noncomputable def complexTextbookIntegral {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (Z : Ω → ℂ) : Option ℂ := by
  classical
  exact
    if hZ : complexTextbookIntegrable μ Z then
      some
        (Complex.ofReal
            (Def66RealSupport.textbookValue μ (fun ω => ((Z ω).re : EReal))) +
          Complex.I *
            Complex.ofReal
              (Def66RealSupport.textbookValue μ (fun ω => ((Z ω).im : EReal))))
    else
      none

noncomputable def def_6_6 {Ω : Type*} [MeasurableSpace Ω]
  (μ : Measure Ω) (Z : Ω → ℂ) :
    Option ℂ :=
  complexTextbookIntegral μ Z


