-- Prove2me | Definitions.Def_levy_foundations_probabilityCharacteristicFun
-- name    : levy_foundations_probabilityCharacteristicFun
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-30T21:08:40.567518+00:00
-- url     : https://prove2.me/theorems/b6e27b02-9c5f-46e2-ad21-e8b565ae0cc5
-- title:
--   Characteristic function of a probability measure on the real line
-- statement:
--   Define a real probability measure's characteristic function using Mathlib's underlying measure charFun, as in frozen LeanLevy.
-- source:
--   https://github.com/slink/LeanLevy/blob/7e73fd9b23ad52956ec2756a815889a783131ce4/LeanLevy/Probability/Characteristic.lean#L68

import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure

open MeasureTheory
namespace LevyFoundations
/-- Characteristic function of a probability law on the real line. -/
noncomputable def probabilityCharacteristicFun (μ : ProbabilityMeasure ℝ)
    (ξ : ℝ) : ℂ := charFun (μ : Measure ℝ) ξ
end LevyFoundations


