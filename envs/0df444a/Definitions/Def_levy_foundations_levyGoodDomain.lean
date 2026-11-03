-- Prove2me | Definitions.Def_levy_foundations_levyGoodDomain
-- name    : levy_foundations_levyGoodDomain
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-30T20:52:49.337928+00:00
-- url     : https://prove2.me/theorems/ce4125be-b8d9-4dde-9aa5-c91864a9bbf0
-- title:
--   Good logarithm domain for a Lévy unit-time characteristic function
-- statement:
--   The frequencies where the Lévy process unit-time marginal characteristic function lies in the complex slit plane.
-- source:
--   https://github.com/slink/LeanLevy/blob/7e73fd9b23ad52956ec2756a815889a783131ce4/LeanLevy/Levy/CharacteristicExponent.lean#L232

import Mathlib.Probability.Independence.CharacteristicFunction
import Definitions.Def_levy_foundations_isLevyProcess
import Definitions.Def_levy_foundations_localLogGoodDomain
import Definitions.Def_levy_foundations_localLogExponent

open scoped NNReal Nat
open MeasureTheory
namespace LevyFoundations
/-- Domain on which the time-one characteristic function has a continuous log. -/
def levyGoodDomain {Ω E : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    [MeasurableAdd₂ E]
    {X : ℝ≥0 → Ω → E} {μ : Measure Ω} [IsProbabilityMeasure μ]
    (_h : IsLevyProcess X μ) (_hX : ∀ t, Measurable (X t)) : Set E :=
  LocalLog.goodDomain (fun ξ => charFun (μ.map (X 1)) ξ)
end LevyFoundations


