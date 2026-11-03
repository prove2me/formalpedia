-- Prove2me | Definitions.Def_levy_foundations_levyLocalCharExponent
-- name    : levy_foundations_levyLocalCharExponent
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-30T20:54:10.064369+00:00
-- url     : https://prove2.me/theorems/87a4be7f-97de-4896-8f1e-e72d5a9e8d8f
-- title:
--   Local logarithmic characteristic exponent of a Lévy process
-- statement:
--   Take the complex logarithm of the unit-time characteristic function of a measurable Lévy process, pointwise in frequency.
-- source:
--   https://github.com/slink/LeanLevy/blob/7e73fd9b23ad52956ec2756a815889a783131ce4/LeanLevy/Levy/CharacteristicExponent.lean#L244

import Mathlib.Probability.Independence.CharacteristicFunction
import Definitions.Def_levy_foundations_isLevyProcess
import Definitions.Def_levy_foundations_localLogGoodDomain
import Definitions.Def_levy_foundations_localLogExponent

open scoped NNReal Nat
open MeasureTheory
namespace LevyFoundations
/-- Local logarithmic exponent of the unit-time Lévy marginal. -/
noncomputable def levyLocalCharExponent {Ω E : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    [MeasurableAdd₂ E]
    {X : ℝ≥0 → Ω → E} {μ : Measure Ω} [IsProbabilityMeasure μ]
    (_h : IsLevyProcess X μ) (_hX : ∀ t, Measurable (X t)) : E → ℂ :=
  LocalLog.localCharExponent (fun ξ => charFun (μ.map (X 1)) ξ)
end LevyFoundations


