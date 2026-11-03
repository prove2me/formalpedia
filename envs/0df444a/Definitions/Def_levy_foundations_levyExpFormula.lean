-- Prove2me | Definitions.Def_levy_foundations_levyExpFormula
-- name    : levy_foundations_levyExpFormula
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-30T21:00:28.063665+00:00
-- url     : https://prove2.me/theorems/6ab851b3-0403-4ee5-af73-614b5840bc0d
-- title:
--   Lévy exponential characteristic-function formula
-- statement:
--   Package the Lévy characteristic exponent as the function of nonnegative time and frequency obtained by exponentiating the product of time and the exponent.
-- source:
--   https://github.com/slink/LeanLevy/blob/7e73fd9b23ad52956ec2756a815889a783131ce4/LeanLevy/Levy/CharacteristicExponent.lean#L497

import Mathlib.Probability.Independence.CharacteristicFunction
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Definitions.Def_levy_foundations_isLevyProcess
import Definitions.Def_levy_foundations_charExponent
import Definitions.Def_levy_foundations_levyGoodDomain
import Definitions.Def_levy_foundations_levyLocalCharExponent

open MeasureTheory
open scoped NNReal
namespace LevyFoundations
/-- Exponential semigroup of the Lévy characteristic exponent. -/
noncomputable def levyExpFormula {Ω E : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    [MeasurableAdd₂ E]
    {X : ℝ≥0 → Ω → E} {μ : Measure Ω} [IsProbabilityMeasure μ]
    (h : LevyFoundations.IsLevyProcess X μ)
    (hX : ∀ t, Measurable (X t))
    (t : ℝ≥0) (ξ : E) : ℂ :=
  Complex.exp (↑(t : ℝ) * LevyFoundations.charExponent h ξ)
end LevyFoundations


