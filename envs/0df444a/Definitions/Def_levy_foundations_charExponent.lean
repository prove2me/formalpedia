-- Prove2me | Definitions.Def_levy_foundations_charExponent
-- name    : levy_foundations_charExponent
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-30T20:58:49.474148+00:00
-- url     : https://prove2.me/theorems/c565a5c3-8a59-4249-b3dc-3506367dd09d
-- title:
--   Generic Lévy characteristic exponent
-- statement:
--   For a process taking values in an additive group with a real inner product, define the characteristic exponent as the right limit of the characteristic function's principal logarithm divided by time.
-- source:
--   https://github.com/slink/LeanLevy/blob/7e73fd9b23ad52956ec2756a815889a783131ce4/LeanLevy/Processes/LevyProcess.lean#L87

import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic
import Mathlib.Probability.Independence.CharacteristicFunction
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Definitions.Def_levy_foundations_isLevyProcess

open MeasureTheory Filter
open scoped NNReal
namespace LevyFoundations
/-- Characteristic exponent defined by the right-hand logarithmic derivative at zero. -/
noncomputable def charExponent {Ω E : Type*}
    [MeasurableSpace Ω] [MeasurableSpace E]
    [TopologicalSpace E] [AddGroup E] [Inner ℝ E]
    {X : ℝ≥0 → Ω → E} {μ : Measure Ω}
    (_h : IsLevyProcess X μ) : E → ℂ :=
  fun ξ => limUnder (nhdsWithin (0 : ℝ≥0) (Set.Ioi 0))
    (fun t => Complex.log (charFun (μ.map (X t)) ξ) / ↑(t : ℝ))
end LevyFoundations


