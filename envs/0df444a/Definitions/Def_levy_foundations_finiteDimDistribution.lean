-- Prove2me | Definitions.Def_levy_foundations_finiteDimDistribution
-- name    : levy_foundations_finiteDimDistribution
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-30T21:16:05.537496+00:00
-- url     : https://prove2.me/theorems/cb0485e2-d565-402d-8b38-13dcc4f46d37
-- title:
--   Finite-dimensional joint law of a stochastic process
-- statement:
--   Finite-dimensional joint law of a stochastic process.
-- source:
--   https://github.com/slink/LeanLevy/blob/7e73fd9b23ad52956ec2756a815889a783131ce4/LeanLevy/Processes/FiniteDimensional.lean#L51

import Mathlib.MeasureTheory.Constructions.Projective
import Definitions.Def_levy_foundations_finiteDimMap

open scoped NNReal
open MeasureTheory
namespace LevyFoundations
/-- Push the base measure forward through finite-dimensional sampling. -/
noncomputable def finiteDimDistribution {Ω E : Type*}
    [MeasurableSpace Ω] [MeasurableSpace E]
    (X : ℝ≥0 → Ω → E) (μ : Measure Ω) (I : Finset ℝ≥0) :
    Measure ((i : I) → E) := μ.map (finiteDimMap X I)
end LevyFoundations


