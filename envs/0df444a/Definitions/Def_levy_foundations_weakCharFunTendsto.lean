-- Prove2me | Definitions.Def_levy_foundations_weakCharFunTendsto
-- name    : levy_foundations_weakCharFunTendsto
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-30T21:18:25.049227+00:00
-- url     : https://prove2.me/theorems/07714142-ee8d-4df1-a2c7-b9cbc980defb
-- title:
--   Pointwise convergence of probability characteristic functions
-- statement:
--   Pointwise convergence of probability characteristic functions.
-- source:
--   https://github.com/slink/LeanLevy/blob/7e73fd9b23ad52956ec2756a815889a783131ce4/LeanLevy/Probability/WeakConvergence.lean#L50

import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic
import Definitions.Def_levy_foundations_probabilityCharacteristicFun

open MeasureTheory Filter Topology
namespace LevyFoundations
/-- Every real-frequency characteristic function converges along the filter. -/
def weakCharFunTendsto {ι : Type*} (μs : ι → ProbabilityMeasure ℝ)
    (F : Filter ι) (μ : ProbabilityMeasure ℝ) : Prop :=
  ∀ ξ : ℝ, Tendsto (fun i => probabilityCharacteristicFun (μs i) ξ) F
    (𝓝 (probabilityCharacteristicFun μ ξ))
end LevyFoundations


