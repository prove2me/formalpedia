-- Prove2me | Definitions.Def_levy_foundations_isInfinitelyDivisibleLaw
-- name    : levy_foundations_isInfinitelyDivisibleLaw
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-30T18:24:43.888905+00:00
-- url     : https://prove2.me/theorems/9dc46fcd-22bc-48f4-a1aa-4b6698cd4692
-- title:
--   Infinite divisibility of a measure on an additive commutative monoid
-- statement:
--   A measure μ on any measurable additive commutative monoid is infinitely divisible if, for every positive natural number n, μ is the n-fold convolution power of a probability measure ν on the same state space.
-- source:
--   https://github.com/slink/LeanLevy/blob/7e73fd9b23ad52956ec2756a815889a783131ce4/LeanLevy/Levy/InfiniteDivisible.lean#L84-L93, using the generic convolution-power definition above.

import Definitions.Def_levy_foundations_iteratedConvolutionPower

open MeasureTheory
namespace LevyFoundations
/-- Every positive convolution order admits a probability-measure root. -/
def isInfinitelyDivisibleLaw {E : Type*}
    [AddCommMonoid E] [MeasurableSpace E] (μ : Measure E) : Prop :=
  ∀ n : ℕ, 0 < n → ∃ ν : Measure E,
    IsProbabilityMeasure ν ∧ μ = iteratedConvolutionPower ν n
end LevyFoundations


