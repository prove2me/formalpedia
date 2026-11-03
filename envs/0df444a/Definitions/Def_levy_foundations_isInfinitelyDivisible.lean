-- Prove2me | Definitions.Def_levy_foundations_isInfinitelyDivisible
-- name    : levy_foundations_isInfinitelyDivisible
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-27T07:50:36.605169+00:00
-- url     : https://prove2.me/theorems/f87824bd-17c6-4d3c-9218-e45c08ec45b3
-- title:
--   Infinite divisibility of a real probability law
-- statement:
--   A probability law is infinitely divisible if, for each positive integer n, it is the n-fold convolution power of another probability law.
-- source:
--   Inspired by Shmuel Link, LeanLevy v0.2.0 (MIT), https://github.com/slink/LeanLevy/blob/7e73fd9b23ad52956ec2756a815889a783131ce4/LeanLevy/Levy/InfiniteDivisible.lean#L89-L96. Real-valued infinite-divisibility predicate. The Prove2Me statement and namespace are independently authored and require verification.

import Definitions.Def_levy_foundations_iteratedConv

open MeasureTheory
namespace LevyFoundations
def isInfinitelyDivisible (μ : Measure ℝ) : Prop :=
  ∀ n : ℕ, 0 < n →
    ∃ ν : Measure ℝ, IsProbabilityMeasure ν ∧ μ = iteratedConv ν n
end LevyFoundations


