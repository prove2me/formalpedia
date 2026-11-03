-- Prove2me | Definitions.Def_levy_foundations_iteratedConvolutionPower
-- name    : levy_foundations_iteratedConvolutionPower
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-30T18:24:32.006333+00:00
-- url     : https://prove2.me/theorems/15ce1732-1db7-439e-88f4-b3564b686b8b
-- title:
--   Convolution powers of a measure on an additive commutative monoid
-- statement:
--   For any measurable additive commutative monoid E and measure μ on E, define the zeroth convolution power to be the Dirac measure at zero and each successive power as the convolution of μ with the previous power.
-- source:
--   https://github.com/slink/LeanLevy/blob/7e73fd9b23ad52956ec2756a815889a783131ce4/LeanLevy/Levy/InfiniteDivisible.lean#L36-L45, adapted under a fresh name because the existing real-specialised reference is immutable.

import Mathlib.MeasureTheory.Group.Convolution

open MeasureTheory
namespace LevyFoundations
/-- The `n`-fold convolution power of a measure on an additive commutative monoid. -/
noncomputable def iteratedConvolutionPower {E : Type*}
    [AddCommMonoid E] [MeasurableSpace E]
    (μ : Measure E) : ℕ → Measure E
  | 0 => Measure.dirac 0
  | n + 1 => μ ∗ iteratedConvolutionPower μ n
end LevyFoundations


