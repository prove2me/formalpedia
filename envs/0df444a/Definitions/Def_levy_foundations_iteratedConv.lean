-- Prove2me | Definitions.Def_levy_foundations_iteratedConv
-- name    : levy_foundations_iteratedConv
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-27T07:50:25.269987+00:00
-- url     : https://prove2.me/theorems/e20fde88-2317-4a8e-82cf-bf0edd159336
-- title:
--   Iterated convolution powers of a real measure
-- statement:
--   The n-fold convolution power of a measure has zeroth power the Dirac measure at zero, and successive powers are formed by convolution with the original measure.
-- source:
--   Inspired by Shmuel Link, LeanLevy v0.2.0 (MIT), https://github.com/slink/LeanLevy/blob/7e73fd9b23ad52956ec2756a815889a783131ce4/LeanLevy/Levy/InfiniteDivisible.lean#L40-L44. Real-valued adaptation of the iterated-convolution definition. The Prove2Me statement and namespace are independently authored and require verification.

import Mathlib.MeasureTheory.Group.Convolution

open MeasureTheory
namespace LevyFoundations
noncomputable def iteratedConv (μ : Measure ℝ) : ℕ → Measure ℝ
  | 0 => Measure.dirac 0
  | n + 1 => μ ∗ iteratedConv μ n
end LevyFoundations


