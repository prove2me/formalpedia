-- Prove2me | Definitions.Def_levy_foundations_compensatedIntegrand
-- name    : levy_foundations_compensatedIntegrand
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-27T10:45:07.261684+00:00
-- url     : https://prove2.me/theorems/e79bb155-f77a-4866-a069-dccec0e37a45
-- title:
--   Compensated complex jump integrand
-- statement:
--   The integrand exp(i x ξ) − 1 − i x ξ 1{|x|<1} compensates small jumps at the unit truncation threshold.
-- source:
--   Inspired by Shmuel Link, LeanLevy v0.2.0 (MIT), https://github.com/slink/LeanLevy/blob/7e73fd9b23ad52956ec2756a815889a783131ce4/LeanLevy/Levy/CompensatedIntegral.lean#L37-L40. Characteristic-exponent jump compensation. The Prove2Me statement and namespace are independently authored and require verification.

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.Integral.Bochner.Basic

namespace LevyFoundations
noncomputable def compensatedIntegrand (ξ x : ℝ) : ℂ :=
  Complex.exp ((x : ℂ) * ↑ξ * Complex.I) - 1
    - ↑x * ↑ξ * Complex.I * (if |x| < 1 then 1 else 0)
end LevyFoundations


