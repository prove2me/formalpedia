-- Prove2me | Definitions.Def_fd06_gaussianHeatFlow
-- name    : fd06_gaussianHeatFlow
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-27T23:16:02.873765+00:00
-- url     : https://prove2.me/theorems/3c027477-ba53-4248-b32d-4ac78e75eb80
-- title:
--   Gaussian heat convolution flow
-- statement:
--   Gaussian heat convolution flow
-- source:
--   Wilmott, Howison and Dewynne (1995), Chapters 4–6; analytic interpretation and rigorous extension.

import Mathlib

open MeasureTheory intervalIntegral

namespace FinancialDerivatives.FD06

/-- Gaussian heat convolution flow. -/
noncomputable def gaussianHeatFlow (f : ℝ → ℝ) (τ x : ℝ) : ℝ := ∫ z : ℝ, f (x + Real.sqrt (2 * τ) * z) ∂ProbabilityTheory.gaussianReal 0 1

end FinancialDerivatives.FD06


