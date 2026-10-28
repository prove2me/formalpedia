-- Prove2me | Definitions.Def_fd06_discountedPutGaussian
-- name    : fd06_discountedPutGaussian
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-27T23:19:52.319003+00:00
-- url     : https://prove2.me/theorems/a4a8b3e3-0473-48bf-8000-5c5b505651d9
-- title:
--   Independently defined Gaussian put expectation
-- statement:
--   Independently defined Gaussian put expectation
-- source:
--   Wilmott, Howison and Dewynne (1995), Chapters 4–6; analytic interpretation and rigorous extension.

import Mathlib
import Definitions.Def_fd06_lognormalTerminal

open MeasureTheory intervalIntegral

namespace FinancialDerivatives.FD06

/-- Independently defined Gaussian put expectation. -/
noncomputable def discountedPutGaussian (S K R Q V : ℝ) : ℝ := Real.exp (-R) * (∫ z : ℝ, max (K - lognormalTerminal S R Q V z) 0 ∂ProbabilityTheory.gaussianReal 0 1)

end FinancialDerivatives.FD06


