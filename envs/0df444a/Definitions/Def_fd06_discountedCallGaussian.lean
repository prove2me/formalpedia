-- Prove2me | Definitions.Def_fd06_discountedCallGaussian
-- name    : fd06_discountedCallGaussian
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-27T23:19:23.640108+00:00
-- url     : https://prove2.me/theorems/9cc7d169-a2fc-483b-9f5d-e38b84f74798
-- title:
--   Independently defined Gaussian call expectation
-- statement:
--   Independently defined Gaussian call expectation
-- source:
--   Wilmott, Howison and Dewynne (1995), Chapters 4–6; analytic interpretation and rigorous extension.

import Mathlib
import Definitions.Def_fd06_lognormalTerminal

open MeasureTheory intervalIntegral

namespace FinancialDerivatives.FD06

/-- Independently defined Gaussian call expectation. -/
noncomputable def discountedCallGaussian (S K R Q V : ℝ) : ℝ := Real.exp (-R) * (∫ z : ℝ, max (lognormalTerminal S R Q V z - K) 0 ∂ProbabilityTheory.gaussianReal 0 1)

end FinancialDerivatives.FD06


