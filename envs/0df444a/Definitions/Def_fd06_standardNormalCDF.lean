-- Prove2me | Definitions.Def_fd06_standardNormalCDF
-- name    : fd06_standardNormalCDF
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-27T23:15:21.620037+00:00
-- url     : https://prove2.me/theorems/c05bfb0b-3996-45ec-a618-da2bf785c4d0
-- title:
--   Standard normal CDF from Gaussian measure
-- statement:
--   Standard normal CDF from Gaussian measure
-- source:
--   Wilmott, Howison and Dewynne (1995), Chapters 4–6; analytic interpretation and rigorous extension.

import Mathlib

namespace FinancialDerivatives.FD06

/-- Standard normal CDF from Gaussian measure. -/
noncomputable def standardNormalCDF (x : ℝ) : ℝ := (ProbabilityTheory.cdf (ProbabilityTheory.gaussianReal 0 1)) x

end FinancialDerivatives.FD06


