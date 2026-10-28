-- Prove2me | Definitions.Def_fd06_standardNormalDensity
-- name    : fd06_standardNormalDensity
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-27T23:15:33.374094+00:00
-- url     : https://prove2.me/theorems/dffeda5b-487a-4b36-a5a4-ff44af041ba1
-- title:
--   Standard normal density
-- statement:
--   Standard normal density
-- source:
--   Wilmott, Howison and Dewynne (1995), Chapters 4–6; analytic interpretation and rigorous extension.

import Mathlib

namespace FinancialDerivatives.FD06

/-- Standard normal density. -/
noncomputable def standardNormalDensity (x : ℝ) : ℝ := Real.exp (-(x ^ 2) / 2) / Real.sqrt (2 * Real.pi)

end FinancialDerivatives.FD06


