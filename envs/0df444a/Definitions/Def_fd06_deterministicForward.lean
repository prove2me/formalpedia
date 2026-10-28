-- Prove2me | Definitions.Def_fd06_deterministicForward
-- name    : fd06_deterministicForward
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-27T23:20:03.305356+00:00
-- url     : https://prove2.me/theorems/f59c0541-0bfc-4f2e-870c-dc0d88c49221
-- title:
--   Continuous dividend-adjusted forward
-- statement:
--   Continuous dividend-adjusted forward
-- source:
--   Wilmott, Howison and Dewynne (1995), Chapters 4–6; analytic interpretation and rigorous extension.

import Mathlib

namespace FinancialDerivatives.FD06

/-- Continuous dividend-adjusted forward. -/
noncomputable def deterministicForward (S R Q : ℝ) : ℝ := S * Real.exp (R - Q)

end FinancialDerivatives.FD06


