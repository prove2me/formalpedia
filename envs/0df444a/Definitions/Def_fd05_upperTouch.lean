-- Prove2me | Definitions.Def_fd05_upperTouch
-- name    : fd05_upperTouch
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-27T17:12:53.912601+00:00
-- url     : https://prove2.me/theorems/e2935618-b60c-4491-9307-369dbb03c23b
-- title:
--   Monitored upper-barrier touch
-- statement:
--   At date t the upper barrier B is touched precisely when monitoring is enabled and the stock price is at least B.
-- source:
--   Wilmott, Howison and Dewynne (1995), The Mathematics of Financial Derivatives, Chapter 12, pp. 206–212. Rigorous finite-binomial first-hit analogue.

import Mathlib.Data.Real.Basic

namespace FinancialDerivatives.FD05

/-- A touch occurs exactly when this date is monitored and stock reaches B. -/
noncomputable def upperTouch (B S : ℝ) (monitor : ℕ → Bool) (t : ℕ) : Bool := by
  classical
  exact monitor t && decide (B ≤ S)

end FinancialDerivatives.FD05


