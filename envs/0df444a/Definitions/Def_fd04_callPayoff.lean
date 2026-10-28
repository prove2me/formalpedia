-- Prove2me | Definitions.Def_fd04_callPayoff
-- name    : fd04_callPayoff
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-27T10:45:23.659966+00:00
-- url     : https://prove2.me/theorems/8d91bbb0-4fb1-4f3a-af23-e68fe14f1da2
-- title:
--   European call payoff
-- statement:
--   Terminal call payment is the positive part of terminal stock price less strike.
-- source:
--   Wilmott, Howison and Dewynne (1995), The Mathematics of Financial Derivatives, Chapter 11, printed pp. 197–205, especially §§11.2–11.4. Original discrete-binomial formalisation.

import Mathlib.Data.Real.Basic

namespace FinancialDerivatives.FD04

/-- Vanilla call payment at expiry. -/
def callPayoff (K spot : ℝ) : ℝ := max (spot - K) 0

end FinancialDerivatives.FD04


