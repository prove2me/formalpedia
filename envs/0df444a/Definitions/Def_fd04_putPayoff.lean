-- Prove2me | Definitions.Def_fd04_putPayoff
-- name    : fd04_putPayoff
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-27T10:45:29.732435+00:00
-- url     : https://prove2.me/theorems/ead77eb7-8055-41bc-98dd-7952df3908cd
-- title:
--   European put payoff
-- statement:
--   Terminal put payment is the positive part of strike less terminal stock price.
-- source:
--   Wilmott, Howison and Dewynne (1995), The Mathematics of Financial Derivatives, Chapter 11, printed pp. 197–205, especially §§11.2–11.4. Original discrete-binomial formalisation.

import Mathlib.Data.Real.Basic

namespace FinancialDerivatives.FD04

/-- Vanilla put payment at expiry. -/
def putPayoff (K spot : ℝ) : ℝ := max (K - spot) 0

end FinancialDerivatives.FD04


