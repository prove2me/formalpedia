-- Prove2me | Definitions.Def_fd04_knockOutCallPayoff
-- name    : fd04_knockOutCallPayoff
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-27T10:47:53.803022+00:00
-- url     : https://prove2.me/theorems/8cc26fe9-45a6-4e61-8fa7-45347a07e463
-- title:
--   Zero-rebate upper knock-out call payment
-- statement:
--   A vanilla call payoff is paid at maturity only on observed paths that never touched the upper barrier.
-- source:
--   Wilmott, Howison and Dewynne (1995), The Mathematics of Financial Derivatives, Chapter 11, printed pp. 197–205, especially §§11.2–11.4. Original discrete-binomial formalisation.

import Mathlib.Data.Real.Basic
import Definitions.Def_fd04_upperBarrierTouched
import Definitions.Def_fd04_callPayoff

namespace FinancialDerivatives.FD04

/-- Upper knock-out terminal call payoff, with zero rebate. -/
noncomputable def knockOutCallPayoff (B K terminalSpot : ℝ)
    (observedSpots : List ℝ) : ℝ :=
  if upperBarrierTouched B observedSpots then 0
  else callPayoff K terminalSpot

end FinancialDerivatives.FD04


