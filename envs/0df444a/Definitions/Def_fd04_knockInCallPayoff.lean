-- Prove2me | Definitions.Def_fd04_knockInCallPayoff
-- name    : fd04_knockInCallPayoff
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-27T10:47:42.084814+00:00
-- url     : https://prove2.me/theorems/305ec4fc-f147-4560-911f-7db10ad8a59f
-- title:
--   Zero-rebate upper knock-in call payment
-- statement:
--   A vanilla call payoff is paid at maturity only on observed paths that touched the upper barrier.
-- source:
--   Wilmott, Howison and Dewynne (1995), The Mathematics of Financial Derivatives, Chapter 11, printed pp. 197–205, especially §§11.2–11.4. Original discrete-binomial formalisation.

import Mathlib.Data.Real.Basic
import Definitions.Def_fd04_upperBarrierTouched
import Definitions.Def_fd04_callPayoff

namespace FinancialDerivatives.FD04

/-- Upper knock-in terminal call payoff, with zero rebate. -/
noncomputable def knockInCallPayoff (B K terminalSpot : ℝ)
    (observedSpots : List ℝ) : ℝ :=
  if upperBarrierTouched B observedSpots then
    callPayoff K terminalSpot else 0

end FinancialDerivatives.FD04


