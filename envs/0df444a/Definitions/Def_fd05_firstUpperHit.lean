-- Prove2me | Definitions.Def_fd05_firstUpperHit
-- name    : fd05_firstUpperHit
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-27T17:13:51.744198+00:00
-- url     : https://prove2.me/theorems/c9424b67-dd2e-4a8f-bf3b-826626cdff31
-- title:
--   Earliest monitored upper-barrier hit with sentinel
-- statement:
--   Among monitored dates from inception through maturity, this records the earliest upper touch, or the sentinel N+1 if none occurs.
-- source:
--   Wilmott, Howison and Dewynne (1995), The Mathematics of Financial Derivatives, Chapter 12, pp. 206–212. Rigorous finite-binomial first-hit analogue.

import Mathlib.Data.Real.Basic
import Mathlib.Data.List.Basic
import Definitions.Def_fd03_BinomialMarket
import Definitions.Def_fd05_historySpot

namespace FinancialDerivatives.FD05
open FinancialDerivatives.FD03

/-- Earliest monitored hit, N+1 if no observation reaches the upper barrier. -/
noncomputable def firstUpperHit (m : BinomialMarket) (N : ℕ) (B : ℝ)
    (monitor : ℕ → Bool) (steps : List Bool) : ℕ := by
  classical
  exact ((List.range (N + 1)).filter (fun t =>
    monitor t && decide (B ≤ historySpot m (steps.take t)))).headD (N + 1)

end FinancialDerivatives.FD05


