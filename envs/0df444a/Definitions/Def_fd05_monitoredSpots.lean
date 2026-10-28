-- Prove2me | Definitions.Def_fd05_monitoredSpots
-- name    : fd05_monitoredSpots
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-27T19:43:46.253716+00:00
-- url     : https://prove2.me/theorems/61957c0b-463e-485b-9001-1a07b263f7bc
-- title:
--   Stock observations at the chosen barrier-monitoring dates
-- statement:
--   The observed spot list contains exactly those path prices whose integer dates are monitored, preserving chronological order.
-- source:
--   Wilmott, Howison and Dewynne (1995), The Mathematics of Financial Derivatives, Chapter 12, pp. 206–212. Rigorous finite-binomial first-hit analogue.

import Mathlib.Data.Real.Basic
import Mathlib.Data.List.Basic
import Definitions.Def_fd03_BinomialMarket
import Definitions.Def_fd05_historySpot

namespace FinancialDerivatives.FD05
open FinancialDerivatives.FD03

/-- Stock values at monitored dates, including t=0 or t=N when selected. -/
noncomputable def monitoredSpots (m : BinomialMarket) (N : ℕ)
    (monitor : ℕ → Bool) (steps : List Bool) : List ℝ :=
  ((List.range (N + 1)).filter (fun t => monitor t)).map
    (fun t => historySpot m (steps.take t))

end FinancialDerivatives.FD05


