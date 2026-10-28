-- Prove2me | Definitions.Def_fd05_historySpot
-- name    : fd05_historySpot
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-27T17:13:41.018051+00:00
-- url     : https://prove2.me/theorems/3610f99c-baa5-4d7d-a3de-60e5350ef9b9
-- title:
--   Stock value of a chronological binomial history
-- statement:
--   The stock price after a list of chronological Boolean moves is the initial price multiplied successively by the up or down factor.
-- source:
--   Wilmott, Howison and Dewynne (1995), The Mathematics of Financial Derivatives, Chapter 12, pp. 206–212. Rigorous finite-binomial first-hit analogue.

import Mathlib.Data.Real.Basic
import Mathlib.Data.List.Basic
import Definitions.Def_fd03_BinomialMarket

namespace FinancialDerivatives.FD05
open FinancialDerivatives.FD03

/-- Interpret each chronological Boolean move as the corresponding multiplier. -/
noncomputable def historySpot (m : BinomialMarket) (steps : List Bool) : ℝ :=
  steps.foldl (fun S b => if b then S * m.up else S * m.down) m.initialSpot

end FinancialDerivatives.FD05


