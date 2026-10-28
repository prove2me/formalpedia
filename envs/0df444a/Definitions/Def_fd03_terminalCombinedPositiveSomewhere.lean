-- Prove2me | Definitions.Def_fd03_terminalCombinedPositiveSomewhere
-- name    : fd03_terminalCombinedPositiveSomewhere
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-27T08:08:27.890711+00:00
-- url     : https://prove2.me/theorems/63f0bc4f-08f5-4a2c-a5c6-fe86e211cb10
-- title:
--   Strictly profitable terminal history for a quoted derivative strategy
-- statement:
--   A stock-bank hedge combined with a fixed signed derivative position has strictly positive maturity cash on at least one up/down history. Combined with nonnegative wealth on every path and zero initial cost, this witnesses finite-state arbitrage.
-- source:
--   Original finite-state strict-profit witness for derivative-augmented arbitrage, with source market conventions in Wilmott, Howison and Dewynne (1995), Chapter 10 §§10.2–10.4, printed pp. 182–189.

import Mathlib.Data.Real.Basic
import Definitions.Def_fd03_HedgeTree
import Definitions.Def_fd03_PayoffTree

namespace FinancialDerivatives.FD03

/-- There is a full-history maturity path with strictly positive combined cash. -/
def terminalCombinedPositiveSomewhere :
    (n : ℕ) → HedgeTree n → PayoffTree n → ℝ → Prop
  | 0, .terminal cash, .leaf payoff, units => 0 < cash + units * payoff
  | n + 1, .node _ _ hu hd, .branch cu cd, units =>
      terminalCombinedPositiveSomewhere n hu cu units ∨
      terminalCombinedPositiveSomewhere n hd cd units

end FinancialDerivatives.FD03


