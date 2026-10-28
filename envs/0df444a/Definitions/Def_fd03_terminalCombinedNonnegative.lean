-- Prove2me | Definitions.Def_fd03_terminalCombinedNonnegative
-- name    : fd03_terminalCombinedNonnegative
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-27T08:08:17.650115+00:00
-- url     : https://prove2.me/theorems/3a2c22c6-13ef-4fa6-badd-df744abdbdca
-- title:
--   Nonnegative terminal wealth for a hedge and quoted derivative position
-- statement:
--   At every maturity history, add the terminal cash held by a self-financing stock-bank strategy to a fixed signed number of derivative units times the claim payoff. Require the combined cash amount to be nonnegative on every path.
-- source:
--   Original finite-state terminal payoff predicate for derivative-augmented arbitrage, with market economics as in Wilmott, Howison and Dewynne (1995), Chapter 10 §§10.2–10.4, printed pp. 182–189.

import Mathlib.Data.Real.Basic
import Definitions.Def_fd03_HedgeTree
import Definitions.Def_fd03_PayoffTree

namespace FinancialDerivatives.FD03

/-- Combined terminal stock-bank and derivative cash is nonnegative on every path. -/
def terminalCombinedNonnegative :
    (n : ℕ) → HedgeTree n → PayoffTree n → ℝ → Prop
  | 0, .terminal cash, .leaf payoff, units => 0 ≤ cash + units * payoff
  | n + 1, .node _ _ hu hd, .branch cu cd, units =>
      terminalCombinedNonnegative n hu cu units ∧
      terminalCombinedNonnegative n hd cd units

end FinancialDerivatives.FD03


