-- Prove2me | Definitions.Def_fd03_quotedClaimArbitrage
-- name    : fd03_quotedClaimArbitrage
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-27T08:08:45.916832+00:00
-- url     : https://prove2.me/theorems/6f3bf26e-69b0-4efd-a377-fcaa07bc2827
-- title:
--   Zero-cost arbitrage after adding a European claim at a quoted price
-- statement:
--   A European derivative quote admits arbitrage if there exist self-financing stock-bank holdings and a signed position in the derivative, costing zero together initially, with combined terminal wealth nonnegative along every possible stock history and strictly positive in at least one history. The quote is arbitrage-free precisely when no such portfolio exists.
-- source:
--   Original derivative-market no-arbitrage formulation for repeated complete binomial steps; economically grounded in Wilmott, Howison and Dewynne (1995), Chapter 10 §§10.2–10.4, printed pp. 182–189.

import Mathlib.Data.Real.Basic
import Definitions.Def_fd03_SelfFinancing
import Definitions.Def_fd03_hedgeWealth
import Definitions.Def_fd03_terminalCombinedNonnegative
import Definitions.Def_fd03_terminalCombinedPositiveSomewhere

namespace FinancialDerivatives.FD03

/-- Finite-market arbitrage involving a quoted terminal derivative claim. -/
def quotedClaimArbitrage (m : BinomialMarket) (n : ℕ)
    (spot : ℝ) (claim : PayoffTree n) (quote : ℝ) : Prop :=
  ∃ (hedge : HedgeTree n) (units : ℝ),
    SelfFinancing m n spot hedge ∧
    hedgeWealth m n spot hedge + units * quote = 0 ∧
    terminalCombinedNonnegative n hedge claim units ∧
    terminalCombinedPositiveSomewhere n hedge claim units

end FinancialDerivatives.FD03


