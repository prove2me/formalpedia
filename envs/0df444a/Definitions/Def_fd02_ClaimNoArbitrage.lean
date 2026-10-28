-- Prove2me | Definitions.Def_fd02_ClaimNoArbitrage
-- name    : fd02_ClaimNoArbitrage
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-26T23:39:25.789446+00:00
-- url     : https://prove2.me/theorems/2b87bbb9-8d9b-48df-b43e-12c689a72ad6
-- title:
--   Strong no-arbitrage after adding a quoted derivative
-- statement:
--   The enlarged market admits unrestricted signed quantities of the claim at quote p. Any zero-cost portfolio with nonnegative payments in both states must pay zero in both.
-- source:
--   Original derived definition based on Wilmott, Howison and Dewynne (1995), §3.2 and §10.3, printed pp. 33–34 and 187; https://doi.org/10.1017/CBO9780511812545. The same object is fixed for all FD-02 theorem statements.

import Mathlib.Data.Real.Basic
import Definitions.Def_fd02_TwoStateMarket
import Definitions.Def_fd02_Trade
import Definitions.Def_fd02_initialCost
import Definitions.Def_fd02_terminalPayoff

namespace FinancialDerivatives.FD02

/-- No free terminal payoff from an unrestricted signed derivative holding. -/
def ClaimNoArbitrage (m : TwoStateMarket) (H : Bool → ℝ) (p : ℝ) : Prop :=
  ∀ (t : Trade) (a : ℝ),
    initialCost m t + a * p = 0 →
    0 ≤ terminalPayoff m t true + a * H true →
    0 ≤ terminalPayoff m t false + a * H false →
    terminalPayoff m t true + a * H true = 0 ∧
      terminalPayoff m t false + a * H false = 0

end FinancialDerivatives.FD02


