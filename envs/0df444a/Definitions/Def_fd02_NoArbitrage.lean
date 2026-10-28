-- Prove2me | Definitions.Def_fd02_NoArbitrage
-- name    : fd02_NoArbitrage
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-26T23:36:49.309446+00:00
-- url     : https://prove2.me/theorems/511d32be-bc60-43a2-98d1-9644f87fbe74
-- title:
--   Strong zero-cost no-arbitrage in the base market
-- statement:
--   Strong absence of arbitrage excludes a zero-cost trading strategy that is nonnegative in both states and strictly positive in either state.
-- source:
--   Original derived definition based on Wilmott, Howison and Dewynne (1995), §3.2, printed pp. 33–34; https://doi.org/10.1017/CBO9780511812545. The same object is fixed for all FD-02 theorem statements.

import Mathlib.Data.Real.Basic
import Definitions.Def_fd02_TwoStateMarket
import Definitions.Def_fd02_Trade
import Definitions.Def_fd02_initialCost
import Definitions.Def_fd02_terminalPayoff

namespace FinancialDerivatives.FD02

/-- Zero initial cost and nonnegative payoffs force zero in both states. -/
def NoArbitrage (m : TwoStateMarket) : Prop :=
  ∀ t : Trade,
    initialCost m t = 0 →
    0 ≤ terminalPayoff m t true →
    0 ≤ terminalPayoff m t false →
    terminalPayoff m t true = 0 ∧ terminalPayoff m t false = 0

end FinancialDerivatives.FD02


