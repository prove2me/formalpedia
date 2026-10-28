-- Prove2me | Definitions.Def_fd03_hedgeTerminalPays
-- name    : fd03_hedgeTerminalPays
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-27T08:00:50.68476+00:00
-- url     : https://prove2.me/theorems/eb555465-71bf-4333-9f14-5d4653a93d79
-- title:
--   Exact terminal replication of a signed full-history claim
-- statement:
--   An adapted hedge terminally replicates a signed full-history payoff tree when its terminal cash at every leaf equals the corresponding contractual payoff, with the condition applied independently to both successor subtrees at each interior node.
-- source:
--   Wilmott, Howison and Dewynne (1995), Chapter 10 §§10.2–10.4, printed pp. 182–189. Original pathwise terminal-claim matching condition for complete binomial replication.

import Mathlib.Data.Real.Basic
import Definitions.Def_fd03_HedgeTree
import Definitions.Def_fd03_PayoffTree

namespace FinancialDerivatives.FD03

/-- Every terminal history delivers precisely the contracted signed cash payoff. -/
def hedgeTerminalPays :
    (n : ℕ) → HedgeTree n → PayoffTree n → Prop
  | 0, .terminal cash, .leaf claim => cash = claim
  | n + 1, .node _ _ up down, .branch upClaim downClaim =>
      hedgeTerminalPays n up upClaim ∧
      hedgeTerminalPays n down downClaim

end FinancialDerivatives.FD03


