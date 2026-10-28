-- Prove2me | Definitions.Def_fd03_SelfFinancing
-- name    : fd03_SelfFinancing
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-27T08:00:39.348226+00:00
-- url     : https://prove2.me/theorems/5f293bf6-fd7e-4c54-a92d-7f1fea2f3ee1
-- title:
--   Pathwise self-financing condition for an adapted binomial hedge
-- statement:
--   A strategy is self-financing if, after either next-period stock move and bank growth, the realised value of the parent's holdings exactly equals the successor strategy's current wealth, and both successor strategies are themselves self-financing. At maturity no further rebalance occurs. This rules out external cash injections at every node.
-- source:
--   Wilmott, Howison and Dewynne (1995), Chapter 10 §§10.2–10.4, printed pp. 182–189. Original pathwise discrete-time self-financing rebalancing predicate.

import Mathlib.Data.Real.Basic
import Definitions.Def_fd03_BinomialMarket
import Definitions.Def_fd03_HedgeTree
import Definitions.Def_fd03_hedgeWealth

namespace FinancialDerivatives.FD03

/-- Rebalancing uses only proceeds from the preceding stock-and-bank portfolio. -/
def SelfFinancing (m : BinomialMarket) :
    (n : ℕ) → ℝ → HedgeTree n → Prop
  | 0, _, .terminal _ => True
  | n + 1, spot, .node shares bank up down =>
      (shares * (spot * m.up) + bank * m.growth =
        hedgeWealth m n (spot * m.up) up) ∧
      (shares * (spot * m.down) + bank * m.growth =
        hedgeWealth m n (spot * m.down) down) ∧
      SelfFinancing m n (spot * m.up) up ∧
      SelfFinancing m n (spot * m.down) down

end FinancialDerivatives.FD03


