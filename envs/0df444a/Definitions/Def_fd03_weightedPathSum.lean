-- Prove2me | Definitions.Def_fd03_weightedPathSum
-- name    : fd03_weightedPathSum
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-27T08:07:06.530934+00:00
-- url     : https://prove2.me/theorems/0a089880-a340-467f-8517-ae6650d37590
-- title:
--   Undiscounted risk-neutral weighted sum over all terminal histories
-- statement:
--   Sum signed terminal cashflows over every full-history up/down route, weighting each up edge by the positive risk-neutral weight q and each down edge by 1-q. No discount factor is applied inside this tree fold. The discounted value is the weighted sum divided by R raised to the number of periods.
-- source:
--   Original full-history finite expectation construction for the risk-neutral valuation formula in Wilmott, Howison and Dewynne (1995), Chapter 10 §§10.2–10.4, printed pp. 182–189.

import Mathlib.Data.Real.Basic
import Definitions.Def_fd03_upWeight
import Definitions.Def_fd03_PayoffTree

namespace FinancialDerivatives.FD03

/-- Sum full-history terminal claims under product risk-neutral state weights. -/
noncomputable def weightedPathSum (m : BinomialMarket) :
    (n : ℕ) → PayoffTree n → ℝ
  | 0, .leaf cash => cash
  | n + 1, .branch up down =>
      upWeight m * weightedPathSum m n up +
      (1 - upWeight m) * weightedPathSum m n down

end FinancialDerivatives.FD03


