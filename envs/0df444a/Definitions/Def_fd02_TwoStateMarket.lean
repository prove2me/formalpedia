-- Prove2me | Definitions.Def_fd02_TwoStateMarket
-- name    : fd02_TwoStateMarket
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-26T23:35:49.334022+00:00
-- url     : https://prove2.me/theorems/539441a3-7a06-4612-b447-6ec79515165e
-- title:
--   Nondegenerate two-state stock and bank market
-- statement:
--   The current stock price and bank growth are strictly positive, with a nonnegative down factor strictly below the up factor. The location of the bank growth relative to the two stock factors remains to be established from no-arbitrage.
-- source:
--   Original derived definition based on Wilmott, Howison and Dewynne (1995), §§3.2,10.1, printed pp. 33–34 and 180–182; https://doi.org/10.1017/CBO9780511812545. The same object is fixed for all FD-02 theorem statements.

import Mathlib.Data.Real.Basic

namespace FinancialDerivatives.FD02

/-- One-period stock-and-bank market with ordered, nonnegative terminal stock factors. -/
structure TwoStateMarket where
  spot : ℝ
  up : ℝ
  down : ℝ
  growth : ℝ
  spot_pos : 0 < spot
  growth_pos : 0 < growth
  down_nonneg : 0 ≤ down
  down_lt_up : down < up

end FinancialDerivatives.FD02


