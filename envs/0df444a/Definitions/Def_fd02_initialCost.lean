-- Prove2me | Definitions.Def_fd02_initialCost
-- name    : fd02_initialCost
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-26T23:36:10.926533+00:00
-- url     : https://prove2.me/theorems/3d390e46-0375-4d4e-abd3-a7d85035929b
-- title:
--   Initial cost of a stock-and-bank trade
-- statement:
--   Date-zero cost equals shares held times the current stock price plus the current cash-account holding.
-- source:
--   Original derived definition based on Wilmott, Howison and Dewynne (1995), §3.2, printed pp. 33–34; https://doi.org/10.1017/CBO9780511812545. The same object is fixed for all FD-02 theorem statements.

import Mathlib.Data.Real.Basic
import Definitions.Def_fd02_TwoStateMarket
import Definitions.Def_fd02_Trade

namespace FinancialDerivatives.FD02

/-- Date-zero portfolio cost in bank-account monetary units. -/
def initialCost (m : TwoStateMarket) (t : Trade) : ℝ :=
  t.shares * m.spot + t.cash

end FinancialDerivatives.FD02


