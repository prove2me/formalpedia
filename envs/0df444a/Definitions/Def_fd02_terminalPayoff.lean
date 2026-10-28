-- Prove2me | Definitions.Def_fd02_terminalPayoff
-- name    : fd02_terminalPayoff
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-26T23:36:23.46656+00:00
-- url     : https://prove2.me/theorems/0ef06e16-ca98-4429-b303-7fd38fbf3396
-- title:
--   Two-state portfolio terminal payoff
-- statement:
--   The same shares and cash holdings are held until the terminal date, with stock factors up/down and common bank growth.
-- source:
--   Original derived definition based on Wilmott, Howison and Dewynne (1995), §2.4 and §10.1, printed pp. 30–31 and 180–182; https://doi.org/10.1017/CBO9780511812545. The same object is fixed for all FD-02 theorem statements.

import Mathlib.Data.Real.Basic
import Definitions.Def_fd02_TwoStateMarket
import Definitions.Def_fd02_Trade

namespace FinancialDerivatives.FD02

/-- Terminal value after the up or down stock move. -/
def terminalPayoff (m : TwoStateMarket) (t : Trade) (ω : Bool) : ℝ :=
  match ω with
  | true => t.shares * m.spot * m.up + t.cash * m.growth
  | false => t.shares * m.spot * m.down + t.cash * m.growth

end FinancialDerivatives.FD02


