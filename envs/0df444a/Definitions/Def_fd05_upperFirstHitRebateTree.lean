-- Prove2me | Definitions.Def_fd05_upperFirstHitRebateTree
-- name    : fd05_upperFirstHitRebateTree
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-27T19:39:14.375506+00:00
-- url     : https://prove2.me/theorems/a0698f79-5b33-4e50-9f36-9a30e56fce8c
-- title:
--   Maturity-equivalent payoff for an immediate first-hit rebate
-- statement:
--   An immediate first-hit rebate is represented as a terminal-equivalent payment accumulated at the bank growth rate from the touching date.
-- source:
--   Wilmott, Howison and Dewynne (1995), The Mathematics of Financial Derivatives, Chapter 12, pp. 206–212. Rigorous finite-binomial first-hit analogue.

import Mathlib.Data.Real.Basic
import Definitions.Def_fd03_BinomialMarket
import Definitions.Def_fd03_PayoffTree
import Definitions.Def_fd03_constantPayoffTree
import Definitions.Def_fd05_upperTouch

namespace FinancialDerivatives.FD05
open FinancialDerivatives.FD03

/-- On first touch at t, carry Z forward by the remaining bank growth. -/
noncomputable def upperFirstHitRebateTree (m : BinomialMarket) (B : ℝ)
    (monitor : ℕ → Bool) (Z : ℝ) :
    (n : ℕ) → ℕ → ℝ → PayoffTree n
  | 0, t, S =>
      .leaf (if upperTouch B S monitor t then Z else 0)
  | n + 1, t, S =>
      if upperTouch B S monitor t
      then constantPayoffTree (n + 1) (Z * m.growth ^ (n + 1))
      else .branch
        (upperFirstHitRebateTree m B monitor Z n (t + 1) (S * m.up))
        (upperFirstHitRebateTree m B monitor Z n (t + 1) (S * m.down))

end FinancialDerivatives.FD05


