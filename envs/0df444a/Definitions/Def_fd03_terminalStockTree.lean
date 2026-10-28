-- Prove2me | Definitions.Def_fd03_terminalStockTree
-- name    : fd03_terminalStockTree
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-27T07:55:10.036669+00:00
-- url     : https://prove2.me/theorems/35d672a1-e360-4b27-98bb-462310268b8a
-- title:
--   Terminal stock-price tree for a fixed binomial horizon
-- statement:
--   Starting at stock value S, each period multiplies it by u in the up branch and d in the down branch. A depth-N full binary tree records the stock price reached at every distinct market history, including histories ending at the same recombined price.
-- source:
--   Wilmott, Howison and Dewynne (1995), Chapter 10 §10.1, printed pp. 180–182, Figure 10.1. Original indexed full-history terminal-price construction.

import Mathlib.Data.Real.Basic
import Definitions.Def_fd03_BinomialMarket
import Definitions.Def_fd03_PayoffTree

namespace FinancialDerivatives.FD03

/-- Terminal node prices of the full non-recombined binomial tree. -/
noncomputable def terminalStockTree (m : BinomialMarket) :
    (n : ℕ) → ℝ → PayoffTree n
  | 0, spot => .leaf spot
  | n + 1, spot =>
      .branch (terminalStockTree m n (spot * m.up))
              (terminalStockTree m n (spot * m.down))

end FinancialDerivatives.FD03


