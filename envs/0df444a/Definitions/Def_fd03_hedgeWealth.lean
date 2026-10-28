-- Prove2me | Definitions.Def_fd03_hedgeWealth
-- name    : fd03_hedgeWealth
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-27T08:00:24.45388+00:00
-- url     : https://prove2.me/theorems/68911714-3d56-4091-b04d-a84d207d9bab
-- title:
--   Node wealth of a finite stock-bank hedge
-- statement:
--   At an interior node with stock price S, stock shares Δ and current bank balance b, the strategy's wealth is ΔS+b. At maturity, its wealth is the terminal cash stored at the leaf. This convention permits exact self-financing balances across the last trading step.
-- source:
--   Wilmott, Howison and Dewynne (1995), Chapter 10 §§10.2–10.4, printed pp. 182–189. Original explicit node-wealth and terminal-liquidation definition.

import Mathlib.Data.Real.Basic
import Definitions.Def_fd03_BinomialMarket
import Definitions.Def_fd03_HedgeTree

namespace FinancialDerivatives.FD03

/-- Current marked-to-market wealth, including liquidation at maturity. -/
noncomputable def hedgeWealth (m : BinomialMarket) :
    (n : ℕ) → ℝ → HedgeTree n → ℝ
  | 0, _, .terminal cash => cash
  | n + 1, spot, .node shares bank _ _ => shares * spot + bank

end FinancialDerivatives.FD03


