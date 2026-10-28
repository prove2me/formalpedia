-- Prove2me | Definitions.Def_fd03_terminalRow
-- name    : fd03_terminalRow
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-27T08:06:41.367991+00:00
-- url     : https://prove2.me/theorems/b6e0e816-e546-4bf6-8d0c-f5eea0fe4e0f
-- title:
--   Recombining maturity payoff row from current stock price
-- statement:
--   For a stock-based payoff function g and maturity N, the terminal row entry indexed by k up moves is g(S₀uᵏdᴺ⁻ᵏ). This has exactly N+1 logical entries, one per recombining stock state.
-- source:
--   Original typed terminal-row implementation of Wilmott, Howison and Dewynne (1995), Chapter 10 §§10.1 and 10.4, Figure 10.4, equation (10.16), printed pp. 180–188.

import Mathlib.Data.Real.Basic
import Definitions.Def_fd03_recombiningStock

namespace FinancialDerivatives.FD03

/-- The finite row of maturity payoffs at each valid up-move count. -/
noncomputable def terminalRow (m : BinomialMarket)
    (n : ℕ) (reward : ℝ → ℝ) : Fin (n + 1) → ℝ :=
  fun k => reward (recombiningStock m n k)

end FinancialDerivatives.FD03


