-- Prove2me | Definitions.Def_fd03_exerciseStockTree
-- name    : fd03_exerciseStockTree
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-27T07:56:07.764722+00:00
-- url     : https://prove2.me/theorems/d781810e-7440-47de-90aa-cfd3925fa11b
-- title:
--   Stock-indexed exercise reward tree with a Bermudan schedule
-- statement:
--   For a node stock price S, terminal payoff function g and Boolean exercise schedule indexed by remaining time, recursively construct the exercise tree with maturity reward g(S). At an earlier node the schedule determines eligibility, the reward is g(S), and the stock moves to Su or Sd along the two branches.
-- source:
--   Wilmott, Howison and Dewynne (1995), Chapter 10 §10.5, printed pp. 189–191, Figure 10.7. Original stock-indexed data construction for American/Bermudan valuation.

import Mathlib.Data.Real.Basic
import Definitions.Def_fd03_BinomialMarket
import Definitions.Def_fd03_ExerciseTree

namespace FinancialDerivatives.FD03

/-- Stock-dependent exercise rewards on the full binomial history tree. -/
noncomputable def exerciseStockTree (m : BinomialMarket)
    (reward : ℝ → ℝ) (allowedAtRemaining : ℕ → Bool) :
    (n : ℕ) → ℝ → ExerciseTree n
  | 0, spot => .maturity (reward spot)
  | n + 1, spot =>
      .node (allowedAtRemaining (n + 1)) (reward spot)
        (exerciseStockTree m reward allowedAtRemaining n (spot * m.up))
        (exerciseStockTree m reward allowedAtRemaining n (spot * m.down))

end FinancialDerivatives.FD03


