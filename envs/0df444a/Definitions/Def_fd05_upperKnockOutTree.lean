-- Prove2me | Definitions.Def_fd05_upperKnockOutTree
-- name    : fd05_upperKnockOutTree
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-27T17:13:05.484483+00:00
-- url     : https://prove2.me/theorems/914c2d11-7c5a-4279-a396-481273a0483f
-- title:
--   Full-history upper knock-out terminal payoff tree
-- statement:
--   The terminal full binary tree pays the supplied reward only when no monitored upper barrier was reached along the complete history.
-- source:
--   Wilmott, Howison and Dewynne (1995), The Mathematics of Financial Derivatives, Chapter 12, pp. 206–212. Rigorous finite-binomial first-hit analogue.

import Mathlib.Data.Real.Basic
import Definitions.Def_fd03_BinomialMarket
import Definitions.Def_fd03_PayoffTree
import Definitions.Def_fd05_upperTouch

namespace FinancialDerivatives.FD05
open FinancialDerivatives.FD03

/-- Construct terminal payoffs from genuine observation-history activation. -/
noncomputable def upperKnockOutTree (m : BinomialMarket) (B : ℝ)
    (monitor : ℕ → Bool) (g : ℝ → ℝ) :
    (n : ℕ) → ℕ → ℝ → Bool → PayoffTree n
  | 0, t, S, hit =>
      .leaf (if hit || upperTouch B S monitor t then 0 else g S)
  | n + 1, t, S, hit =>
      .branch
        (upperKnockOutTree m B monitor g n (t + 1) (S * m.up)
          (hit || upperTouch B S monitor t))
        (upperKnockOutTree m B monitor g n (t + 1) (S * m.down)
          (hit || upperTouch B S monitor t))

end FinancialDerivatives.FD05


