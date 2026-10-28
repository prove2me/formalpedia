-- Prove2me | Definitions.Def_fd05_upperKnockInTree
-- name    : fd05_upperKnockInTree
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-27T17:13:16.511888+00:00
-- url     : https://prove2.me/theorems/27e71125-c176-4da4-aa25-d8b304b001ea
-- title:
--   Full-history upper knock-in terminal payoff tree
-- statement:
--   The complementary knock-in tree pays the terminal reward exactly on histories with at least one monitored upper-barrier touch.
-- source:
--   Wilmott, Howison and Dewynne (1995), The Mathematics of Financial Derivatives, Chapter 12, pp. 206–212. Rigorous finite-binomial first-hit analogue.

import Mathlib.Data.Real.Basic
import Definitions.Def_fd03_BinomialMarket
import Definitions.Def_fd03_PayoffTree
import Definitions.Def_fd05_upperTouch

namespace FinancialDerivatives.FD05
open FinancialDerivatives.FD03

/-- Construct the complementary activated terminal payoff tree. -/
noncomputable def upperKnockInTree (m : BinomialMarket) (B : ℝ)
    (monitor : ℕ → Bool) (g : ℝ → ℝ) :
    (n : ℕ) → ℕ → ℝ → Bool → PayoffTree n
  | 0, t, S, hit =>
      .leaf (if hit || upperTouch B S monitor t then g S else 0)
  | n + 1, t, S, hit =>
      .branch
        (upperKnockInTree m B monitor g n (t + 1) (S * m.up)
          (hit || upperTouch B S monitor t))
        (upperKnockInTree m B monitor g n (t + 1) (S * m.down)
          (hit || upperTouch B S monitor t))

end FinancialDerivatives.FD05


