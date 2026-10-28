-- Prove2me | Definitions.Def_fd03_europeanValue
-- name    : fd03_europeanValue
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-27T07:54:55.605166+00:00
-- url     : https://prove2.me/theorems/412b4206-eace-47ef-9108-e0f8ad5cc10e
-- title:
--   European option value by finite backward induction
-- statement:
--   The value of a depth-N full binary tree of signed maturity payments is obtained recursively: the zero-period value is the maturity payment, and a positive-depth value is the one-step discounted risk-neutral value of the up and down continuation subtrees. This includes path-dependent claims.
-- source:
--   Wilmott, Howison and Dewynne (1995), Chapter 10 §10.4, printed pp. 187–189, equation (10.16), Figure 10.4. Formal recursive extension to signed path-dependent terminal payoffs.

import Mathlib.Data.Real.Basic
import Definitions.Def_fd03_PayoffTree
import Definitions.Def_fd03_oneStepValue

namespace FinancialDerivatives.FD03

/-- Full-history European backward-induction value at every tree depth. -/
noncomputable def europeanValue (m : BinomialMarket) :
    (n : ℕ) → PayoffTree n → ℝ
  | 0, .leaf payoff => payoff
  | n + 1, .branch up down =>
      oneStepValue m (europeanValue m n up) (europeanValue m n down)

end FinancialDerivatives.FD03


