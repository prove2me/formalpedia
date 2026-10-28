-- Prove2me | Definitions.Def_fd03_rowToRoot
-- name    : fd03_rowToRoot
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-27T08:06:27.09301+00:00
-- url     : https://prove2.me/theorems/12d3289f-e509-4c57-ab66-f07415b25190
-- title:
--   Iterated recombining-row backward valuation to time zero
-- statement:
--   For a terminal row containing one option value for each possible up-count at maturity N, repeatedly apply the one-step binomial backward-row operator. After N reductions exactly one time-zero price remains. Each row has its correct finite type, preventing invalid node indices.
-- source:
--   Original typed version of the time-zero backward-row algorithm of Wilmott, Howison and Dewynne (1995), Chapter 10 §10.4, equation (10.16), Figure 10.4, printed p. 188.

import Mathlib.Data.Real.Basic
import Definitions.Def_fd03_backwardRow

namespace FinancialDerivatives.FD03

/-- Reduce the maturity row to one initial price by N backward steps. -/
noncomputable def rowToRoot (m : BinomialMarket) :
    (n : ℕ) → (Fin (n + 1) → ℝ) → ℝ
  | 0, row => row 0
  | n + 1, row => rowToRoot m n (backwardRow m n row)

end FinancialDerivatives.FD03


