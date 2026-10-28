-- Prove2me | Definitions.Def_fd03_backwardRow
-- name    : fd03_backwardRow
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-27T07:59:18.411574+00:00
-- url     : https://prove2.me/theorems/981a96c0-4a37-415c-839d-7ebe8d5e8d82
-- title:
--   One-level backward induction on a recombining row
-- statement:
--   Given a risk-neutral valuation operator and the t+2 option values at time t+1, compute the t+1 values at time t. Node k combines next row entries k+1 (up) and k (down). This is the computationally efficient version of equation (10.16).
-- source:
--   Wilmott, Howison and Dewynne (1995), Chapter 10 §10.4, printed p. 188, equation (10.16), Figure 10.4. Original typed finite-row implementation of the source's backward recursion.

import Mathlib.Data.Real.Basic
import Definitions.Def_fd03_oneStepValue

namespace FinancialDerivatives.FD03

/-- Backward step from a time-(t+1) row to its time-t parent row. -/
noncomputable def backwardRow (m : BinomialMarket) (t : ℕ)
    (next : Fin (t + 2) → ℝ) : Fin (t + 1) → ℝ :=
  fun k => oneStepValue m (next (Fin.succ k)) (next (Fin.castSucc k))

end FinancialDerivatives.FD03


