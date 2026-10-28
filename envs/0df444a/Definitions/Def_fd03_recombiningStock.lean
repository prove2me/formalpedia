-- Prove2me | Definitions.Def_fd03_recombiningStock
-- name    : fd03_recombiningStock
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-27T07:59:10.359703+00:00
-- url     : https://prove2.me/theorems/9b13ee9d-4204-4335-8361-cf0cf6fed854
-- title:
--   Recombining binomial stock price by time and up-count
-- statement:
--   At trading time t, a recombining node indexed by k up moves (0≤k≤t) has stock price S₀uᵏdᵗ⁻ᵏ, independently of the order in which the up and down moves occurred.
-- source:
--   Wilmott, Howison and Dewynne (1995), Chapter 10 §10.1, printed pp. 180–182, Figure 10.1. Explicit recombining stock-price formula.

import Mathlib.Data.Real.Basic
import Definitions.Def_fd03_BinomialMarket

namespace FinancialDerivatives.FD03

/-- Price at time t with k up moves, where k is a valid node index. -/
noncomputable def recombiningStock (m : BinomialMarket)
    (t : ℕ) (k : Fin (t + 1)) : ℝ :=
  m.initialSpot * m.up ^ k.val * m.down ^ (t - k.val)

end FinancialDerivatives.FD03


