-- Prove2me | Definitions.Def_BauerleRiederMDP_TransactionCosts_Market_optimalStock
-- name    : BauerleRiederMDP_TransactionCosts_Market_optimalStock
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T06:30:02.026472+00:00
-- url     : https://prove2.me/theorems/e2287483-6967-4def-b7e5-f3bed3469d70
-- title:
--   Optimal stock amount $f^*_n$ of (4.32)
-- statement:
--   The amount $f^*_n(x)$ invested in the stock at time $n$ in state $x$ given by (4.32) with the thresholds $q_+(V_{n+1})$ and $q_-(V_{n+1})$ of (4.30)–(4.31), computed from the value function $V_{n+1}$ with $i_{n+1}$ and $\tilde R_{n+1}$.
-- source:
--   Bäuerle & Rieder, Markov Decision Processes with Applications to Finance (2011), Theorem 4.5.4 b), eq. (4.32), p.113 (PDF 127)

import Mathlib
import Definitions.Def_BauerleRiederMDP_TransactionCosts_Market
import Definitions.Def_BauerleRiederMDP_TransactionCosts_Market_V
import Definitions.Def_BauerleRiederMDP_TransactionCosts_Market_qPlus
import Definitions.Def_BauerleRiederMDP_TransactionCosts_Market_qMinus
import Definitions.Def_BauerleRiederMDP_TransactionCosts_coneAmount

namespace BauerleRiederMDP.TransactionCosts

/-- The amount `f*_n(x)` invested in the stock at time `n` given by (4.32) of Bäuerle & Rieder
(2011), Theorem 4.5.4 b), p.113 (PDF 127): the three-region rule `coneAmount` with thresholds
`q₊(V_{n+1})` and `q₋(V_{n+1})` of (4.30)–(4.31), computed from the value function `V_{n+1}`
at time `n` (with `i_{n+1}` and `R̃_{n+1}`). -/
noncomputable def Market.optimalStock {Ω : Type*} [MeasurableSpace Ω] (M : Market Ω) (n : ℕ)
    (x : ℝ × ℝ) : ℝ :=
  coneAmount M.c (M.qPlus n (M.V (n + 1))) (M.qMinus n (M.V (n + 1))) x

end BauerleRiederMDP.TransactionCosts


