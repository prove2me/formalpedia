-- Prove2me | Definitions.Def_BauerleRiederMDP_TransactionCosts_Market_transition
-- name    : BauerleRiederMDP_TransactionCosts_Market_transition
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T06:25:14.920197+00:00
-- url     : https://prove2.me/theorems/426b2a8b-d423-433b-9ebb-0ebbc5a10979
-- title:
--   Transition function $T_n$, (4.24)
-- statement:
--   After the transaction the holdings $(a_0,a_1)$ evolve over the period $[n,n+1)$ as
--   $$T_n\big(x,(a_0,a_1),z_{n+1}\big):=\big(a_0(1+i_{n+1}),\ a_1 z_{n+1}\big), \tag{4.24}$$
--   where $z_{n+1}$ is the realized relative price change $\tilde R_{n+1}$ of the stock.
-- source:
--   Bäuerle & Rieder, Markov Decision Processes with Applications to Finance (2011), §4.5, eq. (4.24), p.106 (PDF 120)

import Mathlib
import Definitions.Def_BauerleRiederMDP_TransactionCosts_Market

namespace BauerleRiederMDP.TransactionCosts

/-- The transition function (4.24) of Bäuerle & Rieder (2011), §4.5, p.106 (PDF 120):
`T_n(x, (a₀, a₁), z_{n+1}) := (a₀(1 + i_{n+1}), a₁ z_{n+1})`, where `z_{n+1}` is the realized
relative price change of the stock in period `[n, n + 1)`. It does not depend on `x`. -/
def Market.transition {Ω : Type*} [MeasurableSpace Ω] (M : Market Ω) (n : ℕ)
    (a : ℝ × ℝ) (z : ℝ) : ℝ × ℝ :=
  (a.1 * (1 + M.i (n + 1)), a.2 * z)

end BauerleRiederMDP.TransactionCosts


