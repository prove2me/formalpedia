-- Prove2me | Definitions.Def_BauerleRiederMDP_TransactionCosts_Market_optimalPolicy
-- name    : BauerleRiederMDP_TransactionCosts_Market_optimalPolicy
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T06:31:30.997913+00:00
-- url     : https://prove2.me/theorems/cd2a9352-dd5e-4ccf-a09d-7ee0cd66333e
-- title:
--   The buy/hold/sell policy of Theorem 4.5.4
-- statement:
--   At time $n$ in state $x$, hold $f^*_n(x)$ in the stock and $h(x,f^*_n(x))$ in the bond after transaction:
--   $$\pi^*_n(x)=\big(h(x,f^*_n(x)),\ f^*_n(x)\big).$$
-- source:
--   Bäuerle & Rieder, Markov Decision Processes with Applications to Finance (2011), Theorem 4.5.4 b), p.113 (PDF 127)

import Mathlib
import Definitions.Def_BauerleRiederMDP_TransactionCosts_Market
import Definitions.Def_BauerleRiederMDP_TransactionCosts_Market_optimalStock
import Definitions.Def_BauerleRiederMDP_TransactionCosts_bondAfter

namespace BauerleRiederMDP.TransactionCosts

/-- The policy of Theorem 4.5.4 b) of Bäuerle & Rieder (2011), p.113 (PDF 127): at time `n` in
state `x`, hold `f*_n(x)` (4.32) in the stock and `h(x, f*_n(x))` in the bond after transaction
("the optimal amount invested in the bond at time n is equal to h(x, f*_n(x))"). -/
noncomputable def Market.optimalPolicy {Ω : Type*} [MeasurableSpace Ω] (M : Market Ω) (n : ℕ)
    (x : ℝ × ℝ) : ℝ × ℝ :=
  (bondAfter M.c x (M.optimalStock n x), M.optimalStock n x)

end BauerleRiederMDP.TransactionCosts


