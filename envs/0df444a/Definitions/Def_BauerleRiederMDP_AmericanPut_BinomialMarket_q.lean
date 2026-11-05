-- Prove2me | Definitions.Def_BauerleRiederMDP_AmericanPut_BinomialMarket_q
-- name    : BauerleRiederMDP_AmericanPut_BinomialMarket_q
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T06:30:38.403935+00:00
-- url     : https://prove2.me/theorems/9ae8b7b9-9258-4f9e-bb00-174f16b8584c
-- title:
--   Risk-neutral up probability $q=(1+i-d)/(u-d)$
-- statement:
--   In the binomial market with $d<1+i<u$, the probability of an up movement of the stock under the equivalent martingale measure $\mathbb Q$ is
--   $$q=\frac{1+i-d}{u-d}\in(0,1).$$
-- source:
--   N. Bäuerle and U. Rieder, Markov Decision Processes with Applications to Finance, Universitext, Springer 2011, DOI 10.1007/978-3-642-18324-9, §11.1, eq. (11.1), p.331, PDF 339

import Mathlib
import Definitions.Def_BauerleRiederMDP_AmericanPut_BinomialMarket

namespace BauerleRiederMDP.AmericanPut

/-- The **risk-neutral up probability** (Bäuerle & Rieder, Markov Decision Processes with Applications to
Finance (2011), eq. (11.1), p.331, PDF 339): under the equivalent martingale measure `ℚ` the probability for an
up movement of the stock is `q = (1 + i − d)/(u − d)`.

**Formalization Note.** Since `d < 1 + i < u`, the denominator is positive and `q ∈ (0, 1)`. -/
noncomputable def BinomialMarket.q (M : BinomialMarket) : ℝ :=
  (1 + M.i - M.d) / (M.u - M.d)

end BauerleRiederMDP.AmericanPut


