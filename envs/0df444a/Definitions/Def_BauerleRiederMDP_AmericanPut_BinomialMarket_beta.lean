-- Prove2me | Definitions.Def_BauerleRiederMDP_AmericanPut_BinomialMarket_beta
-- name    : BauerleRiederMDP_AmericanPut_BinomialMarket_beta
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T06:30:37.723233+00:00
-- url     : https://prove2.me/theorems/535fbd28-8268-4283-bd1f-2c42e985f057
-- title:
--   Discount factor $\beta=(1+i)^{-1}$
-- statement:
--   The discount factor of the pricing problem is
--   $$\beta:=(1+i)^{-1}\in(0,1],$$
--   where $i\ge0$ is the interest rate of the bond.
-- source:
--   N. Bäuerle and U. Rieder, Markov Decision Processes with Applications to Finance, Universitext, Springer 2011, DOI 10.1007/978-3-642-18324-9, §11.1, p.332, PDF 340

import Mathlib
import Definitions.Def_BauerleRiederMDP_AmericanPut_BinomialMarket

namespace BauerleRiederMDP.AmericanPut

/-- The **discount factor** `β := (1 + i)⁻¹ ∈ (0, 1]` of the stopping problem of §11.1 (Bäuerle & Rieder,
Markov Decision Processes with Applications to Finance (2011), §11.1, p.332, PDF 340). -/
noncomputable def BinomialMarket.beta (M : BinomialMarket) : ℝ :=
  (1 + M.i)⁻¹

end BauerleRiederMDP.AmericanPut


