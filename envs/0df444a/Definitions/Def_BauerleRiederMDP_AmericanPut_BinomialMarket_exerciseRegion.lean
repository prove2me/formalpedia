-- Prove2me | Definitions.Def_BauerleRiederMDP_AmericanPut_BinomialMarket_exerciseRegion
-- name    : BauerleRiederMDP_AmericanPut_BinomialMarket_exerciseRegion
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T06:34:31.974513+00:00
-- url     : https://prove2.me/theorems/514b63ec-c855-4b7a-891f-52a48d9665e6
-- title:
--   Exercise region $E^*=\{x\in E\mid P(x)=(K-x)^+\}$
-- statement:
--   The **exercise region** of the perpetual put is
--   $$E^*:=\{x\in E\mid P(x)=(K-x)^+\},\qquad E=\mathbb R_+.$$
-- source:
--   N. Bäuerle and U. Rieder, Markov Decision Processes with Applications to Finance, Universitext, Springer 2011, DOI 10.1007/978-3-642-18324-9, Theorem 11.1.3 d), p.337, PDF 345

import Mathlib
import Definitions.Def_BauerleRiederMDP_AmericanPut_BinomialMarket_perpetualPut
open FinancialDerivatives.FD04 (putPayoff)

namespace BauerleRiederMDP.AmericanPut

/-- The **exercise region of the perpetual put** `E* := {x ∈ E | P(x) = (K − x)⁺}` with `E = ℝ₊`
(Bäuerle & Rieder, Markov Decision Processes with Applications to Finance (2011), Theorem 11.1.3 d), p.337,
PDF 345). -/
def BinomialMarket.exerciseRegion (M : BinomialMarket) (K : ℝ) : Set ℝ :=
  {x : ℝ | 0 ≤ x ∧ M.perpetualPut K x = putPayoff K x}

end BauerleRiederMDP.AmericanPut


