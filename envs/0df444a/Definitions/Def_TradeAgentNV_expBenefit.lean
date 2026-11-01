-- Prove2me | Definitions.Def_TradeAgentNV_expBenefit
-- name    : TradeAgentNV_expBenefit
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T10:30:24.869987+00:00
-- url     : https://prove2.me/theorems/4817b969-19e3-42b1-bb5e-b13b7ef3a263
-- title:
--   Expected benefit of bidding $R=\rho E[\min(qU,D)]-hqE[U]$
-- statement:
--   For the yield fraction $U$, lot size $q$, demand $D$ and $\rho=r-t+h+\pi$, the **expected benefit of bidding** is
--   $$
--   R=\rho\,E[\min(qU,D)]-hq\,E[U].
--   $$
--   It is the change in expected profit (gross of the payment $bq$) from winning the bid, and its sign decides whether bidding pays.
-- source:
--   Çakıcı & Karaesmen, When Yield is Not the Only Supply Uncertainty: Newsvendor Model of a Trade Agent, SSRN 4409114 (v. Oct 14, 2023), https://ssrn.com/abstract=4409114, display (7), p.11

import Mathlib
import Definitions.Def_TradeAgentNV_rho

open MeasureTheory

namespace TradeAgentNV

/-- The **expected benefit of bidding** `R = ρE[min(qU, D)] − hqE[U]` (display (7), p.11, of
Çakıcı & Karaesmen, *When Yield is Not the Only Supply Uncertainty: Newsvendor Model of a
Trade Agent*, SSRN 4409114 (v. Oct 14, 2023)), where `U` is the yield fraction on the probability space
`(Ω, P)`, `q` the seller's lot size, `D` the demand and `ρ = r − t + h + π`. -/
noncomputable def expBenefit {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (U : Ω → ℝ)
    (r t h π D q : ℝ) : ℝ :=
  rho r t h π * ∫ ω, min (q * U ω) D ∂P - h * q * ∫ ω, U ω ∂P

end TradeAgentNV


