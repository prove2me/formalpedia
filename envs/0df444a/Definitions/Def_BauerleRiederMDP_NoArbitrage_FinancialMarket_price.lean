-- Prove2me | Definitions.Def_BauerleRiederMDP_NoArbitrage_FinancialMarket_price
-- name    : BauerleRiederMDP_NoArbitrage_FinancialMarket_price
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T06:23:30.960573+00:00
-- url     : https://prove2.me/theorems/2db91e43-561c-4ece-8db1-de0c651db4f1
-- title:
--   Stock prices $S^k_n$
-- statement:
--   For a financial market, the price of risky asset $k$ at time $n$ is
--   $$
--   S^k_n=s^k_0\prod_{t=1}^{n}\tilde R^k_t ,
--   $$
--   the solution of $S^k_0=s^k_0$, $S^k_{n+1}=S^k_n\tilde R^k_{n+1}$; $S_n=(S^1_n,\dots,S^d_n)$.
--
--   The prices generate the filtration $\mathcal F^S_n=\sigma(S_0,\dots,S_n)$ and enter the discounted price processes of the fundamental theorem of asset pricing.
-- source:
--   Bäuerle & Rieder, Markov Decision Processes with Applications to Finance (2011), §3.1, p.61 (PDF 75)

import Mathlib
import Definitions.Def_BauerleRiederMDP_NoArbitrage_FinancialMarket

open MeasureTheory

namespace BauerleRiederMDP.NoArbitrage

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {d : ℕ}

/-- The price `S^k_n` of the risky asset `k` at time `n` (Bäuerle & Rieder 2011, §3.1, p.61,
PDF 75): `S^k_0 = s^k_0` and `S^k_{n+1} = S^k_n R̃^k_{n+1}`, i.e. `S^k_n = s^k_0 ∏_{t<n} R̃^k_{t+1}`.
`S_n = (S^1_n, …, S^d_n)`. -/
noncomputable def FinancialMarket.price (M : FinancialMarket Ω P d) (n : ℕ) (ω : Ω) : Fin d → ℝ :=
  fun k => M.s0 k * ∏ t ∈ Finset.range n, M.Rt (t + 1) ω k

end BauerleRiederMDP.NoArbitrage


