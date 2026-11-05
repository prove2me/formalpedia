-- Prove2me | Definitions.Def_BauerleRiederMDP_NoArbitrage_FinancialMarket_relRisk
-- name    : BauerleRiederMDP_NoArbitrage_FinancialMarket_relRisk
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T06:23:37.924184+00:00
-- url     : https://prove2.me/theorems/07b20312-9768-4788-aa25-e703b0a71357
-- title:
--   Relative risk process $R_n$
-- statement:
--   The **relative risk process** of a financial market is $R_n=(R^1_n,\dots,R^d_n)$ with
--   $$
--   R^k_n=\frac{\tilde R^k_n}{1+i_n}-1,\qquad k=1,\dots,d .
--   $$
--   $R^k_n$ is the excess return of asset $k$ over the bond in the period $[n-1,n)$; the wealth of a self-financing strategy depends on the investment only through $\varphi_n\cdot R_{n+1}$.
--
--   **Formalization Note** $1+i_n\ge1$ at the times $1\le n\le N$ the book uses, so the division is never by zero there.
-- source:
--   Bäuerle & Rieder, Markov Decision Processes with Applications to Finance (2011), §3.1, p.63 (PDF 77)

import Mathlib
import Definitions.Def_BauerleRiederMDP_NoArbitrage_FinancialMarket

open MeasureTheory

namespace BauerleRiederMDP.NoArbitrage

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {d : ℕ}

/-- The relative risk process (Bäuerle & Rieder 2011, §3.1, p.63, PDF 77):
`R_n := (R^1_n, …, R^d_n)` with `R^k_n := R̃^k_n / (1 + i_n) − 1`, `k = 1, …, d`.

**Formalization Note** `1 + i_n ≥ 1` for `1 ≤ n ≤ N` (`FinancialMarket.i_nonneg`), so the
division is never by zero at the times the book uses. -/
noncomputable def FinancialMarket.relRisk (M : FinancialMarket Ω P d) (n : ℕ) (ω : Ω) : Fin d → ℝ :=
  fun k => M.Rt n ω k / (1 + M.i n) - 1

end BauerleRiederMDP.NoArbitrage


