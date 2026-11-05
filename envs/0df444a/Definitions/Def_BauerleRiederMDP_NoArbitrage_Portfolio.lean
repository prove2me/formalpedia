-- Prove2me | Definitions.Def_BauerleRiederMDP_NoArbitrage_Portfolio
-- name    : BauerleRiederMDP_NoArbitrage_Portfolio
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T06:23:25.995206+00:00
-- url     : https://prove2.me/theorems/49b68c04-5cab-42e3-a141-9269388c81fa
-- title:
--   Portfolio strategy (Definition 3.1.1)
-- statement:
--   A **portfolio** or **trading strategy** is an $(\mathcal F_n)$-adapted process $\varphi=(\varphi^0_n,\varphi_n)$ with $\varphi^0_n\in\mathbb R$ and $\varphi_n=(\varphi^1_n,\dots,\varphi^d_n)\in\mathbb R^d$ for $n=0,\dots,N-1$. The number $\varphi^k_n$ is the amount of money invested into asset $k$ during $[n,n+1)$ ($k=0$ is the bond). No sign restriction is imposed: negative amounts are loans or short sales.
--
--   **Formalization Note** The processes are indexed by $\mathbb N$; adaptedness is required for $n<N$ only.
-- source:
--   Bäuerle & Rieder, Markov Decision Processes with Applications to Finance (2011), Definition 3.1.1, p.61 (PDF 75); Remark 3.1.2, p.62 (PDF 76)

import Mathlib
import Definitions.Def_BauerleRiederMDP_NoArbitrage_FinancialMarket

open MeasureTheory

namespace BauerleRiederMDP.NoArbitrage

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {d : ℕ}

/-- Definition 3.1.1 (Bäuerle & Rieder 2011, p.61, PDF 75): a portfolio or trading strategy is an
`(𝓕_n)`-adapted stochastic process `φ = (φ^0_n, φ_n)` with `φ^0_n ∈ ℝ` and
`φ_n = (φ^1_n, …, φ^d_n) ∈ ℝ^d` for `n = 0, …, N − 1`; `φ^k_n` is the amount of money invested
into asset `k` during `[n, n + 1)`. No sign restriction is imposed (Remark 3.1.2).

**Formalization Note** The processes are indexed by `ℕ`; adaptedness is required for
`n = 0, …, N − 1`, the values at `n ≥ N` are unused. -/
structure Portfolio (M : FinancialMarket Ω P d) where
  /-- The amount `φ^0_n` invested in the bond on `[n, n + 1)`. -/
  φ0 : ℕ → Ω → ℝ
  /-- The amounts `φ_n ∈ ℝ^d` invested in the risky assets on `[n, n + 1)`. -/
  φ : ℕ → Ω → Fin d → ℝ
  φ0_adapted : ∀ n, n < M.N → Measurable[M.F n] (φ0 n)
  φ_adapted : ∀ n, n < M.N → Measurable[M.F n] (φ n)

end BauerleRiederMDP.NoArbitrage


