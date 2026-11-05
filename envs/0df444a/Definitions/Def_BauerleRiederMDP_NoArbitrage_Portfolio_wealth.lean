-- Prove2me | Definitions.Def_BauerleRiederMDP_NoArbitrage_Portfolio_wealth
-- name    : BauerleRiederMDP_NoArbitrage_Portfolio_wealth
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T06:24:17.907451+00:00
-- url     : https://prove2.me/theorems/bd4a961c-9650-4d48-9eff-d362a4a150e8
-- title:
--   Wealth $X^\varphi_n$ of a portfolio strategy
-- statement:
--   The wealth of a portfolio strategy $\varphi$ is the value of the initial portfolio
--   $$
--   X_0=\varphi^0_0+\varphi_0\cdot e,
--   $$
--   and, for $n\ge1$, the value at time $n$ before trading,
--   $$
--   X_n=X_{n-}=\varphi^0_{n-1}(1+i_n)+\varphi_{n-1}\cdot\tilde R_n ,
--   $$
--   where $e=(1,\dots,1)\in\mathbb R^d$.
-- source:
--   Bäuerle & Rieder, Markov Decision Processes with Applications to Finance (2011), §3.1, p.62 (PDF 76)

import Mathlib
import Definitions.Def_BauerleRiederMDP_NoArbitrage_Portfolio

open MeasureTheory

namespace BauerleRiederMDP.NoArbitrage

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {d : ℕ} {M : FinancialMarket Ω P d}

/-- The wealth `X^φ_n` of a portfolio strategy (Bäuerle & Rieder 2011, §3.1, p.62, PDF 76): the
value of the initial portfolio `X_0 := φ^0_0 + φ_0 · e`, and for `n ≥ 1` the value before trading
`X_n := X_{n−} := φ^0_{n−1}(1 + i_n) + φ_{n−1} · R̃_n`, where `e = (1, …, 1)` and
`x · y = ∑_k x_k y_k`. -/
noncomputable def Portfolio.wealth (φ : Portfolio M) : ℕ → Ω → ℝ
  | 0 => fun ω => φ.φ0 0 ω + ∑ k, φ.φ 0 ω k
  | n + 1 => fun ω => φ.φ0 n ω * (1 + M.i (n + 1)) + ∑ k, φ.φ n ω k * M.Rt (n + 1) ω k

end BauerleRiederMDP.NoArbitrage


