-- Prove2me | Definitions.Def_MDPFinance_FinancialMarkets_Portfolio
-- name    : MDPFinance_FinancialMarkets_Portfolio
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-27T21:48:00.270503+00:00
-- url     : https://prove2.me/theorems/b0306623-5eb2-4fda-a21d-f7963142c0e8
-- title:
--   Definition 3.1.1 / 3.1.3 — discrete-time portfolios and self-financing
-- statement:
--   A **portfolio (trading strategy)** is an $(\mathcal{F}_n)$-adapted process $\varphi =
--   (\varphi^0_n,\varphi_n)$, $\varphi^0_n \in \mathbb{R}$, $\varphi_n \in \mathbb{R}^d$, for $n =
--   0,\dots,N-1$. Its value **before trading** at time $n$ is $X_n^- := \varphi^0_{n-1}(1+i_n) +
--   \varphi_{n-1}\cdot\tilde R_n$, and **after trading** $X_n^+ := \varphi^0_n +
--   \varphi_n\cdot e$. $\varphi$ is **self-financing** if $X_n^- = X_n^+$ a.s. for $n =
--   1,\dots,N-1$.
--
--   **Formalization Note.** `e := (1,\dots,1)`, so `φ_n · e = Σ_k φ^k_n`. Both `Xminus`/`Xplus`
--   and `IsSelfFinancing` are given as their own declarations (not folded into the goal or
--   `Arbitrage`) since chunks `04a`-`04d` restate this exact vocabulary.
-- source:
--   Bäuerle and Rieder, Markov Decision Processes with Applications to Finance, Universitext, Springer 2011, DOI 10.1007/978-3-642-18324-9, p. 61-62, PDF 76-77, Definition 3.1.1 / Definition 3.1.3

import Mathlib
import Definitions.Def_MDPFinance_FinancialMarkets_DiscreteMarket

open MeasureTheory ProbabilityTheory

namespace MDPFinance.FinancialMarkets

variable {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}

/-- Definition 3.1.1 (Bäuerle–Rieder, p. 61, PDF 76). A portfolio or trading strategy is an
`(Fam n)`-adapted stochastic process `φ = (φ⁰_n, φ_n)` where `φ⁰_n ∈ ℝ` and `φ_n ∈ ℝ^d`, for
`n = 0, …, N-1`. `φ^k_n` is the amount of money invested into asset `k` on `[n,n+1)`. -/
structure Portfolio (M : DiscreteFinancialMarket Ω d) where
  φ0 : ℕ → Ω → ℝ
  φ : ℕ → Ω → (Fin d → ℝ)
  hφ0_adapted : ∀ n < M.N, @Measurable Ω ℝ (M.Fam n) _ (φ0 n)
  hφ_adapted : ∀ n < M.N, @Measurable Ω (Fin d → ℝ) (M.Fam n) _ (φ n)

variable {M : DiscreteFinancialMarket Ω d}

/-- The value of the initial portfolio, `X_0 := φ⁰_0 + φ_0 · e` (Bäuerle–Rieder, p. 61-62,
PDF 76, unnumbered display). -/
noncomputable def Portfolio.X0 (φ : Portfolio M) (ω : Ω) : ℝ :=
  φ.φ0 0 ω + ∑ k, φ.φ 0 ω k

/-- The value of the portfolio at time `n` before trading, `X_n^- := Σ_k φ^k_{n-1} R̃^k_n =
φ⁰_{n-1}(1+i_n) + φ_{n-1} · R̃_n` (Bäuerle–Rieder, p. 62, PDF 76, unnumbered display), for
`1 ≤ n ≤ N`. -/
noncomputable def Portfolio.Xminus (φ : Portfolio M) (n : ℕ) (ω : Ω) : ℝ :=
  φ.φ0 (n - 1) ω * (1 + M.i n) + ∑ k, φ.φ (n - 1) ω k * M.Rtilde n ω k

/-- The value of the portfolio at time `n` after trading, `X_n^+ := φ⁰_n + φ_n · e`
(Bäuerle–Rieder, p. 62, PDF 76, unnumbered display), for `0 ≤ n ≤ N-1`. -/
noncomputable def Portfolio.Xplus (φ : Portfolio M) (n : ℕ) (ω : Ω) : ℝ :=
  φ.φ0 n ω + ∑ k, φ.φ n ω k

/-- Definition 3.1.3 (Bäuerle–Rieder, p. 62, PDF 77). A portfolio strategy `φ` is called
self-financing if `X_n^- = X_n^+` `ℙ`-a.s. for all `n = 1, …, N-1`. -/
def Portfolio.IsSelfFinancing (φ : Portfolio M) : Prop :=
  ∀ n, 1 ≤ n → n ≤ M.N - 1 → ∀ᵐ ω ∂M.measIP, φ.Xminus n ω = φ.Xplus n ω

end MDPFinance.FinancialMarkets


