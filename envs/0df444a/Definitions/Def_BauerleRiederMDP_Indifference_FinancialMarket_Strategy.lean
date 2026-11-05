-- Prove2me | Definitions.Def_BauerleRiederMDP_Indifference_FinancialMarket_Strategy
-- name    : BauerleRiederMDP_Indifference_FinancialMarket_Strategy
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T06:27:58.035034+00:00
-- url     : https://prove2.me/theorems/ef1729d9-bea2-45f0-8b9c-2556028feda2
-- title:
--   Portfolio strategies, wealth and the self-financing condition
-- statement:
--   A portfolio strategy is an adapted process $\phi=(\phi^0_n,\phi_n)$, $n=0,\dots,N-1$, where $\phi^k_n$ is the amount of money invested into asset $k$ during $[n,n+1)$. Its value after trading is $X_{n+}=\phi^0_n+\phi_n\cdot e$, with $X_0=\phi^0_0+\phi_0\cdot e$, and its value at time $n+1$ before trading is
--   $$
--   X_{n+1}=\phi^0_n(1+i_{n+1})+\phi_n\cdot\tilde R_{n+1}.
--   $$
--   The strategy is self-financing if $X_{n-}=X_{n+}$ almost surely for $n=1,\dots,N-1$: the current wealth is only reassigned to the assets.
-- source:
--   Bäuerle & Rieder, Markov Decision Processes with Applications to Finance (2011), Definitions 3.1.1 and 3.1.3, pp.61–62

import Mathlib
import Definitions.Def_BauerleRiederMDP_Indifference_FinancialMarket

open MeasureTheory

namespace BauerleRiederMDP.Indifference

namespace FinancialMarket

variable {Ω : Type*} [MeasurableSpace Ω] {d N : ℕ}

/-- A portfolio strategy (Bäuerle & Rieder, Markov Decision Processes with Applications to Finance
(2011), Definition 3.1.1, p.61, PDF 75): an `(𝓕_n)`-adapted process `φ = (φ⁰_n, φ_n)`,
`n = 0, …, N - 1`, where `φ^k_n` is the amount of money invested into asset `k` during `[n, n + 1)`. -/
structure Strategy (M : FinancialMarket Ω d N) where
  /-- The amount `φ⁰_n` in the bond. -/
  φ0 : ℕ → Ω → ℝ
  /-- The amounts `φ^k_n` in the risky assets. -/
  φ : ℕ → Ω → Fin d → ℝ
  adapted0 : ∀ n, n < N → Measurable[M.F n] (φ0 n)
  adapted : ∀ n, n < N → ∀ k, Measurable[M.F n] fun ω => φ n ω k

/-- The value `X_{n+} = φ⁰_n + φ_n · e` of the portfolio at time `n` after trading (p.62, PDF 76). -/
def Xplus {M : FinancialMarket Ω d N} (φ : M.Strategy) (n : ℕ) (ω : Ω) : ℝ :=
  φ.φ0 n ω + ∑ k, φ.φ n ω k

/-- The value `X_n` of the portfolio: `X₀ = φ⁰₀ + φ₀ · e` and, before trading at time `n + 1`,
`X_{n+1} = X_{(n+1)-} = φ⁰_n (1 + i_{n+1}) + φ_n · R̃_{n+1}` (p.62, PDF 76). -/
def X {M : FinancialMarket Ω d N} (φ : M.Strategy) : ℕ → Ω → ℝ
  | 0, ω => Xplus φ 0 ω
  | n + 1, ω => φ.φ0 n ω * (1 + M.i (n + 1)) + ∑ k, φ.φ n ω k * M.Rt (n + 1) ω k

/-- A self-financing strategy (Definition 3.1.3, p.62, PDF 76): `X_{n-} = X_{n+}` `ℙ`-a.s. for
`n = 1, …, N - 1`. -/
def IsSelfFinancing {M : FinancialMarket Ω d N} (φ : M.Strategy) : Prop :=
  ∀ n, 1 ≤ n → n < N → ∀ᵐ ω ∂M.P, X φ n ω = Xplus φ n ω

end FinancialMarket

end BauerleRiederMDP.Indifference


