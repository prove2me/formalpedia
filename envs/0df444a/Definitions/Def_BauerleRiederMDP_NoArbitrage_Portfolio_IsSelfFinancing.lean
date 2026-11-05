-- Prove2me | Definitions.Def_BauerleRiederMDP_NoArbitrage_Portfolio_IsSelfFinancing
-- name    : BauerleRiederMDP_NoArbitrage_Portfolio_IsSelfFinancing
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T06:25:25.992821+00:00
-- url     : https://prove2.me/theorems/64d86592-b702-41d3-9989-bcf0e6f0ab4c
-- title:
--   Self-financing strategy (Definition 3.1.3)
-- statement:
--   A portfolio strategy $\varphi$ is **self-financing** if
--   $$
--   X^\varphi_{n-}=X^\varphi_{n+}\quad\mathbb P\text{-a.s.},\qquad n=1,\dots,N-1,
--   $$
--   where $X_{n+}=\varphi^0_n+\varphi_n\cdot e$ is the value after trading: the current wealth is only reassigned to the assets.
-- source:
--   Bäuerle & Rieder, Markov Decision Processes with Applications to Finance (2011), Definition 3.1.3, p.62 (PDF 76)

import Mathlib
import Definitions.Def_BauerleRiederMDP_NoArbitrage_Portfolio_wealth

open MeasureTheory

namespace BauerleRiederMDP.NoArbitrage

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {d : ℕ} {M : FinancialMarket Ω P d}

/-- Definition 3.1.3 (Bäuerle & Rieder 2011, p.62, PDF 76): a portfolio strategy `φ` is
self-financing if `X^φ_{n−} = X^φ_{n+}` `ℙ`-a.s. for all `n = 1, …, N − 1`, where
`X_{n+} := φ^0_n + φ_n · e` is the value after trading. -/
def Portfolio.IsSelfFinancing (φ : Portfolio M) : Prop :=
  ∀ n, 1 ≤ n → n < M.N → ∀ᵐ ω ∂P, φ.wealth n ω = φ.φ0 n ω + ∑ k, φ.φ n ω k

end BauerleRiederMDP.NoArbitrage


