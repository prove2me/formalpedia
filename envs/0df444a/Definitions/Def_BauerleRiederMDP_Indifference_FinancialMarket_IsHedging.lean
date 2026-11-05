-- Prove2me | Definitions.Def_BauerleRiederMDP_Indifference_FinancialMarket_IsHedging
-- name    : BauerleRiederMDP_Indifference_FinancialMarket_IsHedging
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T06:29:07.70349+00:00
-- url     : https://prove2.me/theorems/99dfb759-8bab-4258-9e0b-87ec0320696d
-- title:
--   Contingent claims and hedging strategies
-- statement:
--   A contingent claim is a non-negative, $\mathcal F_N$-measurable random variable $H$. A self-financing strategy $\phi$ is a replicating or hedging strategy of $H$ if $H=X^\phi_N$ almost surely, and $H$ is attainable when such a strategy exists. The price of an attainable claim is the initial amount needed to replicate it, $\pi(H):=\phi^0_0+\phi_0\cdot e=X^\phi_0$.
-- source:
--   Bäuerle & Rieder, Markov Decision Processes with Applications to Finance (2011), Definitions C.1.3 and C.1.5, pp.365–366

import Mathlib
import Definitions.Def_BauerleRiederMDP_Indifference_FinancialMarket_Strategy

open MeasureTheory

namespace BauerleRiederMDP.Indifference

namespace FinancialMarket

variable {Ω : Type*} [MeasurableSpace Ω] {d N : ℕ}

/-- A contingent claim (Bäuerle & Rieder, Markov Decision Processes with Applications to Finance
(2011), Definition C.1.3 a), p.365, PDF 370): a non-negative, `𝓕_N`-measurable random variable. -/
def IsContingentClaim (M : FinancialMarket Ω d N) (H : Ω → ℝ) : Prop :=
  Measurable[M.F N] H ∧ ∀ ω, 0 ≤ H ω

/-- `φ` is a replicating or hedging strategy of `H` (Definition C.1.3 b), pp.365–366, PDF 370–371): a
self-financing strategy with `H = X^φ_N` `ℙ`-a.s. A claim is attainable when such a `φ` exists, and
its price is then `π(H) := φ⁰₀ + φ₀ · e`, the value `X^φ₀` (Definition C.1.5, p.366, PDF 371). -/
def IsHedging {M : FinancialMarket Ω d N} (φ : M.Strategy) (H : Ω → ℝ) : Prop :=
  IsSelfFinancing φ ∧ H =ᵐ[M.P] X φ N

end FinancialMarket

end BauerleRiederMDP.Indifference


