-- Prove2me | Definitions.Def_BauerleRiederMDP_Indifference_FinancialMarket_NoArbitrage
-- name    : BauerleRiederMDP_Indifference_FinancialMarket_NoArbitrage
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T06:28:52.716365+00:00
-- url     : https://prove2.me/theorems/e7194806-bd84-409f-af79-87acb6f49a44
-- title:
--   Absence of arbitrage opportunities
-- statement:
--   An arbitrage opportunity is a self-financing strategy $\phi$ with $X^\phi_0=0$, $\mathbb P(X^\phi_N\ge 0)=1$ and $\mathbb P(X^\phi_N>0)>0$. The market admits no arbitrage opportunities if no strategy has these properties.
-- source:
--   Bäuerle & Rieder, Markov Decision Processes with Applications to Finance (2011), Definition 3.1.4, p.63

import Mathlib
import Definitions.Def_BauerleRiederMDP_Indifference_FinancialMarket_Strategy

open MeasureTheory

namespace BauerleRiederMDP.Indifference

namespace FinancialMarket

variable {Ω : Type*} [MeasurableSpace Ω] {d N : ℕ}

/-- An arbitrage opportunity (Bäuerle & Rieder, Markov Decision Processes with Applications to
Finance (2011), Definition 3.1.4, p.63, PDF 77): a self-financing strategy with `X^φ₀ = 0`,
`ℙ(X^φ_N ≥ 0) = 1` and `ℙ(X^φ_N > 0) > 0`. -/
def IsArbitrage {M : FinancialMarket Ω d N} (φ : M.Strategy) : Prop :=
  IsSelfFinancing φ ∧ (∀ ω, X φ 0 ω = 0) ∧ (∀ᵐ ω ∂M.P, 0 ≤ X φ N ω) ∧
    0 < M.P {ω | 0 < X φ N ω}

/-- The market admits no arbitrage opportunities. -/
def NoArbitrage (M : FinancialMarket Ω d N) : Prop :=
  ∀ φ : M.Strategy, ¬ IsArbitrage φ

end FinancialMarket

end BauerleRiederMDP.Indifference


