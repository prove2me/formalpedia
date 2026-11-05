-- Prove2me | Definitions.Def_BauerleRiederMDP_NoArbitrage_Portfolio_IsArbitrage
-- name    : BauerleRiederMDP_NoArbitrage_Portfolio_IsArbitrage
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T06:26:30.722793+00:00
-- url     : https://prove2.me/theorems/6f65e698-9c0c-40c9-abf6-0f728c0319c6
-- title:
--   Arbitrage opportunity (Definition 3.1.4)
-- statement:
--   An **arbitrage opportunity** is a self-financing portfolio strategy $\varphi$ with
--   $$
--   X^\varphi_0=0,\qquad \mathbb P(X^\varphi_N\ge0)=1,\qquad \mathbb P(X^\varphi_N>0)>0 .
--   $$
--   It is a riskless strategy with a chance of a gain.
--
--   **Formalization Note** $X^\varphi_0=0$ is required at every $\omega$; for $N\ge1$ the initial portfolio is $\mathcal F_0$-measurable with $\mathcal F_0$ trivial, hence constant. For $N=0$ the terminal wealth is $X_0$, so there is no arbitrage.
-- source:
--   Bäuerle & Rieder, Markov Decision Processes with Applications to Finance (2011), Definition 3.1.4, p.63 (PDF 77)

import Mathlib
import Definitions.Def_BauerleRiederMDP_NoArbitrage_Portfolio_IsSelfFinancing

open MeasureTheory

namespace BauerleRiederMDP.NoArbitrage

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {d : ℕ} {M : FinancialMarket Ω P d}

/-- Definition 3.1.4 (Bäuerle & Rieder 2011, p.63, PDF 77): an arbitrage opportunity is a
self-financing portfolio strategy `φ` with `X^φ_0 = 0`, `ℙ(X^φ_N ≥ 0) = 1` and `ℙ(X^φ_N > 0) > 0`.

**Formalization Note** `X^φ_0 = 0` is required at every `ω`: `X_0` is `𝓕_0`-measurable and
`𝓕_0 = {∅, Ω}`, so it is a constant (when `N ≥ 1`). For `N = 0` the terminal wealth is `X_0`, so
there is no arbitrage. -/
def Portfolio.IsArbitrage (φ : Portfolio M) : Prop :=
  φ.IsSelfFinancing ∧ (∀ ω, φ.wealth 0 ω = 0) ∧ (∀ᵐ ω ∂P, 0 ≤ φ.wealth M.N ω) ∧
    0 < P {ω | 0 < φ.wealth M.N ω}

end BauerleRiederMDP.NoArbitrage


