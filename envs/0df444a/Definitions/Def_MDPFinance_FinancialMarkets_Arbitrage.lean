-- Prove2me | Definitions.Def_MDPFinance_FinancialMarkets_Arbitrage
-- name    : MDPFinance_FinancialMarkets_Arbitrage
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-27T21:49:21.634969+00:00
-- url     : https://prove2.me/theorems/1ea05110-0762-4485-95b2-044f3ddd9d9a
-- title:
--   Definition 3.1.4 — arbitrage opportunity
-- statement:
--   An **arbitrage opportunity** is a self-financing portfolio $\varphi$ with initial wealth
--   $X_0^\varphi = 0$ a.s., terminal wealth $X_N^\varphi \geq 0$ a.s., and $\mathbb{P}(X_N^\varphi
--   > 0) > 0$: a riskless strategy with a chance of gain. A market has **no arbitrage** if no
--   such $\varphi$ exists.
--
--   **Formalization Note.** $X_N^\varphi$ is `Xminus M.N φ` (the value at the terminal date
--   before any further trading, which self-financing forces to equal `Xplus` at every interior
--   date anyway).
-- source:
--   Bäuerle and Rieder, Markov Decision Processes with Applications to Finance, Universitext, Springer 2011, DOI 10.1007/978-3-642-18324-9, p. 63, PDF 77, Definition 3.1.4

import Mathlib
import Definitions.Def_MDPFinance_FinancialMarkets_DiscreteMarket
import Definitions.Def_MDPFinance_FinancialMarkets_Portfolio

open MeasureTheory ProbabilityTheory

namespace MDPFinance.FinancialMarkets

variable {Ω : Type*} [MeasurableSpace Ω] {d : ℕ} {M : DiscreteFinancialMarket Ω d}

/-- Definition 3.1.4 (Bäuerle–Rieder, p. 63, PDF 77). An arbitrage opportunity is a
self-financing portfolio strategy `φ` with `X_0^φ = 0` and `ℙ(X_N^φ ≥ 0) = 1`,
`ℙ(X_N^φ > 0) > 0`, where `X_N^φ` is the terminal wealth `Xminus M.N φ`. -/
def IsArbitrageOpportunity (φ : Portfolio M) : Prop :=
  φ.IsSelfFinancing ∧ (∀ᵐ ω ∂M.measIP, φ.X0 ω = 0) ∧
    M.measIP {ω | 0 ≤ φ.Xminus M.N ω} = 1 ∧ M.measIP {ω | 0 < φ.Xminus M.N ω} > 0

/-- The market `M` has no arbitrage opportunities (Bäuerle–Rieder, p. 63, PDF 77-78, Theorem
3.1.5's part a)). -/
def NoArbitrage (M : DiscreteFinancialMarket Ω d) : Prop :=
  ¬ ∃ φ : Portfolio M, IsArbitrageOpportunity φ

end MDPFinance.FinancialMarkets


