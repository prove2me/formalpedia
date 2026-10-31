-- Prove2me | Definitions.Def_FullPriceTime_IsFullPriceDecisionMaker
-- name    : FullPriceTime_IsFullPriceDecisionMaker
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T19:48:19.63655+00:00
-- url     : https://prove2.me/theorems/a435ecab-7709-4049-bdc6-4b98564a745a
-- title:
--   Full-price decision-maker (Definition 1)
-- statement:
--   A consumer (horizon $T$, utility $U$, overhead time $O$, compensation $\Pi_\theta$) is a **full-price decision-maker** if there is $\eta>0$ such that for all prices $r,\hat r\ge 0$ and time commitments $\delta,\hat\delta\ge 0$,
--   $$(\hat r,\hat\delta)\ \text{feasible and}\ r+\eta\delta=\hat r+\eta\hat\delta\ \Longrightarrow\ u^B(\theta,r,\delta)=u^B(\theta,\hat r,\hat\delta).$$
--   The consumer then converts time into money at the constant rate $\eta$: the full price $r+\eta\delta$ is a sufficient statistic for the buying consumer's leisure utility, and hence for her purchase decision.
--
--   **Formalization Note** The pair $(r,\delta)$, free in the paper's sentence, is universally quantified and need not be feasible; only $(\hat r,\hat\delta)$ is required to be, as on the page. Prices and time commitments are non-negative, as everywhere in the paper ($r$ is paid out of earnings, $\delta$ is a block of time).
-- source:
--   Li, Lariviere, Bassamboo, Is Full Price the Full Story When Consumers Have Time and Budget Constraints?, SSRN 4223388, Definition 1, p.7

import Mathlib
import Definitions.Def_FullPriceTime_IsFeasiblePair
import Definitions.Def_FullPriceTime_buyerUtility

namespace FullPriceTime

/-- **Full-price decision-maker (Definition 1).**
Li, Lariviere, Bassamboo, *Is Full Price the Full Story When Consumers Have Time and Budget
Constraints?*, SSRN 4223388, §2.2, Definition 1, p.7 (PDF p.7): "A consumer is a full-price
decision-maker if there exists an η > 0 such that uB(θ,r,δ) = uB(θ, r̂, δ̂) for every feasible
(r̂, δ̂) with r + ηδ = r̂ + ηδ̂."

The consumer with horizon `T`, utility `U`, overhead time `O` and compensation `comp` is a
full-price decision-maker when there is `η > 0` such that for all non-negative prices `r, r̂` and
time commitments `δ, δ̂`, if `(r̂, δ̂)` is feasible and `r + ηδ = r̂ + ηδ̂`, then
`u^B(r, δ) = u^B(r̂, δ̂)`.

**Formalization Note** The pair `(r, δ)`, free in the paper's sentence, is universally
quantified and is not required to be feasible; only `(r̂, δ̂)` is, as on the page. Prices and time
commitments are non-negative: `r` is a price paid out of earnings and `δ` a block of time (the
paper writes `r ∈ ℝ₊` on p.14); with negative prices the definition would compare plans the paper
never considers. -/
def IsFullPriceDecisionMaker (T : ℝ) (U : ℝ × ℝ → ℝ) (O : ℝ → ℝ) (comp : ℝ → ℝ) : Prop :=
  ∃ η : ℝ, 0 < η ∧
    ∀ r δ r' δ' : ℝ, 0 ≤ r → 0 ≤ δ → 0 ≤ r' → 0 ≤ δ' →
      IsFeasiblePair T O comp r' δ' →
      r + η * δ = r' + η * δ' →
      buyerUtility T U O comp r δ = buyerUtility T U O comp r' δ'

end FullPriceTime


