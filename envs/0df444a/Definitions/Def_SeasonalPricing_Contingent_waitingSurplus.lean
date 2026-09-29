-- Prove2me | Definitions.Def_SeasonalPricing_Contingent_waitingSurplus
-- name    : SeasonalPricing_Contingent_waitingSurplus
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T11:09:23.618084+00:00
-- url     : https://prove2.me/theorems/7ec91230-3f9d-4f72-b7ec-6a869814f8a9
-- title:
--   Expected surplus of waiting for the contingent discount (right-hand side of Eq. (2)) and the immediate-purchase rule
-- statement:
--   Fix a season with discount time $T$, an exponential valuation decline factor $\alpha \ge 0$, a premium price $p_1$, and a contingent discount menu $p_2(1), \dots, p_2(Q)$, where $p_2(q)$ is the price charged from time $T$ on when $q$ units remain. Let $(\pi, a)$ be a customer's belief about the remaining inventory $Q_T$ and the allocation event $\mathcal A$.
--
--   A customer arriving at time $t < T$ with current valuation $\psi$ will have valuation $\psi e^{-\alpha(T-t)}$ at time $T$. The **expected surplus of waiting** is the right-hand side of equation (2) of Aviv and Pazgal:
--
--   $$
--   W_t(\psi) = \mathrm E_{Q_T}\!\left[\max\{\psi e^{-\alpha(T-t)} - p_2(Q_T), 0\}\cdot \mathbf 1\{\mathcal A \mid Q_T\}\right] = \sum_{q=0}^{Q} \pi(q)\, a(q)\, \max\{\psi e^{-\alpha(T-t)} - p_2(q), 0\}.
--   $$
--
--   The **purchase rule** of the paper (p. 344): a customer arriving at time $t < T$ with current valuation $v = V e^{-\alpha t}$ buys immediately at price $p_1$ if and only if
--
--   1. the current surplus is nonnegative, $v - p_1 \ge 0$, and
--   2. it is at least the expected surplus of waiting, $v - p_1 \ge W_t(v)$.
--
--   Theorem 1 shows that this rule is a threshold rule in the current valuation.
--
--   **Formalization Note** `waitingSurplus Q π a p2 α T t ψ` is $W_t(\psi)$ with $e^{-\alpha(T-t)}$ written `Real.exp (-(α * (T - t)))`; `buysNow Q π a p2 p1 α T t v` is the rule above. The term $q = 0$ carries the factor $a(0)$, which a belief sets to $0$, so the value $p_2(0)$ never matters. The belief does not depend on the arrival time $t$: the focal customer's arrival time does not affect the inventory left at $T$ or the rationing among waiting customers when he waits (as in Eq. (4), p. 346).
-- source:
--   Aviv and Pazgal, Optimal Pricing of Seasonal Products in the Presence of Forward-Looking Consumers, Manufacturing & Service Operations Management 10(3), 2008, p. 343, §3 (V_j(t) = V_j e^{−αt}); p. 344, §3 purchase rule (i)–(ii) and Theorem 1, Eq. (2)

import Mathlib

namespace SeasonalPricing.Contingent

/-- The right-hand side of Eq. (2) (Aviv–Pazgal 2008, p. 344): the expected surplus that a
customer arriving at time `t < T` with current valuation `ψ` gains by postponing the purchase
to time `T`,
`E_{Q_T}[max{ψ e^{-α(T-t)} - p₂(Q_T), 0} · 1{𝒜 | Q_T}]
  = ∑_{q=0}^{Q} pmf q · alloc q · max{ψ e^{-α(T-t)} - p₂(q), 0}`,
where `pmf` is the law of the remaining inventory `Q_T`, `alloc q` the allocation probability
given `Q_T = q`, and `p2 q` the contingent discount price charged when `q` units remain. -/
noncomputable def waitingSurplus (Q : ℕ) (pmf alloc p2 : ℕ → ℝ) (α T t ψ : ℝ) : ℝ :=
  ∑ q ∈ Finset.range (Q + 1),
    pmf q * alloc q * max (ψ * Real.exp (-(α * (T - t))) - p2 q) 0

/-- The purchase rule of p. 344: a customer arriving at time `t < T` with current valuation
`v = V e^{-αt}` buys immediately at the premium price `p1` iff (i) the current surplus
`v - p1` is nonnegative and (ii) it is at least the expected surplus of waiting for the
discount, `waitingSurplus … t v`. -/
def buysNow (Q : ℕ) (pmf alloc p2 : ℕ → ℝ) (p1 α T t v : ℝ) : Prop :=
  0 ≤ v - p1 ∧ waitingSurplus Q pmf alloc p2 α T t v ≤ v - p1

end SeasonalPricing.Contingent


