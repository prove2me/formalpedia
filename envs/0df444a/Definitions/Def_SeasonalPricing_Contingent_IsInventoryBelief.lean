-- Prove2me | Definitions.Def_SeasonalPricing_Contingent_IsInventoryBelief
-- name    : SeasonalPricing_Contingent_IsInventoryBelief
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T11:09:00.724354+00:00
-- url     : https://prove2.me/theorems/29618fbc-143c-4c9c-ab12-67a043b85223
-- title:
--   A customer's belief about remaining inventory and allocation at the discount time
-- statement:
--   Consider a seller who starts the season with $Q$ units. A customer who postpones the purchase to the discount time $T$ faces two uncertainties: the number $Q_T \in \{0, 1, \dots, Q\}$ of units still unsold at time $T$, and the event $\mathcal A$ that a unit is actually allocated to him when he requests one (units are rationed at random when fewer remain than customers ask for).
--
--   A **belief** is a pair of functions $\pi, a : \mathbb N \to \mathbb R$ such that
--
--   1. $\pi(q) \ge 0$ for $q = 0, \dots, Q$ and $\sum_{q=0}^{Q} \pi(q) = 1$; here $\pi(q) = \Pr\{Q_T = q\}$;
--   2. $0 \le a(q) \le 1$ for $q = 0, \dots, Q$; here $a(q) = \Pr\{\mathcal A \mid Q_T = q\}$ is the allocation probability given $q$ remaining units;
--   3. $a(0) = 0$: with no unit left, no unit is allocated.
--
--   Values of $\pi$ and $a$ outside $\{0, \dots, Q\}$ play no role. The belief summarizes everything a customer needs to know about the other customers' purchasing strategies; Theorem 1 of Aviv and Pazgal holds for an arbitrary belief, i.e. under arbitrary strategies of the others.
--
--   **Formalization Note** The pmf and the allocation probabilities are finite real vectors indexed by $\mathbb N$ and restricted to `Finset.range (Q + 1)`, rather than a random variable on a probability space; only the joint law of $(Q_T, \mathbf 1\{\mathcal A\})$ enters equation (2).
-- source:
--   Aviv and Pazgal, Optimal Pricing of Seasonal Products in the Presence of Forward-Looking Consumers, Manufacturing & Service Operations Management 10(3), 2008, p. 344, Theorem 1, Eq. (2) and the sentence after it; p. 345 (the allocation probability 1{𝒜 | Q_T}); p. 346, Eq. (4) and A(q | Λ)

import Mathlib

namespace SeasonalPricing.Contingent

/-- A customer's belief about the discount period (Aviv–Pazgal 2008, Eq. (2), p. 344):
`pmf q` is the probability that `Q_T = q` units remain at time `T` (`q ∈ {0, …, Q}`), and
`alloc q` is the probability that the customer is allocated a unit when `Q_T = q`
(the conditional probability of the event 𝒜 given `Q_T = q`). With no unit left there is
no allocation: `alloc 0 = 0`. Values outside `{0, …, Q}` play no role. -/
def IsInventoryBelief (Q : ℕ) (pmf alloc : ℕ → ℝ) : Prop :=
  (∀ q ∈ Finset.range (Q + 1), 0 ≤ pmf q) ∧
  (∑ q ∈ Finset.range (Q + 1), pmf q) = 1 ∧
  (∀ q ∈ Finset.range (Q + 1), 0 ≤ alloc q ∧ alloc q ≤ 1) ∧
  alloc 0 = 0

end SeasonalPricing.Contingent


