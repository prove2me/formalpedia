-- Prove2me | Definitions.Def_GreedyReusableNet_DecayingReward
-- name    : GreedyReusableNet_DecayingReward
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T13:34:50.003159+00:00
-- url     : https://prove2.me/theorems/1c503ddf-71e8-4a62-99d9-977e200a65c3
-- title:
--   Assumption 5.1 (Decaying Reward)
-- statement:
--   **Assumption 5.1.** For every period $t<T$, bundle $B\in\mathcal B_t$ and counting vectors $n,n'$ with $n_i\le n'_i$ for every $i\in B$,
--   $$r_t(B;n(B))\ \ge\ r_t(B;n'(B)).$$
--   The reward of a bundle can only decrease as its arms are used more.
--
--   **Formalization Note** Applied to vectors that agree on $B$, the condition also makes the reward depend on the counting vector only through $n(B)$.
-- source:
--   Simchi-Levi, Zheng & Zhu, On Greedy-like Policies in Online Matching with Reusable Network Resources and Decaying Rewards, SSRN 3981123, §2.1, Assumption 5.1, p.12

import Mathlib
import Definitions.Def_GreedyReusableNet_ProblemInstance

namespace GreedyReusableNet

/-- **Assumption 5.1 (Decaying Reward)** (Simchi-Levi, Zheng & Zhu, SSRN 3981123, §2.1, p.12):
"`∀t ∈ [T]` and `B ∈ 𝓑_t`, if `n_t(B) ≤ n′_t(B)`, then `r_t(B; n_t(B)) ≥ r_t(B; n′_t(B))`. Here,
“`≤`” is taken as an element-wise operator."

**Formalization Note** `n(B) ≤ n'(B)` element-wise is `∀ i ∈ B, n i ≤ n' i`. Applied with `n`
and `n'` agreeing on `B`, the condition also makes the reward depend on the counting vector only
through `n(B)`, as in the paper's notation `r_t(B; n(B))`. Periods are 0-based. -/
def DecayingReward {N : ℕ} (I : ProblemInstance N) (T : ℕ) : Prop :=
  ∀ t < T, ∀ B ∈ (I.period t).bundles, ∀ n n' : Fin N → ℕ, (∀ i ∈ B, n i ≤ n' i) →
    (I.period t).reward B n' ≤ (I.period t).reward B n

end GreedyReusableNet


