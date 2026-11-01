-- Prove2me | Definitions.Def_GreedyReusableNet_DecayingProbability
-- name    : GreedyReusableNet_DecayingProbability
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T13:35:22.532625+00:00
-- url     : https://prove2.me/theorems/338e2790-d581-4e4b-96cb-a5979f3f6f9d
-- title:
--   Assumption 5.2 (Decaying Probability)
-- statement:
--   **Assumption 5.2.** For every period $t<T$, bundle $B\in\mathcal B_t$, action set $\mathcal A\in\mathscr A_t$ and counting vectors $n,n'$ with $n_i\le n'_i$ for every $i\in B$,
--   $$\mathbb P_t(B\mid\mathcal A,n(B))\ \ge\ \mathbb P_t(B\mid\mathcal A,n'(B)).$$
--   The activation probability of a bundle can only decrease as its arms are used more.
-- source:
--   Simchi-Levi, Zheng & Zhu, On Greedy-like Policies in Online Matching with Reusable Network Resources and Decaying Rewards, SSRN 3981123, §2.1, Assumption 5.2, p.12

import Mathlib
import Definitions.Def_GreedyReusableNet_ProblemInstance
import Definitions.Def_GreedyReusableNet_prob

namespace GreedyReusableNet

/-- **Assumption 5.2 (Decaying Probability)** (Simchi-Levi, Zheng & Zhu, SSRN 3981123, §2.1,
p.12): "`∀t ∈ [T]`, `B ∈ 𝓑_t` and `𝒜_t ∈ 𝒜_t`, if `n_t(B) ≤ n′_t(B)`, then
`ℙ_t(B|𝒜_t, n_t(B)) ≥ ℙ_t(B|𝒜_t, n′_t(B))`. Here, “`≤`” is taken as an element-wise operator."

**Formalization Note** `n(B) ≤ n'(B)` element-wise is `∀ i ∈ B, n i ≤ n' i`; with `n`, `n'`
agreeing on `B` it also makes `ℙ_t(B | A, ·)` depend only on `n(B)`. Periods are 0-based. -/
def DecayingProbability {N : ℕ} (I : ProblemInstance N) (T : ℕ) : Prop :=
  ∀ t < T, ∀ B ∈ (I.period t).bundles, ∀ A ∈ (I.period t).actions,
    ∀ n n' : Fin N → ℕ, (∀ i ∈ B, n i ≤ n' i) →
      prob (I.period t) B A n' ≤ prob (I.period t) B A n

end GreedyReusableNet


