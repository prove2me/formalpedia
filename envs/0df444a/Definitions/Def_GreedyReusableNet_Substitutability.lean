-- Prove2me | Definitions.Def_GreedyReusableNet_Substitutability
-- name    : GreedyReusableNet_Substitutability
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T13:34:42.949375+00:00
-- url     : https://prove2.me/theorems/346eaeee-8e61-4fcc-ba62-fc8dd5d26130
-- title:
--   Assumption 2 (Substitutability)
-- statement:
--   **Assumption 2.** For every period $t<T$, bundle $B\in\mathcal B_t$, counting vector $n$ and action sets $\mathcal A\subseteq\mathcal A'$ with $B\in\mathcal A$ and $\mathcal A'\in\mathscr A_t$,
--   $$\mathbb P_t(B\mid\mathcal A,n(B))\ \ge\ \mathbb P_t(B\mid\mathcal A',n(B)).$$
--   Adding bundles to an action set never raises the activation probability of a bundle already in it.
--
--   **Formalization Note** The larger set ranges over $\mathscr A_t$, where $\mathbb P_t$ is defined; the smaller one then lies in $\mathscr A_t$ under Assumption 1.
-- source:
--   Simchi-Levi, Zheng & Zhu, On Greedy-like Policies in Online Matching with Reusable Network Resources and Decaying Rewards, SSRN 3981123, §2.1, Assumption 2, p.10

import Mathlib
import Definitions.Def_GreedyReusableNet_ProblemInstance
import Definitions.Def_GreedyReusableNet_prob

namespace GreedyReusableNet

/-- **Assumption 2 (Substitutability)** (Simchi-Levi, Zheng & Zhu, SSRN 3981123, §2.1, p.10):
"`∀t ∈ [T]`, `B ∈ 𝓑_t` and `n_t(B)`, if `B ∈ 𝒜_t ⊂ 𝒜′_t`, then
`ℙ_t(B|𝒜_t, n_t(B)) ≥ ℙ_t(B|𝒜′_t, n_t(B))`."

**Formalization Note** The larger action set `A'` ranges over `𝒜_t` (the marginal `ℙ_t` is only
defined for action sets of `𝒜_t`, Algorithm 1 step 2); `A ⊆ A'` then lies in `𝒜_t` too under
Assumption 1. Periods are 0-based (`t < T`). -/
def Substitutability {N : ℕ} (I : ProblemInstance N) (T : ℕ) : Prop :=
  ∀ t < T, ∀ B ∈ (I.period t).bundles, ∀ A A' : Finset (Finset (Fin N)),
    A' ∈ (I.period t).actions → B ∈ A → A ⊆ A' → ∀ n : Fin N → ℕ,
      prob (I.period t) B A' n ≤ prob (I.period t) B A n

end GreedyReusableNet


