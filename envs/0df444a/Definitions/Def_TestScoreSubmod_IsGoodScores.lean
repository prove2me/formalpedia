-- Prove2me | Definitions.Def_TestScoreSubmod_IsGoodScores
-- name    : TestScoreSubmod_IsGoodScores
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T02:47:11.055554+00:00
-- url     : https://prove2.me/theorems/a20ed9e5-d08f-47e0-9b1f-638e723e8213
-- title:
--   $(p,q)$-good test scores
-- statement:
--   Test scores $a_1,\dots,a_n$ are **$(p,q)$-good** for a set function $u$ with cardinality parameter $k$ if the minorant $\underline v(S)=\min_{i\in S}a_i$ and the majorant $\bar v(S)=\max_{i\in S}a_i$ of eq. (9) form a $(p,q)$-sketch of $u$ (eq. (8)) on the relevant sets:
--
--   1. $p\,\min_{i\in S}a_i\le u(S)$ for every $S$ with $|S|=k$, and
--   2. $u(S)\le q\,\max_{i\in S}a_i$ for every nonempty $S$ with $|S|\le k$.
--
--   Good scores reduce the maximization of $u$ under a cardinality constraint to sorting the scores.
--
--   **Formalization Note** Definition 3 asks for (8) at every $S\subseteq N$; the minimum and maximum of $\emptyset$ are undefined, and on all sizes Lemma 4 is false (with $g=\sum_i x_i$ and $X_i\equiv1$: at $k=2$ the lower bound fails at a singleton, and at $k=1$, $n=5$ the upper bound fails at $S=N$). The lower bound is required at $|S|=k$, as in Appendices C and D (p.35), and the upper bound at $0<|S|\le k$, which the proof of Lemma 4 gives and Corollary 1 uses.
-- source:
--   Sekar, Vojnovic, Yun, A Test Score Based Approach to Stochastic Submodular Optimization, arXiv:1605.07172v4, §3, p.19 (definition of (p,q)-good scores), Definition 3, eq. (8), p.18, eq. (9), p.19

import Mathlib

namespace TestScoreSubmod

/-- **`(p, q)`-good test scores** (Sekar, Vojnovic, Yun, arXiv:1605.07172v4, §3, p.19: "We say
that a₁, a₂, …, aₙ are (p, q)-good test scores if (v̲, v̄) is a (p, q)-sketch of the set function
u", with the sketch of Definition 3, eq. (8), p.18, and `v̲(S) = min{aᵢ | i ∈ S}`,
`v̄(S) = max{aᵢ | i ∈ S}` of eq. (9)).

`IsGoodScores k p q a u` says:

1. `p · min_{i∈S} aᵢ ≤ u(S)` for every set `S` with `|S| = k`, and
2. `u(S) ≤ q · max_{i∈S} aᵢ` for every nonempty set `S` with `|S| ≤ k`.

**Formalization Note** Definition 3 asks for (8) at every `S ⊆ N`. The minimum and maximum of
`∅` are undefined, and on all sizes Lemma 4 is false (with `g = Σ` and `Xᵢ ≡ 1`: at `k = 2` the
lower bound fails at a singleton, at `k = 1` the upper bound fails at `S = N` with `n = 5`).
The lower bound is required at `|S| = k`, as in Appendices C and D (p.35); the upper bound at
`0 < |S| ≤ k`, which the proof of Lemma 4 gives and Corollary 1 needs. -/
def IsGoodScores {ι : Type*} (k : ℕ) (p q : ℝ) (a : ι → ℝ) (u : Finset ι → ℝ) : Prop :=
  (∀ (S : Finset ι) (h : S.Nonempty), S.card = k → p * S.inf' h a ≤ u S) ∧
  (∀ (S : Finset ι) (h : S.Nonempty), S.card ≤ k → u S ≤ q * S.sup' h a)

end TestScoreSubmod


