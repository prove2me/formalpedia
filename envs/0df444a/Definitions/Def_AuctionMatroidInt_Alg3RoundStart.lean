-- Prove2me | Definitions.Def_AuctionMatroidInt_Alg3RoundStart
-- name    : AuctionMatroidInt_Alg3RoundStart
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T02:29:21.305934+00:00
-- url     : https://prove2.me/theorems/6b0eafb9-71da-4163-9a84-f44ec8a32237
-- title:
--   Algorithm 3: configurations at the beginning of a round
-- statement:
--   Algorithm 3 starts with $X=\emptyset$ (all prices $\bot$) and each round starts from the pair $(X,\pi)$ left by the previous round. A pair $(X,\pi)$ is a **round-start configuration** if it is $(\emptyset,\pi_0)$ or the end of a round started from a round-start configuration.
--
--   These are the pairs $(X^*,\pi^*)$ at the beginning of some round of some execution of Algorithm 3 (with a sufficiently large number $T$ of rounds), over which the invariants of §5.2 are stated.
--
--   **Formalization Note** An inductive predicate. The initial prices $\pi_0$ are arbitrary: they are read only on $X=\emptyset$, i.e. never.
-- source:
--   Huang, Kobayashi, Terao, Auction-Based Algorithms for Weighted Matroid Intersection with Near-Linear Query Complexity (manuscript, sha256 2e12cb4a…), Algorithm 3, Lines 1–3, p.22 (PDF p.24)

import Mathlib
import Definitions.Def_AuctionMatroidInt_Alg3Round

namespace AuctionMatroidInt

/-- **The configurations of Algorithm 3 at the beginning of a round.**
Huang, Kobayashi, Terao (manuscript, sha256 2e12cb4a…), Algorithm 3, p.22: Line 1 sets
`X ← ∅`, and each round (Lines 3–15) starts from the `(X, π)` left by the previous one.
`Alg3RoundStart … X π` says that `(X, π)` is the pair `(X, π)` at the beginning of some round of
some execution: either `X = ∅` (the start, with any `π`), or the end of a round started from such
a pair.

**Formalization Note.** At the start `π` is arbitrary: the paper has `π = ⊥` everywhere, and
since `π` is read only on `X = ∅` the choice is irrelevant. The number of rounds is not bounded
here: a pair reached after `k` rounds is a round-start of Algorithm 3 run with any `T > k`, so
"throughout the execution" of Algorithm 3 for some `T` means at one of these pairs. -/
inductive Alg3RoundStart {α : Type*} [Fintype α] [DecidableEq α] (ε : ℝ) (w : α → ℝ)
    (I₁ I₂ : Finset α → Prop) : Finset α → (α → ℝ) → Prop
  | init (π₀ : α → ℝ) : Alg3RoundStart ε w I₁ I₂ ∅ π₀
  | next (X : Finset α) (π : α → ℝ) (s' : Alg3State α) :
      Alg3RoundStart ε w I₁ I₂ X π → Alg3Round ε w I₁ I₂ X π s' →
      Alg3RoundStart ε w I₁ I₂ s'.X s'.π

end AuctionMatroidInt


