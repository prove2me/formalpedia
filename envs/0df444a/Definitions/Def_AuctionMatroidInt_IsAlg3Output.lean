-- Prove2me | Definitions.Def_AuctionMatroidInt_IsAlg3Output
-- name    : AuctionMatroidInt_IsAlg3Output
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T02:29:07.324208+00:00
-- url     : https://prove2.me/theorems/c09cc35e-0894-4e58-acf0-c473ebe49296
-- title:
--   Algorithm 3: runs with $T$ rounds and their outputs
-- statement:
--   A **run** of Algorithm 3 with $T$ rounds is a sequence $X_0=\emptyset, X_1,\dots,X_T$, with prices $\pi_0,\dots,\pi_T$, such that round $t+1$ started from $(X_t,\pi_t)$ ends with $(X_{t+1},\pi_{t+1})$ for every $t<T$. The algorithm **returns** a set $X_t$ maximizing $w(X_t)$ over $t\in\{0,1,\dots,T\}$ (Line 16).
--
--   `IsAlg3Output ε w I₁ I₂ T X` says that $X$ is a set returned by some run with $T$ rounds.
--
--   **Formalization Note** Every scan order, every tie-break of Line 12 and every maximizer in Line 16 is allowed, so statements about the output hold for all of them.
-- source:
--   Huang, Kobayashi, Terao, Auction-Based Algorithms for Weighted Matroid Intersection with Near-Linear Query Complexity (manuscript, sha256 2e12cb4a…), Algorithm 3, Lines 2, 15, 16, p.22, and §5.1.2, p.21 (PDF pp.23–24)

import Mathlib
import Definitions.Def_CombOpt_MatroidPolytope_weight
import Definitions.Def_AuctionMatroidInt_Alg3Round

namespace AuctionMatroidInt

/-- **A run of Algorithm 3 with `T` rounds** (p.22): `Xt t` is the set `X_t` at the end of round
`t` (`X_0 = ∅`, p.21), and there are prices `πt t` such that, for every `t < T`, round `t + 1`
started from `(X_t, π_t)` ends with `(X_{t+1}, π_{t+1})`.
Huang, Kobayashi, Terao (manuscript, sha256 2e12cb4a…), Algorithm 3 and §5.1.2, pp.21–22.

**Formalization Note.** Every scan order and every tie-break of Line 12 is allowed, since
`Alg3Round` quantifies over both. The initial prices `πt 0` are arbitrary (read only on
`X_0 = ∅`). Values `Xt t` for `t > T` are irrelevant. -/
def IsAlg3Run {α : Type*} [Fintype α] [DecidableEq α] (ε : ℝ) (w : α → ℝ)
    (I₁ I₂ : Finset α → Prop) (T : ℕ) (Xt : ℕ → Finset α) : Prop :=
  ∃ πt : ℕ → α → ℝ, Xt 0 = ∅ ∧
    ∀ t < T, ∃ s' : Alg3State α, Alg3Round ε w I₁ I₂ (Xt t) (πt t) s' ∧
      s'.X = Xt (t + 1) ∧ s'.π = πt (t + 1)

/-- **An output of Algorithm 3 with `T` rounds** (Line 16, p.22): "return `X_t` maximizing
`w(X_t)` over `t ∈ {0, 1, …, T}`". `IsAlg3Output … T X` says that `X` is such a returned set for
some run.

**Formalization Note.** Any maximizer may be returned (ties are not broken), and the run is any
run (`IsAlg3Run`); statements about the output therefore hold for every order, tie-break and
maximizer. -/
def IsAlg3Output {α : Type*} [Fintype α] [DecidableEq α] (ε : ℝ) (w : α → ℝ)
    (I₁ I₂ : Finset α → Prop) (T : ℕ) (X : Finset α) : Prop :=
  ∃ Xt : ℕ → Finset α, IsAlg3Run ε w I₁ I₂ T Xt ∧
    ∃ t ≤ T, X = Xt t ∧
      ∀ t' ≤ T, CombOpt.MatroidPolytope.weight w (Xt t') ≤ CombOpt.MatroidPolytope.weight w (Xt t)

end AuctionMatroidInt


