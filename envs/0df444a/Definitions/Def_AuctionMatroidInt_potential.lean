-- Prove2me | Definitions.Def_AuctionMatroidInt_potential
-- name    : AuctionMatroidInt_potential
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T02:27:12.233605+00:00
-- url     : https://prove2.me/theorems/1f6b3a94-b78f-41c7-b611-953242490a4b
-- title:
--   The upper bound $U(X,\pi)$
-- statement:
--   For $X\subseteq E$ and prices $\pi$ on $X$, let $q$ be the utility vector induced by $X$ and $\pi$ and $\mathcal B_1$ the base family of $M_1$. Define
--
--   $$
--   U(X,\pi)=\pi(X)+\max_{B\in\mathcal B_1}q(B),\qquad \pi(X)=\sum_{e\in X}\pi(e).
--   $$
--
--   By Lemma 5.5 this quantity bounds $(1-\varepsilon)$ times the optimal weight throughout Algorithm 3, and Lemma 5.7 controls its change in one round; together they give the approximation guarantee.
--
--   **Formalization Note** $\pi(X)$ is the published `CombOpt.MatroidPolytope.weight π X`; the maximum is `maxBaseWeight`.
-- source:
--   Huang, Kobayashi, Terao, Auction-Based Algorithms for Weighted Matroid Intersection with Near-Linear Query Complexity (manuscript, sha256 2e12cb4a…), §5.2.2, p.24 (PDF p.26)

import Mathlib
import Definitions.Def_CombOpt_MatroidPolytope_weight
import Definitions.Def_AuctionMatroidInt_maxBaseWeight
import Definitions.Def_AuctionMatroidInt_utility

namespace AuctionMatroidInt

/-- **The upper bound `U(X, π)`.**
Huang, Kobayashi, Terao (manuscript, sha256 2e12cb4a…), §5.2.2, p.24: "For X and π, let
U(X, π) := π(X) + max_{B ∈ 𝓑₁} q(B), where q is the utility vector induced by X and π."

**Formalization Note.** `π(X) = Σ_{e ∈ X} π(e)` is `CombOpt.MatroidPolytope.weight π X`, which
reads `π` only on `X`; `max_{B ∈ 𝓑₁}` is `maxBaseWeight I₁`; `q` is `utility ε w I₂ X π`. -/
noncomputable def potential {α : Type*} [Fintype α] [DecidableEq α] (ε : ℝ) (w : α → ℝ)
    (I₁ I₂ : Finset α → Prop) (X : Finset α) (π : α → ℝ) : ℝ :=
  CombOpt.MatroidPolytope.weight π X + maxBaseWeight I₁ (utility ε w I₂ X π)

end AuctionMatroidInt


