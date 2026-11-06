-- Prove2me | Definitions.Def_AuctionMatroidInt_IsMaxBase
-- name    : AuctionMatroidInt_IsMaxBase
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T02:25:40.017973+00:00
-- url     : https://prove2.me/theorems/380ba06e-2187-4ed4-8ac2-74c79a3450ec
-- title:
--   $p$-maximum and $p$-minimum bases
-- statement:
--   Let $M=(E,\mathcal I)$ be a matroid and $p\in\mathbb R^E$, with $p(X)=\sum_{e\in X}p(e)$. A **base** of $M$ is an inclusion-wise maximal independent set. A **$p$-maximum base** is a base $B$ with $p(B')\le p(B)$ for every base $B'$; a **$p$-minimum base** is a base $B$ with $p(B)\le p(B')$ for every base $B'$.
--
--   These are the objects of the gross substitutes property (Lemma 2.2) and of the line of Algorithm 3 asking whether $Y+e$ is contained in a $q^*$-maximum base of $M_1$. The optimization is over **bases**, not over all independent sets.
--
--   **Formalization Note** Bases are the published `CombOpt.MatroidPolytope.IsBasisOf I Finset.univ`, weights the published `CombOpt.MatroidPolytope.weight`. The module defines `IsMaxBase` and `IsMinBase`.
-- source:
--   Huang, Kobayashi, Terao, Auction-Based Algorithms for Weighted Matroid Intersection with Near-Linear Query Complexity (manuscript, sha256 2e12cb4a…), §2.1, p.10 (PDF p.12)

import Mathlib
import Definitions.Def_CombOpt_MatroidPolytope_IsBasisOf
import Definitions.Def_CombOpt_MatroidPolytope_weight

namespace AuctionMatroidInt

/-- **p-maximum base.**
Huang, Kobayashi, Terao (manuscript, sha256 2e12cb4a…), §2.1, p.10: "For a matroid M = (E, I)
and a vector p ∈ ℝ^E, a p-minimum base of M is a base B of M that minimizes p(B). We define a
p-minimum independent set and a p-maximum base/independent set in a similar way."

`IsMaxBase I c B`: `B` is a base of `M = (α, I)` (a maximal independent set) and
`c(B') ≤ c(B)` for every base `B'`.

**Formalization Note.** Bases are the published `CombOpt.MatroidPolytope.IsBasisOf I Finset.univ`
(maximal independent subsets of the ground set `α`) and `c(B) = Σ_{e ∈ B} c(e)` is the published
`CombOpt.MatroidPolytope.weight`. The maximum is over **bases**, not over independent sets. -/
def IsMaxBase {α : Type*} [Fintype α] (I : Finset α → Prop) (c : α → ℝ) (B : Finset α) : Prop :=
  CombOpt.MatroidPolytope.IsBasisOf I Finset.univ B ∧
    ∀ B' : Finset α, CombOpt.MatroidPolytope.IsBasisOf I Finset.univ B' →
      CombOpt.MatroidPolytope.weight c B' ≤ CombOpt.MatroidPolytope.weight c B

/-- **p-minimum base** (§2.1, p.10): `B` is a base of `M = (α, I)` and `p(B) ≤ p(B')` for every
base `B'`. -/
def IsMinBase {α : Type*} [Fintype α] (I : Finset α → Prop) (p : α → ℝ) (B : Finset α) : Prop :=
  CombOpt.MatroidPolytope.IsBasisOf I Finset.univ B ∧
    ∀ B' : Finset α, CombOpt.MatroidPolytope.IsBasisOf I Finset.univ B' →
      CombOpt.MatroidPolytope.weight p B ≤ CombOpt.MatroidPolytope.weight p B'

end AuctionMatroidInt


