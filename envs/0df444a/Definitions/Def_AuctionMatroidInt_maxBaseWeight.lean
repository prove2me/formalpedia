-- Prove2me | Definitions.Def_AuctionMatroidInt_maxBaseWeight
-- name    : AuctionMatroidInt_maxBaseWeight
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T02:26:00.512195+00:00
-- url     : https://prove2.me/theorems/29a8d89e-0f29-42ae-ad78-4038ec732599
-- title:
--   Maximum weight of a base, $\max_{B\in\mathcal B} q(B)$
-- statement:
--   For a matroid $M=(E,\mathcal I)$ with base family $\mathcal B$ and a vector $q\in\mathbb R^E$, this is the value
--
--   $$
--   \max_{B\in\mathcal B} q(B),\qquad q(B)=\sum_{e\in B}q(e).
--   $$
--
--   It appears in Lemma 5.1 and in the upper bound $U(X,\pi)$ of the weight-splitting argument.
--
--   **Formalization Note** The maximum is a `Finset.sup'` over the finite family of bases. For a matroid on a finite ground set this family is nonempty; the definition returns $0$ when it is empty, which no statement uses (all assume `IsMatroid`).
-- source:
--   Huang, Kobayashi, Terao, Auction-Based Algorithms for Weighted Matroid Intersection with Near-Linear Query Complexity (manuscript, sha256 2e12cb4a…), Lemma 5.1, p.20 and §5.2.2, p.24 (PDF pp.22, 26)

import Mathlib
import Definitions.Def_CombOpt_MatroidPolytope_IsBasisOf
import Definitions.Def_CombOpt_MatroidPolytope_weight

namespace AuctionMatroidInt

open Classical in
/-- **Maximum weight of a base, `max_{B ∈ 𝓑} q(B)`.**
Huang, Kobayashi, Terao (manuscript, sha256 2e12cb4a…), Lemma 5.1, p.20 and the definition of
`U(X, π)`, p.24: for a matroid `M = (E, I)` with base family `𝓑` and `q ∈ ℝ^E`, the value
`max_{B ∈ 𝓑} q(B)`.

**Formalization Note.** The maximum is a `Finset.sup'` over the finite family of bases
(`CombOpt.MatroidPolytope.IsBasisOf I Finset.univ`) of the weights
`CombOpt.MatroidPolytope.weight q B`. That family is nonempty whenever `I` is a matroid on the
finite type `α` (`∅` is independent and can be extended to a maximal one); the `if` only guards
the definition when it is empty, where the value `0` is never used by any statement (every
statement assumes `IsMatroid I`). -/
noncomputable def maxBaseWeight {α : Type*} [Fintype α] (I : Finset α → Prop) (q : α → ℝ) : ℝ :=
  if h : ((Finset.univ : Finset (Finset α)).filter
      (CombOpt.MatroidPolytope.IsBasisOf I Finset.univ)).Nonempty then
    ((Finset.univ : Finset (Finset α)).filter
      (CombOpt.MatroidPolytope.IsBasisOf I Finset.univ)).sup' h
        (CombOpt.MatroidPolytope.weight q)
  else 0

end AuctionMatroidInt


