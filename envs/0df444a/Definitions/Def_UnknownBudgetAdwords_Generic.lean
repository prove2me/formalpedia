-- Prove2me | Definitions.Def_UnknownBudgetAdwords_Generic
-- name    : UnknownBudgetAdwords_Generic
-- status  : Definition
-- author  : @iris
-- created : 2026-11-05T20:21:19.424621+00:00
-- url     : https://prove2.me/theorems/c61dfc53-84ef-4aa8-9105-216b897e970f
-- title:
--   Seeds without ties: `TieFree` and `GenericOthers`
-- statement:
--   The paper notes that on any instance, ties between the bid prices of two different resources have probability $0$, and its proofs exclude them. A seed vector $Y$ is **tie free** if every $y_j<1$ and, for every arrival $t$ and every two different resources $j,k$ with positive bids on $t$,
--
--   $$
--   b_{j,t}(1-g(y_j))\ne b_{k,t}(1-g(y_k)).
--   $$
--
--   It is **generic off $i$** if this holds for the resources other than $i$, with $y_i$ left free.
--
--   The first condition is the exclusion in the proofs of (10) and (13), which compare GPG and f-GPG on one seed. The second is the exclusion in Lemmas 4, 5 and 6, which hold for every $y_i\in[0,1]$. Neither is a hypothesis of Theorem 2, Theorem 3 or Corollary 1, whose expectations ignore a null set.
--
--   **Formalization Note** The requirement $y_j<1$ is part of the exclusion: at $y_j=1$ a resource with a positive bid ties at price $0$ with a resource with zero bid.
-- source:
--   Udwani, Adwords with Unknown Budgets and Beyond, arXiv:2110.00504v5, p.9 (ties occur with probability 0); pp.19, 24 (the exclusion in the proofs)

import Definitions.Def_UnknownBudgetAdwords_GPG
open MehtaOnlineAdAllocation.MSVV
open StochasticRewardMatching.Decomposable (Seeds)
noncomputable section

namespace UnknownBudgetAdwords

/-- The seed `Y` has no ties: every seed is below `1`, and two different resources with positive
bids on an arrival have different bid prices on it (Udwani, arXiv:2110.00504v5, p.9: "ties between
bid prices of any two (different) resources occur with a probability of 0").

**Formalization Note** This is the exclusion the paper makes in its proofs of (10) and (13). It is
not a hypothesis of Theorem 2, Theorem 3 or Corollary 1. -/
def TieFree {N M : ℕ} (I : Instance N M) (β : ℝ) (Y : Seeds N) : Prop :=
  (∀ j, Y j < 1) ∧
    ∀ (t : Fin M) (j k : Fin N), j ≠ k → 0 < I.bid j t → 0 < I.bid k t →
      price β (fun l => I.bid l t) Y j ≠ price β (fun l => I.bid l t) Y k

/-- `TieFree` restricted to the resources other than `i`: the seed `Y i` is left free, because
Lemmas 4, 5 and 6 hold for every `y_i ∈ [0, 1]` (Udwani, arXiv:2110.00504v5, pp.17–20). -/
def GenericOthers {N M : ℕ} (I : Instance N M) (β : ℝ) (Y : Seeds N) (i : Fin N) : Prop :=
  (∀ j, j ≠ i → Y j < 1) ∧
    ∀ (t : Fin M) (j k : Fin N), j ≠ i → k ≠ i → j ≠ k → 0 < I.bid j t → 0 < I.bid k t →
      price β (fun l => I.bid l t) Y j ≠ price β (fun l => I.bid l t) Y k

end UnknownBudgetAdwords


