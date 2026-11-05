-- Prove2me | Definitions.Def_OnlineMatchFrameworks_Instance
-- name    : OnlineMatchFrameworks_Instance
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T05:29:33.609246+00:00
-- url     : https://prove2.me/theorems/f7a0fd34-8d9a-4323-afed-34e0abb26124
-- title:
--   Online matching instance: probabilities $p_{u,v}$, vertex weights $w_u$, survival function $S_v$
-- statement:
--   An instance fixes finite sets $U$ of offline items and $V$ of online customers, and:
--
--   1. edge probabilities $p_{u,v}\in[0,1]$, where a non-edge has $p_{u,v}=0$;
--   2. vertex weights $w_u\ge 0$, the reward for matching $u$;
--   3. a survival function: for a customer $v$ and a list $l$ of items, $S_v(l)\in[0,1]$ is the probability that $v$ is still available for another probe once the items of $l$ have been probed and all those probes failed. It satisfies
--   $$
--   S_v(l)\le S_v(l')\quad\text{whenever } l' \text{ is a sublist of } l .
--   $$
--
--   Each of the patience models of the paper is one such survival function: deterministic patience, an arbitrary patience distribution, and item-dependent hazard rates. Every statement of the mission is written in this one model.
--
--   **Formalization Note** The monotonicity cannot be dropped: if a failed offer could raise survival, constraint (1d) of LP (1) would fail. $U$ and $V$ may be empty.
-- source:
--   Brubach, Grammel, Ma & Srinivasan, Online Matching Frameworks under Stochastic Rewards, Product Ranking, and Unknown Patience, arXiv:1907.03963v6, §3, pp.10–12; §4.1, p.14; §5.1, pp.22–23; §5.2, pp.23–25

import Mathlib

namespace OnlineMatchFrameworks

/-- **An instance of online matching with stochastic rewards and patience.** Brubach, Grammel, Ma &
Srinivasan, *Online Matching Frameworks under Stochastic Rewards, Product Ranking, and Unknown
Patience*, arXiv:1907.03963v6, §3, pp.10–12, vertex weights §4.1, p.14. `U` is the set of offline
items and `V` the set of online customers.

* `p u v` is the probability `p_{u,v}` that edge `(u,v)` exists when probed, independently of
  everything else; a non-edge has `p u v = 0` (p.11).
* `w u` is the vertex weight `w_u` of item `u`, the reward of matching it (p.11, p.14).
* `surv v l` is the probability that customer `v` is still available for another probe once the
  items of the list `l` have been probed and all those probes failed, computed in the patience
  model alone (the coins of the edges are not part of it).

**Formalization Note.** The paper treats patience as deterministic (p.11), as an arbitrary
distribution (§5.2) or as item hazard rates (§5.1), and applies §4 to each. The one survival
function covers all three (`tailSurvival`, `hazardSurvival`). The only assumption on it, besides
being a probability, is `surv_mono`: deleting items from what was probed cannot lower survival.
That assumption cannot be removed: without it a failed offer could "refresh" patience, which no
model of the paper does, and constraint (1d) of LP (1) fails. Weights are nonnegative (they are
prices and rewards, p.14). `U` and `V` are finite and may be empty. -/
structure Instance (U V : Type*) where
  /-- The edge probability `p_{u,v}`. -/
  p : U → V → ℝ
  /-- The vertex weight `w_u`. -/
  w : U → ℝ
  /-- The survival probability of customer `v` after the failed probes of a list. -/
  surv : V → List U → ℝ
  p_nonneg : ∀ u v, 0 ≤ p u v
  p_le_one : ∀ u v, p u v ≤ 1
  w_nonneg : ∀ u, 0 ≤ w u
  surv_nonneg : ∀ v l, 0 ≤ surv v l
  surv_le_one : ∀ v l, surv v l ≤ 1
  surv_mono : ∀ v (l l' : List U), l'.Sublist l → surv v l ≤ surv v l'

end OnlineMatchFrameworks


