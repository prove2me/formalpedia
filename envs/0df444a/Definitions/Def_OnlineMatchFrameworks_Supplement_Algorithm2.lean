-- Prove2me | Definitions.Def_OnlineMatchFrameworks_Supplement_Algorithm2
-- name    : OnlineMatchFrameworks_Supplement_Algorithm2
-- status  : Definition
-- author  : @iris
-- created : 2026-11-27T00:19:21.887797+00:00
-- url     : https://prove2.me/theorems/bb55d867-634b-567e-8065-e49958b1c238
-- title:
--   Algorithm 2: policy rounding with skipped and simulated probes
-- statement:
--   Let $x$ be a solution of LP (2) and $w^*_u=\sum_vw_{uv}\sum_\pi p_{uv}(\pi)x_v(\pi)$. At each time $t$ a type $v$ is drawn with probability $q_{tv}$, and **Algorithm 2** draws a policy $\pi$ with probability $x_v(\pi)/q_v$ and walks it in order:
--
--   1. an item $u$ with $w_{uv}<w^*_u/2$ is skipped, without a probe and without use of patience;
--   2. otherwise, an unmatched item is probed, and a success earns $w_{uv}$, removes $u$ and ends the arrival;
--   3. otherwise the probe is **simulated**: a coin of probability $p_{uv}$ ends the arrival with no reward if it succeeds.
--
--   A failed simulated probe counts towards patience exactly as a failed real probe. Thus, if $l$ is the list of the items that are not skipped, position $i$ ends the arrival by a success with probability $\mathrm{mp}_v(l,i)$, whichever items are still available. The definition gives the expected reward
--
--   $$
--   \mathrm{ALG}(G)=\mathrm{alg}\bigl((1,\dots,T),U\bigr)
--   $$
--
--   by the backward recursion of total expectation over the remaining times and the available items.
--
--   **Formalization Note** If $q_v=0$ the quotient $x_v(\pi)/q_v$ only appears multiplied by $q_{tv}=0$.
-- source:
--   Brubach, Grammel, Ma & Srinivasan, Online Matching Frameworks under Stochastic Rewards, Product Ranking, and Unknown Patience, arXiv:1907.03963v6, §4.2.2, p.19; Algorithm 2, p.20

import Definitions.Def_OnlineMatchFrameworks_Supplement_PolicyLP

open scoped BigOperators

namespace OnlineMatchFrameworks.Supplement

namespace ProphetInstance

variable {U V : Type*} [Fintype U] [DecidableEq U] [Fintype V]

/-- **`w*_u`.** arXiv:1907.03963v6, §4.2.2, p.19: `w*_u = ∑_{v ∈ V} w_{uv} ∑_{π ∈ 𝒫} p_{uv}(π) x*_v(π)`. -/
def starWeight (G : ProphetInstance U V) (x : V → OnlineMatchFrameworks.Policy U → ℝ) (u : U) : ℝ :=
  ∑ v, G.w u v * ∑ l : OnlineMatchFrameworks.Policy U, G.policyMatchProb v l.1 u * x v l

/-- **One arrival with simulated probes.** arXiv:1907.03963v6, Algorithms 2 and 3, pp.20–21. The list `l`
of the items attempted for a customer of type `v` is walked when `A` is the set of unmatched items. At
position `i` an unmatched item is probed, and an item already matched is probed in simulation with the
same probability `p`. A success ends the arrival: it earns `w` and removes the item if the item was
unmatched, and earns nothing otherwise. A failure, real or simulated, counts as a failed probe for
patience. `f` is the value of the continuation. -/
def simulatedStep (G : ProphetInstance U V) (v : V) (l : List U) (f : Finset U → ℝ) (A : Finset U) : ℝ :=
  ∑ i : Fin l.length, (G.atType v).matchProb v l i *
      (if l.get i ∈ A then G.w (l.get i) v + f (A.erase (l.get i)) else f A) +
    (1 - ∑ i : Fin l.length, (G.atType v).matchProb v l i) * f A

/-- **Expected reward of policy rounding from a given state.** arXiv:1907.03963v6, Algorithms 2 and 3,
pp.20–21. At each remaining time `t` a type `v` is drawn with probability `q_{tv}` and a policy `π` with
probability `x_v(π)/q_v`; the items attempted are `keep v π`.

**Formalization Note.** If `q_v = 0` then `q_{tv} = 0` for all `t`, so the Lean value `x/0 = 0` is only
ever multiplied by `0`. -/
noncomputable def roundingFrom (G : ProphetInstance U V)
    (x : V → OnlineMatchFrameworks.Policy U → ℝ) (keep : V → List U → List U) :
    List (Fin G.horizon) → Finset U → ℝ
  | [], _ => 0
  | t :: ts, A =>
      ∑ v, G.q t v * ∑ l : OnlineMatchFrameworks.Policy U,
        x v l / G.expectedArrivals v * G.simulatedStep v (keep v l.1) (G.roundingFrom x keep ts) A

/-- **`ALG(G)` of Algorithm 2.** arXiv:1907.03963v6, Algorithm 2, p.20. An item `π_i` with
`w_{π_i,v} < w*_{π_i}/2` is skipped ("Skip to next i"): it is not probed and uses no patience. The other
items are probed, really or in simulation, in the order of `π`. -/
noncomputable def ALG2 (G : ProphetInstance U V) (x : V → OnlineMatchFrameworks.Policy U → ℝ) : ℝ :=
  G.roundingFrom x (fun v l => l.filter fun u => decide (G.starWeight x u / 2 ≤ G.w u v))
    (List.finRange G.horizon) Finset.univ

end ProphetInstance

end OnlineMatchFrameworks.Supplement


