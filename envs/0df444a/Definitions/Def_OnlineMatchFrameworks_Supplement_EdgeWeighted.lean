-- Prove2me | Definitions.Def_OnlineMatchFrameworks_Supplement_EdgeWeighted
-- name    : OnlineMatchFrameworks_Supplement_EdgeWeighted
-- status  : Definition
-- author  : @iris
-- created : 2026-11-27T00:17:39.746707+00:00
-- url     : https://prove2.me/theorems/7fbac2c1-58c5-4dff-9381-0ad886fd2992
-- title:
--   Instance with edge weights $w_{u,v}$; the match probability $p_{uv}(\pi)$
-- statement:
--   An **edge-weighted instance** consists of sets $U$ of offline items and $V$ of online vertices or vertex types, and
--
--   1. edge probabilities $p_{u,v}\in[0,1]$, with $p_{u,v}=0$ for a non-edge;
--   2. edge weights $w_{u,v}\ge0$;
--   3. a survival function $S_v(l)\in[0,1]$, the probability that a customer of type $v$ accepts another probe after the failed probes of the list $l$, with $S_v(l)\le S_v(l')$ whenever $l'$ is a sublist of $l$.
--
--   For a type $v$, fixing $v$ in $w_{u,v}$ gives a vertex-weighted instance, whose reach and match probabilities are those of a single customer of type $v$. For a policy $\pi$, an ordered list of items, the probability that such a customer is matched to $u$ when every item of $\pi$ is available is
--
--   $$
--   p_{uv}(\pi)=\sum_{i:\pi_i=u}S_v(\pi_1,\dots,\pi_{i-1})\prod_{i'<i}(1-p_{\pi_{i'},v})\,p_{u,v}.
--   $$
--
--   This is the model of the results of the paper with arbitrary edge weights.
--
--   **Formalization Note** The published vertex-weighted instance `OnlineMatchFrameworks.Instance` is obtained type by type, so its reach and match probabilities are reused.
-- source:
--   Brubach, Grammel, Ma & Srinivasan, Online Matching Frameworks under Stochastic Rewards, Product Ranking, and Unknown Patience, arXiv:1907.03963v6, §3, pp.10–11; §4.2, p.16

import Definitions.Def_OnlineMatchFrameworks_StarPolicy

open scoped BigOperators

namespace OnlineMatchFrameworks.Supplement

/-- **An instance with edge weights.** Brubach, Grammel, Ma & Srinivasan, *Online Matching Frameworks
under Stochastic Rewards, Product Ranking, and Unknown Patience*, arXiv:1907.03963v6, §3, pp.10–11,
and §4.2, p.16 ("arbitrary edge weights"). `U` is the set of offline items, `V` the set of online
vertices (or of their types), `p u v` the probability `p_{u,v}` of edge `(u,v)`, `w u v` its weight
`w_{u,v}` and `surv v l` the patience survival function, exactly as in `OnlineMatchFrameworks.Instance`.

**Formalization Note.** `OnlineMatchFrameworks.Instance` has vertex weights `w_u` only. Here the
weights may depend on the edge; everything else, including the sublist monotonicity of `surv`, is the
same. -/
structure EdgeInstance (U V : Type*) where
  /-- The edge probability `p_{u,v}`; a non-edge has `p u v = 0`. -/
  p : U → V → ℝ
  /-- The edge weight `w_{u,v}`. -/
  w : U → V → ℝ
  /-- The survival probability of a customer of type `v` after the failed probes of a list. -/
  surv : V → List U → ℝ
  p_nonneg : ∀ u v, 0 ≤ p u v
  p_le_one : ∀ u v, p u v ≤ 1
  w_nonneg : ∀ u v, 0 ≤ w u v
  surv_nonneg : ∀ v l, 0 ≤ surv v l
  surv_le_one : ∀ v l, surv v l ≤ 1
  surv_mono : ∀ v (l l' : List U), l'.Sublist l → surv v l ≤ surv v l'

namespace EdgeInstance

variable {U V : Type*}

/-- **The instance seen by a customer of type `v`.** arXiv:1907.03963v6, §3, p.11 (star graphs): the
vertex-weighted instance in which the weight of item `u` is `w_{u,v}`. At customer `v`, its `reach`,
`matchProb` and `starValue` are those of the edge-weighted instance. -/
def atType (G : EdgeInstance U V) (v : V) : OnlineMatchFrameworks.Instance U V where
  p := G.p
  w := fun u => G.w u v
  surv := G.surv
  p_nonneg := G.p_nonneg
  p_le_one := G.p_le_one
  w_nonneg := fun u => G.w_nonneg u v
  surv_nonneg := G.surv_nonneg
  surv_le_one := G.surv_le_one
  surv_mono := G.surv_mono

/-- **`p_{uv}(π)`.** arXiv:1907.03963v6, §4.2, p.16: "the probability that an online arrival of type v is
matched to offline vertex u when following policy π, assuming that all vertices of π are still
unmatched". It is `matchProb` summed over the positions of `u` in the list. -/
def policyMatchProb [DecidableEq U] (G : EdgeInstance U V) (v : V) (l : List U) (u : U) : ℝ :=
  ∑ i : Fin l.length, if l.get i = u then (G.atType v).matchProb v l i else 0

end EdgeInstance

end OnlineMatchFrameworks.Supplement


