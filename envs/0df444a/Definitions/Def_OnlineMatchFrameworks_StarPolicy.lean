-- Prove2me | Definitions.Def_OnlineMatchFrameworks_StarPolicy
-- name    : OnlineMatchFrameworks_StarPolicy
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T05:30:17.998205+00:00
-- url     : https://prove2.me/theorems/594a56b7-2402-4a98-a8e8-45a11696a95a
-- title:
--   List policies, reach, match probabilities, star value and star optimum $\mathrm{OPT}(U',v)$
-- statement:
--   A deterministic policy for a customer is a duplicate-free list $l=(l_0,\dots,l_{k-1})$ of items, offered in order until a match, the end of the list or the end of patience. For position $i$:
--   $$
--   \mathrm{reach}_v(l,i)=S_v(l_0,\dots,l_{i-1})\prod_{j<i}(1-p_{l_j,v}),\qquad \mathrm{mp}_v(l,i)=\mathrm{reach}_v(l,i)\,p_{l_i,v} .
--   $$
--   The expected reward and the expected number of probes of the list are
--   $$
--   \mathrm{star}_v(l)=\sum_i\mathrm{mp}_v(l,i)\,w_{l_i},\qquad \mathrm{probes}_v(l)=\sum_i\mathrm{reach}_v(l,i).
--   $$
--   The star optimum $\mathrm{OPT}(A,v)$ is the largest $\mathrm{star}_v(l)$ over the policies with all items in $A$. These quantities are the single-customer problem that the black box solves, and they enter LP (1) through (1d).
--
--   **Formalization Note** Lean takes the real supremum over a finite nonempty index type (it contains the empty list), so it is a maximum.
-- source:
--   Brubach, Grammel, Ma & Srinivasan, Online Matching Frameworks under Stochastic Rewards, Product Ranking, and Unknown Patience, arXiv:1907.03963v6, §4.2, p.16; LP (1), p.15; (22), p.46

import Definitions.Def_OnlineMatchFrameworks_Instance

open scoped BigOperators

namespace OnlineMatchFrameworks

variable {U V : Type*}

/-- **Deterministic star policies.** arXiv:1907.03963v6, §4.2, p.16: "A deterministic policy π … is
characterized by a permutation of some subset of U". The policy is a duplicate-free list of items,
offered in that order. -/
abbrev Policy (U : Type*) := {l : List U // l.Nodup}

namespace Instance

/-- **Probability of reaching position `i`.** arXiv:1907.03963v6, §4.2, p.16, and (22), p.46:
`reach_v(l,i) = S_v(l_0,…,l_{i-1}) · ∏_{j<i} (1 - p_{l_j,v})`, the probability that customer `v` is
still present and unmatched when the `i`-th item of `l` is offered.

**Formalization Note.** `surv` is unconditional in the patience, and is multiplied by the chance
that all earlier edges failed. No conditional hazards are multiplied in addition. -/
def reach (G : Instance U V) (v : V) (l : List U) (i : Fin l.length) : ℝ :=
  G.surv v (l.take i) * ((l.take i).map fun u => 1 - G.p u v).prod

/-- **Probability of matching at position `i`.** arXiv:1907.03963v6, §4.2, p.16 (`p_{uv}(π)`):
`mp_v(l,i) = reach_v(l,i) · p_{l_i,v}`. -/
def matchProb (G : Instance U V) (v : V) (l : List U) (i : Fin l.length) : ℝ :=
  G.reach v l i * G.p (l.get i) v

/-- **Expected reward of a list on a star.** arXiv:1907.03963v6, §4.2, p.16: the "immediate expected
reward" `∑_i mp_v(l,i) · w_{l_i}` of the policy `l` for customer `v`, assuming that all items of `l`
are available. -/
def starValue (G : Instance U V) (v : V) (l : List U) : ℝ :=
  ∑ i : Fin l.length, G.matchProb v l i * G.w (l.get i)

/-- **Expected number of probes of a list.** `∑_i reach_v(l,i)`. arXiv:1907.03963v6, proof of
Lemma 1, p.39, "we cannot probe more than θ_v edges". -/
def probes (G : Instance U V) (v : V) (l : List U) : ℝ :=
  ∑ i : Fin l.length, G.reach v l i

/-- **The star optimum `OPT(U′, v)`.** arXiv:1907.03963v6, p.15: "`OPT(U′, v)` denote[s] `OPT(G′)` for a
star graph `G′ = (U′, {v}, U′ × {v})`". It is the largest `starValue` over the policies with all
items in `A`.

**Formalization Note.** The index type is finite and contains the empty list, so the real supremum
is a genuine maximum. While a customer is present the only feedback is "failed, still here", so
lists are the deterministic star strategies (p.16). -/
noncomputable def starOpt (G : Instance U V) (A : Finset U) (v : V) : ℝ :=
  ⨆ l : {l : Policy U // ∀ u ∈ l.1, u ∈ A}, G.starValue v l.1.1

end Instance

end OnlineMatchFrameworks


