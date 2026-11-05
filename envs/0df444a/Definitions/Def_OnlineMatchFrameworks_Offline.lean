-- Prove2me | Definitions.Def_OnlineMatchFrameworks_Offline
-- name    : OnlineMatchFrameworks_Offline
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T05:31:03.294528+00:00
-- url     : https://prove2.me/theorems/3fd2419f-d9b5-4043-807f-10c803e87efe
-- title:
--   Offline probing strategies, $\mathrm{OPT}(G)$ and probe frequencies
-- statement:
--   The offline benchmark. A **strategy** is a decision tree: it either stops, or picks an unserved customer $v$ and a list $l$ of available items, continues with a subtree $g(u)$ after a match on $u$ and with a subtree $h$ after no match. A customer is visited at most once, and the interaction with one customer ends before the next begins. Its value is
--   $$
--   \mathrm{value}(\mathrm{visit}\ v\,l\,g\,h)=\sum_i\mathrm{mp}_v(l,i)\bigl(w_{l_i}+\mathrm{value}(g(l_i))\bigr)+\Bigl(1-\sum_i\mathrm{mp}_v(l,i)\Bigr)\mathrm{value}(h),
--   $$
--   and $\mathrm{OPT}(G)$ is the supremum of the value over strategies valid from all items and all customers. The **probe frequency** $x^T_{u,v}$ is the probability that $T$ probes edge $(u,v)$, computed by the same recursion.
--
--   **Formalization Note** The tree may choose the next customer adaptively, which only raises the benchmark above that of a fixed order. The real supremum is over a nonempty family bounded by $\sum_u w_u$.
-- source:
--   Brubach, Grammel, Ma & Srinivasan, Online Matching Frameworks under Stochastic Rewards, Product Ranking, and Unknown Patience, arXiv:1907.03963v6, §3, p.12; Appendix A, proof of Lemma 1, p.39

import Definitions.Def_OnlineMatchFrameworks_StarPolicy

open scoped BigOperators

namespace OnlineMatchFrameworks

/-- **Sequential offline probing strategies.** arXiv:1907.03963v6, p.12, "the best sequential probing
algorithm on G that has access to this offline information", which "must finish the interactions
with one online vertex before moving to the next". A strategy either stops, or picks a customer
`v` and a list `l`, and continues with `onMatch u` after a match on `u` and with `onFail` when no
match occurs.

**Formalization Note.** The tree may choose the next customer adaptively. A fixed order is a special
case, so this only raises the benchmark. Randomized offline algorithms are mixtures of trees and do
not raise the supremum. Observing where patience ran out does not help either, since continuations
are independent of it. -/
inductive Strategy (U V : Type*) where
  | done : Strategy U V
  | visit (v : V) (l : List U) (onMatch : U → Strategy U V) (onFail : Strategy U V) : Strategy U V

variable {U V : Type*} [DecidableEq U] [DecidableEq V]

/-- **A strategy respects the model from the state `(A, R)`.** arXiv:1907.03963v6, §3, pp.11–12: `A` is
the set of available items and `R` the set of customers not yet served. Each visited customer is in
`R` and is then removed, so it is visited once (item iv on p.12); the list is a duplicate-free list
of available items ("each edge may be probed at most once", p.11); and a matched item is removed. -/
def Strategy.ValidFrom : Strategy U V → Finset U → Finset V → Prop
  | .done, _, _ => True
  | .visit v l g h, A, R =>
      v ∈ R ∧ l.Nodup ∧ (∀ u ∈ l, u ∈ A) ∧
        (∀ u ∈ l, (g u).ValidFrom (A.erase u) (R.erase v)) ∧ h.ValidFrom A (R.erase v)

namespace Instance

/-- **Expected reward of an offline strategy.** arXiv:1907.03963v6, p.12: the recursion of total
expectation over the tree. -/
def value (G : Instance U V) : Strategy U V → ℝ
  | .done => 0
  | .visit v l g h =>
      ∑ i : Fin l.length, G.matchProb v l i * (G.w (l.get i) + G.value (g (l.get i))) +
        (1 - ∑ i : Fin l.length, G.matchProb v l i) * G.value h

/-- **`OPT(G)`.** arXiv:1907.03963v6, p.12: the supremum of the expected reward over the offline
strategies valid from all items and all customers.

**Formalization Note.** The index type is nonempty and the values are bounded by `∑_u w_u`, so the
real supremum has its intended value; both facts are proved in the sanity file. -/
noncomputable def OPT [Fintype U] [Fintype V] (G : Instance U V) : ℝ :=
  ⨆ T : {T : Strategy U V // T.ValidFrom Finset.univ Finset.univ}, G.value T.1

/-- **Probe frequencies of a strategy.** arXiv:1907.03963v6, proof of Lemma 1, p.39: `probeFreq T u v`
is "the probability that this strategy probes edge (u, v)", computed by the same recursion as
`value`. -/
def probeFreq (G : Instance U V) : Strategy U V → U → V → ℝ
  | .done, _, _ => 0
  | .visit v' l g h, u, v =>
      (if v = v' then ∑ i : Fin l.length, if l.get i = u then G.reach v' l i else 0 else 0) +
        ∑ i : Fin l.length, G.matchProb v' l i * G.probeFreq (g (l.get i)) u v +
        (1 - ∑ i : Fin l.length, G.matchProb v' l i) * G.probeFreq h u v

end Instance

end OnlineMatchFrameworks


