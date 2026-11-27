-- Prove2me | Definitions.Def_OnlineMatchFrameworks_Supplement_SimpleGreedy
-- name    : OnlineMatchFrameworks_Supplement_SimpleGreedy
-- status  : Definition
-- author  : @iris
-- created : 2026-11-27T00:23:33.275209+00:00
-- url     : https://prove2.me/theorems/1e84f3c2-8cef-48e9-95f7-f2b6918515a9
-- title:
--   SimpleGreedy
-- statement:
--   A **SimpleGreedy rule** assigns to the set $A$ of unmatched items and an arriving vertex $v$ an item of $A$ adjacent to $v$ (one with $p_{u,v}>0$) whenever one exists, and nothing otherwise:
--
--   $$
--   c(A,v)\in\{u\in A:p_{u,v}>0\}\quad\text{if this set is nonempty}.
--   $$
--
--   SimpleGreedy probes the edge $(c(A,v),v)$ only. As a black box it is the deterministic one-item policy, so its expected reward on an arrival order is the published value $\mathrm{ALG}(G)$ of Algorithm 1 with this black box. The choice is arbitrary in the paper, so a statement about SimpleGreedy's worst case may pick the rule.
-- source:
--   Brubach, Grammel, Ma & Srinivasan, Online Matching Frameworks under Stochastic Rewards, Product Ranking, and Unknown Patience, arXiv:1907.03963v6, §6.2, p.31

import Definitions.Def_OnlineMatchFrameworks_BlackBox

namespace OnlineMatchFrameworks.Supplement

variable {U V : Type*}

/-- **A choice rule of SimpleGreedy.** arXiv:1907.03963v6, §6.2, p.31: an algorithm "which always attempts
to probe an edge incident to an online arriving vertex v ∈ V if one exists", and SimpleGreedy "chooses a
neighbor u ∈ U of v arbitrarily and probes the edge (u,v)". When `A` is the set of unmatched items,
`choose A v` is an item of `A` adjacent to `v` (`p > 0`) if there is one, and `none` otherwise. -/
def IsSimpleGreedyRule (G : OnlineMatchFrameworks.Instance U V)
    (choose : Finset U → V → Option U) : Prop :=
  ∀ A v, (∀ u, choose A v = some u → u ∈ A ∧ 0 < G.p u v) ∧
    (choose A v = none → ∀ u ∈ A, G.p u v = 0)

/-- **SimpleGreedy as a black box.** arXiv:1907.03963v6, §6.2, p.31: the deterministic policy that probes
the single chosen edge, or nothing. The expected reward of a run is the published `ALG` with this
black box. -/
noncomputable def greedyBox (choose : Finset U → V → Option U) :
    Finset U → V → PMF (OnlineMatchFrameworks.Policy U) :=
  fun A v => PMF.pure ⟨(choose A v).toList, by cases choose A v <;> simp⟩

end OnlineMatchFrameworks.Supplement


