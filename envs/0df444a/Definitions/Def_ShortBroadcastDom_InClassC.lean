-- Prove2me | Definitions.Def_ShortBroadcastDom_InClassC
-- name    : ShortBroadcastDom_InClassC
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T07:25:44.777759+00:00
-- url     : https://prove2.me/theorems/6e149c3c-d88e-4603-acaa-7d4c31e2351e
-- title:
--   The class $\mathcal C_a$: every minor $J$ satisfies $|E(J)|\le a|V(J)|$
-- statement:
--   A **minor** of a graph is obtained by deleting vertices and edges and contracting disjoint connected sets, after which loops are removed and one edge is kept from each group of parallel edges. For a rational $a\ge 1$, the class $\mathcal C_a$ consists of the graphs $G$ such that every nonempty minor $J$ of $G$ satisfies
--
--   $$
--   |E(J)|\le a\,|V(J)|.
--   $$
--
--   The class is closed under subgraphs and minors. Planar graphs lie in $\mathcal C_3$, and by Mader's theorem every class excluding a fixed minor lies in some $\mathcal C_a$. The mission's guarantees for the fractional solver and the integer case of the rounding are stated over $\mathcal C_a$.
--
--   **Formalization Note** Minors are the published branch-set definition `RobertsonSeymour1986.GM5.IsMinor`: nonempty, connected, pairwise disjoint branch sets with a host edge between the branch sets of every edge of $J$; $J$ ranges over all finite vertex types. The empty minor satisfies the bound trivially. The parameter is a real number; statements in which the paper's $a$ is rational take $a\in\mathbb Q$ and cast it.
-- source:
--   Amiri, Siebertz, Wawrzyniak, Paying for Fractional Error: Tight Constant-Round Approximation of Covering Problems with Short Broadcasts (arXiv:2611.02057, sha256 f4dc98d2cf73d74a105e5b0e61c4b72d15ae82b3f202490e2e4ecf864b40646a), §1.1, p.2 (PDF p.5); §4, p.15 (PDF p.18)

import Mathlib
import Definitions.Def_RobertsonSeymour1986_GM5_IsMinor

namespace ShortBroadcastDom

/-- **The class `C_a`** of graphs of minor density at most `a`: `G ∈ C_a` when every (nonempty)
minor `J` of `G` satisfies `|E(J)| ≤ a·|V(J)|`.

Amiri, Siebertz, Wawrzyniak, *Paying for Fractional Error* (arXiv:2611.02057, sha256 prefix
f4dc98d2), §1.1, p.2 (PDF 5) and §4, p.15 (PDF 18): "For fixed rational a ≥ 1, the class Ca
consists of graphs for which every nonempty minor J satisfies |E(J)| ≤ a|V(J)|." "A minor of a
graph is obtained by deleting vertices and edges and contracting disjoint connected sets, after
which loops are removed and just one edge is retained from each group of parallel edges."

**Formalization Note** Minors are the published branch-set definition
`RobertsonSeymour1986.GM5.IsMinor` (nonempty, connected, pairwise disjoint branch sets, and an edge
of `G` between the branch sets of every edge of `J`), which describes exactly the simple graphs
obtained by deletions and contractions, up to isomorphism; `J` ranges over all finite vertex types
`W`. The empty minor gives `0 ≤ 0`, so "nonempty" needs no separate clause. The parameter is real;
the paper's `a` is rational and every statement of the mission that says so takes `a : ℚ` and casts
it. -/
def InClassC {V : Type} (a : ℝ) (G : SimpleGraph V) : Prop :=
  ∀ (W : Type) [Fintype W] (J : SimpleGraph W),
    RobertsonSeymour1986.GM5.IsMinor J G → (J.edgeSet.ncard : ℝ) ≤ a * Fintype.card W

end ShortBroadcastDom


