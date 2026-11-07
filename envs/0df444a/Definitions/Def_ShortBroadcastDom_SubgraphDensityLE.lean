-- Prove2me | Definitions.Def_ShortBroadcastDom_SubgraphDensityLE
-- name    : ShortBroadcastDom_SubgraphDensityLE
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T07:25:25.571244+00:00
-- url     : https://prove2.me/theorems/5de93fb9-b3eb-41e2-be7f-b940371c2319
-- title:
--   Subgraph density at most $a$: $|E(H)|\le a|V(H)|$ for every subgraph $H$
-- statement:
--   The **density** of a graph is its ratio of edges to vertices, with density zero for the empty graph. A graph $G$ has **subgraph density at most $a$** if every subgraph $H\subseteq G$ satisfies
--
--   $$
--   |E(H)|\le a\,|V(H)|.
--   $$
--
--   This hypothesis appears in Lemma 4.1 (with an integer $p$), Lemma 6.10, Lemma 7.1, the non-integer case of §7.3 and clause (ii) of Theorem C. It is weaker than minor density: contracting edges can increase the density.
--
--   **Formalization Note** It suffices to bound, for every vertex set $S$, the number of edges of $G$ with both ends in $S$ by $a|S|$: any subgraph on the vertex set $S$ has no more edges than the induced one.
-- source:
--   Amiri, Siebertz, Wawrzyniak, Paying for Fractional Error: Tight Constant-Round Approximation of Covering Problems with Short Broadcasts (arXiv:2611.02057, sha256 f4dc98d2cf73d74a105e5b0e61c4b72d15ae82b3f202490e2e4ecf864b40646a), §4, p.15 (PDF p.18)

import Mathlib

namespace ShortBroadcastDom

/-- `SubgraphDensityLE a G`: every subgraph of `G` has at most `a` times as many edges as vertices.

Amiri, Siebertz, Wawrzyniak, *Paying for Fractional Error* (arXiv:2611.02057, sha256 prefix
f4dc98d2), §4, p.15 (PDF 18): "The density of a graph is its ratio of edges to vertices, with
density zero for the empty graph." Used as "every subgraph of H has a ratio of edges to vertices of
at most a" (Lemma 6.10, p.34), "every subgraph H of G satisfies |E(H)| ≤ p|V(H)|" (Lemma 4.1, p.15)
and "every subgraph of G has edge density at most a" (Lemma 7.1, p.44).

**Formalization Note** It is enough to bound induced subgraphs: for each vertex set `S`, the number
of edges of `G` with both ends in `S` is at most `a·|S|`. An arbitrary subgraph on `S` has no more
edges than the induced one, so this is the same condition. Edges are counted as `Set.ncard` of a
subset of `G.edgeSet` (no decidability instance needed). The empty set gives `0 ≤ 0`. -/
def SubgraphDensityLE {V : Type} (a : ℝ) (G : SimpleGraph V) : Prop :=
  ∀ S : Finset V, (({e | e ∈ G.edgeSet ∧ ∀ v ∈ e, v ∈ S} : Set (Sym2 V)).ncard : ℝ) ≤ a * S.card

end ShortBroadcastDom


