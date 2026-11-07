-- Prove2me | Definitions.Def_DoublingMST_IsMSTOf
-- name    : DoublingMST_IsMSTOf
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:30:43.904918+00:00
-- url     : https://prove2.me/theorems/d901e284-5693-46b5-8327-f5dfd572d565
-- title:
--   Minimum spanning tree of a graph $G$ on $X$
-- statement:
--   For a set $G$ of edges on $X$, $T$ is a **minimum spanning tree of $G$** if $T\subseteq G$ is a spanning tree of $X$ and $w(T)\le w(T')$ for every spanning tree $T'\subseteq G$. This is $\mathrm{MST}(G)$ of Algorithm 2, Line 16.
-- source:
--   Höckendorff, Hommelsheim, Sohler, Yue, Tight Bounds for (1+ϵ)-Approximation for Minimum Spanning Trees in Doubling Metrics, STOC 2027 submission (manuscript sha256 4855d6b39caaedcdac985f11ec23b5833ef4686c045f97ef13a21bdff2fbe759), Algorithm 2, Line 16, p.18 (PDF p.20)

import Mathlib
import Definitions.Def_CombOpt_SpanningTree_Graph_IsSpanningTree
import Definitions.Def_DoublingMST_completeGraph
import Definitions.Def_DoublingMST_treeWeight

namespace DoublingMST

/-- **A minimum spanning tree of a graph `G` on the points.**
Höckendorff–Hommelsheim–Sohler–Yue, *Tight Bounds for (1+ϵ)-Approximation for Minimum Spanning Trees in Doubling Metrics*, STOC 2027 submission (manuscript sha256 4855d6b3…be759), Algorithm 2, Line 16, p.18 (PDF p.20): "return MST(G)".

`IsMSTOf d G T`: `T` is a spanning tree of `X` all of whose edges lie in `G`, of least weight
among all such spanning trees.

**Formalization Note.** `G` is a set of unordered pairs of points (the edges added at Line 15),
weighted by `d`. A spanning tree of the subgraph `(X, G)` is a spanning tree of the complete graph
contained in `G`. -/
def IsMSTOf {n : ℕ} (d : Fin n → Fin n → ℝ) (G T : Finset (Sym2 (Fin n))) : Prop :=
  (completeGraph n).IsSpanningTree T ∧ T ⊆ G ∧
    ∀ T' : Finset (Sym2 (Fin n)), (completeGraph n).IsSpanningTree T' → T' ⊆ G →
      treeWeight d T ≤ treeWeight d T'

end DoublingMST


