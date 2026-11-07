-- Prove2me | Definitions.Def_HeilmanMax3Cut_IsSimple
-- name    : HeilmanMax3Cut_IsSimple
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T12:27:10.431138+00:00
-- url     : https://prove2.me/theorems/dd0c2544-92df-475b-ad9c-8babf541a5b6
-- title:
--   Simple (unweighted) graph
-- statement:
--   Let $G$ be a weighted MAX-CUT instance: a loopless graph on the vertex set $\{0,\dots,n-1\}$ given by a list of edges, in which an edge listed $m$ times has weight $m$. The instance is **simple** when every unordered pair of vertices appears at most once in the list: no entry is repeated, and the list never contains both $(u,v)$ and $(v,u)$.
--
--   A simple instance is an ordinary finite undirected graph, every edge having weight $1$. This is the input of the (unweighted) MAX-3-CUT problem of the paper.
-- source:
--   Heilman, Sharp Hardness for MAX-3-CUT and Quantum MAX-CUT, arXiv:2608.00333 (held version, sha256 2b4f1d11…), §1.1, p.3 (MAX-3-CUT on a finite undirected graph) and p.1 (weighted vs unweighted versions)

import Mathlib
import Definitions.Def_OptInapprox_MaxCut_UGC
open OptInapprox.MaxCut

namespace HeilmanMax3Cut

/-- **Simple (unweighted) graph.** Heilman, *Sharp Hardness for MAX-3-CUT and Quantum MAX-CUT*, arXiv:2608.00333 (held version,
sha256 2b4f1d11…), §1.1, p.3: "The MAX-3-CUT problem asks for the partition of the
vertices of a finite undirected graph into three sets that maximizes the number of edges going
between the three sets", and p.1 ("the weighted and unweighted versions").

A weighted MAX-CUT instance `G` (the published `OptInapprox.MaxCut.WMaxCut`: vertices `Fin G.n`, a
loopless list of edges, an edge listed `m` times having weight `m`) is *simple* when every
unordered pair of vertices is listed at most once: the list has no repeated entry and never lists
both `(u, v)` and `(v, u)`. Then every edge has weight `1` and `G` is an ordinary finite undirected
graph.

**Formalization Note.** Loops are already excluded by `WMaxCut.loopless`. -/
def IsSimple (G : WMaxCut) : Prop :=
  G.edges.Nodup ∧ ∀ e ∈ G.edges, (e.2, e.1) ∉ G.edges

end HeilmanMax3Cut


