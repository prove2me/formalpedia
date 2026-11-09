-- Prove2me | Definitions.Def_PivotADO_OneHop_WeightedGraph
-- name    : PivotADO_OneHop_WeightedGraph
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T11:11:56.731018+00:00
-- url     : https://prove2.me/theorems/f23b943f-3086-4e2f-8d3c-3eb75227389e
-- title:
--   Undirected weighted storage and three-step cost
-- statement:
--   Let $H$ be a simple undirected storage graph on a vertex set $V$, with symmetric edge weights in $[0,+\infty]$. Extend the weights by $\widehat w(a,a)=0$ and $\widehat w(a,b)=+\infty$ when $a\ne b$ is not an edge. For endpoints $u,v$ and proposed pivots $p_u,p_v$, define
--
--   $$W_H(u,v;p_u,p_v)=\widehat w(u,p_u)+\widehat w(p_u,p_v)+\widehat w(p_v,v).$$
--
--   Every step uses stored weights; all stored edges, including those used for pivot jumps, count in $|E_H|$. Values of the raw symmetric weight function away from edges are ignored. There is no requirement relating the edge sets of $H$ and $G$. Allowing infinite edge weights generalizes finite-weight storage without changing any finite-weight instance.
-- source:
--   Avi Kadria, Liam Roditty, STOC 2027 submission #584 (October 2026), Definition 2, (5.1), p.17; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/584.pdf

import Definitions.Def_PivotADO_OneHop_Geometry

set_option autoImplicit false
open scoped Classical ENNReal
noncomputable section

namespace PivotADO.OneHop

/-- Undirected weighted storage graph, §5.1 Definition 2, p.17.
Values away from edges are immaterial; `weight` supplies the printed conventions. -/
structure WeightedGraph (V : Type*) where
  graph : SimpleGraph V
  edgeWeight : V → V → ℝ≥0∞
  symmetric : ∀ u v, edgeWeight u v = edgeWeight v u

def WeightedGraph.weight {V : Type*} (H : WeightedGraph V) (u v : V) : ℝ≥0∞ :=
  if u = v then 0 else if H.graph.Adj u v then H.edgeWeight u v else ⊤

/-- Every summand in (5.1) uses stored weights, including both pivot jumps. -/
def walkWeight {V : Type*} (H : WeightedGraph V) (u v pu pv : V) : ℝ≥0∞ :=
  H.weight u pu + H.weight pu pv + H.weight pv v

end PivotADO.OneHop


