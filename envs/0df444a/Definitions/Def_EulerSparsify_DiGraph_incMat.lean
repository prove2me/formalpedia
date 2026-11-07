-- Prove2me | Definitions.Def_EulerSparsify_DiGraph_incMat
-- name    : EulerSparsify_DiGraph_incMat
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T12:32:15.883208+00:00
-- url     : https://prove2.me/theorems/1fc436c3-b232-489d-8220-1bb1a77fc746
-- title:
--   Incidence matrix $B=H-T$
-- statement:
--   For a graph with edges $E$ and vertices $V$, let $H,T\in\{0,1\}^{E\times V}$ indicate the heads and the tails of the edges: $H_{ev}=1$ iff $h(e)=v$ and $T_{ev}=1$ iff $t(e)=v$. The **edge–vertex incidence matrix** is
--
--   $$B = H - T \in \{-1,0,1\}^{E\times V},$$
--
--   so that for an edge $e=(u,v)$ the row $B_{e:}$ has $B_{eu}=1$ and $B_{ev}=-1$. A vector $x\in\mathbb R^E$ is a **circulation** if $B^\top x=0$.
--
--   **Formalization Note** For an undirected graph the paper fixes an arbitrary consistent orientation; here it is the head/tail of each edge. A self-loop has a zero row of $B$.
-- source:
--   Peng, Sachdeva, Zhang, Zhao, Nested Effective Resistance Partitions and Eulerian Sparsification, STOC 2027 submission (manuscript sha256 0cdf0d3973c1d2c682db79c667cac6e49bab79e8912a5fc379a98fe0aece077d), §3, Graph matrices, p.9 (PDF p.11)

import Mathlib
import Definitions.Def_EulerSparsify_DiGraph

namespace EulerSparsify

/-- The head-indicator matrix `H ∈ {0,1}^{E×V}`: `H e v = 1` iff `h(e) = v`. -/
def DiGraph.Hmat {V E : Type} [DecidableEq V] (G : DiGraph V E) : Matrix E V ℝ :=
  Matrix.of fun e v => if G.head e = v then 1 else 0

/-- The tail-indicator matrix `T ∈ {0,1}^{E×V}`: `T e v = 1` iff `t(e) = v`. -/
def DiGraph.Tmat {V E : Type} [DecidableEq V] (G : DiGraph V E) : Matrix E V ℝ :=
  Matrix.of fun e v => if G.tail e = v then 1 else 0

/-- **Edge-vertex incidence matrix** `B = H − T` (§3, "Graph matrices", p.9, PDF p.11).
Peng, Sachdeva, Zhang, Zhao, *Nested Effective Resistance Partitions and Eulerian
Sparsification*, STOC 2027 submission (manuscript sha256 0cdf0d39…), §3, p.9: "we let
B ∈ {−1, 0, 1}^{E×V} be its edge-vertex incidence (or transfer) matrix, so that when ⃗G is directed and
e = (u, v), B_{e:} is 2-sparse with B_{eu} = 1, B_{ev} = −1 … We let H, T ∈ {0, 1}^{E×V} indicate the
heads and tails of each edge … and B = H − T."

**Formalization Note.** For an undirected graph the paper fixes "an arbitrary consistent
orientation"; here that orientation is the `head`/`tail` of the edge. A self-loop has a zero row of
`B`. -/
def DiGraph.incMat {V E : Type} [DecidableEq V] (G : DiGraph V E) : Matrix E V ℝ :=
  G.Hmat - G.Tmat

end EulerSparsify


