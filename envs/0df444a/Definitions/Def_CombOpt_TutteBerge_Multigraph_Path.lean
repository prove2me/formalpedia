-- Prove2me | Definitions.Def_CombOpt_TutteBerge_Multigraph_Path
-- name    : CombOpt_TutteBerge_Multigraph_Path
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T22:04:05.750782+00:00
-- url     : https://prove2.me/theorems/7b6f3f96-18cd-453f-a5c7-c2e4759ac3e5
-- title:
--   Path
-- statement:
--   A **path** of $G$ from $v_0$ to $v_k$ is a sequence $v_0,e_1,v_1,\dots,e_k,v_k$ in which each $v_i$ is a node, each $e_i$ is an edge, and the ends of $e_i$ are $v_{i-1}$ and $v_i$ for $1\le i\le k$. The case $k=0$ is allowed.
--
--   **Formalization Note** As in the book, a path may repeat nodes and edges.
-- source:
--   Cook, Cunningham, Pulleyblank & Schrijver, Combinatorial Optimization (Wiley, 1998), §2.1, p. 10 (PDF p. 19)

import Mathlib
import Definitions.Def_CombOpt_TutteBerge_Multigraph

universe u v

namespace CombOpt.TutteBerge

/-- **A path, from `u` to `w`.**
Cook, Cunningham, Pulleyblank & Schrijver, *Combinatorial Optimization* (Wiley, 1998), §2.1, p. 10 (PDF p. 19): "A *path* P in a graph G is a sequence v₀, e₁, v₁, …, e_k, v_k where
each vᵢ is a node, each eᵢ is an edge, and for 1 ≤ i ≤ k, the ends of eᵢ are vᵢ₋₁ and vᵢ. We say
that P is *from* v₀ *to* v_k, or that it is a (v₀, v_k)-path."

`nil v` is the path with `k = 0`, and `cons e he p` prepends the node `u` and the edge `e` to `p`.

**Formalization Note.** As in the book, a path may repeat nodes and edges; `Path.IsSimple` and
`Path.IsCircuit` impose the restrictions. -/
inductive Multigraph.Path {V : Type u} {E : Type v} (G : Multigraph V E) : V → V → Type (max u v)
  | nil (v : V) : Multigraph.Path G v v
  | cons {u v w : V} (e : E) (he : G.ends e = s(u, v)) (p : Multigraph.Path G v w) :
      Multigraph.Path G u w

end CombOpt.TutteBerge


