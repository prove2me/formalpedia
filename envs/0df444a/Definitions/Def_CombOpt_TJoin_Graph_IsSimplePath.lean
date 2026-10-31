-- Prove2me | Definitions.Def_CombOpt_TJoin_Graph_IsSimplePath
-- name    : CombOpt_TJoin_Graph_IsSimplePath
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T22:04:32.985981+00:00
-- url     : https://prove2.me/theorems/0cfcaa14-859a-48fd-a913-2076cd0eaf9e
-- title:
--   Edge set of a simple $(u,v)$-path
-- statement:
--   A **path** in $G$ is a sequence $v_0,e_1,v_1,\dots,e_k,v_k$ of nodes $v_i$ and edges $e_i$ such that the ends of $e_i$ are $v_{i-1}$ and $v_i$; it is a $(v_0,v_k)$-path, and it is **simple** if $v_0,\dots,v_k$ are distinct. A set $P\subseteq E$ is the **edge set of a simple $(u,v)$-path** if $P=\{e_1,\dots,e_k\}$ for some simple path from $u$ to $v$.
--
--   **Formalization Note** The path is witnessed by a duplicate-free list of nodes from $u$ to $v$ and a list of edges, the $i$-th edge having as ends the $i$-th consecutive pair of nodes.
-- source:
--   Cook, Cunningham, Pulleyblank & Schrijver, Combinatorial Optimization (Wiley, 1998), §2.1, p. 10 (PDF p. 19)

import Mathlib
import Definitions.Def_CombOpt_TJoin_Graph

namespace CombOpt.TJoin

/-- **Edge set of a simple path.**
Cook, Cunningham, Pulleyblank & Schrijver, *Combinatorial Optimization* (Wiley, 1998), §2.1, p. 10 (PDF p. 19): "A path P in a graph G is a sequence v₀, e₁, v₁, …, e_k, v_k
where each vᵢ is a node, each eᵢ is an edge, and for 1 ≤ i ≤ k, the ends of eᵢ are vᵢ₋₁ and vᵢ.
We say that P is from v₀ to v_k, or that it is a (v₀, v_k)-path. … it is simple if v₀, …, v_k
are distinct." `E(P)` denotes its edge set (p. 169).

`G.IsSimplePath u v P` holds when `P` is the edge set `{e₁, …, e_k}` of a simple
`(u, v)`-path: there are distinct nodes `vs = [v₀, …, v_k]` with `v₀ = u`, `v_k = v`, and edges
`es = [e₁, …, e_k]` with `ends eᵢ = {vᵢ₋₁, vᵢ}`.

**Formalization Note.** `List.Forall₂` pairs `eᵢ` with the consecutive pair `(vᵢ₋₁, vᵢ)` and
forces `k + 1` nodes for `k` edges. The edges of a simple path are distinct automatically, and
a simple path uses no loop. -/
def Graph.IsSimplePath {V E : Type*} [DecidableEq E] (G : Graph V E) (u v : V)
    (P : Finset E) : Prop :=
  ∃ (vs : List V) (es : List E), vs.Nodup ∧ vs.head? = some u ∧ vs.getLast? = some v ∧
    List.Forall₂ (fun (e : E) (p : V × V) => G.ends e = s(p.1, p.2)) es (vs.zip vs.tail) ∧
    P = es.toFinset

end CombOpt.TJoin


