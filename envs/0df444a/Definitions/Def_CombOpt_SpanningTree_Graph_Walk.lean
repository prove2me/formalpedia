-- Prove2me | Definitions.Def_CombOpt_SpanningTree_Graph_Walk
-- name    : CombOpt_SpanningTree_Graph_Walk
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T22:01:01.244974+00:00
-- url     : https://prove2.me/theorems/e9c53cf0-5658-45e6-8992-97df55518898
-- title:
--   Path in a graph (nodes and edges may repeat)
-- statement:
--   A **path** from $v_0$ to $v_k$ in a graph $G$ is a sequence
--   $$v_0, e_1, v_1, e_2, \dots, e_k, v_k$$
--   of nodes $v_i$ and edges $e_i$ such that, for $1\le i\le k$, the ends of $e_i$ are $v_{i-1}$ and $v_i$. Nodes and edges may repeat; $k\ge 0$, and $k=0$ gives the one-node path $v_0$. A loop at $v$ is a step from $v$ to $v$.
--
--   Paths are the basic object behind connectivity, circuits and forests in this mission.
--
--   **Formalization Note** The type `G.Walk u v` is built inductively: `nil v` is the one-node path, and `cons e h p` prepends a node $u$ and an edge $e$ with ends $u, v$ to a path $p$ from $v$. The Lean name follows Mathlib's `Walk`; the book's word is "path". A path in a subgraph $(V,F)$ is a path of $G$ all of whose edges lie in $F$.
-- source:
--   Cook, Cunningham, Pulleyblank & Schrijver, Combinatorial Optimization (Wiley, 1998), §2.1, p. 10 (PDF p. 19)

import Mathlib
import Definitions.Def_CombOpt_SpanningTree_Graph

namespace CombOpt.SpanningTree

/-- **A path of a graph (in the book's sense: nodes and edges may repeat).**
Cook, Cunningham, Pulleyblank & Schrijver, *Combinatorial Optimization* (Wiley, 1998), §2.1, p. 10 (PDF p. 19): "A path P in a graph G is a sequence v_0, e_1, v_1, …, e_k, v_k
where each v_i is a node, each e_i is an edge, and for 1 ≤ i ≤ k, the ends of e_i are v_{i−1}
and v_i. We say that P is from v_0 to v_k, or that it is a (v_0, v_k)-path."

`G.Walk u v` is such a sequence from `u` to `v`: `nil v` is the one-node path `v` (k = 0), and
`cons e h p` prepends the node `u` and the edge `e` with ends `u, v` (`h : G.ends e = s(u, v)`) to
a path `p` from `v` to `w`.

**Formalization Note.** The name `Walk` follows Mathlib; the book's word is "path", and its
"simple path" (distinct nodes) is `p.support.Nodup`. A loop at `u` (`G.ends e = s(u, u)`) is a
legal step from `u` to `u`. A path *in a subgraph* `(V, F)` is a path of `G` all of whose edges
lie in `F` (a subgraph keeps the ends of its edges, p. 10). -/
inductive Graph.Walk {V E : Type*} (G : Graph V E) : V → V → Type _
  | nil (v : V) : G.Walk v v
  | cons {u v w : V} (e : E) (h : G.ends e = s(u, v)) (p : G.Walk v w) : G.Walk u w

end CombOpt.SpanningTree


