-- Prove2me | Definitions.Def_CombOpt_TJoin_Graph_IsShortestPath
-- name    : CombOpt_TJoin_Graph_IsShortestPath
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T22:05:38.083602+00:00
-- url     : https://prove2.me/theorems/39488f1d-c1ef-4007-98ed-7d7761e825ad
-- title:
--   Shortest $(u,v)$-path
-- statement:
--   Given costs $c\in\mathbb R^E$, a set $P\subseteq E$ is the edge set of a **shortest (least-cost) $(u,v)$-path** if it is the edge set of a simple $(u,v)$-path and
--
--   $$c(P)\le c(P')\quad\text{for the edge set } P' \text{ of every simple } (u,v)\text{-path}.$$
--
--   **Formalization Note** The comparison is with simple paths. For $c\ge0$, the case in which the book uses shortest paths in §5.4, every $(u,v)$-path contains the edges of a simple $(u,v)$-path, so this is least cost among all paths.
-- source:
--   Cook, Cunningham, Pulleyblank & Schrijver, Combinatorial Optimization (Wiley, 1998), §5.4, p. 169 (PDF p. 177)

import Mathlib
import Definitions.Def_CombOpt_TJoin_Graph
import Definitions.Def_CombOpt_TJoin_Graph_IsSimplePath

namespace CombOpt.TJoin

/-- **Shortest (least-cost) path.**
Cook, Cunningham, Pulleyblank & Schrijver, *Combinatorial Optimization* (Wiley, 1998), §5.4, p. 169 (PDF p. 177): "P is a minimum-cost (u, v)-path", "shortest paths joining the
nodes of T in pairs".

`G.IsShortestPath c u v P` holds when `P` is the edge set of a simple `(u, v)`-path whose cost
`c(P) = ∑_{e ∈ P} c e` is at most the cost of the edge set of every simple `(u, v)`-path.

**Formalization Note.** The comparison is with simple paths. For `c ≥ 0`, the only case in which
the book uses shortest paths here, every `(u, v)`-path contains the edges of a simple one, so the
least cost over all paths equals the least cost over simple paths. -/
def Graph.IsShortestPath {V E : Type*} [DecidableEq E] (G : Graph V E) (c : E → ℝ)
    (u v : V) (P : Finset E) : Prop :=
  G.IsSimplePath u v P ∧ ∀ P' : Finset E, G.IsSimplePath u v P' → ∑ e ∈ P, c e ≤ ∑ e ∈ P', c e

end CombOpt.TJoin


