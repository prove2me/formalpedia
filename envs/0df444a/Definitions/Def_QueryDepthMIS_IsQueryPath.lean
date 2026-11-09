-- Prove2me | Definitions.Def_QueryDepthMIS_IsQueryPath
-- name    : QueryDepthMIS_IsQueryPath
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T22:28:12.161886+00:00
-- url     : https://prove2.me/theorems/8fa86fca-0505-41e7-b932-dd0c41f23736
-- title:
--   Query path: increasing path with $p_{i-1} \le \operatorname{inhib}(p_i)$
-- statement:
--   Let $G$ be a graph with ranking $r$, $V^*$ the greedy maximal independent set obtained by scanning the vertices in increasing rank, and for a vertex $v$ let $\operatorname{inhib}(v)$ be $v$ itself if $v \in V^*$ and otherwise its lowest-ranked neighbour in $V^*$. A sequence of vertices $(v_1, \dots, v_L)$ is a **query path** if
--
--   1. it is an increasing path, and
--   2. $r(v_{i-1}) \le r(\operatorname{inhib}(v_i))$ for every $1 < i \le L$, i.e. $v_i$ is alive at time $r(v_{i-1})$.
--
--   Reversed, query paths are exactly the recursion paths explored by the recursive oracle (Algorithm 1) that decides membership in $V^*$.
--
--   **Formalization Note** $r(\operatorname{inhib}(v))$ is the published `RGMISFast.tau G r v` $= \min\{r(x) : x \in V^* \cap N[v]\}$, with $V^*$ given by `RGMISFast.inMIS`. The paper's positions $p_i$ are the ranks $r(v_i)$.
-- source:
--   Mitrović–Sheu, Tight Query Depth of Recursive Randomized Greedy MIS, STOC 2027 submission (manuscript sha256 805e76d8…), Definition 2.5, p.8

import Mathlib
import Definitions.Def_RGMISFast_tau
import Definitions.Def_QueryDepthMIS_IsIncreasingPath

set_option autoImplicit false

namespace QueryDepthMIS

/-- Query path (Mitrović–Sheu, *Tight Query Depth of Recursive Randomized Greedy MIS*, STOC 2027 submission (manuscript sha256 805e76d8…), Definition 2.5, p.8): "We say a sequence of positions p₁, …, p_L forms a
query path with respect to π if all of the following hold. • (p₁, p₂, …, p_L) forms an increasing
path, and • p_{i−1} ≤ inhib(p_i) holds for all i > 1."

A nonempty list `[v₁, …, v_L]` of vertices (the vertices `π(p₁), …, π(p_L)` in increasing rank)
that is an increasing path and in which `r(v_{i−1}) ≤ τ(v_i)` for every `i > 1`, where
`τ(v) = RGMISFast.tau G r v` is the rank of the inhibitor of `v` (Definition 2.1: `v` itself if
`v ∈ V*`, else its lowest-ranked neighbour in `V*`), computed from the greedy MIS of `G` under the
ranks `r`.

**Formalization Note** Positions are encoded by vertices (`p_i = r(v_i)`). `RGMISFast.tau G r v`
is `min{r(x) : x ∈ V* ∩ N[v]}` with `V*` the greedy MIS (`RGMISFast.inMIS`); for injective ranks
this is `rank(inhib(v))`. The condition says that `v_i` is alive at time `r(v_{i−1})`
(Definition 2.2). -/
def IsQueryPath {V : Type*} [Fintype V] [LinearOrder V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (r : V → ℕ) (l : List V) : Prop :=
  IsIncreasingPath G r l ∧ l.IsChain (fun a b => r a ≤ RGMISFast.tau G r b)

instance {V : Type*} [Fintype V] [LinearOrder V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (r : V → ℕ) (l : List V) : Decidable (IsQueryPath G r l) := by
  unfold IsQueryPath; infer_instance

end QueryDepthMIS


