-- Prove2me | Definitions.Def_QueryDepthMIS_aliveSet
-- name    : QueryDepthMIS_aliveSet
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T22:26:22.917408+00:00
-- url     : https://prove2.me/theorems/2082d0ca-f44c-4146-b9dd-138ed4d3d861
-- title:
--   Vertex set of the alive graph $G_{\mathrm{alive}}(l, r)$
-- statement:
--   A vertex $v$ is **alive at time** $t$ if $\operatorname{rank}(\operatorname{inhib}(v)) \ge t$, i.e. it has not been removed after the greedy algorithm processes the first $t - 1$ positions. For integers $l \le r'$, $G_{\mathrm{alive}}(l, r')$ is the subgraph induced by the vertices at positions $l, \dots, r'$ that are alive at time $l$; its vertex set is
--   $$
--   \{v \in V : l \le \operatorname{rank}(v) \le r',\ \operatorname{rank}(\operatorname{inhib}(v)) \ge l\}.
--   $$
-- source:
--   Mitrović–Sheu, Tight Query Depth of Recursive Randomized Greedy MIS, STOC 2027 submission (manuscript sha256 805e76d8…), §2.3, p.9 (with Definition 2.2, p.8)

import Mathlib
import Definitions.Def_RGMISFast_tau

set_option autoImplicit false

namespace QueryDepthMIS

/-- The vertex set of `G_alive(l, r')` (Mitrović–Sheu, *Tight Query Depth of Recursive Randomized Greedy MIS*, STOC 2027 submission (manuscript sha256 805e76d8…), §2.3, p.9): "For positive integers l ≤ r ≤ n,
define G_alive(l, r) as the subgraph induced by vertices in π(l, r) alive at time l", where a
vertex `v` is alive at time `t` if `rank(inhib(v)) ≥ t` (Definition 2.2, p.8).

`aliveSet G r l r'` is the set of vertices `v` with `l ≤ r(v) ≤ r'` and `l ≤ τ(v)`, with
`τ = RGMISFast.tau G r` the rank of the inhibitor.

**Formalization Note** Only integer endpoints occur in the mission. -/
def aliveSet {V : Type*} [Fintype V] [LinearOrder V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (r : V → ℕ) (l r' : ℕ) : Finset V :=
  Finset.univ.filter (fun v => l ≤ r v ∧ r v ≤ r' ∧ l ≤ RGMISFast.tau G r v)

end QueryDepthMIS


