-- Prove2me | Definitions.Def_QueryDepthMIS_inducedDepth
-- name    : QueryDepthMIS_inducedDepth
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T22:34:14.825205+00:00
-- url     : https://prove2.me/theorems/52c37bbe-af3e-4c36-8d25-a83183d0f798
-- title:
--   Query depth $\sigma(H)$ of an induced subgraph with the inherited order
-- statement:
--   For a vertex set $U$ and the subgraph $H = G[U]$ it induces, $\sigma(H)$ is the query depth of $H$ when the permutation on $V(H)$ is inherited from $\pi$: query paths of $H$ are formed with the inhibitors of the greedy process run on $H$ itself under the restricted ranks.
--
--   **Formalization Note** $\sigma(G_{\mathrm{alive}}(l, r))$ is this quantity for $U$ the vertex set of $G_{\mathrm{alive}}(l, r)$. The paper's remark (p.9) that inhibitors in $G_{\mathrm{alive}}(l, r)$ agree with those in $G$ is a fact about this object, not part of its definition.
-- source:
--   Mitrović–Sheu, Tight Query Depth of Recursive Randomized Greedy MIS, STOC 2027 submission (manuscript sha256 805e76d8…), Definition 2.6, p.9

import Mathlib
import Definitions.Def_QueryDepthMIS_queryDepth

set_option autoImplicit false

namespace QueryDepthMIS

/-- The query depth `σ(H)` of an induced subgraph `H = G[U]` with the inherited order (Mitrović–Sheu, *Tight Query Depth of Recursive Randomized Greedy MIS*, STOC 2027 submission (manuscript sha256 805e76d8…),
Definition 2.6, p.9): "For a subgraph H of G, denote by σ(H) the query depth of H when the
permutation on V(H) is inherited from π."

`inducedDepth G r U` is `queryDepth` of the induced graph `G[U]` with the restricted ranks
`r|_U`: query paths of `H` use the inhibitors of `H`'s own greedy process, not those of `G`.

**Formalization Note** `σ(G_alive(l, r))` is `inducedDepth G r (aliveSet G r l r)`. The paper's
observation (p.9) that the inhibitors in `G_alive(l, r)` agree with those in `G` is not built in. -/
def inducedDepth {V : Type*} [Fintype V] [LinearOrder V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (r : V → ℕ) (U : Finset V) : ℕ :=
  queryDepth (G.induce (U : Set V)) (fun x => r x.1)

end QueryDepthMIS


