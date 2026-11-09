-- Prove2me | Definitions.Def_QueryDepthMIS_maxDegOn
-- name    : QueryDepthMIS_maxDegOn
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T22:25:32.054512+00:00
-- url     : https://prove2.me/theorems/b6e65921-f4b0-4058-945a-153b6eee7191
-- title:
--   Maximum degree $\Delta(G[U])$ of an induced subgraph
-- statement:
--   For a vertex set $U$, $\Delta(G[U])$ is the largest number of neighbours inside $U$ of a vertex of $U$, and $0$ if $U = \emptyset$. With $U$ the vertex set of $G_{\mathrm{alive}}(t, n)$ it is the maximum degree of the alive graph.
-- source:
--   Mitrović–Sheu, Tight Query Depth of Recursive Randomized Greedy MIS, STOC 2027 submission (manuscript sha256 805e76d8…), §2.1, p.7

import Mathlib

set_option autoImplicit false

namespace QueryDepthMIS

/-- The maximum degree `Δ(G[U])` of the subgraph of `G` induced by a vertex set `U` (Mitrović–Sheu, *Tight Query Depth of Recursive Randomized Greedy MIS*, STOC 2027 submission (manuscript sha256 805e76d8…), §2.1,
p.7: "Denote by Δ(H) the maximum degree of a graph H"): the largest number of neighbours inside
`U` of a vertex of `U`; `0` if `U` is empty. -/
def maxDegOn {V : Type*} [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (U : Finset V) : ℕ :=
  U.sup (fun v => (U.filter (fun w => G.Adj v w)).card)

end QueryDepthMIS


