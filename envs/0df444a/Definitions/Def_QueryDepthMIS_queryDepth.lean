-- Prove2me | Definitions.Def_QueryDepthMIS_queryDepth
-- name    : QueryDepthMIS_queryDepth
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T22:31:49.347044+00:00
-- url     : https://prove2.me/theorems/a8ff3a17-cf0c-4ee8-bad7-a59155a7b894
-- title:
--   Query depth $\sigma(G)$: the maximum length of a query path
-- statement:
--   The **query depth** $\sigma(G)$ of a graph $G$ with ranking $r$ is the maximum number of vertices of a query path. It equals the maximum recursion depth of the recursive greedy-MIS oracle over all starting vertices.
--
--   **Formalization Note** A query path has strictly increasing ranks, so it is the rank-sorted listing of its vertex set; the maximum is taken over the finitely many vertex sets whose sorted listing is a query path. On a nonempty graph $\sigma(G) \ge 1$ (single vertices are query paths) and $\sigma(G) \le |V|$.
-- source:
--   Mitrović–Sheu, Tight Query Depth of Recursive Randomized Greedy MIS, STOC 2027 submission (manuscript sha256 805e76d8…), Definition 2.6, p.9

import Mathlib
import Definitions.Def_QueryDepthMIS_IsQueryPath

set_option autoImplicit false

namespace QueryDepthMIS

/-- Query depth (Mitrović–Sheu, *Tight Query Depth of Recursive Randomized Greedy MIS*, STOC 2027 submission (manuscript sha256 805e76d8…), Definition 2.6, p.9): "The query depth of G with respect to π is the
maximum length of a query path."

`queryDepth G r` (the paper's `σ(G)`) is the maximum number of vertices of a query path of `G`
under the ranks `r`. A query path has strictly increasing ranks, so it is the rank-sorted listing
(`RGMISFast.scanOrder r U`) of its vertex set `U`; the maximum is taken over the finitely many
vertex sets `U` whose sorted listing is a query path.

**Formalization Note** `Finset.sup` of the cardinalities; every singleton `[v]` is a query path,
so on a nonempty vertex type the maximum is over a nonempty family and is at least `1`; on the
empty type it is `0`. -/
def queryDepth {V : Type*} [Fintype V] [LinearOrder V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (r : V → ℕ) : ℕ :=
  ((Finset.univ : Finset (Finset V)).filter
    (fun U => IsQueryPath G r (RGMISFast.scanOrder r U))).sup Finset.card

end QueryDepthMIS


