-- Prove2me | Definitions.Def_QueryDepthMIS_T
-- name    : QueryDepthMIS_T
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T22:32:11.870648+00:00
-- url     : https://prove2.me/theorems/736a8d16-ea59-433a-afbb-6cdb9d308e64
-- title:
--   $T(v, \pi)$: the number of query paths ending at $v$
-- statement:
--   For a ranking $r$ and a vertex $v$, $T(v, \pi)$ is the number of query paths whose last (highest-ranked) vertex is $v$, the singleton path $(v)$ included. Equivalently, it is the total number of calls in the recursion tree of the oracle started at $v$, counted with multiplicity.
-- source:
--   Mitrović–Sheu, Tight Query Depth of Recursive Randomized Greedy MIS, STOC 2027 submission (manuscript sha256 805e76d8…), §2.3, p.9

import Mathlib
import Definitions.Def_QueryDepthMIS_IsQueryPath

set_option autoImplicit false

namespace QueryDepthMIS

/-- `T(v, π)` (Mitrović–Sheu, *Tight Query Depth of Recursive Randomized Greedy MIS*, STOC 2027 submission (manuscript sha256 805e76d8…), §2.3, p.9): "For a permutation π and vertex v, let T(v, π) be the number of
query paths ending at v, including the singleton path (v)."

The number of query paths of `G` under ranks `r` whose last (highest-ranked) vertex is `v`. A
query path is the rank-sorted listing of its vertex set, so query paths are counted through their
vertex sets `U`. -/
def T {V : Type*} [Fintype V] [LinearOrder V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (r : V → ℕ) (v : V) : ℕ :=
  ((Finset.univ : Finset (Finset V)).filter (fun U =>
    IsQueryPath G r (RGMISFast.scanOrder r U) ∧
      (RGMISFast.scanOrder r U).getLast? = some v)).card

end QueryDepthMIS


