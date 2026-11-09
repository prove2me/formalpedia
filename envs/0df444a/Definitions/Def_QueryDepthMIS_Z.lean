-- Prove2me | Definitions.Def_QueryDepthMIS_Z
-- name    : QueryDepthMIS_Z
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T22:34:50.353292+00:00
-- url     : https://prove2.me/theorems/a3dcceb7-11f7-439f-bf49-ff59950dead4
-- title:
--   $Z(\pi) = \sum_{v} T(v, \pi)$: the total number of query paths
-- statement:
--   $$
--   Z(\pi) = \sum_{v \in V} T(v, \pi),
--   $$
--   the total number of query paths of $G$ under $\pi$, i.e. the total number of oracle calls over all starting vertices.
-- source:
--   Mitrović–Sheu, Tight Query Depth of Recursive Randomized Greedy MIS, STOC 2027 submission (manuscript sha256 805e76d8…), §2.3, p.9

import Mathlib
import Definitions.Def_QueryDepthMIS_T

set_option autoImplicit false

namespace QueryDepthMIS

/-- `Z(π) = ∑_{v ∈ V} T(v, π)` (Mitrović–Sheu, *Tight Query Depth of Recursive Randomized Greedy MIS*, STOC 2027 submission (manuscript sha256 805e76d8…), §2.3, p.9), the total number of query paths of `G`. -/
def Z {V : Type*} [Fintype V] [LinearOrder V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (r : V → ℕ) : ℕ :=
  ∑ v, T G r v

end QueryDepthMIS


