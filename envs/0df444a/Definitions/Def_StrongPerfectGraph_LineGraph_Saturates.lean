-- Prove2me | Definitions.Def_StrongPerfectGraph_LineGraph_Saturates
-- name    : StrongPerfectGraph_LineGraph_Saturates
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-05T02:33:31.515063+00:00
-- url     : https://prove2.me/theorems/507a187d-bd80-4511-b711-8a6408a25900
-- title:
--   A set of edges saturating $L(H)$
-- statement:
--   Let $H$ be bipartite and cyclically $3$-connected. A set $X$ **saturates** $L(H)$ if for every branch-vertex $v$ of $H$ at most one edge of $\delta_H(v)$ is not in $X$; equivalently, every triangle of $L(H)$ has at least two of its vertices in $X$.
--
--   A vertex of $G$ outside an appearance $L(H)$ is **major** if its set of neighbours in $L(H)$, viewed as a set of edges of $H$, saturates $L(H)$.
-- source:
--   Chudnovsky, Robertson, Seymour & Thomas, The strong perfect graph theorem, Ann. of Math. 164 (2006), p. 77 (saturates) and p. 81 (major)

import Mathlib
import Definitions.Def_StrongPerfectGraph_LineGraph_IsTrack

namespace StrongPerfectGraph.LineGraph

/-- A set `X` of edges of `H` **saturates** `L(H)` (p. 77): for every branch-vertex `v` of `H`, at
most one edge of `δ_H(v)` is not in `X`. -/
def Saturates {U : Type*} (H : SimpleGraph U) (X : Set (Sym2 U)) : Prop :=
  ∀ v : U, IsBranchVertex H v → (H.incidenceSet v \ X).Subsingleton

end StrongPerfectGraph.LineGraph


