-- Prove2me | Definitions.Def_MatchVec3_maxDegree
-- name    : MatchVec3_maxDegree
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T10:40:53.087703+00:00
-- url     : https://prove2.me/theorems/9f2bf872-6d1c-4e15-b739-aa7fdbaa3ae9
-- title:
--   The maximum vertex degree $\Delta(F)$
-- statement:
--   For a hypergraph $F$ on $[K]$, the **maximum vertex degree** is $\Delta(F)=\max_i\#\{A\in F:\ i\in A\}$. It is $0$ when $K=0$.
-- source:
--   Aggarwal, Obremski, Subexponential Upper Bounds for 3-Restricted Matching Vector Families, STOC 2027 submission (manuscript sha256 44199413…), proof of Theorem 5.2, p.14

import Mathlib

namespace MatchVec3

/-- **The maximum vertex degree `∆(F)`** of a hypergraph `F` on `[K]` (Aggarwal, Obremski, STOC 2027
submission (manuscript sha256 44199413…), proof of Theorem 5.2, p.14): `max_i #{A ∈ F : i ∈ A}`. It is
`0` at `K = 0`. -/
def maxDegree {K : ℕ} (F : Finset (Finset (Fin K))) : ℕ :=
  Finset.univ.sup fun i => (F.filter fun A => i ∈ A).card

end MatchVec3


