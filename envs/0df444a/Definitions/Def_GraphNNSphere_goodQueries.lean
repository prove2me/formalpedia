-- Prove2me | Definitions.Def_GraphNNSphere_goodQueries
-- name    : GraphNNSphere_goodQueries
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T06:42:05.188061+00:00
-- url     : https://prove2.me/theorems/ce0a541c-2842-4244-9157-586c23e421b2
-- title:
--   Query set $Q_D$ of Proposition 3.2
-- statement:
--   For a sample $D_n$, the set $Q_D\subseteq S^{d-1}$ of queries for which both $C(q)$ and $P(q)$ hold, with the bisectors of the data excluded.
-- source:
--   Lu, Sharp Limits of Graph-Based Nearest Neighbor Search on the Sphere, STOC 2027 submission (manuscript sha256 93565bc5…), Proposition 3.2, p.20

import Mathlib
import Definitions.Def_GraphNNSphere_PEvent
import Definitions.Def_GraphNNSphere_CEvent
import Definitions.Def_GraphNNSphere_OffBisectors

namespace GraphNNSphere

/-- The query set `Q_D` of Proposition 3.2: the queries for which both `C(q)` and `P(q)` hold, with
bisectors excluded (Lu, *Sharp Limits of Graph-Based Nearest Neighbor Search on the Sphere*, STOC
2027 submission (manuscript sha256 93565bc5…), Proposition 3.2, p.20). -/
def goodQueries {n d : ℕ} (k : ℕ) (X : Fin n → Sph d) (A r h : ℝ) : Set (Sph d) :=
  {q | CEvent k X q A r ∧ PEvent X q A r h ∧ OffBisectors X q}

end GraphNNSphere


