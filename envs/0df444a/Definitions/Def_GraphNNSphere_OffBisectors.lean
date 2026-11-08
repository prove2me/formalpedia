-- Prove2me | Definitions.Def_GraphNNSphere_OffBisectors
-- name    : GraphNNSphere_OffBisectors
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T06:39:10.209074+00:00
-- url     : https://prove2.me/theorems/efde0592-ee5d-44fc-a98a-2094e64116ee
-- title:
--   Query off the bisectors of the data
-- statement:
--   The query $q$ lies on no bisector $\{q\in S^{d-1}:\delta(q,x)=\delta(q,y)\}$ of distinct data points $x,y$. Each bisector has surface measure zero.
-- source:
--   Lu, Sharp Limits of Graph-Based Nearest Neighbor Search on the Sphere, STOC 2027 submission (manuscript sha256 93565bc5…), §2.1, p.14

import Mathlib
import Definitions.Def_GraphNNSphere_geo

namespace GraphNNSphere

/-- The query `q` lies on no bisector `{q : δ(q, x) = δ(q, y)}` of distinct data points `x`, `y` (Lu,
*Sharp Limits of Graph-Based Nearest Neighbor Search on the Sphere*, STOC 2027 submission (manuscript
sha256 93565bc5…), §2.1, p.14). -/
def OffBisectors {n d : ℕ} (X : Fin n → Sph d) (q : Sph d) : Prop :=
  ∀ i j, X i ≠ X j → geo q (X i) ≠ geo q (X j)

end GraphNNSphere


