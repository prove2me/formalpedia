-- Prove2me | Definitions.Def_GraphNNSphere_geo
-- name    : GraphNNSphere_geo
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T06:38:08.325605+00:00
-- url     : https://prove2.me/theorems/9cd560a6-f2ee-4e69-9ec3-2bfd34d5880a
-- title:
--   Geodesic distance $\delta(x,y)$
-- statement:
--   The geodesic distance $\delta(x,y)$ between points $x,y\in S^{d-1}$, that is, the angle between them, with values in $[0,\pi]$. On unit vectors $\delta(x,y)=\arccos\langle x,y\rangle$. All comparisons of points in the model use this distance.
--
--   **Formalization Note** It is `InnerProductGeometry.angle` applied to the underlying vectors.
-- source:
--   Lu, Sharp Limits of Graph-Based Nearest Neighbor Search on the Sphere, STOC 2027 submission (manuscript sha256 93565bc5…), §1.2, p.3

import Mathlib
import Definitions.Def_GraphNNSphere_Sph

namespace GraphNNSphere

/-- Geodesic distance `δ(x, y)` on `S^{d-1}` (Lu, *Sharp Limits of Graph-Based Nearest Neighbor
Search on the Sphere*, STOC 2027 submission (manuscript sha256 93565bc5…), §1.2, p.3).

**Formalization Note** `δ` is `InnerProductGeometry.angle`, which equals `arccos ⟪x, y⟫` on unit
vectors and takes values in `[0, π]`. -/
noncomputable def geo {d : ℕ} (x y : Sph d) : ℝ :=
  InnerProductGeometry.angle (x : EuclideanSpace ℝ (Fin d)) (y : EuclideanSpace ℝ (Fin d))

end GraphNNSphere


