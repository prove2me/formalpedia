-- Prove2me | Definitions.Def_PolygonPack_diag
-- name    : PolygonPack_diag
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T10:52:24.653273+00:00
-- url     : https://prove2.me/theorems/1d3f20db-1107-47b2-99fd-b297f151b763
-- title:
--   Diagonal coordinates
-- statement:
--   The **diagonal coordinates** of a point $(x,y)$ are
--   $$
--   u=\frac{x+y-1}{\sqrt2},\qquad v=\frac{y-x}{\sqrt2}.
--   $$
--   In them the unit square becomes the diamond $|u|+|v|\le s$, with $s=1/\sqrt2$, and the $u$-axis runs along its rising diagonal.
-- source:
--   Khan, Mathur, Constant Approximation Algorithms for Knapsack and Bin Packing for Convex Polygons, STOC 2027 submission (manuscript sha256 7a527fb3…), §2, p.5; App. A.1, p.21

import Mathlib

namespace PolygonPack

/-- **Diagonal coordinates.** Khan, Mathur, *Constant Approximation Algorithms for Knapsack and Bin Packing for Convex Polygons*, STOC 2027 submission (manuscript sha256 7a527fb3…), §2, p.5 and App. A.1, p.21: "u = (x + y − 1)/√2 and v = (y − x)/√2,
in which the square becomes D = {(u, v) : |u| + |v| ≤ s}, where s = 1/√2."

`diag (x, y) = (u, v)`, and `diagS` is `s`. -/
noncomputable def diag (p : ℝ × ℝ) : ℝ × ℝ :=
  ((p.1 + p.2 - 1) / Real.sqrt 2, (p.2 - p.1) / Real.sqrt 2)

/-- The half-diagonal `s = 1/√2`. -/
noncomputable def diagS : ℝ := 1 / Real.sqrt 2

end PolygonPack


