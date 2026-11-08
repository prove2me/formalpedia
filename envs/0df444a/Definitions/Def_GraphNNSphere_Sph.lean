-- Prove2me | Definitions.Def_GraphNNSphere_Sph
-- name    : GraphNNSphere_Sph
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T06:37:12.14634+00:00
-- url     : https://prove2.me/theorems/4e852447-e37f-46e1-93c5-0cd2d8ea25b9
-- title:
--   Unit sphere $S^{d-1}\subset\mathbb R^d$
-- statement:
--   The unit sphere $S^{d-1}=\{x\in\mathbb R^d:\|x\|=1\}$, on which the data points and the queries of the mission live.
--
--   **Formalization Note** It is the metric sphere of radius $1$ about the origin of `EuclideanSpace ℝ (Fin d)`. It is empty for $d=0$ and has two points for $d=1$.
-- source:
--   Lu, Sharp Limits of Graph-Based Nearest Neighbor Search on the Sphere, STOC 2027 submission (manuscript sha256 93565bc5…), §1.2, p.2

import Mathlib

namespace GraphNNSphere

/-- The unit sphere `S^{d-1} ⊂ ℝ^d` (Lu, *Sharp Limits of Graph-Based Nearest Neighbor Search on
the Sphere*, STOC 2027 submission (manuscript sha256 93565bc5…), §1.2, p.2).

**Formalization Note** The sphere is `Metric.sphere 0 1` in `EuclideanSpace ℝ (Fin d)`; it is empty
for `d = 0` and has two points for `d = 1`. -/
abbrev Sph (d : ℕ) : Type := Metric.sphere (0 : EuclideanSpace ℝ (Fin d)) 1

end GraphNNSphere


