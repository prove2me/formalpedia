-- Prove2me | Definitions.Def_GraphNNSphere_maxDeg
-- name    : GraphNNSphere_maxDeg
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T06:38:10.491991+00:00
-- url     : https://prove2.me/theorems/ccd0b764-0896-438b-a7a3-71328e536533
-- title:
--   Degree $\Delta(G)$
-- statement:
--   The degree of a graph, $\Delta(G)=\max_x|G(x)|$.
-- source:
--   Lu, Sharp Limits of Graph-Based Nearest Neighbor Search on the Sphere, STOC 2027 submission (manuscript sha256 93565bc5…), §1.1, p.1

import Mathlib
import Definitions.Def_GraphNNSphere_NavGraph

namespace GraphNNSphere

/-- The degree `Δ(G) = max_x |G(x)|` (Lu, *Sharp Limits of Graph-Based Nearest Neighbor Search on
the Sphere*, STOC 2027 submission (manuscript sha256 93565bc5…), §1.1, p.1). -/
def maxDeg {n : ℕ} (G : NavGraph n) : ℕ := Finset.univ.sup (fun i => (G i).card)

end GraphNNSphere


