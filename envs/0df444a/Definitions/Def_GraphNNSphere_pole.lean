-- Prove2me | Definitions.Def_GraphNNSphere_pole
-- name    : GraphNNSphere_pole
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T06:38:16.943292+00:00
-- url     : https://prove2.me/theorems/9a34cc57-ab2f-415d-a83f-e7125ed43009
-- title:
--   A fixed pole of $S^{m}$
-- statement:
--   The first basis vector of $\mathbb R^{m+1}$, as a point of $S^{m}$. It is the center at which the cap mass $F_{d-1}$ is evaluated.
-- source:
--   Lu, Sharp Limits of Graph-Based Nearest Neighbor Search on the Sphere, STOC 2027 submission (manuscript sha256 93565bc5…), §1.2, p.3

import Mathlib
import Definitions.Def_GraphNNSphere_Sph

namespace GraphNNSphere

/-- A fixed pole of `S^m ⊂ ℝ^{m+1}`, the first basis vector. It is the center at which the cap mass
`F_{d-1}` is evaluated (Lu, *Sharp Limits of Graph-Based Nearest Neighbor Search on the Sphere*,
STOC 2027 submission (manuscript sha256 93565bc5…), §1.2, p.3). -/
noncomputable def pole (m : ℕ) : Sph (m + 1) :=
  ⟨EuclideanSpace.single 0 1, by simp⟩

end GraphNNSphere


