-- Prove2me | Definitions.Def_GraphNNSphere_rGamma
-- name    : GraphNNSphere_rGamma
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T06:42:41.703198+00:00
-- url     : https://prove2.me/theorems/c1fa04d0-8580-4bdc-8f47-46882a5ffe0c
-- title:
--   Neighbor radius $r_\gamma$
-- statement:
--   The radius $r_\gamma$ with $nF_{d-1}(r_\gamma)=e^{\gamma d}$, the neighbor radius of the degree choice $e^{\gamma d}$ in the dense regime.
--
--   **Formalization Note** It is `capRadius d (e^{γd}/n)`.
-- source:
--   Lu, Sharp Limits of Graph-Based Nearest Neighbor Search on the Sphere, STOC 2027 submission (manuscript sha256 93565bc5…), §2.2, p.15

import Mathlib
import Definitions.Def_GraphNNSphere_capRadius

namespace GraphNNSphere

/-- The neighbor radius `r_γ`, defined by `n F_{d-1}(r_γ) = e^{γd}` (Lu, *Sharp Limits of
Graph-Based Nearest Neighbor Search on the Sphere*, STOC 2027 submission (manuscript sha256
93565bc5…), §2.2, p.15).

**Formalization Note** See `capRadius` for the infimum encoding. -/
noncomputable def rGamma (n d : ℕ) (γ : ℝ) : ℝ :=
  capRadius d (Real.exp (γ * (d : ℝ)) / (n : ℝ))

end GraphNNSphere


