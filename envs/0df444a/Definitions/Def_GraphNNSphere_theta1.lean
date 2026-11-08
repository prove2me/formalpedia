-- Prove2me | Definitions.Def_GraphNNSphere_theta1
-- name    : GraphNNSphere_theta1
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T06:42:26.910877+00:00
-- url     : https://prove2.me/theorems/23f81b9f-eaf9-4c04-932c-14f73f42ad07
-- title:
--   Nearest-neighbor scale $\theta_1$
-- statement:
--   The radius $\theta_1$ with $nF_{d-1}(\theta_1)=1$, so that a cap of radius $\theta_1$ contains one data point in expectation. It gives the typical exact nearest-neighbor scale.
--
--   **Formalization Note** It is `capRadius d (1/n)`.
-- source:
--   Lu, Sharp Limits of Graph-Based Nearest Neighbor Search on the Sphere, STOC 2027 submission (manuscript sha256 93565bc5…), §1.2, p.3

import Mathlib
import Definitions.Def_GraphNNSphere_capRadius

namespace GraphNNSphere

/-- The nearest-neighbor scale `θ₁`, defined by `n F_{d-1}(θ₁) = 1` (Lu, *Sharp Limits of
Graph-Based Nearest Neighbor Search on the Sphere*, STOC 2027 submission (manuscript sha256
93565bc5…), §1.2, p.3).

**Formalization Note** See `capRadius` for the infimum encoding. -/
noncomputable def theta1 (n d : ℕ) : ℝ := capRadius d (1 / (n : ℝ))

end GraphNNSphere


