-- Prove2me | Definitions.Def_GraphNNSphere_capMass
-- name    : GraphNNSphere_capMass
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T06:40:16.675449+00:00
-- url     : https://prove2.me/theorems/5e8fe38c-4702-4bb3-854b-88a41c3844e0
-- title:
--   Cap mass $F_{d-1}(\theta)$
-- statement:
--   The normalized surface measure of a cap of radius $\theta$:
--   $$F_{d-1}(\theta)=\sigma_{d-1}(C(x,\theta)).$$
--   It does not depend on the center $x$, by rotational symmetry. It is the function through which every neighbor radius and rank of the mission is expressed.
--
--   **Formalization Note** The center is the fixed pole, so independence of $x$ is a property and not part of the definition. At $d=0$, where the sphere is empty, the value is the junk value $0$.
-- source:
--   Lu, Sharp Limits of Graph-Based Nearest Neighbor Search on the Sphere, STOC 2027 submission (manuscript sha256 93565bc5…), §1.2, p.3

import Mathlib
import Definitions.Def_GraphNNSphere_unif
import Definitions.Def_GraphNNSphere_cap
import Definitions.Def_GraphNNSphere_pole

namespace GraphNNSphere

/-- The normalized cap mass `F_{d-1}(θ) = σ_{d-1}(C(x, θ))` (Lu, *Sharp Limits of Graph-Based
Nearest Neighbor Search on the Sphere*, STOC 2027 submission (manuscript sha256 93565bc5…), §1.2,
p.3).

**Formalization Note** The paper notes that the value does not depend on `x`, by rotational
symmetry. Here `x` is the fixed `pole`, so that independence is a property and not part of the
definition. The value at `d = 0`, where the sphere is empty, is the junk value `0`. -/
noncomputable def capMass : ℕ → ℝ → ℝ
  | 0, _ => 0
  | m + 1, θ => (unif (m + 1) (cap (pole m) θ)).toReal

end GraphNNSphere


