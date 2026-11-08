-- Prove2me | Definitions.Def_GraphNNSphere_rhoBeta
-- name    : GraphNNSphere_rhoBeta
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T06:42:24.340883+00:00
-- url     : https://prove2.me/theorems/c26a4cec-8d15-4827-adad-4ddb0af2f30a
-- title:
--   Neighbor radius $\rho_\beta$
-- statement:
--   The radius $\rho_\beta$ with $nF_{d-1}(\rho_\beta)=n^\beta$, the neighbor radius of the degree choice $n^\beta$ in the logarithmic regime.
--
--   **Formalization Note** It is `capRadius d (n^β/n)`.
-- source:
--   Lu, Sharp Limits of Graph-Based Nearest Neighbor Search on the Sphere, STOC 2027 submission (manuscript sha256 93565bc5…), §2.2, p.15

import Mathlib
import Definitions.Def_GraphNNSphere_capRadius

namespace GraphNNSphere

/-- The neighbor radius `ρ_β`, defined by `n F_{d-1}(ρ_β) = n^β` (Lu, *Sharp Limits of Graph-Based
Nearest Neighbor Search on the Sphere*, STOC 2027 submission (manuscript sha256 93565bc5…), §2.2,
p.15).

**Formalization Note** See `capRadius` for the infimum encoding. -/
noncomputable def rhoBeta (n d : ℕ) (β : ℝ) : ℝ := capRadius d ((n : ℝ) ^ β / (n : ℝ))

end GraphNNSphere


