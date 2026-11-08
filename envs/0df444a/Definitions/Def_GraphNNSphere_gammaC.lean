-- Prove2me | Definitions.Def_GraphNNSphere_gammaC
-- name    : GraphNNSphere_gammaC
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T06:37:13.28521+00:00
-- url     : https://prove2.me/theorems/acb043db-fc3a-47bc-b137-412804ac9414
-- title:
--   Critical exponent $\gamma_c$
-- statement:
--   The critical degree exponent of the dense regime, $\gamma_c=\tfrac12\log2$. The critical degree in that regime is $2^{d/2+o(d)}$.
-- source:
--   Lu, Sharp Limits of Graph-Based Nearest Neighbor Search on the Sphere, STOC 2027 submission (manuscript sha256 93565bc5…), §1.2, p.3

import Mathlib

namespace GraphNNSphere

/-- The critical exponent `γ_c = (1/2) log 2` of the dense regime (Lu, *Sharp Limits of Graph-Based
Nearest Neighbor Search on the Sphere*, STOC 2027 submission (manuscript sha256 93565bc5…), §1.2,
p.3). -/
noncomputable def gammaC : ℝ := Real.log 2 / 2

end GraphNNSphere


