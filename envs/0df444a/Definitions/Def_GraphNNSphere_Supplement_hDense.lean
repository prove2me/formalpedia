-- Prove2me | Definitions.Def_GraphNNSphere_Supplement_hDense
-- name    : GraphNNSphere_Supplement_hDense
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T09:43:13.144085+00:00
-- url     : https://prove2.me/theorems/ff5c9d97-b8ad-4024-b7fd-ec68176b1204
-- title:
--   Dense density-variation boundary $h(\gamma)$ and $\kappa_0$
-- statement:
--   For a degree exponent $\gamma$ define
--
--   $$h(\gamma)=\frac12\log\frac{e^{2\gamma}+2}{4},\qquad \kappa_0=\frac12\log\frac32 .$$
--
--   For $\gamma_c\le\gamma\le\log 2$ the boundary of the dense nonuniform critical curve is $\kappa=h(\gamma)$, equivalently $e^{2\gamma}=4e^{2\kappa}-2$, and $\kappa_0$ is the density endpoint of that curve.
-- source:
--   Lu, Sharp Limits of Graph-Based Nearest Neighbor Search on the Sphere, STOC 2027 submission (manuscript sha256 93565bc5…), Eq. (11), p.19; Eq. (3), p.4; Theorem 4.1, p.28

import Mathlib

namespace GraphNNSphere

namespace Supplement

/-- The dense-regime density-variation boundary `h(γ) = ½ log((e^{2γ} + 2)/4)`
(Lu, *Sharp Limits of Graph-Based Nearest Neighbor Search on the Sphere*, STOC 2027 submission (manuscript sha256 93565bc5…), Eq. (11), p.19). -/
noncomputable def hDense (γ : ℝ) : ℝ := Real.log ((Real.exp (2 * γ) + 2) / 4) / 2

/-- The density endpoint `κ₀ = ½ log(3/2)` of the dense critical curve
(Lu, *Sharp Limits of Graph-Based Nearest Neighbor Search on the Sphere*, STOC 2027 submission (manuscript sha256 93565bc5…), Eq. (3), p.4, and Theorem 4.1, p.28). -/
noncomputable def kappa0 : ℝ := Real.log (3 / 2) / 2

end Supplement

end GraphNNSphere


