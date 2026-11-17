-- Prove2me | Definitions.Def_GraphNNSphere_Supplement_critDeg
-- name    : GraphNNSphere_Supplement_critDeg
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T09:41:21.7062+00:00
-- url     : https://prove2.me/theorems/45d8bb63-f005-4f7b-b7b4-253ed2e3ae11
-- title:
--   Critical degree $\Delta^*=nF_{d-1}(\rho^*)$
-- statement:
--   Let $\theta_1$ be the nearest-neighbor scale, $nF_{d-1}(\theta_1)=1$, where $F_{d-1}(\theta)$ is the normalized surface measure of a spherical cap of radius $\theta$ on $S^{d-1}$. The **critical radius** $\rho^*$ and the **critical degree** $\Delta^*$ are defined by
--
--   $$\cos\rho^*=\cos^2\theta_1,\qquad \Delta^*=nF_{d-1}(\rho^*).$$
--
--   $\Delta^*$ is the degree scale at which greedy search from every entry becomes possible for uniform data: $\Delta^*=n^{\beta^*(c)+o(1)}$ in the logarithmic regime and $e^{(\gamma_c+o(1))d}$ in the dense regime. Theorem 3.4 bounds average degree and evaluation cost below by $(\Delta^*)^{1-o(1)}$.
--
--   **Formalization Note** $\rho^*=r^*(\theta_1)$ with the base mission's lens boundary $r^*$, and $F_{d-1}$ is the base mission's cap mass.
-- source:
--   Lu, Sharp Limits of Graph-Based Nearest Neighbor Search on the Sphere, STOC 2027 submission (manuscript sha256 93565bc5…), Eq. (1), p.3

import Mathlib
import Definitions.Def_GraphNNSphere_capMass
import Definitions.Def_GraphNNSphere_theta1
import Definitions.Def_GraphNNSphere_rStar

namespace GraphNNSphere

namespace Supplement

/-- The critical degree `Δ* = n F_{d-1}(ρ*)`, where the critical radius `ρ*` is defined by
`cos ρ* = cos² θ₁` (Lu, *Sharp Limits of Graph-Based Nearest Neighbor Search on the Sphere*, STOC 2027 submission (manuscript sha256 93565bc5…), Eq. (1), p.3).

**Formalization Note** `ρ* = r*(θ₁)` with the base mission's `rStar` and `theta1`, and
`F_{d-1}` is the base mission's `capMass`. -/
noncomputable def critDeg (n d : ℕ) : ℝ := (n : ℝ) * capMass d (rStar (theta1 n d))

end Supplement

end GraphNNSphere


