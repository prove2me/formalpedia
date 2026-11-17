-- Prove2me | Definitions.Def_GraphNNSphere_Supplement_rhoF
-- name    : GraphNNSphere_Supplement_rhoF
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T09:42:35.537703+00:00
-- url     : https://prove2.me/theorems/120fd451-2239-4d8c-9461-f6557b42c818
-- title:
--   Local nearest-neighbor scale $\rho_f(x)$ and $\rho_{\min}$
-- statement:
--   For a sampling distribution $P=f\,d\sigma_{d-1}$ and $x\in S^{d-1}$, the **local nearest-neighbor scale** $\rho_f(x)$ is the smallest radius whose cap centered at $x$ has probability at least $1/n$:
--
--   $$\rho_f(x)=\inf\{\rho\in[0,\pi]:\ nP(C(x,\rho))\ge 1\},\qquad \rho_{\min}=\inf_{x\in S^{d-1}}\rho_f(x).$$
--
--   By continuity of cap probability in the radius, $nP(C(x,\rho_f(x)))=1$. For uniform data $\rho_f\equiv\theta_1$. The radii $K e^{\gamma}\rho_f(x)$ define the neighborhoods on which the density is controlled in the dense nonuniform theorems.
--
--   **Formalization Note** $C(x,\rho)$ is the closed cap of the base mission. For $n\ge1$ the radius $\pi$ belongs to the set, since $C(x,\pi)$ is the whole sphere.
-- source:
--   Lu, Sharp Limits of Graph-Based Nearest Neighbor Search on the Sphere, STOC 2027 submission (manuscript sha256 93565bc5…), §1.2, p.4; §2.5, p.18

import Mathlib
import Definitions.Def_GraphNNSphere_cap
import Definitions.Def_GraphNNSphere_Supplement_sampleLaw

open MeasureTheory

namespace GraphNNSphere

namespace Supplement

/-- The local nearest-neighbor scale `ρ_f(x)`: the smallest radius whose cap centered at `x` has
probability at least `1/n` under `P = f dσ_{d-1}` (Lu, *Sharp Limits of Graph-Based Nearest Neighbor Search on the Sphere*, STOC 2027 submission (manuscript sha256 93565bc5…), §1.2, p.4, and §2.5, p.18).

**Formalization Note** It is the infimum of `{r ∈ [0, π] : n P(C(x, r)) ≥ 1}`. For `n ≥ 1` and a
density, `r = π` belongs to the set because `C(x, π)` is the whole sphere. -/
noncomputable def rhoF (n d : ℕ) (f : Sph d → ℝ) (x : Sph d) : ℝ :=
  sInf {r | r ∈ Set.Icc 0 Real.pi ∧ 1 ≤ (n : ℝ) * (sampleLaw d f (cap x r)).toReal}

/-- `ρ_min = inf_{x ∈ S^{d-1}} ρ_f(x)` (Lu, *Sharp Limits of Graph-Based Nearest Neighbor Search on the Sphere*, STOC 2027 submission (manuscript sha256 93565bc5…), §1.2, p.4, and §2.5, p.18). -/
noncomputable def rhoMin (n d : ℕ) (f : Sph d → ℝ) : ℝ := ⨅ x, rhoF n d f x

end Supplement

end GraphNNSphere


