-- Prove2me | Definitions.Def_PolySphereLP_Rmom
-- name    : PolySphereLP_Rmom
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T16:56:19.240734+00:00
-- url     : https://prove2.me/theorems/6e05a43b-e736-40f0-a78a-2cb5d60828e3
-- title:
--   The radial-moment product $\mathrm R_{m,j}$
-- statement:
--   For integers $m,j\ge0$,
--   $$\mathrm R_{m,j}=\prod_{t=0}^{j-1}(m+2t),\qquad \mathrm R_{m,0}=1.$$
--   It is the normalizing constant of spherical moments: $\int\langle v,x\rangle^{2j}\,d\sigma=(2j-1)!!\,\|v\|^{2j}/\mathrm R_{n,j}$ on $S^{n-1}$.
-- source:
--   Ghosh, Hardness of Approximation for Polynomial Optimization over Sphere for LP Relaxation Hierarchy (manuscript, sha256 b9e9c812…), (21), p.11; App. A, p.23

import Mathlib

namespace PolySphereLP

/-- **The radial-moment product `R_{m,j}`.** Ghosh, *Hardness of Approximation for Polynomial Optimization over Sphere for LP Relaxation
Hierarchy* (manuscript, sha256 b9e9c812…), (21), p.11: `R_{m,j} = ∏_{t=0}^{j−1} (m + 2t)`,
`R_{m,0} = 1`.

**Formalization Note.** Real-valued; the empty product gives `R_{m,0} = 1`. -/
noncomputable def Rmom (m j : ℕ) : ℝ :=
  ∏ t ∈ Finset.range j, ((m : ℝ) + 2 * (t : ℝ))

end PolySphereLP


