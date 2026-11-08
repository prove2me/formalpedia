-- Prove2me | Definitions.Def_GaussianSweep_kappa
-- name    : GaussianSweep_kappa
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T07:53:52.307938+00:00
-- url     : https://prove2.me/theorems/965a7ffc-fee2-4fe6-934e-2de1b71fcacb
-- title:
--   $\kappa(r) = \frac{3}{4\pi}\arccos b(r)$
-- statement:
--   For a real $r$ put
--   $$
--   \kappa(r) = \frac{3}{4\pi}\arccos b(r), \qquad b(r) = \frac{3r^2-1}{2}.
--   $$
--   On $(0,1)$ it is continuous, it is the value at threshold zero of the ideal 3-star function, and $\kappa(2\sqrt2/3) = c_3$.
--
--   **Formalization Note** Defined for every real $r$; the results using it assume $0 < r < 1$.
-- source:
--   Gaspers, Path Decompositions of Sparse Graphs via Gaussian Sweeps and Faster Exponential Algorithms, arXiv:2611.05146 (held version, sha256 e0ed039f…9eac), Eq. (8.1), p.45 (PDF p.47)

import Mathlib
import Definitions.Def_GaussianSweep_bCorr

namespace GaussianSweep

/-- `κ(r) = (3/(4π)) arccos b(r)` (Gaspers, *Path Decompositions of Sparse Graphs via Gaussian Sweeps and Faster Exponential Algorithms*, arXiv:2611.05146 (held version, sha256 e0ed039f…9eac), Eq. (8.1), p.45 (PDF p.47)).

**Formalization Note** Defined for every real `r`; the paper uses it for `0 < r < 1`, where
`b(r) ∈ (−1/2, 1)`. -/
noncomputable def kappa (r : ℝ) : ℝ := 3 / (4 * Real.pi) * Real.arccos (bCorr r)

end GaussianSweep


