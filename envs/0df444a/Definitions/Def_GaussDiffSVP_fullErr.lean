-- Prove2me | Definitions.Def_GaussDiffSVP_fullErr
-- name    : GaussDiffSVP_fullErr
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T21:58:36.431374+00:00
-- url     : https://prove2.me/theorems/73315ea7-de65-42ab-8862-42eb7dbe3d7f
-- title:
--   Error recursion $\varepsilon_j$ of Theorem 8.2
-- statement:
--   Given a leaf error $\varepsilon_0$, a local loss $\eta$, the nominal intensities $A_j$ and the bridge factors $B_j$,
--   $$\varepsilon_j = 2\varepsilon_{j-1} + \eta + \log\Big(1+\frac{2}{A_{j-1}B_j}\Big),$$
--   with the natural logarithm.
-- source:
--   Gao–Han–Hu, Gaussian Difference Dynamics: Breaking the 2^{n/2} Barrier for the Shortest Vector Problem and Discrete Gaussian Sampling, arXiv:2611.04336 (held version, sha256 233bf8bb…0692), (83), p.40

import Mathlib

namespace GaussDiffSVP

/-- The error recursion of Theorem 8.2 (Gao–Han–Hu, *Gaussian Difference Dynamics*, arXiv:2611.04336 (held version, sha256 233bf8bb…0692), (83), p.40):
`ε_0` is the leaf error and `ε_j = 2ε_{j−1} + η_n + log(1 + 2/(A_{j−1}B_j))`, for the nominal
intensities `A` (`A j = A_j`) and the bridge factors `Bf` (`Bf j = B_j`). "log" is natural. -/
noncomputable def fullErr (ε₀ η : ℝ) (A Bf : ℕ → ℝ) : ℕ → ℝ
  | 0 => ε₀
  | j + 1 => 2 * fullErr ε₀ η A Bf j + η + Real.log (1 + 2 / (A j * Bf (j + 1)))

end GaussDiffSVP


