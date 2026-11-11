-- Prove2me | Definitions.Def_GaussDiffSVP_nomIntensity
-- name    : GaussDiffSVP_nomIntensity
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T21:58:10.190326+00:00
-- url     : https://prove2.me/theorems/9d041d29-2336-4293-934b-68671e771308
-- title:
--   Nominal intensities $A_j = A_{j-1}^2 B_j$
-- statement:
--   Given $A_0$ and bridge factors $B_j$, the nominal intensity per atom of a full difference tree is defined by $A_j = A_{j-1}^2B_j$; in the paper $B_j = V_r(eE_j/4)^{n/2}$ with $E_j = 4a_{j-1}-a_j$.
-- source:
--   Gao–Han–Hu, Gaussian Difference Dynamics: Breaking the 2^{n/2} Barrier for the Shortest Vector Problem and Discrete Gaussian Sampling, arXiv:2611.04336 (held version, sha256 233bf8bb…0692), (79), p.40

import Mathlib

namespace GaussDiffSVP

/-- The nominal intensity per atom of a full difference tree (Gao–Han–Hu, *Gaussian Difference Dynamics*, arXiv:2611.04336 (held version, sha256 233bf8bb…0692), (79), p.40):
`A_0` is given and `A_j = A_{j−1}² B_j`, where `B_j = V_r (eE_j/4)^{n/2}` is supplied as the
sequence `Bf` (`Bf j = B_j`). -/
noncomputable def nomIntensity (A₀ : ℝ) (Bf : ℕ → ℝ) : ℕ → ℝ
  | 0 => A₀
  | j + 1 => nomIntensity A₀ Bf j ^ 2 * Bf (j + 1)

end GaussDiffSVP


