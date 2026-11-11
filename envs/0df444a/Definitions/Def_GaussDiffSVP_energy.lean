-- Prove2me | Definitions.Def_GaussDiffSVP_energy
-- name    : GaussDiffSVP_energy
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T21:57:54.353315+00:00
-- url     : https://prove2.me/theorems/2315c1a9-7fd7-4d5b-b6d2-33469f133d6a
-- title:
--   Normalized energy $E_r(x) = 2\pi\|x\|^2/(nr^2)$
-- statement:
--   For $x\in\mathbb R^n$ and a Gaussian width $r>0$, the **normalized energy** is
--   $$E_r(x) = \frac{2\pi\|x\|^2}{n r^2}.$$
--   It measures squared lengths in units of the Gaussian scale: a typical sample of $\rho_r$ has energy close to $1$.
-- source:
--   Gao–Han–Hu, Gaussian Difference Dynamics: Breaking the 2^{n/2} Barrier for the Shortest Vector Problem and Discrete Gaussian Sampling, arXiv:2611.04336 (held version, sha256 233bf8bb…0692), (7), §3.3, p.18

import Mathlib
import Definitions.Def_SuperlatSVP_lat

namespace GaussDiffSVP

/-- The normalized energy `E_r(x) = 2π‖x‖² / (n r²)` of `x ∈ ℝⁿ` at Gaussian width `r`
(Gao–Han–Hu, *Gaussian Difference Dynamics: Breaking the 2^{n/2} Barrier for the Shortest Vector Problem and Discrete Gaussian Sampling*, arXiv:2611.04336 (held version, sha256 233bf8bb…0692), (7), p.18). -/
noncomputable def energy {n : ℕ} (r : ℝ) (x : SuperlatSVP.E n) : ℝ :=
  2 * Real.pi * ‖x‖ ^ 2 / (n * r ^ 2)

end GaussDiffSVP


