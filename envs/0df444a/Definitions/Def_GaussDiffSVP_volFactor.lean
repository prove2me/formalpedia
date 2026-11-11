-- Prove2me | Definitions.Def_GaussDiffSVP_volFactor
-- name    : GaussDiffSVP_volFactor
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T21:57:43.036367+00:00
-- url     : https://prove2.me/theorems/8f36c972-838c-4ed7-81e2-af804828420d
-- title:
--   Gaussian volume factor $V_r = r^n/\det\Gamma$
-- statement:
--   For a full-rank lattice $\Gamma = B\mathbb Z^n$ and a width $r$, $V_r = r^n/\det\Gamma$, with $\det\Gamma = |\det B|$. By Poisson summation, $V_r$ is the Gaussian mass $\rho_r$ of any coset of $\Gamma$ when $r$ is above the smoothing parameter.
-- source:
--   Gao–Han–Hu, Gaussian Difference Dynamics: Breaking the 2^{n/2} Barrier for the Shortest Vector Problem and Discrete Gaussian Sampling, arXiv:2611.04336 (held version, sha256 233bf8bb…0692), (7), §3.3, p.18

import Mathlib

namespace GaussDiffSVP

/-- The Gaussian volume factor `V_r = rⁿ / det Γ` of the lattice `Γ = Bℤⁿ` (Gao–Han–Hu, *Gaussian Difference Dynamics: Breaking the 2^{n/2} Barrier for the Shortest Vector Problem and Discrete Gaussian Sampling*, arXiv:2611.04336 (held version, sha256 233bf8bb…0692), (7), p.18).

**Formalization Note.** A full-rank lattice is given by a basis matrix `B` (`B.det ≠ 0` is
assumed wherever this is used) and `det Γ = |det B|`. -/
noncomputable def volFactor {n : ℕ} (B : Matrix (Fin n) (Fin n) ℝ) (r : ℝ) : ℝ :=
  r ^ n / |B.det|

end GaussDiffSVP


