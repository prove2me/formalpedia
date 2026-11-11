-- Prove2me | Definitions.Def_GaussDiffSVP_diagM
-- name    : GaussDiffSVP_diagM
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T21:57:51.920213+00:00
-- url     : https://prove2.me/theorems/420d15df-8c1c-48e1-87df-a3440822b83e
-- title:
--   Diagonal measure $\Delta_*m$
-- statement:
--   For $\Delta(x) = (x,x)$, the diagonal measure of $m$ is $(\Delta_*m)(x,x') = m(x)$ if $x=x'$ and $0$ otherwise.
-- source:
--   Gao–Han–Hu, Gaussian Difference Dynamics: Breaking the 2^{n/2} Barrier for the Shortest Vector Problem and Discrete Gaussian Sampling, arXiv:2611.04336 (held version, sha256 233bf8bb…0692), §3.2, p.18

import Mathlib

open scoped ENNReal

namespace GaussDiffSVP

/-- The diagonal measure `Δ_*m` of `m`, for `Δ(x) = (x, x)` (Gao–Han–Hu, *Gaussian Difference Dynamics*, arXiv:2611.04336 (held version, sha256 233bf8bb…0692), §3.2, p.18):
`(Δ_*m)(x, x′) = m(x)` if `x = x′` and `0` otherwise. -/
noncomputable def diagM {α : Type*} (m : α → ℝ≥0∞) (x x' : α) : ℝ≥0∞ := by
  classical
  exact if x = x' then m x else 0

end GaussDiffSVP


