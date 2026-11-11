-- Prove2me | Definitions.Def_GaussDiffSVP_rateJ
-- name    : GaussDiffSVP_rateJ
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T21:57:42.875227+00:00
-- url     : https://prove2.me/theorems/7d41a94d-de47-4acb-93d9-9cd2ecccfbba
-- title:
--   Gaussian shell cost $J(z) = (z-1-\log z)/(2\log 2)$
-- statement:
--   $$J(z) = \frac{z-1-\log z}{2\log 2},\qquad z>0,$$
--   with the natural logarithm. $J(a)\,n$ is, to leading order, the $\log_2$ of the factor by which the Gaussian mass of the shell of energy $a$ falls below the total mass.
-- source:
--   Gao–Han–Hu, Gaussian Difference Dynamics: Breaking the 2^{n/2} Barrier for the Shortest Vector Problem and Discrete Gaussian Sampling, arXiv:2611.04336 (held version, sha256 233bf8bb…0692), (8), p.19; p.6

import Mathlib

namespace GaussDiffSVP

/-- The Gaussian shell cost `J(z) = (z − 1 − log z) / (2 log 2)` (Gao–Han–Hu, *Gaussian Difference Dynamics: Breaking the 2^{n/2} Barrier for the Shortest Vector Problem and Discrete Gaussian Sampling*, arXiv:2611.04336 (held version, sha256 233bf8bb…0692), (8), p.19; also p.6).
"All logarithms without a subscript are natural" (p.17).

**Formalization Note.** Used only at `z > 0`, where `Real.log` is the natural logarithm. -/
noncomputable def rateJ (z : ℝ) : ℝ := (z - 1 - Real.log z) / (2 * Real.log 2)

end GaussDiffSVP


