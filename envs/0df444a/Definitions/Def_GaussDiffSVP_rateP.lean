-- Prove2me | Definitions.Def_GaussDiffSVP_rateP
-- name    : GaussDiffSVP_rateP
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T21:57:44.781965+00:00
-- url     : https://prove2.me/theorems/083ca950-3c85-4cd0-a60f-dcddb2733f67
-- title:
--   Angular pair and cap cost $P(u) = -\tfrac12\log_2(1-u^2)$
-- statement:
--   $$P(u) = -\tfrac12\log_2(1-u^2),\qquad |u|<1,$$
--   the exponential rate of the fraction of pairs of directions with correlation $u$ (and of a spherical cap).
-- source:
--   Gao–Han–Hu, Gaussian Difference Dynamics: Breaking the 2^{n/2} Barrier for the Shortest Vector Problem and Discrete Gaussian Sampling, arXiv:2611.04336 (held version, sha256 233bf8bb…0692), (8), p.19

import Mathlib

namespace GaussDiffSVP

/-- The angular pair and cap cost `P(u) = −½ log₂(1 − u²)` (Gao–Han–Hu, *Gaussian Difference Dynamics: Breaking the 2^{n/2} Barrier for the Shortest Vector Problem and Discrete Gaussian Sampling*, arXiv:2611.04336 (held version, sha256 233bf8bb…0692), (8), p.19).

**Formalization Note.** Used only for `|u| < 1`, where the argument is positive. -/
noncomputable def rateP (u : ℝ) : ℝ := -(1 / 2) * Real.logb 2 (1 - u ^ 2)

end GaussDiffSVP


