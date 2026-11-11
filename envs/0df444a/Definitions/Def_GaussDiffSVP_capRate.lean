-- Prove2me | Definitions.Def_GaussDiffSVP_capRate
-- name    : GaussDiffSVP_capRate
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T21:57:43.715637+00:00
-- url     : https://prove2.me/theorems/0816ab8e-7daa-489c-8b42-09ae5c0d21bc
-- title:
--   Common cap rate $K_\tau(u) = -\tfrac12\log_2\big(1 - 2\tau^2/(1+u)\big)$
-- statement:
--   $$K_\tau(u) = -\tfrac12\log_2\Big(1-\frac{2\tau^2}{1+u}\Big),$$
--   the rate for two directions of correlation $u$ to enter a common cap of threshold $\tau$, defined whenever the logarithm has positive argument.
--
--   **Formalization Note** Every use is at a point where the argument is positive.
-- source:
--   Gao–Han–Hu, Gaussian Difference Dynamics: Breaking the 2^{n/2} Barrier for the Shortest Vector Problem and Discrete Gaussian Sampling, arXiv:2611.04336 (held version, sha256 233bf8bb…0692), (9), p.19

import Mathlib

namespace GaussDiffSVP

/-- The common cap rate `K_τ(u) = −½ log₂(1 − 2τ²/(1 + u))` (Gao–Han–Hu, *Gaussian Difference Dynamics: Breaking the 2^{n/2} Barrier for the Shortest Vector Problem and Discrete Gaussian Sampling*, arXiv:2611.04336 (held version, sha256 233bf8bb…0692), (9), p.19), "whenever the
logarithm has positive argument".

**Formalization Note.** `Real.logb` returns a junk value on a nonpositive argument; every
statement that uses `capRate τ u` does so only where `1 − 2τ²/(1 + u) > 0` (this is part of
its hypotheses or follows from them). -/
noncomputable def capRate (τ u : ℝ) : ℝ := -(1 / 2) * Real.logb 2 (1 - 2 * τ ^ 2 / (1 + u))

end GaussDiffSVP


