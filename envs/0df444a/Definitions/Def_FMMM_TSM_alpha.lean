-- Prove2me | Definitions.Def_FMMM_TSM_alpha
-- name    : FMMM_TSM_alpha
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T01:17:37.496778+00:00
-- url     : https://prove2.me/theorems/1a7132ad-8b5e-4d99-b947-3e8b5b41329f
-- title:
--   The ratio $\alpha = (1 - 2/e^2)/(4/3 - 2/(3e))$
-- statement:
--   The approximation ratio of the two suggested matchings algorithm is
--
--   $$\alpha = \frac{1 - \frac{2}{e^2}}{\frac43 - \frac{2}{3e}} \approx 0.67029,$$
--
--   where $e$ is Euler's number. It exceeds $1 - 1/e \approx 0.632$, the ratio of the one suggested matching algorithm.
-- source:
--   Feldman, Mehta, Mirrokni, Muthukrishnan, Online Stochastic Matching: Beating 1-1/e, arXiv:0905.4100v1, Theorem 5, p. 6 (definition of α)

import Mathlib

namespace FMMM.TSM

/-- **The ratio `α` of the TSM algorithm.**
Feldman, Mehta, Mirrokni, Muthukrishnan, *Online Stochastic Matching: Beating 1-1/e*,
arXiv:0905.4100v1, Theorem 5, p. 6: "α := (1 − 2/e²)/(4/3 − 2/(3e)) ≈ 0.67029".

`alpha = (1 − 2/e²) / (4/3 − 2/(3e))` with `e = exp 1`. -/
noncomputable def alpha : ℝ := (1 - 2 / Real.exp 2) / (4 / 3 - 2 / (3 * Real.exp 1))

end FMMM.TSM


