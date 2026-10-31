-- Prove2me | Definitions.Def_LeGallBrownianMap_kappaP
-- name    : LeGallBrownianMap_kappaP
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T02:36:38.033423+00:00
-- url     : https://prove2.me/theorems/50cabbd5-84cf-4646-ad0c-8cbae5f6541b
-- title:
--   The constant $\kappa_p$
-- statement:
--   For $p\ge2$, $\kappa_p=\big(9/(4p(p-1))\big)^{1/4}$, the factor by which $n^{-1/4}$ times labels and distances converge. For $q=2p$ it equals $c_q$ of Theorem 1.1.
--
--   **Formalization Note** Real power $1/4$ (`Real.rpow`).
-- source:
--   Le Gall, Uniqueness and universality of the Brownian map, arXiv:1105.4842v2, §2.5, p.16

import Mathlib

namespace LeGallBrownianMap

/-- Le Gall, *Uniqueness and universality of the Brownian map*, arXiv:1105.4842v2, §2.5, p.16:
"κ_p = (9/(4p(p − 1)))^{1/4}". Used for `p ≥ 2`.

**Formalization Note.** `Real.rpow` with real exponent `1/4`; the base is positive for `p ≥ 2`.
For `q = 2p` this equals the constant `c_q` of Theorem 1.1. -/
noncomputable def kappaP (p : ℕ) : ℝ := (9 / (4 * (p : ℝ) * ((p : ℝ) - 1))) ^ (1 / 4 : ℝ)

end LeGallBrownianMap


