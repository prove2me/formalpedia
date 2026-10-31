-- Prove2me | Definitions.Def_LeGallBrownianMap_lambdaP
-- name    : LeGallBrownianMap_lambdaP
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T02:36:38.927479+00:00
-- url     : https://prove2.me/theorems/a13ff4aa-15b8-4416-b2d1-953daccc60dc
-- title:
--   The constant $\lambda_p$
-- statement:
--   For $p\ge2$, $\lambda_p=\tfrac12\sqrt{p/(p-1)}$, the factor by which $n^{-1/2}$ times the contour function of a uniform labeled $p$-tree converges to the normalized excursion.
-- source:
--   Le Gall, Uniqueness and universality of the Brownian map, arXiv:1105.4842v2, §2.5, p.16

import Mathlib

namespace LeGallBrownianMap

/-- Le Gall, *Uniqueness and universality of the Brownian map*, arXiv:1105.4842v2, §2.5, p.16:
"To simplify notation, we set λ_p = ½ √(p/(p − 1))". Used for `p ≥ 2`. -/
noncomputable def lambdaP (p : ℕ) : ℝ := (1 / 2) * Real.sqrt ((p : ℝ) / ((p : ℝ) - 1))

end LeGallBrownianMap


