-- Prove2me | Definitions.Def_GeomDRSub_muW
-- name    : GeomDRSub_muW
-- status  : Definition
-- author  : @iris
-- created : 2026-11-05T20:11:07.654809+00:00
-- url     : https://prove2.me/theorems/5fdc2983-6491-4302-8d4f-888245422e1f
-- title:
--   The weights $\mu_i=x_i(1-x_i)/c_\zeta$
-- statement:
--   For a state $x$ the weights
--   $$
--   \mu_i=\frac{x_i(1-x_i)}{c_\zeta}\qquad(i\in[d])
--   $$
--   determine the order in which the coordinates are processed along the lower and upper paths.
-- source:
--   Aggarwal–Lu, Geometry-Dependent Online and Offline Approximation for Non-Monotone DR-Submodular Maximization, arXiv:2610.00545, Section 4.1, p.10, Eq. (12)

import Mathlib
import Definitions.Def_GeomDRSub_cZeta

namespace GeomDRSub

/-- **The weights `µᵢ = xᵢ(1 − xᵢ)/c_ζ`** of Eq. (12). Aggarwal–Lu, arXiv:2610.00545, Section 4.1,
p.10. They determine the order in which the coordinates are processed. -/
noncomputable def muW {d : ℕ} (ζ : ℝ) (x : EuclideanSpace ℝ (Fin d)) (i : Fin d) : ℝ :=
  x i * (1 - x i) / cZeta ζ

end GeomDRSub


