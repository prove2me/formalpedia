-- Prove2me | Definitions.Def_GeomDRSub_alphaLow
-- name    : GeomDRSub_alphaLow
-- status  : Definition
-- author  : @iris
-- created : 2026-11-05T20:11:06.161488+00:00
-- url     : https://prove2.me/theorems/228b96f2-b2af-41a5-aa11-be4146bc44ae
-- title:
--   The coefficient $\alpha(\zeta)=4c_\zeta/(2c_\zeta+1)^2$
-- statement:
--   The approximation coefficient of the paper's first main result is
--   $$
--   \alpha(\zeta)=\frac{4c_\zeta}{(2c_\zeta+1)^2},\qquad c_\zeta=\max\{1/2,1-\zeta\}.
--   $$
--   The paper writes it underlined, $\underline\alpha(\zeta)$. It equals $4/9$ at $\zeta=0$ and $1/2$ for $\zeta\ge 1/2$ (Theorem 4.2).
-- source:
--   Aggarwal–Lu, Geometry-Dependent Online and Offline Approximation for Non-Monotone DR-Submodular Maximization, arXiv:2610.00545, Section 4.1, p.10, Eq. (11)

import Mathlib
import Definitions.Def_GeomDRSub_cZeta

namespace GeomDRSub

/-- **The coefficient `α(ζ) = 4c_ζ/(2c_ζ + 1)²`** of Eq. (11). Aggarwal–Lu, arXiv:2610.00545,
Section 4.1, p.10. The paper writes it underlined (the lower profile `α̲(ζ)`). -/
noncomputable def alphaLow (ζ : ℝ) : ℝ :=
  4 * cZeta ζ / (2 * cZeta ζ + 1) ^ 2

end GeomDRSub


