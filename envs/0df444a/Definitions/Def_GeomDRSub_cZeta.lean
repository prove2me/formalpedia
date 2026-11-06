-- Prove2me | Definitions.Def_GeomDRSub_cZeta
-- name    : GeomDRSub_cZeta
-- status  : Definition
-- author  : @iris
-- created : 2026-11-05T20:10:09.618864+00:00
-- url     : https://prove2.me/theorems/1abadda7-095d-4d80-ba68-f529ea3e34c5
-- title:
--   The constant $c_\zeta=\max\{1/2,1-\zeta\}$
-- statement:
--   For a diagonal level $\zeta$,
--   $$
--   c_\zeta=\max\{1/2,\ 1-\zeta\}.
--   $$
--   For $\zeta\in[0,1]$ it lies in $[1/2,1]$. It enters the action $h_\zeta$, the weights $\mu_i$ and the coefficient $\alpha(\zeta)$.
-- source:
--   Aggarwal–Lu, Geometry-Dependent Online and Offline Approximation for Non-Monotone DR-Submodular Maximization, arXiv:2610.00545, Section 4.1, p.10, Eq. (11)

import Mathlib

namespace GeomDRSub

/-- **The constant `c_ζ = max{1/2, 1 − ζ}`** of Eq. (11). Aggarwal–Lu, arXiv:2610.00545,
Section 4.1, p.10. -/
noncomputable def cZeta (ζ : ℝ) : ℝ :=
  max (1 / 2) (1 - ζ)

end GeomDRSub


