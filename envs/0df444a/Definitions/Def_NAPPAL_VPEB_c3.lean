-- Prove2me | Definitions.Def_NAPPAL_VPEB_c3
-- name    : NAPPAL_VPEB_c3
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-29T18:16:16.711806+00:00
-- url     : https://prove2.me/theorems/7c315dc0-fd8b-4012-a11d-d39d0bdaa3ff
-- title:
--   The constant $c_3$ of Lemma 4.3
-- statement:
--   $$c_3 = \min\Big\{ \frac12,\ c_4,\ \frac{1}{3\gamma} \Big\}.$$
--   It is the sufficient-decrease constant of the potential $\Lambda^k$ in (19).
-- source:
--   Zhu, Zhao, Zhang, A First-Order Primal-Dual Method for Nonconvex Constrained Optimization Based on the Augmented Lagrangian, arXiv:2007.12219v1, Lemma 4.3, p. 15

import Mathlib
import Definitions.Def_NAPPAL_VPEB_Problem
import Definitions.Def_NAPPAL_VPEB_Params
import Definitions.Def_NAPPAL_VPEB_c4

namespace NAPPAL.VPEB

/-- **The constant `c₃` of Lemma 4.3.**
Zhu, Zhao, Zhang, *A First-Order Primal-Dual Method for Nonconvex Constrained Optimization
Based on the Augmented Lagrangian*, arXiv:2007.12219v1, Lemma 4.3, p. 15: "c3 := min{1/2, c4, 1/(3γ)}". -/
noncomputable def c3 {n d m : ℕ} (P : Problem n d m) (A : Params n) : ℝ :=
  min (1 / 2) (min (c4 P A) (1 / (3 * A.γ)))

end NAPPAL.VPEB


