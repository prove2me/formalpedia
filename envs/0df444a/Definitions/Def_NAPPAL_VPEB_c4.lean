-- Prove2me | Definitions.Def_NAPPAL_VPEB_c4
-- name    : NAPPAL_VPEB_c4
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-29T18:15:28.742538+00:00
-- url     : https://prove2.me/theorems/6f9814d0-ab58-4049-a8ab-f4a6498c0274
-- title:
--   The constant $c_4$ of Lemma 4.3
-- statement:
--   $$c_4 = \frac{\gamma\lambda_{\min}(B^\top B) - (L_G + L_H)}{2} - c_2 .$$
--   Lemma 4.3 asserts $c_4 > 0$ under Assumption 2.
-- source:
--   Zhu, Zhao, Zhang, A First-Order Primal-Dual Method for Nonconvex Constrained Optimization Based on the Augmented Lagrangian, arXiv:2007.12219v1, Lemma 4.3, p. 15

import Mathlib
import Definitions.Def_NAPPAL_VPEB_lamMin
import Definitions.Def_NAPPAL_VPEB_Problem
import Definitions.Def_NAPPAL_VPEB_Params
import Definitions.Def_NAPPAL_VPEB_c2

namespace NAPPAL.VPEB

/-- **The constant `c₄` of Lemma 4.3.**
Zhu, Zhao, Zhang, *A First-Order Primal-Dual Method for Nonconvex Constrained Optimization
Based on the Augmented Lagrangian*, arXiv:2007.12219v1, Lemma 4.3, p. 15: "c4 := (γλmin(B⊤B) − (LG + LH))/2 − c2 (> 0)". -/
noncomputable def c4 {n d m : ℕ} (P : Problem n d m) (A : Params n) : ℝ :=
  (A.γ * lamMin P.B - (P.LG + P.LH)) / 2 - c2 P A

end NAPPAL.VPEB


