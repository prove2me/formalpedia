-- Prove2me | Definitions.Def_NAPPAL_VPEB_c2
-- name    : NAPPAL_VPEB_c2
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-29T18:14:50.029798+00:00
-- url     : https://prove2.me/theorems/4906111a-7cd2-45cf-89a5-aa7837482bcb
-- title:
--   The constant $c_2$ of (18)
-- statement:
--   $$c_2 = \frac{7(L_G + L_H)^2}{\gamma\lambda_{\min}(B^\top B)} .$$
--   It weighs $\|v^{k-1} - v^k\|^2$ in the potential $\Lambda^k$.
-- source:
--   Zhu, Zhao, Zhang, A First-Order Primal-Dual Method for Nonconvex Constrained Optimization Based on the Augmented Lagrangian, arXiv:2007.12219v1, p. 14, after eq. (18)

import Mathlib
import Definitions.Def_NAPPAL_VPEB_lamMin
import Definitions.Def_NAPPAL_VPEB_Problem
import Definitions.Def_NAPPAL_VPEB_Params

namespace NAPPAL.VPEB

/-- **The constant `c₂` of (18).**
Zhu, Zhao, Zhang, *A First-Order Primal-Dual Method for Nonconvex Constrained Optimization
Based on the Augmented Lagrangian*, arXiv:2007.12219v1, p. 14, after (18): "c2 := 7(LG + LH)²/(γλmin(B⊤B))". -/
noncomputable def c2 {n d m : ℕ} (P : Problem n d m) (A : Params n) : ℝ :=
  7 * (P.LG + P.LH) ^ 2 / (A.γ * lamMin P.B)

end NAPPAL.VPEB


