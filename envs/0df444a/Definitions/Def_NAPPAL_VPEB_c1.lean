-- Prove2me | Definitions.Def_NAPPAL_VPEB_c1
-- name    : NAPPAL_VPEB_c1
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-29T18:14:07.736707+00:00
-- url     : https://prove2.me/theorems/10c21c9d-0f1a-457a-8fbb-f226ef6a7cb4
-- title:
--   The constant $c_1$ of (18)
-- statement:
--   $$c_1 = \frac{7(L_G + \gamma\|B\|L^0_\Theta)^2}{\gamma\lambda_{\min}(B^\top B)} .$$
--   It weighs $\|u^{k-1} - u^k\|^2$ in the potential $\Lambda^k$.
-- source:
--   Zhu, Zhao, Zhang, A First-Order Primal-Dual Method for Nonconvex Constrained Optimization Based on the Augmented Lagrangian, arXiv:2007.12219v1, p. 14, after eq. (18)

import Mathlib
import Definitions.Def_NAPPAL_VPEB_lamMin
import Definitions.Def_NAPPAL_VPEB_Problem
import Definitions.Def_NAPPAL_VPEB_Params

namespace NAPPAL.VPEB

/-- **The constant `c₁` of (18).**
Zhu, Zhao, Zhang, *A First-Order Primal-Dual Method for Nonconvex Constrained Optimization
Based on the Augmented Lagrangian*, arXiv:2007.12219v1, p. 14, after (18): "c1 := 7(LG + γ‖B‖L0Θ)²/(γλmin(B⊤B))". -/
noncomputable def c1 {n d m : ℕ} (P : Problem n d m) (A : Params n) : ℝ :=
  7 * (P.LG + A.γ * ‖P.B‖ * P.L0Θ) ^ 2 / (A.γ * lamMin P.B)

end NAPPAL.VPEB


