-- Prove2me | Definitions.Def_NAPPAL_VPEB_hcoef
-- name    : NAPPAL_VPEB_hcoef
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-29T18:12:44.81942+00:00
-- url     : https://prove2.me/theorems/6558a55a-4fec-4923-ba7f-199d58c68994
-- title:
--   The factor $h(u^k,p^k)$ of Proposition 3.1
-- statement:
--   For a sequence $w^k$,
--   $$h(u^k,p^k) = \max\Big\{ 2L_G + \|q^k\|L_\Omega + \gamma\|B\|L^0_\Theta + \gamma(L^0_\Theta)^2 + \frac{L_K}{\sigma\delta_k},\ 2L_G + L_H + \gamma\|B\|L^0_\Theta,\ L^0_\Theta + \|B\| + \frac{1}{\gamma} \Big\}.$$
--   It is the coefficient in the subgradient bound of Proposition 3.1.
-- source:
--   Zhu, Zhao, Zhang, A First-Order Primal-Dual Method for Nonconvex Constrained Optimization Based on the Augmented Lagrangian, arXiv:2007.12219v1, Proposition 3.1, p. 9

import Mathlib
import Definitions.Def_NAPPAL_VPEB_W
import Definitions.Def_NAPPAL_VPEB_Problem
import Definitions.Def_NAPPAL_VPEB_Params
import Definitions.Def_NAPPAL_VPEB_qk
import Definitions.Def_NAPPAL_VPEB_deltaK

namespace NAPPAL.VPEB

/-- **The factor `h(u^k, p^k)` of Proposition 3.1.**
Zhu, Zhao, Zhang, *A First-Order Primal-Dual Method for Nonconvex Constrained Optimization
Based on the Augmented Lagrangian*, arXiv:2007.12219v1, Proposition 3.1, p. 9: "h(u^k, p^k) := max{2LG + ‖q^k‖LΩ + γ‖B‖L0Θ + γ(L0Θ)² + LK/(σδk),
2LG + LH + γ‖B‖L0Θ, L0Θ + ‖B‖ + 1/γ}."

`hcoef P A w k` is that maximum, with `q^k = qk P A w k`, `δ_k = deltaK P A w k` and
`L_Ω = Σ_j L_{Ω_j}`. -/
noncomputable def hcoef {n d m : ℕ} (P : Problem n d m) (A : Params n) (w : ℕ → W n d m)
    (k : ℕ) : ℝ :=
  max (2 * P.LG + ‖qk P A w k‖ * (∑ j, P.LΩj j) + A.γ * ‖P.B‖ * P.L0Θ + A.γ * P.L0Θ ^ 2 +
      A.LK / (A.σ * deltaK P A w k))
    (max (2 * P.LG + P.LH + A.γ * ‖P.B‖ * P.L0Θ) (P.L0Θ + ‖P.B‖ + 1 / A.γ))

end NAPPAL.VPEB


