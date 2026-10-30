-- Prove2me | Definitions.Def_NAPPAL_VPEB_Assumption2
-- name    : NAPPAL_VPEB_Assumption2
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-29T18:06:57.237148+00:00
-- url     : https://prove2.me/theorems/7fabeda2-f324-47d2-9988-3e8c2fd5bfd0
-- title:
--   Assumption 2 and the parameter ranges of NAPP-AL
-- statement:
--   The parameters satisfy **Assumption 2** (with the ranges of the NAPP-AL box) if:
--
--   1. $K$ is differentiable on $\mathbb{R}^n$, $\beta$-strongly convex with $\beta > 0$, and $\|\nabla K(x) - \nabla K(y)\| \le L_K \|x - y\|$ with $L_K \ge 0$;
--   2. $\gamma > 0$ and
--   $$\gamma > \frac{\sqrt{57} + 1}{2\lambda_{\min}(B^\top B)}\,(L_G + L_H);$$
--   3. $0 < \sigma < 1$.
--
--   **Formalization Note** Strong convexity is $K(ax + by) \le aK(x) + bK(y) - ab\frac{\beta}{2}\|x - y\|^2$ for $a, b \ge 0$, $a + b = 1$, the convention under which the paper uses $D(u,u') \ge \frac{\beta}{2}\|u - u'\|^2$ in (14).
-- source:
--   Zhu, Zhao, Zhang, A First-Order Primal-Dual Method for Nonconvex Constrained Optimization Based on the Augmented Lagrangian, arXiv:2007.12219v1, Assumption 2, p. 9 and NAPP-AL box, p. 8

import Mathlib
import Definitions.Def_NAPPAL_VPEB_lamMin
import Definitions.Def_NAPPAL_VPEB_Problem
import Definitions.Def_NAPPAL_VPEB_Params

namespace NAPPAL.VPEB

/-- **Assumption 2 together with the parameter ranges of NAPP-AL.**
Zhu, Zhao, Zhang, *A First-Order Primal-Dual Method for Nonconvex Constrained Optimization
Based on the Augmented Lagrangian*, arXiv:2007.12219v1, Assumption 2, p. 9:
"(i) K is strongly convex with parameter β and differentiable with its gradient Lipschitz
continuous with parameter LK on Rn.
(ii) Parameter γ is chosen to satisfy: γ > (√57 + 1)/(2λmin(B⊤B)) (LG + LH)."
and the NAPP-AL box, p. 8: "γ > 0, β, 0 < σ < 1".

The fields: `K` differentiable, `β`-strongly convex on `ℝⁿ` with `β > 0`, `∇K` is
`L_K`-Lipschitz with `L_K ≥ 0`; `γ > 0` and `γ > (√57 + 1)/(2λ_min(BᵀB)) · (L_G + L_H)`;
`0 < σ < 1`.

**Formalization Note.** Strong convexity is Mathlib's `StrongConvexOn Set.univ β K`:
`K(ax + by) ≤ aK(x) + bK(y) − ab(β/2)‖x − y‖²`, the convention under which the paper's (14)
uses `D(u, u′) ≥ (β/2)‖u − u′‖²`. "Strongly convex with parameter β" entails `β > 0`. -/
structure Assumption2 {n d m : ℕ} (P : Problem n d m) (A : Params n) : Prop where
  K_differentiable : Differentiable ℝ A.K
  K_strongConvex : StrongConvexOn Set.univ A.β A.K
  β_pos : 0 < A.β
  LK_nonneg : 0 ≤ A.LK
  K_gradient_lipschitz : ∀ x y : EuclideanSpace ℝ (Fin n),
    ‖gradient A.K x - gradient A.K y‖ ≤ A.LK * ‖x - y‖
  γ_pos : 0 < A.γ
  γ_large : (Real.sqrt 57 + 1) / (2 * lamMin P.B) * (P.LG + P.LH) < A.γ
  σ_pos : 0 < A.σ
  σ_lt_one : A.σ < 1

end NAPPAL.VPEB


