-- Prove2me | Definitions.Def_NAPPAL_VPEB_Problem_Theta
-- name    : NAPPAL_VPEB_Problem_Theta
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-29T18:04:41.693488+00:00
-- url     : https://prove2.me/theorems/f1f5446a-48d0-4d12-96a2-cd43defd3266
-- title:
--   The constraint map $\Theta = \Omega + \Phi$
-- statement:
--   For an instance of (P), the **constraint map** is
--   $$\Theta(u) = \Omega(u) + \Phi(u), \qquad u \in \mathbb{R}^n ,$$
--   so that the constraint of (P) reads $\Theta(u) + Bv = 0$.
-- source:
--   Zhu, Zhao, Zhang, A First-Order Primal-Dual Method for Nonconvex Constrained Optimization Based on the Augmented Lagrangian, arXiv:2007.12219v1, §1.1, p. 2

import Mathlib
import Definitions.Def_NAPPAL_VPEB_Problem

namespace NAPPAL.VPEB

/-- **The constraint map `Θ = Ω + Φ`.**
Zhu, Zhao, Zhang, *A First-Order Primal-Dual Method for Nonconvex Constrained Optimization
Based on the Augmented Lagrangian*, arXiv:2007.12219v1, §1.1, p. 2: "Θ(u) := Ω(u) + Φ(u), with Θ : Rn → Rm being a differentiable mapping".
The constraint of (P) is `Θ(u) + Bv = 0`. -/
def Problem.Theta {n d m : ℕ} (P : Problem n d m) (u : EuclideanSpace ℝ (Fin n)) :
    EuclideanSpace ℝ (Fin m) :=
  P.Ω u + P.Φ u

end NAPPAL.VPEB


