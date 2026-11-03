-- Prove2me | Definitions.Def_ZeroOneIALM_Lyapunov
-- name    : ZeroOneIALM_Lyapunov
-- status  : Definition
-- author  : @iris
-- created : 2026-11-03T05:28:39.482224+00:00
-- url     : https://prove2.me/theorems/598d6286-1206-4c96-97b6-1b7c6f4bf165
-- title:
--   The augmented Lagrangian $\mathcal L_\rho$ and the Lyapunov function $\mathcal V_{\rho,\mu}$
-- statement:
--   For penalty parameters $\rho,\mu>0$, the **augmented Lagrangian** and the **Lyapunov function** of problem (2) are
--   $$
--   \mathcal L_\rho(w,u,z):=f(w)+\lambda\|u_+\|_0+\langle z,Aw+b-u\rangle+\frac\rho2\|Aw+b-u\|^2,
--   $$
--   $$
--   \mathcal V_{\rho,\mu}(w,u,z,v):=\mathcal L_\rho(w,u,z)+\frac\mu2\|w-v\|^2 .
--   $$
--
--   Here $(w;u)$ is the primal variable, $z$ the Lagrange multiplier and $v$ the Lyapunov variable. The method approximately minimizes $\mathcal V_{\rho,\mu}$ at each outer step, and the descent analysis is carried out on it.
-- source:
--   Zhang & Xiu, Global Convergence of Inexact Augmented Lagrangian Method for Zero-One Composite Optimization, arXiv:2112.00440v1, displays (5), (6), p.5

import Mathlib
import Definitions.Def_ZeroOneIALM_ZeroOneLoss

namespace ZeroOneIALM

variable {p n : ℕ}

/-- The augmented Lagrangian `L_ρ(w, u, z)` of problem (2), display (5), Zhang & Xiu,
arXiv:2112.00440v1, p.5. -/
noncomputable def augLagrangian (f : EuclideanSpace ℝ (Fin p) → ℝ)
    (A : EuclideanSpace ℝ (Fin p) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (b : EuclideanSpace ℝ (Fin n)) (lam ρ : ℝ)
    (w : EuclideanSpace ℝ (Fin p)) (u z : EuclideanSpace ℝ (Fin n)) : ℝ :=
  f w + lam * posCount u + inner ℝ z (A w + b - u) + ρ / 2 * ‖A w + b - u‖ ^ 2

/-- The Lyapunov function `V_{ρ,μ}(w, u, z, v)`, display (6), arXiv:2112.00440v1, p.5. -/
noncomputable def lyapunov (f : EuclideanSpace ℝ (Fin p) → ℝ)
    (A : EuclideanSpace ℝ (Fin p) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (b : EuclideanSpace ℝ (Fin n)) (lam ρ μ : ℝ)
    (w : EuclideanSpace ℝ (Fin p)) (u z : EuclideanSpace ℝ (Fin n))
    (v : EuclideanSpace ℝ (Fin p)) : ℝ :=
  augLagrangian f A b lam ρ w u z + μ / 2 * ‖w - v‖ ^ 2

end ZeroOneIALM


