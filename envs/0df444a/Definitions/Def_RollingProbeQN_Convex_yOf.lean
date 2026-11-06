-- Prove2me | Definitions.Def_RollingProbeQN_Convex_yOf
-- name    : RollingProbeQN_Convex_yOf
-- status  : Definition
-- author  : @iris
-- created : 2026-11-05T20:19:48.482741+00:00
-- url     : https://prove2.me/theorems/f122fbf8-d12e-4c6c-b43e-1bad793e9fdc
-- title:
--   The extrapolated point $y(\lambda)=(A x+a(\lambda)z)/(A+a(\lambda))$
-- statement:
--   For a mass $A$, points $x,z$ and a stepsize $\lambda>0$,
--
--   $$y(\lambda)=\frac{A\,x+a(\lambda)\,z}{A+a(\lambda)},$$
--
--   a convex combination of $x$ and $z$ when $A\ge0$. The recursion (1) takes $y_k=y(\lambda_k)$ with $x=x_k$, $z=z_k$, $A=A_k$.
-- source:
--   Mokhtari, Patitucci, Improved Gradient Complexity for Quasi-Newton Proximal Extragradient Methods via Certified Curvature Reuse, arXiv:2610.40608, (1), p. 7; §3.2, p. 10

import Mathlib
import Definitions.Def_RollingProbeQN_Convex_aOf

namespace RollingProbeQN.Convex

/-- **The extrapolated point `y(λ)`.**
Mokhtari, Patitucci, *Improved Gradient Complexity for Quasi-Newton Proximal Extragradient
Methods via Certified Curvature Reuse*, arXiv:2610.40608, (1), p. 7, and §3.2, p. 10: "`y(λ) = (A_k x_k + a(λ) z_k)/(A_k + a(λ))`".

**Formalization Note.** Division by `A + a(λ)` is multiplication by its inverse; `A + a(λ) > 0`
whenever `A ≥ 0` and `λ > 0`. -/
noncomputable def yOf {d : ℕ} (A : ℝ) (x z : EuclideanSpace ℝ (Fin d)) (lam : ℝ) :
    EuclideanSpace ℝ (Fin d) :=
  (A + aOf A lam)⁻¹ • (A • x + aOf A lam • z)

end RollingProbeQN.Convex


