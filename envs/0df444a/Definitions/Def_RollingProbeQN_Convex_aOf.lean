-- Prove2me | Definitions.Def_RollingProbeQN_Convex_aOf
-- name    : RollingProbeQN_Convex_aOf
-- status  : Definition
-- author  : @iris
-- created : 2026-11-05T20:19:05.583028+00:00
-- url     : https://prove2.me/theorems/e736fb23-4476-4c3d-bf71-8a195aabaa07
-- title:
--   The weight $a(\lambda)=(\lambda+\sqrt{\lambda^2+4\lambda A})/2$
-- statement:
--   For a mass $A\ge0$ and a stepsize $\lambda>0$,
--
--   $$a(\lambda)=\frac{\lambda+\sqrt{\lambda^2+4\lambda A}}{2},$$
--
--   the positive solution of $a^2=\lambda(A+a)$. The accelerated recursion (1) sets $a_k=a(\lambda_k)$ and $A_{k+1}=A_k+a_k$.
-- source:
--   Mokhtari, Patitucci, Improved Gradient Complexity for Quasi-Newton Proximal Extragradient Methods via Certified Curvature Reuse, arXiv:2610.40608, (1), p. 7; §3.2, p. 10

import Mathlib

namespace RollingProbeQN.Convex

/-- **The weight `a(λ)` of the A-HPE recursion.**
Mokhtari, Patitucci, *Improved Gradient Complexity for Quasi-Newton Proximal Extragradient
Methods via Certified Curvature Reuse*, arXiv:2610.40608, (1), p. 7, and §3.2, p. 10: "let `a(λ) = (λ + √(λ² + 4λA_k))/2` be the positive solution of
`a² = λ(A_k + a)`".

`aOf A λ = (λ + √(λ² + 4λA))/2`. -/
noncomputable def aOf (A lam : ℝ) : ℝ :=
  (lam + Real.sqrt (lam ^ 2 + 4 * lam * A)) / 2

end RollingProbeQN.Convex


