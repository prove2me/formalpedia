-- Prove2me | Definitions.Def_RollingProbeQN_Convex_mOf
-- name    : RollingProbeQN_Convex_mOf
-- status  : Definition
-- author  : @iris
-- created : 2026-11-05T20:19:41.252734+00:00
-- url     : https://prove2.me/theorems/b89aa288-0a6b-42e2-b2da-3d798ecae59c
-- title:
--   The displacement $m(\lambda)=\zeta\,a(\lambda)/(A+a(\lambda))$ of (7)
-- statement:
--   For a mass $A$, a distance $\zeta=\|z_k-x_k\|$ and a stepsize $\lambda>0$,
--
--   $$m(\lambda)=\frac{a(\lambda)}{A+a(\lambda)}\,\zeta ,$$
--
--   which equals $\|y(\lambda)-x_k\|$, the distance from the gradient anchor $x_k$ to the extrapolated point. Subroutine 1.1 evaluates its surrogate through this closed form.
--
--   **Formalization Note** The first form of (7) is used. At $A=0$ it equals $\zeta$; along Algorithm 1, $A_k=0$ only at $k=0$, where $\zeta_0=0$, so $m\equiv0$ there as the page says.
-- source:
--   Mokhtari, Patitucci, Improved Gradient Complexity for Quasi-Newton Proximal Extragradient Methods via Certified Curvature Reuse, arXiv:2610.40608, (7), p. 10

import Mathlib
import Definitions.Def_RollingProbeQN_Convex_aOf

namespace RollingProbeQN.Convex

/-- **The displacement `m(λ)`, first form of (7).**
Mokhtari, Patitucci, *Improved Gradient Complexity for Quasi-Newton Proximal Extragradient
Methods via Certified Curvature Reuse*, arXiv:2610.40608, (7), p. 10: "`m(λ) = ‖y(λ) − x_k‖ = a(λ)/(A_k + a(λ)) · ζ_k`", with `ζ_k = ‖z_k − x_k‖`.

**Formalization Note.** The first form of (7) is used. At `A = 0` it equals `ζ`; along Algorithm 1,
`A_k = 0` only at `k = 0`, where `ζ_0 = ‖z_0 − x_0‖ = 0`, which is the paper's "`m ≡ 0` when
`A_k = 0`". -/
noncomputable def mOf (A ζ lam : ℝ) : ℝ :=
  ζ * aOf A lam / (A + aOf A lam)

end RollingProbeQN.Convex


