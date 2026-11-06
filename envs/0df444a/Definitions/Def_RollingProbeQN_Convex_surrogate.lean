-- Prove2me | Definitions.Def_RollingProbeQN_Convex_surrogate
-- name    : RollingProbeQN_Convex_surrogate
-- status  : Definition
-- author  : @iris
-- created : 2026-11-05T20:20:39.694228+00:00
-- url     : https://prove2.me/theorems/4f13f69a-d1ac-4c50-9a0c-1872d3af52ef
-- title:
--   The scalar surrogate $\widehat\Psi_k(\lambda)$ of (10)
-- statement:
--   For stored scalars $A=A_k$, $\zeta=\zeta_k$, $g=g_k$, $\bar E=\bar E_k$ and $\lambda>0$, with $m=m(\lambda)$,
--
--   $$\widehat\Psi_k(\lambda)=\lambda\min\{L_1,\bar E+L_2m\}+\frac{L_2g}{2}\lambda^2+\frac{L_2}{2}\lambda m+\frac{L_2\bar E}{2}\lambda^2m+\frac{L_2^2}{4}\lambda^2m^2 .$$
--
--   $\widehat\Psi_k(\lambda)\le\sigma$ certifies the relative proximal condition (2) without any gradient evaluation; Subroutine 1.1 bisects on it.
-- source:
--   Mokhtari, Patitucci, Improved Gradient Complexity for Quasi-Newton Proximal Extragradient Methods via Certified Curvature Reuse, arXiv:2610.40608, (10), p. 10

import Mathlib
import Definitions.Def_RollingProbeQN_Convex_mOf

namespace RollingProbeQN.Convex

/-- **The scalar surrogate `Ψ̂_k`, (10).**
Mokhtari, Patitucci, *Improved Gradient Complexity for Quasi-Newton Proximal Extragradient
Methods via Certified Curvature Reuse*, arXiv:2610.40608, (10), p. 10:
"`Ψ̂_k(λ) = λ min{L1, Ē_k + L2 m} + (L2 g_k/2) λ² + (L2/2) λ m + (L2 Ē_k/2) λ² m + (L2²/4) λ² m²`",
with `m = m(λ)` from (7).

`surrogate L₁ L₂ A ζ g Ē λ` is `Ψ̂_k(λ)` for the stored scalars `A = A_k`, `ζ = ζ_k`, `g = g_k`,
`Ē = Ē_k`. -/
noncomputable def surrogate (L₁ L₂ A ζ g Ebar lam : ℝ) : ℝ :=
  lam * min L₁ (Ebar + L₂ * mOf A ζ lam) + L₂ * g / 2 * lam ^ 2 + L₂ / 2 * lam * mOf A ζ lam
    + L₂ * Ebar / 2 * lam ^ 2 * mOf A ζ lam + L₂ ^ 2 / 4 * lam ^ 2 * mOf A ζ lam ^ 2

end RollingProbeQN.Convex


