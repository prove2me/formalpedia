-- Prove2me | Definitions.Def_GPhNGIDiffusion_OccupationCLT_Mollified
-- name    : GPhNGIDiffusion_OccupationCLT_Mollified
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-13T23:30:23.370154+00:00
-- url     : https://prove2.me/theorems/71b36553-81b7-4bef-8c53-e8905d721ad4
-- title:
--   (3.3), p. 13 — the mollifier ρ_ε and the mollified drift g_ε
-- statement:
--   For $0<\varepsilon<1$ the **mollifier** of $y\mapsto y^+$ is
--   $$
--   \rho_\varepsilon(y)=\begin{cases}0,& y<-\varepsilon,\\ y,& y>\varepsilon,\\ \dfrac{3\varepsilon}{16}-\dfrac{1}{16\varepsilon^3}y^4+\dfrac{3}{8\varepsilon}y^2+\dfrac12y,& |y|\le\varepsilon,\end{cases}
--   $$
--   and the **mollified drift** is
--   $$
--   g_\varepsilon(x)=-\beta p-Rx+\rho_\varepsilon(e'x)(R-\alpha I)p .
--   $$
--   The mollified diffusion (3.3) is $dX^\varepsilon_t=g_\varepsilon(X^\varepsilon_t)\,dt+\sigma\,dB_t$, driven by the same Brownian motion as (1.1).
--
--   The function $\rho_\varepsilon$ is $C^1$ with $\|\dot\rho_\varepsilon\|_\infty\le1$, so $g_\varepsilon$ is a smooth Lipschitz approximation of the piecewise-linear drift $g$; it is used to differentiate the diffusion in its starting point.
-- source:
--   Jin, Pang, Xu & Xu, An Approximation to the Invariant Measure of the Limiting Diffusion of G/Ph/n+GI Queues in the Halfin-Whitt Regime and Related Asymptotics, arXiv:2209.07361v1, p. 13, (3.3)

import Mathlib
import Definitions.Def_GPhNGIDiffusion_OccupationCLT_Model

namespace GPhNGIDiffusion.OccupationCLT

variable {d : ℕ}

/-- The mollifier of `y ↦ y⁺` on p. 13: for `0 < ε < 1`,
`ρ_ε(y) = 0` for `y < −ε`, `ρ_ε(y) = y` for `y > ε`, and
`ρ_ε(y) = 3ε/16 − y⁴/(16ε³) + 3y²/(8ε) + y/2` for `|y| ≤ ε`. -/
noncomputable def rho (ε y : ℝ) : ℝ :=
  if y < -ε then 0
  else if ε < y then y
  else 3 * ε / 16 - y ^ 4 / (16 * ε ^ 3) + 3 * y ^ 2 / (8 * ε) + y / 2

/-- The mollified drift (3.3): `g_ε(x) = −βp − Rx + ρ_ε(e′x)(R − αI)p`. -/
noncomputable def Model.gEps (M : Model d) (ε : ℝ) (x : E d) : E d :=
  -(M.β • M.pE) - mat M.R x + rho ε (eDot x) • mat (M.R - M.α • 1) M.pE

end GPhNGIDiffusion.OccupationCLT


