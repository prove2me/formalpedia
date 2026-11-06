-- Prove2me | Definitions.Def_TiltedCvx_eta
-- name    : TiltedCvx_eta
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T01:40:11.75638+00:00
-- url     : https://prove2.me/theorems/5e18daf9-8d11-40ef-93d4-7661bf4fe605
-- title:
--   The secant parameter $\eta(\gamma)$
-- statement:
--   For $\gamma\in(0,1]$,
--
--   $$
--   \eta(\gamma):=\Big(\frac{\tau_\gamma}{1-\tau_\gamma}\Big)^2,
--   $$
--
--   and $\eta(0):=0$ (Corollary 8). Theorem 22 shows $\mathcal F^\gamma\subseteq\mathcal F^{\eta(\gamma)}_{\mathrm{sec}}$, with $\gamma^2<\eta(\gamma)<\gamma$ for $\gamma\in(0,1)$ and $\eta(1)=1$.
-- source:
--   Pedramfar–Khanna–Quinn–Aggarwal, Tilted Convexity and an Exact Offline–Online Separation, arXiv:2611.03472, Theorem 22, p.27; Corollary 8, p.32

import Mathlib
import Definitions.Def_TiltedCvx_tau

namespace TiltedCvx

/-- **The secant parameter `η(γ)`.** Pedramfar–Khanna–Quinn–Aggarwal, arXiv:2611.03472,
Theorem 22, p.27: `η(γ) := (τγ/(1 − τγ))²` for `γ ∈ (0, 1]`; Corollary 8, p.32, extends it to
`[0, 1]` by `η(0) := 0`. -/
noncomputable def eta (γ : ℝ) : ℝ :=
  if γ = 0 then 0 else (tau γ / (1 - tau γ)) ^ 2

end TiltedCvx


