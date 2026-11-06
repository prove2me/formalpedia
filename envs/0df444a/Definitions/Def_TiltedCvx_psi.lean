-- Prove2me | Definitions.Def_TiltedCvx_psi
-- name    : TiltedCvx_psi
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T01:39:09.629586+00:00
-- url     : https://prove2.me/theorems/dfc34c88-dd62-4781-af66-ac07d8452097
-- title:
--   The tilt $\psi_\gamma$
-- statement:
--   For $\gamma\in(0,1]$ the **tilt** $\psi_\gamma:\overline{\mathbb R}\to\overline{\mathbb R}$ multiplies positive numbers by $\gamma$ and divides negative numbers by $\gamma$:
--
--   $$
--   \psi_\gamma(z):=\gamma^{\operatorname{sign}(z)}\,z=\min\{\gamma z,\ \gamma^{-1}z\}.
--   $$
--
--   For $\gamma=0$ it is $\psi_0(z)=0$ if $z>0$, $\psi_0(z)=-\infty$ if $z<0$, and $\psi_0(0)$ is undefined. In particular $\psi_\gamma(\pm\infty)=\pm\infty$ for $\gamma>0$, and $\psi_1$ is the identity.
--
--   Applying $\psi_\gamma$ to the right-hand side of the support inequality, of the monotonicity inequality and of the secant-slope inequality of convexity gives the three tilted classes of the mission.
--
--   **Formalization Note** For $\gamma\ne0$ the value is `min (γ z) (γ⁻¹ z)` in `EReal`. The undefined value $\psi_0(0)$ is stored as the placeholder $0$; every statement that evaluates a tilt carries the hypothesis `TiltDefined γ z` ("whenever defined"), so the placeholder never decides anything.
-- source:
--   Pedramfar–Khanna–Quinn–Aggarwal, Tilted Convexity and an Exact Offline–Online Separation, arXiv:2611.03472, §3, p.12

import Mathlib

namespace TiltedCvx

/-- **The tilt `ψγ`.** Pedramfar–Khanna–Quinn–Aggarwal, arXiv:2611.03472, §3, p.12: for
`γ ∈ (0, 1]`, `ψγ(z) := γ^{sign(z)} z = min{γz, γ⁻¹z}` over the extended reals; for `γ = 0`,
`ψ₀(z) := 0` if `z > 0`, undefined if `z = 0`, `−∞` if `z < 0`.

**Formalization Note** For `γ ≠ 0` the value is `min (γ z) (γ⁻¹ z)` in `EReal`, so
`ψγ(±∞) = ±∞` for `γ > 0`. The undefined value `ψ₀(0)` is given the placeholder `0`; every
statement that evaluates a tilt carries the hypothesis `TiltDefined γ z`, so this placeholder
never decides anything. Only `γ ∈ [0, 1]` is used. -/
noncomputable def psi (γ : ℝ) (z : EReal) : EReal :=
  if γ = 0 then (if 0 < z then 0 else if z < 0 then ⊥ else 0)
  else min ((γ : EReal) * z) ((γ⁻¹ : ℝ) * z)

end TiltedCvx


