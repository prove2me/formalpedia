-- Prove2me | Definitions.Def_TiltedCvx_psiBar
-- name    : TiltedCvx_psiBar
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T01:39:07.824134+00:00
-- url     : https://prove2.me/theorems/98014090-a3e4-45df-9369-a83937807a4a
-- title:
--   The upper tilt $\bar\psi_\gamma$
-- statement:
--   For $\gamma\in(0,1]$ the **upper tilt** $\bar\psi_\gamma:\overline{\mathbb R}\to\overline{\mathbb R}$ is
--
--   $$
--   \bar\psi_\gamma(z):=\gamma^{-\operatorname{sign}(z)}\,z=\max\{\gamma z,\ \gamma^{-1}z\}.
--   $$
--
--   For $\gamma=0$ it is $\bar\psi_0(z)=+\infty$ if $z>0$, $\bar\psi_0(z)=0$ if $z<0$, and $\bar\psi_0(0)$ is undefined. It is the inverse of $\psi_\gamma$ for $\gamma>0$ and appears in the Jensen-type characterizations of tilted secant convexity.
--
--   **Formalization Note** For $\gamma\ne0$ the value is `max (γ z) (γ⁻¹ z)` in `EReal`; the undefined $\bar\psi_0(0)$ is the placeholder $0$, guarded by `TiltDefined` wherever it is used.
-- source:
--   Pedramfar–Khanna–Quinn–Aggarwal, Tilted Convexity and an Exact Offline–Online Separation, arXiv:2611.03472, §3, p.12

import Mathlib

namespace TiltedCvx

/-- **The upper tilt `ψ̄γ`.** Pedramfar–Khanna–Quinn–Aggarwal, arXiv:2611.03472, §3, p.12: for
`γ ∈ (0, 1]`, `ψ̄γ(z) := γ^{−sign(z)} z = max{γz, γ⁻¹z}` over the extended reals; for `γ = 0`,
`ψ̄₀(z) := ∞` if `z > 0`, undefined if `z = 0`, `0` if `z < 0`.

**Formalization Note** For `γ ≠ 0` the value is `max (γ z) (γ⁻¹ z)` in `EReal`. The undefined
value `ψ̄₀(0)` is given the placeholder `0`; statements that evaluate it carry
`TiltDefined γ z`. Only `γ ∈ [0, 1]` is used. -/
noncomputable def psiBar (γ : ℝ) (z : EReal) : EReal :=
  if γ = 0 then (if 0 < z then ⊤ else if z < 0 then 0 else 0)
  else max ((γ : EReal) * z) ((γ⁻¹ : ℝ) * z)

end TiltedCvx


