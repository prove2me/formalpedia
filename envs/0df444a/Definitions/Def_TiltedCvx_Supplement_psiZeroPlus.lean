-- Prove2me | Definitions.Def_TiltedCvx_Supplement_psiZeroPlus
-- name    : TiltedCvx_Supplement_psiZeroPlus
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T13:21:20.253204+00:00
-- url     : https://prove2.me/theorems/94be4b0f-c57a-4ccc-a06e-a28e1d7db0f8
-- title:
--   The tilt $\psi_{0^+}$
-- statement:
--   The tilt $\psi_{0^+}:\overline{\mathbb R}\to\overline{\mathbb R}$ is
--
--   $$
--   \psi_{0^+}(z):=\begin{cases}0,&z\ge0,\\-\infty,&z<0.\end{cases}
--   $$
--
--   It differs from $\psi_0$ only at $z=0$, where $\psi_0$ is undefined and $\psi_{0^+}(0)=0$. Retaining the inequality at a zero inner product gives the endpoint $0^+$ (pseudoconvexity) instead of $0$ (quasiconvexity).
-- source:
--   Pedramfar–Khanna–Quinn–Aggarwal, Tilted Convexity and an Exact Offline–Online Separation, arXiv:2611.03472, p.17 (before Definition 12)

import Mathlib

namespace TiltedCvx.Supplement

/-- **The tilt `ψ_{0+}`.** Pedramfar–Khanna–Quinn–Aggarwal, arXiv:2611.03472, p.17 (before
Definition 12): `ψ_{0+}(z) := 0` if `z ≥ 0` and `−∞` if `z < 0`. It differs from `ψ₀` only at
`z = 0`, where `ψ₀` is undefined; `ψ_{0+}` is defined everywhere. -/
noncomputable def psiZeroPlus (z : EReal) : EReal :=
  if 0 ≤ z then 0 else ⊥

end TiltedCvx.Supplement


