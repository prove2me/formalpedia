-- Prove2me | Definitions.Def_TiltedCvx_TiltDefined
-- name    : TiltedCvx_TiltDefined
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T01:39:10.824938+00:00
-- url     : https://prove2.me/theorems/bddc053c-0853-4555-8b44-ae2df3e56c53
-- title:
--   When a tilt is defined
-- statement:
--   The tilts $\psi_\gamma(z)$ and $\bar\psi_\gamma(z)$ are defined for every $\gamma\in[0,1]$ and $z\in\overline{\mathbb R}$ except in the single case $\gamma=0$, $z=0$. The predicate
--
--   $$
--   \mathrm{TiltDefined}(\gamma,z)\ :\Longleftrightarrow\ \gamma\neq0\ \text{ or }\ z\neq0
--   $$
--
--   encodes the paper's recurring proviso "whenever the right-hand side is well-defined".
-- source:
--   Pedramfar–Khanna–Quinn–Aggarwal, Tilted Convexity and an Exact Offline–Online Separation, arXiv:2611.03472, §3, p.12

import Mathlib

namespace TiltedCvx

/-- **When a tilt is defined.** Pedramfar–Khanna–Quinn–Aggarwal, arXiv:2611.03472, §3, p.12:
`ψγ(z)` and `ψ̄γ(z)` are defined except when `γ = 0` and `z = 0`. This predicate encodes every
"whenever … is defined" of the paper. -/
def TiltDefined (γ : ℝ) (z : EReal) : Prop :=
  γ ≠ 0 ∨ z ≠ 0

end TiltedCvx


