-- Prove2me | Definitions.Def_TiltedCvx_theta
-- name    : TiltedCvx_theta
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T01:40:08.573741+00:00
-- url     : https://prove2.me/theorems/3c8505b3-550b-4fc4-bb4d-66e58fe382db
-- title:
--   The extremal profile $\vartheta_\gamma$
-- statement:
--   For $\gamma\in(0,1]$ the function $\vartheta_\gamma:\mathbb R\to\overline{\mathbb R}$ is
--
--   $$
--   \vartheta_\gamma(s):=\begin{cases}\min\{s^{\gamma},\,1-(1-s)^{1/\gamma}\}, & s\in[0,1],\\ +\infty, & s\notin[0,1].\end{cases}
--   $$
--
--   It is the pointwise largest normalized $\gamma$–tilted convex function on $[0,1]$ (Theorem 13) and attains the sharp secant parameter $\eta(\gamma)$ (Example 3).
-- source:
--   Pedramfar–Khanna–Quinn–Aggarwal, Tilted Convexity and an Exact Offline–Online Separation, arXiv:2611.03472, Theorem 13, (11), p.22; Example 3, p.29

import Mathlib
import Definitions.Def_TiltedCvx_thetaProfile

namespace TiltedCvx

/-- **The extremal profile `ϑγ`.** Pedramfar–Khanna–Quinn–Aggarwal, arXiv:2611.03472,
Theorem 13, (11), p.22 and Example 3, p.29: `ϑγ(s) := min{s^γ, 1 − (1 − s)^{1/γ}}` for
`s ∈ [0, 1]` and `ϑγ(s) = +∞` for `s ∉ [0, 1]`.

**Formalization Note** A function `ℝ → EReal`; used for `γ ∈ (0, 1]`. -/
noncomputable def theta (γ : ℝ) (s : ℝ) : EReal :=
  if 0 ≤ s ∧ s ≤ 1 then ((thetaProfile γ s : ℝ) : EReal) else ⊤

end TiltedCvx


