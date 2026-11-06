-- Prove2me | Definitions.Def_TiltedCvx_classF
-- name    : TiltedCvx_classF
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T01:42:29.284592+00:00
-- url     : https://prove2.me/theorems/716c4d31-06ad-4383-87e6-0b49ac9a6b81
-- title:
--   The class $\mathcal F^\gamma$
-- statement:
--   For $\gamma\in[0,1]$, $\mathcal F^\gamma$ is the class of proper lower semicontinuous $\gamma$–tilted convex functions $f:\mathbb R^d\to\overline{\mathbb R}$:
--
--   $$
--   \mathcal F^\gamma:=\{f \mid f \text{ proper, lsc, and } \gamma\text{–tilted convex}\}.
--   $$
--
--   $\mathcal F^1$ is the class of proper lsc convex functions.
-- source:
--   Pedramfar–Khanna–Quinn–Aggarwal, Tilted Convexity and an Exact Offline–Online Separation, arXiv:2611.03472, §4.1, p.13

import Mathlib
import Definitions.Def_TiltedCvx_IsProper
import Definitions.Def_TiltedCvx_TiltedConvex

namespace TiltedCvx

/-- **The class `F^γ`.** Pedramfar–Khanna–Quinn–Aggarwal, arXiv:2611.03472, §4.1, p.13: for
`γ ∈ [0, 1]`, `F^γ` is the class of proper lsc γ–tilted convex functions `f : ℝ^d → ℝ̄`. -/
def classF {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] (γ : ℝ) :
    Set (E → EReal) :=
  {f | IsProper f ∧ LowerSemicontinuous f ∧ TiltedConvex γ f}

end TiltedCvx


