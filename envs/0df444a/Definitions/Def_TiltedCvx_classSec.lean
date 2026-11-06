-- Prove2me | Definitions.Def_TiltedCvx_classSec
-- name    : TiltedCvx_classSec
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T01:41:09.669342+00:00
-- url     : https://prove2.me/theorems/9ed74a09-5af1-4bbd-b65e-6b2867d34d4f
-- title:
--   The class $\mathcal F^\gamma_{\mathrm{sec}}$
-- statement:
--   For $\gamma\in[0,1]$, $\mathcal F^\gamma_{\mathrm{sec}}$ is the class of proper lsc $\gamma$–tilted secant convex functions $f:\mathbb R^d\to\overline{\mathbb R}$.
-- source:
--   Pedramfar–Khanna–Quinn–Aggarwal, Tilted Convexity and an Exact Offline–Online Separation, arXiv:2611.03472, §4.3, p.14

import Mathlib
import Definitions.Def_TiltedCvx_IsProper
import Definitions.Def_TiltedCvx_TiltedSecant

namespace TiltedCvx

/-- **The class `F^γ_sec`.** Pedramfar–Khanna–Quinn–Aggarwal, arXiv:2611.03472, §4.3, p.14: for
`γ ∈ [0, 1]`, `F^γ_sec` is the class of proper lsc γ–tilted secant convex functions
`f : ℝ^d → ℝ̄`. -/
def classSec {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] (γ : ℝ) :
    Set (E → EReal) :=
  {f | IsProper f ∧ LowerSemicontinuous f ∧ TiltedSecant γ f}

end TiltedCvx


