-- Prove2me | Definitions.Def_TiltedCvx_gammaMono
-- name    : TiltedCvx_gammaMono
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T01:41:29.061825+00:00
-- url     : https://prove2.me/theorems/6fa27a4c-d464-4f4a-aeb9-1cf04f3c8451
-- title:
--   Optimal monotonicity parameter $\gamma^*_{\mathrm{mono}}(f)$
-- statement:
--   For a proper lsc $f$,
--
--   $$
--   \gamma^*_{\mathrm{mono}}(f):=\sup\{\gamma\in[0,1] : \bar\partial f \text{ is } \gamma\text{–tilted monotone}\},\qquad \sup\emptyset:=0 .
--   $$
--
--   **Formalization Note** A real supremum of a subset of $[0,1]$, with `sSup ∅ = 0`.
-- source:
--   Pedramfar–Khanna–Quinn–Aggarwal, Tilted Convexity and an Exact Offline–Online Separation, arXiv:2611.03472, Definition 5, p.14

import Mathlib
import Definitions.Def_TiltedCvx_TiltedMonotone
import Definitions.Def_ClarkeStrat_Proj_Setting

open ClarkeStrat.Proj

namespace TiltedCvx

/-- **The optimal parameter `γ*_mono(f)`.** Pedramfar–Khanna–Quinn–Aggarwal, arXiv:2611.03472,
Definition 5, p.14: `γ*_mono(f) := sup{γ ∈ [0, 1] : ∂̄f is γ–tilted monotone}`, with
`sup ∅ := 0`.

**Formalization Note** A real `sSup` of a subset of `[0, 1]` (bounded by `1`; `sSup ∅ = 0`). `∂̄f`
is the published `ClarkeStrat.Proj.ClarkeSubdiff`. -/
noncomputable def gammaMono {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (f : E → EReal) : ℝ :=
  sSup {γ : ℝ | γ ∈ Set.Icc (0 : ℝ) 1 ∧ TiltedMonotone γ (ClarkeSubdiff f)}

end TiltedCvx


