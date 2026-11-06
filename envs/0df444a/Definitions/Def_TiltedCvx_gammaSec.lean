-- Prove2me | Definitions.Def_TiltedCvx_gammaSec
-- name    : TiltedCvx_gammaSec
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T01:41:07.357288+00:00
-- url     : https://prove2.me/theorems/2a403305-772d-487f-9073-0522cfc512bc
-- title:
--   Optimal secant parameter $\gamma^*_{\mathrm{sec}}(f)$
-- statement:
--   For a function $f$,
--
--   $$
--   \gamma^*_{\mathrm{sec}}(f):=\sup\{\gamma\in[0,1] : f \text{ is } \gamma\text{–tilted secant convex}\},\qquad \sup\emptyset:=0 .
--   $$
--
--   **Formalization Note** A real supremum of a subset of $[0,1]$, with `sSup ∅ = 0`.
-- source:
--   Pedramfar–Khanna–Quinn–Aggarwal, Tilted Convexity and an Exact Offline–Online Separation, arXiv:2611.03472, Definition 6, p.14

import Mathlib
import Definitions.Def_TiltedCvx_TiltedSecant

namespace TiltedCvx

/-- **The optimal parameter `γ*_sec(f)`.** Pedramfar–Khanna–Quinn–Aggarwal, arXiv:2611.03472,
Definition 6, p.14: `γ*_sec(f) := sup{γ ∈ [0, 1] : f is γ–tilted secant convex}`, with
`sup ∅ := 0`.

**Formalization Note** A real `sSup` of a subset of `[0, 1]` (bounded by `1`; `sSup ∅ = 0`). -/
noncomputable def gammaSec {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (f : E → EReal) : ℝ :=
  sSup {γ : ℝ | γ ∈ Set.Icc (0 : ℝ) 1 ∧ TiltedSecant γ f}

end TiltedCvx


