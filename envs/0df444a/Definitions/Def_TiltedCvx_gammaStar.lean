-- Prove2me | Definitions.Def_TiltedCvx_gammaStar
-- name    : TiltedCvx_gammaStar
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T01:42:15.165753+00:00
-- url     : https://prove2.me/theorems/08ef9b85-1fbd-4d14-bb11-084259f03754
-- title:
--   Optimal tilted-convexity parameter $\gamma^*(f)$
-- statement:
--   For a proper lsc $f$,
--
--   $$
--   \gamma^*(f):=\sup\{\gamma\in[0,1] : f \text{ is } \gamma\text{–tilted convex}\},\qquad \sup\emptyset:=0 .
--   $$
--
--   **Formalization Note** A real supremum of a subset of $[0,1]$; Mathlib's `sSup ∅ = 0` is the paper's convention, and the set is bounded by $1$, so $\gamma^*(f)\in[0,1]$ always.
-- source:
--   Pedramfar–Khanna–Quinn–Aggarwal, Tilted Convexity and an Exact Offline–Online Separation, arXiv:2611.03472, Definition 3, p.13

import Mathlib
import Definitions.Def_TiltedCvx_TiltedConvex

namespace TiltedCvx

/-- **The optimal parameter `γ*(f)`.** Pedramfar–Khanna–Quinn–Aggarwal, arXiv:2611.03472,
Definition 3, p.13: `γ*(f) := sup{γ ∈ [0, 1] : f is γ–tilted convex}`, with `sup ∅ := 0`.

**Formalization Note** A real `sSup` of a subset of `[0, 1]`: the set is bounded above by `1`,
and Mathlib's `sSup ∅ = 0` is the paper's convention `sup ∅ := 0`. The paper defines `γ*` for
proper lsc `f`; the theorems add those hypotheses. -/
noncomputable def gammaStar {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (f : E → EReal) : ℝ :=
  sSup {γ : ℝ | γ ∈ Set.Icc (0 : ℝ) 1 ∧ TiltedConvex γ f}

end TiltedCvx


