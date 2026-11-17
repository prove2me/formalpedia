-- Prove2me | Definitions.Def_TiltedCvx_Supplement_IsPseudoconvex
-- name    : TiltedCvx_Supplement_IsPseudoconvex
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T13:21:03.960138+00:00
-- url     : https://prove2.me/theorems/da0398dd-9268-40a7-a674-d4712f37fde1
-- title:
--   Pseudoconvexity, general form (Definition 10)
-- statement:
--   Following Hadjisavvas, Komlósi and Schaible, a proper, lower semicontinuous and radially continuous function $f:\mathbb R^d\to\overline{\mathbb R}$ is **pseudoconvex** if for all $x,y\in\operatorname{dom}(f)$ and every Clarke subgradient $v\in\overline\partial f(x)$,
--
--   $$
--   \langle y-x,v\rangle\ge0\ \Longrightarrow\ f(y)\ge f(x).
--   $$
--
--   For differentiable $f$ this is the classical condition with $v=\nabla f(x)$. It is the endpoint $0^+$ of the tilted-convexity scale (Theorem 3).
--
--   **Formalization Note** $\overline\partial f$ is the Clarke–Rockafellar subdifferential (the published `ClarkeStrat.Proj.ClarkeSubdiff`). The standing hypotheses proper, lsc and radially continuous are not part of the predicate; the theorems that use it carry them.
-- source:
--   Pedramfar–Khanna–Quinn–Aggarwal, Tilted Convexity and an Exact Offline–Online Separation, arXiv:2611.03472, Definition 10, p.16

import Mathlib
import Definitions.Def_TiltedCvx_effDom
import Definitions.Def_ClarkeStrat_Proj_Setting

open scoped InnerProductSpace
open ClarkeStrat.Proj

namespace TiltedCvx.Supplement

/-- **Pseudoconvexity (Definition 10, general form).** Pedramfar–Khanna–Quinn–Aggarwal,
arXiv:2611.03472, Definition 10, p.16: following [HKS05], a proper, lsc and radially continuous
`f : ℝ^d → ℝ̄` is pseudoconvex if, for all `x, y ∈ dom(f)` and `v ∈ ∂̄f(x)`,
`⟨y − x, v⟩ ≥ 0 ⟹ f(y) ≥ f(x)`.

**Formalization Note** `∂̄f` is the Clarke–Rockafellar subdifferential, the published
`ClarkeStrat.Proj.ClarkeSubdiff` (as in `TiltedCvx.TiltedConvex`). The standing hypotheses
"proper, lsc and radially continuous" are not part of this predicate; every statement that uses
it carries them. -/
def IsPseudoconvex {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (f : E → EReal) : Prop :=
  ∀ x ∈ TiltedCvx.effDom f, ∀ y ∈ TiltedCvx.effDom f, ∀ v ∈ ClarkeSubdiff f x,
    0 ≤ ⟪y - x, v⟫_ℝ → f x ≤ f y

end TiltedCvx.Supplement


