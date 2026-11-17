-- Prove2me | Definitions.Def_TiltedCvx_Supplement_RadiallyContinuous
-- name    : TiltedCvx_Supplement_RadiallyContinuous
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T13:20:07.415516+00:00
-- url     : https://prove2.me/theorems/a94d4a1d-d8af-452c-9b7b-5160b1077a31
-- title:
--   Radial continuity (Definition 1)
-- statement:
--   A function $f:\mathbb R^d\to\overline{\mathbb R}$ is **radially continuous**, or continuous on lines, if for all $x,y\in\operatorname{dom}(f)$ the restriction of $f$ to the closed segment $[x,y]$ is continuous:
--
--   $$
--   f|_{[x,y]}\ \text{is continuous for all } x,y\in\operatorname{dom}(f).
--   $$
--
--   Radial continuity is the regularity under which the classical characterizations of quasiconvexity and pseudoconvexity through the Clarke subdifferential hold (Theorems 2 and 3).
--
--   **Formalization Note** Continuity of the restriction is `ContinuousOn f (segment ℝ x y)` for the order topology of $\overline{\mathbb R}$ (`EReal`). Convexity of $\operatorname{dom}(f)$ is not part of the definition.
-- source:
--   Pedramfar–Khanna–Quinn–Aggarwal, Tilted Convexity and an Exact Offline–Online Separation, arXiv:2611.03472, Definition 1, p.10

import Mathlib
import Definitions.Def_TiltedCvx_effDom

namespace TiltedCvx.Supplement

/-- **Radial continuity (Definition 1).** Pedramfar–Khanna–Quinn–Aggarwal, *Tilted Convexity and an
Exact Offline–Online Separation*, arXiv:2611.03472, Definition 1, p.10: `f : ℝ^d → ℝ̄` is radially
continuous, or continuous on lines, if, for all `x, y ∈ dom(f)`, the restriction of `f` to the
closed line segment `[x, y]` is continuous.

**Formalization Note** The ambient space is a real inner product space `E`; `ℝ̄` is `EReal` with
its order topology. "The restriction to `[x, y]` is continuous" is `ContinuousOn f (segment ℝ x y)`
(continuity for the subspace topology of the segment). Convexity of `dom f` is not part of the
definition. -/
def RadiallyContinuous {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (f : E → EReal) : Prop :=
  ∀ x ∈ effDom f, ∀ y ∈ effDom f, ContinuousOn f (segment ℝ x y)

end TiltedCvx.Supplement


