-- Prove2me | Definitions.Def_PerspEpi_horizonFn
-- name    : PerspEpi_horizonFn
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T04:50:12.758188+00:00
-- url     : https://prove2.me/theorems/13729ead-afaa-46b3-96c2-62bb27ed1148
-- title:
--   Horizon function $f^\infty$
-- statement:
--   The **horizon function** of $f \in \Gamma_0(E)$ is the function $f^\infty : E \to \overline{\mathbb R}$ with $\operatorname{epi} f^\infty = (\operatorname{epi} f)^\infty$, i.e.
--
--   $$
--   f^\infty(y) = \inf\{\alpha \in \mathbb R \mid (y,\alpha) \in (\operatorname{epi} f)^\infty\}\qquad(\inf\emptyset = +\infty).
--   $$
--
--   It is closed, proper, convex and positively homogeneous, and it is the limit of the epi-multiples $\lambda\star f$ as $\lambda\downarrow 0$ (Lemma 1).
--
--   **Formalization Note** $\operatorname{epi} f$ is the published `ShortestGCS.MICP.epigraph f`. For $f\in\Gamma_0(E)$ the cone $(\operatorname{epi} f)^\infty$ is closed and is an epigraph, so the infimum recovers the function whose epigraph it is.
-- source:
--   Friedlander, Goodwin, Hoheisel, From perspective maps to epigraphical projections, arXiv:2102.06809v1, §1.2 Notation, p.4

import Mathlib
import Definitions.Def_ShortestGCS_MICP_PerspectiveFun
import Definitions.Def_PerspEpi_horizonCone

namespace PerspEpi

/-- **Horizon function** `f^∞`. Friedlander, Goodwin, Hoheisel, *From perspective maps to epigraphical projections*, arXiv:2102.06809v1, §1.2 Notation, p.4: "The horizon function of
f ∈ Γ0(E) is the closed proper convex and positively homogeneous function f^∞ : E → R̄ defined via
epi f^∞ = (epi f)^∞."

`horizonFn f y = inf {α ∈ ℝ | (y, α) ∈ (epi f)^∞}`, the function whose epigraph is
`(epi f)^∞`.

**Formalization Note.** For `f ∈ Γ0(E)` the cone `(epi f)^∞` is closed and is an epigraph
(Rockafellar–Wets, Theorem 3.21), so the infimum is attained when finite and `epi f^∞ = (epi f)^∞`.
The infimum of the empty set is `⊤ = +∞`. `epi f ⊆ E × ℝ` is the published
`ShortestGCS.MICP.epigraph f = {(x, α) | f x ≤ α}`; only its set and the product topology enter. -/
noncomputable def horizonFn {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : E → EReal) (y : E) : EReal :=
  sInf ((fun a : ℝ => (a : EReal)) '' {a | (y, a) ∈ horizonCone (ShortestGCS.MICP.epigraph f)})

end PerspEpi


