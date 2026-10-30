-- Prove2me | Definitions.Def_GeometricDL_GroupAverage_groupAverage
-- name    : GeometricDL_GroupAverage_groupAverage
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T03:10:35.126172+00:00
-- url     : https://prove2.me/theorems/e6eb88d0-add7-44b4-8cc0-be8f9ced9ed3
-- title:
--   $\mathfrak G$-average $Ax = \frac{1}{\mu(\mathfrak G)}\int_{\mathfrak G} \mathfrak g.x \, d\mu(\mathfrak g)$
-- statement:
--   Let $\mu$ be a measure on a group $\mathfrak G$ and $\rho$ a representation of $\mathfrak G$ on a real normed space $E$. The **$\mathfrak G$-average** of a signal $x \in E$ is
--   $$Ax = \frac{1}{\mu(\mathfrak G)} \int_{\mathfrak G} \rho(\mathfrak g)x \, d\mu(\mathfrak g),$$
--   the integral of the orbit $\mathfrak g \mapsto \rho(\mathfrak g)x$ over the whole group, normalised by the total mass. In the paper $\mu$ is the Haar measure of $\mathfrak G$; for images under translation, $Ax$ is the average colour of the image.
--
--   The $\mathfrak G$-average is the operator through which every linear $\mathfrak G$-invariant function factors.
--
--   **Formalization Note** $1/\mu(\mathfrak G)$ is `(μ Set.univ).toReal⁻¹` and the integral is the Bochner integral. The definition accepts any measure and any signal; Lean's integral is $0$ for a non-integrable orbit, so the theorems that use $A$ assume $\mu$ finite and nonzero and the orbit of each signal integrable.
-- source:
--   Bronstein, Bruna, Cohen, Veličković, Geometric Deep Learning: Grids, Groups, Graphs, Geodesics, and Gauges, arXiv:2104.13478v2, §3.5, unnumbered, p. 27 (PDF p. 31), definition of the G-average after the display; side note on the Haar measure, p. 27

import Mathlib
open MeasureTheory

namespace GeometricDL.GroupAverage

/-- **The G-average `Ax = (1/µ(G)) ∫_G (g.x) dµ(g)` (§3.5, p. 27).**
Bronstein, Bruna, Cohen & Veličković, *Geometric Deep Learning: Grids, Groups, Graphs, Geodesics,
and Gauges*, arXiv:2104.13478v2, §3.5, unnumbered, printed p. 27 (PDF p. 31): "which indicates
that F only depends on x through the G-average Ax = (1/µ(G)) ∫_G (g.x)dµ(g)." Side note, same
page: "Here, µ(g) is known as the Haar measure of the group G, and the integral is performed over
the entire group."

For a measure `μ` on `G`, a representation `ρ : G →* (E →L[ℝ] E)` and a signal `x : E`,
`groupAverage μ ρ x = (μ G)⁻¹ • ∫ g, ρ g x ∂μ`, the Bochner integral of the orbit `g ↦ ρ g x`
over the whole group, divided by the total mass.

**Formalization Note.** `1/µ(G)` is `(μ Set.univ).toReal⁻¹` and `g.x` is `ρ g x`. The definition
takes any measure; the theorems that use it assume `μ` finite and nonzero, so the normalisation is
the paper's. Lean's Bochner integral is `0` when the orbit is not integrable (or `E` is not
complete), so every theorem about `groupAverage` assumes the integrability of the orbit of each
signal it is applied to; the definition itself builds in no such hypothesis. -/
noncomputable def groupAverage {G : Type*} [Group G] [MeasurableSpace G]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (μ : Measure G) (ρ : G →* (E →L[ℝ] E)) (x : E) : E :=
  (μ Set.univ).toReal⁻¹ • ∫ g, ρ g x ∂μ

end GeometricDL.GroupAverage


