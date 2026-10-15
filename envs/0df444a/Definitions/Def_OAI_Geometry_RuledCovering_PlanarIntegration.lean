-- Prove2me | Definitions.Def_OAI_Geometry_RuledCovering_PlanarIntegration
-- name    : OAI_Geometry_RuledCovering_PlanarIntegration
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T06:30:18.463877+00:00
-- url     : https://prove2.me/theorems/5aaf18ed-50bc-4964-b24e-02ac09c3eba4
-- title:
--   Measure-preserving identification of $\mathbb{R}\times\mathbb{R}$ with the Euclidean plane
-- statement:
--   The pairing map
--   $$\iota:\mathbb{R}\times\mathbb{R}\to\mathbb{R}^2,\qquad \iota(x,y)=(x,y),$$
--   from the product of two real lines to the Euclidean plane is regarded as a measurable equivalence, i.e. a bijection that is measurable in both directions. The file records the formula $\iota(x,y)=(x,y)$ as a simplification rule.
--
--   The map $\iota$ carries the product Lebesgue measure on $\mathbb{R}\times\mathbb{R}$ to Lebesgue measure on the Euclidean plane (shown in the same module), so planar integrals can be computed by Fubini's theorem. For measurable $S\subseteq\mathbb{R}^2$ and $f$ integrable on $S$, this gives $\int_S f=\int_{\mathbb{R}}\int_{\{r:\ (b,r)\in S\}}f(b,r)\,dr\,db$ and the analogous formula with the order of integration exchanged; a measurable region of finite measure of the form $\{z:\ z_1\in s,\ l(z_1)\le z_2\le u(z_1)\}$, with $s$ measurable, has area $\int_s\max(u-l,0)$. These slice formulas compute the areas and energy integrals of the triangular and band-shaped regions in the singular construction.
--
--   **Formalization Note** `pairPlaneEquiv : (ℝ × ℝ) ≃ᵐ Plane` is `MeasurableEquiv.finTwoArrow.symm.trans (MeasurableEquiv.toLp 2 (Fin 2 → ℝ))`, and `pairPlaneEquiv_apply` states that it sends `q` to `vec2 q.1 q.2`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/RuledCovering/PlanarIntegration.lean

-- Generated from openai/math@1581d4c lean/OAI/Geometry/RuledCovering/PlanarIntegration.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the RuledCovering mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_RuledCovering
import Definitions.Def_OAI_Geometry_RuledCovering_Projection
import Definitions.Def_OAI_Geometry_RuledCovering_Frames
import Definitions.Def_OAI_Geometry_RuledCovering_OuterApproximation
import Definitions.Def_OAI_Geometry_RuledCovering_Lattice
import Definitions.Def_OAI_Geometry_RuledCovering_LocalApproximation
import Definitions.Def_OAI_Geometry_RuledCovering_HyperbolicLattice
import Definitions.Def_OAI_Geometry_RuledCovering_HyperbolicCover
import Definitions.Def_OAI_Geometry_RuledCovering_Isometries
import Definitions.Def_OAI_Geometry_RuledCovering_Hyperbolic
import Definitions.Def_OAI_Geometry_RuledCovering_NilpotentLattice
import Definitions.Def_OAI_Geometry_RuledCovering_Nilpotent
import Definitions.Def_OAI_Geometry_RuledCovering_SingularField

namespace OAI

noncomputable section

open Set MeasureTheory Filter Metric
open scoped Topology ContDiff Pointwise

namespace RuledApproximation

def pairPlaneEquiv : (ℝ × ℝ) ≃ᵐ Plane :=
  MeasurableEquiv.finTwoArrow.symm.trans (MeasurableEquiv.toLp 2 (Fin 2 → ℝ))

@[simp] lemma pairPlaneEquiv_apply (q : ℝ × ℝ) : pairPlaneEquiv q = vec2 q.1 q.2 := rfl

end RuledApproximation

end

end OAI


