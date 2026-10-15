-- Prove2me | Definitions.Def_OAI_Analysis_ProductSpaces_ScalarBounds
-- name    : OAI_Analysis_ProductSpaces_ScalarBounds
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T01:59:02.251523+00:00
-- url     : https://prove2.me/theorems/3a3a6cd7-21b6-4b24-a85b-6c1abe77ba39
-- title:
--   The polarization rotation of the plane
-- statement:
--   The *polarization rotation* is the linear map $R:\mathbb R^2\to\mathbb R^2$ given by
--
--   $$
--   R(z_1,z_2)=\Big(\frac{z_1+z_2}{\sqrt2},\ \frac{z_1-z_2}{\sqrt2}\Big).
--   $$
--
--   It is an orthogonal involution of the plane, so it preserves the standard Gaussian measure $N(0,1)\otimes N(0,1)$ on $\mathbb R^2$, and it satisfies the polarization identity $z_1^2-z_2^2=2\,R(z)_1\,R(z)_2$.
--
--   It is used to symmetrize quadratic Gaussian expressions: the difference $\sum_i a_i(x_i^2-y_i^2)$ of two independent copies of a weighted sum of squared standard Gaussians becomes, after applying $R$ to each pair $(x_i,y_i)$, twice a Gaussian bilinear form $\sum_i a_i x'_i y'_i$ in two independent standard Gaussian vectors.
--
--   **Formalization Note** The map is `gaussianRotate : ℝ × ℝ → ℝ × ℝ`, with the factor $1/\sqrt2$ written as `(Real.sqrt 2)⁻¹`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/ProductSpaces/ScalarBounds.lean

-- Generated from openai/math@1581d4c lean/OAI/Analysis/ProductSpaces/ScalarBounds.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the IndependentProducts mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_IndependentProducts
import Definitions.Def_OAI_Analysis_ProductSpaces_TreeObstruction
import Definitions.Def_OAI_Analysis_ProductSpaces_PathMoments
import Definitions.Def_OAI_Analysis_ProductSpaces_WeakNullity

namespace OAI

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology

noncomputable section

universe uΩ uι

namespace IndependentProducts

section SecondMoment
variable {Ω : Type uΩ} [MeasurableSpace Ω] {μ : Measure Ω}

variable [IsProbabilityMeasure μ]

end SecondMoment
end IndependentProducts

namespace IndependentProducts

/-- Polarization on one independent standard Gaussian pair. -/
def gaussianRotate (z : ℝ × ℝ) : ℝ × ℝ :=
  ((Real.sqrt 2)⁻¹ * (z.1 + z.2), (Real.sqrt 2)⁻¹ * (z.1 - z.2))

section GaussianSum
variable {Ω : Type uΩ} {ι : Type uι} [MeasurableSpace Ω] [DecidableEq ι]
  {P : Measure Ω} [IsProbabilityMeasure P]

variable [Fintype ι]

end GaussianSum
end IndependentProducts

end

end OAI


