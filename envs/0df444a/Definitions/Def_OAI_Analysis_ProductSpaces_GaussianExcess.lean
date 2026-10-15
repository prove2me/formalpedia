-- Prove2me | Definitions.Def_OAI_Analysis_ProductSpaces_GaussianExcess
-- name    : OAI_Analysis_ProductSpaces_GaussianExcess
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T02:01:30.986706+00:00
-- url     : https://prove2.me/theorems/e6d33ea4-6e3e-4f7f-b66a-0d9a476d29d6
-- title:
--   The law of a squared standard Gaussian is a probability measure
-- statement:
--   Let $\gamma_1=N(0,1)$ be the standard Gaussian law on $\mathbb R$ and let
--
--   $$
--   \chi^2_1=\gamma_1\circ(x\mapsto x^2)^{-1}
--   $$
--
--   be the law of $G^2$ for $G\sim N(0,1)$, the chi-square law with one degree of freedom; it is the multiplier law of the squared-Gaussian case of the product-space construction. This file registers that $\chi^2_1$ is a probability measure on $\mathbb R$, as the push-forward of a probability measure under the measurable map $x\mapsto x^2$.
--
--   The instance is what allows the general results on product measures, path products and their closed $L^1$ span, all of which assume a probability multiplier law, to be applied with multipliers distributed as squared standard Gaussians.
--
--   **Formalization Note** The law itself is `gaussianSquareLaw = (gaussianReal 0 1).map (fun x => x ^ 2)`, introduced with the base definitions of the project; this file contributes only the instance `gaussianSquareLaw_probability : IsProbabilityMeasure gaussianSquareLaw`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/ProductSpaces/GaussianExcess.lean

-- Generated from openai/math@1581d4c lean/OAI/Analysis/ProductSpaces/GaussianExcess.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the IndependentProducts mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_IndependentProducts
import Definitions.Def_OAI_Analysis_ProductSpaces_TreeObstruction
import Definitions.Def_OAI_Analysis_ProductSpaces_PathMoments
import Definitions.Def_OAI_Analysis_ProductSpaces_WeakNullity
import Definitions.Def_OAI_Analysis_ProductSpaces_ScalarBounds
import Definitions.Def_OAI_Analysis_ProductSpaces_GaussianMoments

namespace OAI

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology

noncomputable section

universe uι

namespace IndependentProducts
section GaussianScalar
variable {ι : Type uι} [Fintype ι]

instance gaussianSquareLaw_probability : IsProbabilityMeasure gaussianSquareLaw := by
  unfold gaussianSquareLaw
  exact Measure.isProbabilityMeasure_map (measurable_id.pow_const 2).aemeasurable

end GaussianScalar
end IndependentProducts

end

end OAI


