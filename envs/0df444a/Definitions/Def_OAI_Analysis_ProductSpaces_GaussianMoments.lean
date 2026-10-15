-- Prove2me | Definitions.Def_OAI_Analysis_ProductSpaces_GaussianMoments
-- name    : OAI_Analysis_ProductSpaces_GaussianMoments
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T02:00:00.123497+00:00
-- url     : https://prove2.me/theorems/79d72a16-3892-468d-a6f7-fd4caf0319e8
-- title:
--   Standard Gaussian vectors, the excess function, and coordinatewise polarization
-- statement:
--   Let $\iota$ be a finite index set.
--
--   1. **Standard Gaussian vector.** $\gamma_\iota=N(0,1)^{\otimes\iota}$ is the standard Gaussian probability measure on $\mathbb R^\iota$, the product of independent standard normal laws, one per coordinate.
--
--   2. **Excess function.** For real parameters $t,r$ and $z\in\mathbb R$,
--
--      $$\operatorname{exc}_{t,r}(z)=\max\big(t|z|-r,\ 0\big),$$
--
--      the amount by which $t|z|$ exceeds the threshold $r$. It is nonnegative and even in $z$, and convex when $t\ge 0$.
--
--   3. **Coordinatewise polarization.** For $(x,y)\in\mathbb R^\iota\times\mathbb R^\iota$,
--
--      $$\mathcal R(x,y)=\Big(\Big(\frac{x_i+y_i}{\sqrt2}\Big)_{i\in\iota},\ \Big(\frac{x_i-y_i}{\sqrt2}\Big)_{i\in\iota}\Big),$$
--
--      i.e. the polarization rotation of the plane applied to each pair $(x_i,y_i)$; it preserves $\gamma_\iota\otimes\gamma_\iota$.
--
--   The excess function is the scalar quantity behind the $L^1$ midpoint gain: for real $u,c$ and $t\ge 0$ one has $\tfrac12\big(|u+tc|+|u-tc|\big)-|u|=\operatorname{exc}_{t,|u|}(c)$, so lower bounds for expected excesses of random affine forms translate into lower bounds for midpoint moduli of $L^1$ spaces.
--
--   **Formalization Note** The measure is `gaussianVector = Measure.pi (fun _ => gaussianReal 0 1)`, registered as a probability measure by an instance; `excess t r z` is `max (t * |z| - r) 0`; `gaussianVectorRotate` applies `gaussianRotate` to each coordinate pair.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/ProductSpaces/GaussianMoments.lean

-- Generated from openai/math@1581d4c lean/OAI/Analysis/ProductSpaces/GaussianMoments.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the IndependentProducts mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_IndependentProducts
import Definitions.Def_OAI_Analysis_ProductSpaces_TreeObstruction
import Definitions.Def_OAI_Analysis_ProductSpaces_PathMoments
import Definitions.Def_OAI_Analysis_ProductSpaces_WeakNullity
import Definitions.Def_OAI_Analysis_ProductSpaces_ScalarBounds

namespace OAI

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology

noncomputable section

universe uΩ uι

namespace IndependentProducts
section WeightedMoments
variable {Ω : Type uΩ} {ι : Type uι} [MeasurableSpace Ω] [Fintype ι]
variable {P : Measure Ω}

variable [IsProbabilityMeasure P]

end WeightedMoments
section GaussianVector
variable {ι : Type uι} [Fintype ι]

def gaussianVector : Measure (ι → ℝ) := Measure.pi (fun _ => gaussianReal 0 1)
instance : IsProbabilityMeasure (gaussianVector (ι := ι)) := by unfold gaussianVector; infer_instance

end GaussianVector
end IndependentProducts

namespace IndependentProducts

def excess (t r z : ℝ) : ℝ := max (t * |z| - r) 0

end IndependentProducts

namespace IndependentProducts

section GaussianFinite
variable {ι : Type uι} [Fintype ι]

def gaussianVectorRotate (z : (ι → ℝ) × (ι → ℝ)) : (ι → ℝ) × (ι → ℝ) :=
  (fun i => (gaussianRotate (z.1 i, z.2 i)).1, fun i => (gaussianRotate (z.1 i, z.2 i)).2)

end GaussianFinite
end IndependentProducts

end

end OAI


