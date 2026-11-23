-- Prove2me | Definitions.Def_DistTransform_Distortion_Supplement_Algebra
-- name    : DistTransform_Distortion_Supplement_Algebra
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-23T13:02:39.527237+00:00
-- url     : https://prove2.me/theorems/5077ff16-8c93-47e2-bf19-0a8d8cba5eee
-- title:
--   §2–§4 — affine laws, comonotonic addition, constant preservation and additivity
-- statement:
--   For a real constant x, write δ_x for the law concentrated at x. For a real scale a≥0 and shift b∈ℝ, let A_{a,b}(F) be the law of aX+b when X has law F. In particular, a⊗F=A_{a,0}(F), including a=0. The comonotonic sum is the unique distribution with
--
--   $$
--   (F\oplus G)^{-1}(p)=F^{-1}(p)+G^{-1}(p),\qquad 0<p<1.
--   $$
--
--   A transform preserves constants if T(δ_x)=δ_x for every x∈ℝ. It is additive on the bounded laws M∞ if T(F⊕G)=T(F)⊕T(G) for every F,G∈M∞.
--
--   These operations describe common-uniform aggregation rather than independent convolution. The published base definitions supply bounded laws, quantiles and stochastic monotonicity.
--
--   **Formalization Note** The comonotonic sum uses classical definite description of the law by its full interior quantile function, exactly the characterization used on p. 10. Existence and uniqueness of this law are mathematical quantile infrastructure to prove, not assumptions added to a target. The affine law is an actual measurable pushforward. Values of affineLaw at negative scales totalize the function and are never used as allowed scale parameters.
-- source:
--   Liu, Schied and Wang, Distributional transforms, probability distortions, and their applications, SSRN 3419388 (version of March 19, 2020), pp. 4–5, Examples 1 and 3, Definition 2; p. 10, comonotonic sum and additivity; p. 14, scalar multiplication

import Mathlib
import Definitions.Def_DistTransform_Distortion_Model

namespace DistTransform.Distortion.Supplement

open MeasureTheory ProbabilityTheory

/-- Example 1 and Definition 2: a constant law, for every real constant. -/
noncomputable def constantLaw (x : ℝ) : ProbabilityMeasure ℝ :=
  ⟨Measure.dirac x, inferInstance⟩

/-- Example 3, p. 4. Used for every nonnegative scale, including zero. -/
noncomputable def affineLaw (a b : ℝ) (F : ProbabilityMeasure ℝ) : ProbabilityMeasure ℝ :=
  F.map (f := fun x : ℝ => a * x + b)
    ((measurable_const.mul measurable_id).add measurable_const).aemeasurable

/-- p. 10: the law whose quantile is the sum of the two input quantiles.
Definite description by the paper's unique characterization; quantiles at 0 and 1
are never inspected. Existence and uniqueness of this law are standard quantile
infrastructure, not hypotheses on a transform. -/
noncomputable def comonoSum (F G : ProbabilityMeasure ℝ) : ProbabilityMeasure ℝ :=
  @Classical.epsilon (ProbabilityMeasure ℝ) ⟨constantLaw 0⟩
    (fun H => ∀ p ∈ Set.Ioo (0 : ℝ) 1,
      leftQuantile H p = leftQuantile F p + leftQuantile G p)

/-- Definition 2, p. 5, with the full range of constants. -/
def PreservesConstants (T : ProbabilityMeasure ℝ → ProbabilityMeasure ℝ) : Prop :=
  ∀ x : ℝ, T (constantLaw x) = constantLaw x

/-- p. 10: addition is comonotonic, not independent convolution. -/
def IsAdditive (T : ProbabilityMeasure ℝ → ProbabilityMeasure ℝ) : Prop :=
  ∀ F ∈ Minf, ∀ G ∈ Minf, T (comonoSum F G) = comonoSum (T F) (T G)

end DistTransform.Distortion.Supplement


