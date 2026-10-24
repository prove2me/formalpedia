-- Prove2me | Definitions.Def_KLS408915f_FunctionalInequalities_Probability_Posterior_CompactQuadratic
-- name    : KLS408915f_FunctionalInequalities_Probability_Posterior_CompactQuadratic
-- status  : Definition
-- author  : @Lazyfill
-- created : 2026-10-23T04:56:53.29972+00:00
-- url     : https://prove2.me/theorems/8ecce49c-a1d6-4edb-b458-80a2d5efd52f
-- title:
--   Probability of compactly supported quadratic posteriors
-- statement:
--   For a probability measure $\mu$ on a finite-dimensional real inner-product space with compact topological support, `isProbabilityMeasure_tilted_quadraticExponent_of_compact` states that the tilt by `quadraticExponent c Q` is a probability measure for every $c\in E$ and continuous linear map $Q:E\to E$. The assertion includes arbitrary finite parameters, with no positivity or symmetry assumption on $Q$.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Probability/Posterior/CompactQuadratic.lean#L41-L47 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Probability.Posterior.CompactQuadratic`, definition bundle `KLS408915f_FunctionalInequalities_Probability_Posterior_CompactQuadratic`; the repository is private at upload time).

import Definitions.Def_KLS408915f_FunctionalInequalities_Probability_Posterior_CompactPrior
import Definitions.Def_KLS408915f_FunctionalInequalities_Probability_Posterior_Exponent
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Convex.Function
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Continuous
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Measure.Support
import Mathlib.MeasureTheory.Measure.Tilted
import Mathlib.Probability.Moments.Covariance

noncomputable section
open MeasureTheory Filter Topology ProbabilityTheory
open scoped RealInnerProductSpace
namespace FunctionalInequalities
namespace Probability
namespace Posterior
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
/-- Every posterior of a compactly supported prior is a probability law. -/
theorem isProbabilityMeasure_tilted_quadraticExponent_of_compact (μ : ProbabilityMeasure E)
    (hc : IsCompact (μ : Measure E).support) (c : E) (Q : E →L[ℝ] E) :
    IsProbabilityMeasure ((μ : Measure E).tilted (quadraticExponent c Q)) := by
  apply isProbabilityMeasure_tilted_of_compact μ hc
  unfold quadraticExponent
  fun_prop
end Posterior
end Probability
end FunctionalInequalities


