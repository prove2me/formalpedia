-- Prove2me | Definitions.Def_KLSModular_FunctionalInequalities_Probability_Posterior_CompactQuadratic
-- name    : KLSModular_FunctionalInequalities_Probability_Posterior_CompactQuadratic
-- status  : Definition
-- author  : @Lazyfill
-- created : 2026-10-25T15:16:53.450997+00:00
-- url     : https://prove2.me/theorems/5018405c-ce78-4ccb-b2c7-5abb1f0295c8
-- title:
--   Probability of compactly supported quadratic posteriors
-- statement:
--   For a probability measure $\mu$ on a finite-dimensional real inner-product space with compact topological support, `isProbabilityMeasure_tilted_quadraticExponent_of_compact` states that the tilt by `quadraticExponent c Q` is a probability measure for every $c\in E$ and continuous linear map $Q:E\to E$. The assertion includes arbitrary finite parameters, with no positivity or symmetry assumption on $Q$.
--
--   **Original module imports**
--
--   ```lean
--   import FunctionalInequalities.Probability.Posterior.CompactPrior
--   import FunctionalInequalities.Probability.Posterior.Coercive
--   ```
--
--   **Original declaration excerpt**
--
--   Shown in the original module context.
--
--   ```lean
--   theorem isProbabilityMeasure_tilted_quadraticExponent_of_compact (μ : ProbabilityMeasure E)
--       (hc : IsCompact (μ : Measure E).support) (c : E) (Q : E →L[ℝ] E) :
--       IsProbabilityMeasure ((μ : Measure E).tilted (quadraticExponent c Q)) := by
--     apply isProbabilityMeasure_tilted_of_compact μ hc
--     unfold quadraticExponent
--     fun_prop
--   ```
--
--   **Module navigation**
--
--   Direct project imports: [`Probability/Posterior/CompactPrior`](https://prove2.me/theorems/e9642070-1d94-4ba1-98bc-8d40d5fe9489), [`Probability/Posterior/Coercive`](https://prove2.me/theorems/587ce164-a2b8-4d14-ae0e-f6f78c250559).
--
--   Theorems in source order:
--
--   - [`exists_uniform_norm_moments_tilted_quadraticExponent_of_compact`](https://prove2.me/theorems/840d9ee9-637c-4b2c-918e-01a3cf6f78a7)
--
--   Project result: [The KLS conjecture](https://prove2.me/theorems/c4e9e57c-586c-4945-927e-7f33933f1111).
--
--   [Original module](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Probability/Posterior/CompactQuadratic.lean) · `FunctionalInequalities.Probability.Posterior.CompactQuadratic` · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Probability/Posterior/CompactQuadratic.lean#L41-L47 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Probability.Posterior.CompactQuadratic`, definition bundle `KLSModular_FunctionalInequalities_Probability_Posterior_CompactQuadratic`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_Probability_Posterior_CompactPrior
import Definitions.Def_KLSModular_FunctionalInequalities_Probability_Posterior_Coercive

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


