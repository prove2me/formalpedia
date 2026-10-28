-- Prove2me | Definitions.Def_KLSModular_FunctionalInequalities_Probability_Posterior_CompactDomain
-- name    : KLSModular_FunctionalInequalities_Probability_Posterior_CompactDomain
-- status  : Definition
-- author  : @Lazyfill
-- created : 2026-10-25T15:18:54.175658+00:00
-- url     : https://prove2.me/theorems/38dd017c-ecae-4018-a0fd-eec5fa1b0dda
-- title:
--   Compactly supported quadratic posterior law
-- statement:
--   For a probability measure $\mu$ on a finite-dimensional real inner-product space with compact support, `compactPosterior μ hc c Q` is the probability measure whose underlying measure is the tilt of $\mu$ by $x\mapsto\langle c,x\rangle-\frac12\langle Qx,x\rangle$. The probability structure is justified by `isProbabilityMeasure_tilted_quadraticExponent_of_compact`, and the definition permits every $c$ and continuous linear map $Q$.
--
--   **Original module imports**
--
--   ```lean
--   import FunctionalInequalities.Probability.Posterior.CompactQuadratic
--   import FunctionalInequalities.Probability.Covariance.Positivity
--   import FunctionalInequalities.Probability.Transport
--   ```
--
--   **Original declaration excerpt**
--
--   Shown in the original module context.
--
--   ```lean
--   def compactPosterior (μ : ProbabilityMeasure E) (hc : IsCompact (μ : Measure E).support)
--       (c : E) (Q : E →L[ℝ] E) : ProbabilityMeasure E :=
--     ⟨(μ : Measure E).tilted (quadraticExponent c Q), isProbabilityMeasure_tilted_quadraticExponent_of_compact μ hc c Q⟩
--   ```
--
--   **Module navigation**
--
--   Direct project imports: [`Probability/Posterior/CompactQuadratic`](https://prove2.me/theorems/5018405c-ce78-4ccb-b2c7-5abb1f0295c8), [`Probability/Covariance/Positivity`](https://prove2.me/theorems/11f9423c-d823-4cf1-ba54-703b7213bca5), [`Probability/Transport`](https://prove2.me/theorems/49c9fb1d-757f-4dd4-935d-0244caf50564).
--
--   Project result: [The KLS conjecture](https://prove2.me/theorems/c4e9e57c-586c-4945-927e-7f33933f1111).
--
--   [Original module](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Probability/Posterior/CompactDomain.lean) · `FunctionalInequalities.Probability.Posterior.CompactDomain` · Frozen source `408915f`.
-- source:
--   Source: Bizeul–Klartag–Lehec, Presenting a proof of the Kannan–Lovász–Simonovits conjecture (arXiv:2610.05474v1), item E67. Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Probability/Posterior/CompactDomain.lean#L26-L30 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Probability.Posterior.CompactDomain`, definition bundle `KLSModular_FunctionalInequalities_Probability_Posterior_CompactDomain`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_Probability_Posterior_CompactQuadratic
import Definitions.Def_KLSModular_FunctionalInequalities_Probability_Covariance_Positivity
import Definitions.Def_KLSModular_FunctionalInequalities_Probability_Transport

noncomputable section
open MeasureTheory
open scoped RealInnerProductSpace
namespace FunctionalInequalities
namespace Probability
namespace Posterior
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
/-- The BKL posterior `μ.tilted (⟪c,·⟫ − ½⟪Q·,·⟫)` of a compactly supported prior, as a probability law
(every finite `(c, Q)`, including `0` and negative `Q`). -/
def compactPosterior (μ : ProbabilityMeasure E) (hc : IsCompact (μ : Measure E).support)
    (c : E) (Q : E →L[ℝ] E) : ProbabilityMeasure E :=
  ⟨(μ : Measure E).tilted (quadraticExponent c Q), isProbabilityMeasure_tilted_quadraticExponent_of_compact μ hc c Q⟩
end Posterior
end Probability
end FunctionalInequalities


