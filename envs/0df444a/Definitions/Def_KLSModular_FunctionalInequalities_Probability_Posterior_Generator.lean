-- Prove2me | Definitions.Def_KLSModular_FunctionalInequalities_Probability_Posterior_Generator
-- name    : KLSModular_FunctionalInequalities_Probability_Posterior_Generator
-- status  : Definition
-- author  : @Lazyfill
-- created : 2026-10-25T15:24:04.061989+00:00
-- url     : https://prove2.me/theorems/f83f846f-96fd-4858-aa50-76e79f5d2363
-- title:
--   Posterior expectations and means
-- statement:
--   For a probability measure $\mu$ on a finite-dimensional real inner-product space, `posteriorExpectation μ c Q f` is the integral of a real-valued function $f$ against the tilt of $\mu$ by $\langle c,x\rangle-\frac12\langle Qx,x\rangle$. Under completeness of the space, `posteriorMean μ c Q` is the vector integral $\int x\,d\mu_{c,Q}$ for that same tilted measure. These declarations are definitions only; they do not assert differentiability, covariance formulas, or a generator identity.
--
--   **Original module imports**
--
--   ```lean
--   import FunctionalInequalities.Probability.Posterior.CompactQuadratic
--   import FunctionalInequalities.Analysis.BakryEmery.Tilt.Local
--   import FunctionalInequalities.Analysis.BakryEmery.Calculus
--   import Mathlib.Analysis.Calculus.Deriv.Comp
--   import Mathlib.Analysis.InnerProductSpace.PiL2
--   ```
--
--   **Original declaration excerpt**
--
--   Shown in the original module context.
--
--   ```lean
--   def posteriorExpectation (μ : ProbabilityMeasure E) (c : E) (Q : E →L[ℝ] E) (f : E → ℝ) : ℝ :=
--     ∫ x, f x ∂((μ : Measure E).tilted (quadraticExponent c Q))
--   ```
--
--   **Module navigation**
--
--   Direct project imports: [`Probability/Posterior/CompactQuadratic`](https://prove2.me/theorems/5018405c-ce78-4ccb-b2c7-5abb1f0295c8), [`Analysis/BakryEmery/Tilt/Local`](https://prove2.me/theorems/d11ffd4f-fcf9-45c5-b131-86144d86211a), [`Analysis/BakryEmery/Calculus`](https://prove2.me/theorems/aff8478c-96df-49c0-bd72-24bb70d5d99a).
--
--   Theorems in source order:
--
--   - [`integrable_exp_norm_mul_of_compact`](https://prove2.me/theorems/93df8d91-b0d9-4aa8-a712-e52703fff899)
--   - [`contDiff_weighted_integral_quadraticExponent_of_compact`](https://prove2.me/theorems/4fe89257-70b6-4433-b7b3-1b2d874f4eb1)
--   - [`contDiff_posteriorExpectation_c`](https://prove2.me/theorems/ddae5880-1008-4ea8-8902-6d872c26def3)
--   - [`fderiv_posteriorExpectation_c_apply`](https://prove2.me/theorems/7e365baf-6866-48b0-8974-871a453169bb)
--   - [`bilinearIteratedFDerivTwo_posteriorExpectation_c`](https://prove2.me/theorems/7f1d74c8-ab70-45c8-8bf8-3c55be335051)
--   - [`sum_bilinearIteratedFDerivTwo_posteriorExpectation_c`](https://prove2.me/theorems/2a7c5069-4ad3-4727-be3f-94142fd12abe)
--
--   Project result: [The KLS conjecture](https://prove2.me/theorems/c4e9e57c-586c-4945-927e-7f33933f1111).
--
--   [Original module](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Probability/Posterior/Generator.lean) · `FunctionalInequalities.Probability.Posterior.Generator` · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Probability/Posterior/Generator.lean#L29-L181 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Probability.Posterior.Generator`, definition bundle `KLSModular_FunctionalInequalities_Probability_Posterior_Generator`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_Probability_Posterior_CompactQuadratic
import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_BakryEmery_Tilt_Local
import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_BakryEmery_Calculus
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.InnerProductSpace.PiL2

noncomputable section
open MeasureTheory Filter Topology ProbabilityTheory
open FunctionalInequalities.Analysis.BakryEmery
open scoped RealInnerProductSpace ContDiff
namespace FunctionalInequalities
namespace Probability
namespace Posterior
section Smooth
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
/-- The expectation `∫ f dμ_{c,Q}` of `f` under the posterior with parameters `(c, Q)`. -/
def posteriorExpectation (μ : ProbabilityMeasure E) (c : E) (Q : E →L[ℝ] E) (f : E → ℝ) : ℝ :=
  ∫ x, f x ∂((μ : Measure E).tilted (quadraticExponent c Q))
end Smooth
section Mean
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
/-- The mean `a = ∫ x dμ_{c,Q}` of the posterior. -/
def posteriorMean (μ : ProbabilityMeasure E) (c : E) (Q : E →L[ℝ] E) : E :=
  ∫ x, x ∂((μ : Measure E).tilted (quadraticExponent c Q))
variable {ι : Type*} [Fintype ι]
end Mean
end Posterior
end Probability
end FunctionalInequalities


