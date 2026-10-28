-- Prove2me | Definitions.Def_KLSModular_FunctionalInequalities_KLS_Isotropic
-- name    : KLSModular_FunctionalInequalities_KLS_Isotropic
-- status  : Definition
-- author  : @Lazyfill
-- created : 2026-10-25T15:20:12.339682+00:00
-- url     : https://prove2.me/theorems/b8da0fa3-d27f-46ae-b3b9-8c204df57e02
-- title:
--   Isotropic probability law
-- statement:
--   `FunctionalInequalities.KLS.Isotropic μ` is a proposition for a probability measure $\mu$ on a complete real inner-product space requiring three fields: `memLp_two` says that the identity map has finite second moment, `mean_zero` says $\int x\,d\mu=0$, and `covariance_identity` says the centered covariance operator `Covariance.operator` is the identity continuous linear map. The structure is only a definition of isotropy and includes no whitening or equivalence theorem.
--
--   **Original module imports**
--
--   ```lean
--   import FunctionalInequalities.Probability.Covariance.Basic
--   import FunctionalInequalities.Probability.Basic
--   import Mathlib.MeasureTheory.Function.LpSpace.Basic
--   import Mathlib.Analysis.Calculus.Gradient.Basic
--   import FunctionalInequalities.Analysis.BakryEmery.IntegrationByParts.Basic
--   import FunctionalInequalities.Analysis.BakryEmery.IntegrationByParts.ConvexHessian
--   import FunctionalInequalities.Analysis.Matrix.Sign
--   import Mathlib.Probability.Moments.CovarianceBilin
--   import Mathlib.Analysis.CStarAlgebra.Matrix
--   ```
--
--   **Original declaration excerpt**
--
--   Shown in the original module context.
--
--   ```lean
--   structure Isotropic (μ : ProbabilityMeasure E) : Prop where
--     memLp_two : MemLp id 2 (μ : Measure E)
--     mean_zero : ∫ x, x ∂(μ : Measure E) = 0
--     covariance_identity : Covariance.operator (μ : Measure E) = ContinuousLinearMap.id ℝ E
--   ```
--
--   **Module navigation**
--
--   Direct project imports: [`Probability/Covariance/Basic`](https://prove2.me/theorems/c4e236b4-be51-468e-9de3-e2203fe87adc), [`Probability/Basic`](https://prove2.me/theorems/e4217deb-9c6f-471c-9339-30946409c625), [`Analysis/BakryEmery/IntegrationByParts/Basic`](https://prove2.me/theorems/63cbd0f3-2def-4aae-8836-ba5c303c076a), [`Analysis/BakryEmery/IntegrationByParts/ConvexHessian`](https://prove2.me/theorems/9e175e47-8f9e-4f9e-bc34-a0a0891d0139), [`Analysis/Matrix/Sign`](https://prove2.me/theorems/2761ff4f-5f84-494d-b685-5a11640444c8).
--
--   Theorems in source order:
--
--   - [`Isotropic.map_linearIsometryEquiv`](https://prove2.me/theorems/2a04e022-1e2a-44a3-9511-86cbce831c79)
--   - [`integral_fderiv_mul_fderiv_eq_inner_of_isotropic_map`](https://prove2.me/theorems/5232fd28-307b-473d-a267-0276d096b8b7)
--   - [`Isotropic.integral_norm_sq`](https://prove2.me/theorems/d8804772-cf20-4fb4-8ca9-55643b773065)
--
--   Project result: [The KLS conjecture](https://prove2.me/theorems/c4e9e57c-586c-4945-927e-7f33933f1111).
--
--   [Original module](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/KLS/Isotropic.lean) · `FunctionalInequalities.KLS.Isotropic` · Frozen source `408915f`.
-- source:
--   Source: Guédon–Milman, Interpolating thin-shell and sharp large-deviation estimates for isotropic log-concave measures (arXiv:1011.0943v3), item DISO; Jambulapati–Lee–Vempala, A slightly improved bound for the KLS constant (arXiv:2208.11644v2), item D3; Klartag–Lehec, Bourgain’s slicing problem and KLS isoperimetry up to polylog (arXiv:2203.15551v2), item D3; Letwin, The KLS constant is O(log^(1/4) n) (arXiv:2607.24164v1), item DISO. Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/KLS/Isotropic.lean#L30-L35 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.KLS.Isotropic`, definition bundle `KLSModular_FunctionalInequalities_KLS_Isotropic`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_Probability_Covariance_Basic
import Definitions.Def_KLSModular_FunctionalInequalities_Probability_Basic
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.Analysis.Calculus.Gradient.Basic
import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_BakryEmery_IntegrationByParts_Basic
import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_BakryEmery_IntegrationByParts_ConvexHessian
import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Matrix_Sign
import Mathlib.Probability.Moments.CovarianceBilin
import Mathlib.Analysis.CStarAlgebra.Matrix

noncomputable section
open MeasureTheory
open scoped RealInnerProductSpace
namespace FunctionalInequalities
namespace KLS
variable {E : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable [MeasurableSpace E] [BorelSpace E]
/-- A probability law with finite second moment, mean zero, and identity centered covariance.
The moment field prevents the totalized integral/covariance from encoding integrability. -/
structure Isotropic (μ : ProbabilityMeasure E) : Prop where
  memLp_two : MemLp id 2 (μ : Measure E)
  mean_zero : ∫ x, x ∂(μ : Measure E) = 0
  covariance_identity : Covariance.operator (μ : Measure E) = ContinuousLinearMap.id ℝ E
end KLS
end FunctionalInequalities


