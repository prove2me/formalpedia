-- Prove2me | Definitions.Def_KLSModular_FunctionalInequalities_KLS_LogConcave_Translation
-- name    : KLSModular_FunctionalInequalities_KLS_LogConcave_Translation
-- status  : Definition
-- author  : @Lazyfill
-- created : 2026-10-25T15:31:05.033575+00:00
-- url     : https://prove2.me/theorems/90dffb15-6ccb-4069-ada2-b620f287fe68
-- title:
--   Translation preserves log-concavity
-- statement:
--   For a log-concave probability law μ on a finite-dimensional real inner-product space and any vector b, `LogConcave.translateLaw` proves that the translated law `Probability.translateLaw μ b` is log-concave. The statement is valid without the completeness, second-countability, and finite-dimensionality assumptions omitted by the theorem. This declaration does not assert translation invariance of a Poincaré constant, a Poincaré inequality, or any KLS bound.
--
--   **Original module imports**
--
--   ```lean
--   import FunctionalInequalities.KLS.LogConcave.Covariance
--   import FunctionalInequalities.Poincare.CovarianceGradient.Translation
--   ```
--
--   **Original declaration excerpt**
--
--   Shown in the original module context.
--
--   ```lean
--   theorem translateLaw (hμ : LogConcave μ) (b : E) :
--       LogConcave (Probability.translateLaw μ b) := by
--     refine hμ.of_affineIsometry_map (Probability.translateLaw μ b)
--       (AffineIsometryEquiv.constVAdd ℝ E (-b)).toAffineIsometry ?_
--     have hf : ⇑(AffineIsometryEquiv.constVAdd ℝ E (-b)).toAffineIsometry = fun x ↦ -b + x := by
--       funext x
--       rfl
--     rw [hf]
--     exact (Probability.measurePreserving_translate_symm μ b).map_eq
--   ```
--
--   **Module navigation**
--
--   Direct project imports: [`KLS/LogConcave/Covariance`](https://prove2.me/theorems/a7f988cb-dbf8-4fdf-82f1-fb76302f0c56), [`Poincare/CovarianceGradient/Translation`](https://prove2.me/theorems/45f830f9-aeae-45f7-8c0f-0d89ac972021).
--
--   Theorems in source order:
--
--   - [`memLp_id_two`](https://prove2.me/theorems/1e1255d8-1cf4-45ef-8f96-0337bafe649e)
--
--   Project result: [The KLS conjecture](https://prove2.me/theorems/c4e9e57c-586c-4945-927e-7f33933f1111).
--
--   [Original module](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/KLS/LogConcave/Translation.lean) · `FunctionalInequalities.KLS.LogConcave.Translation` · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/KLS/LogConcave/Translation.lean#L38-L48 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.KLS.LogConcave.Translation`, definition bundle `KLSModular_FunctionalInequalities_KLS_LogConcave_Translation`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_KLS_LogConcave_Covariance
import Definitions.Def_KLSModular_FunctionalInequalities_Poincare_CovarianceGradient_Translation

noncomputable section
open MeasureTheory Filter Topology
namespace FunctionalInequalities
namespace KLS
namespace LogConcave
open Energy.Euclidean Probability
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] [FiniteDimensional ℝ E]
  {μ : ProbabilityMeasure E}
omit [CompleteSpace E] [SecondCountableTopology E] [FiniteDimensional ℝ E] in
/-- Translating a log-concave law in the ambient space keeps it log-concave. -/
theorem translateLaw (hμ : LogConcave μ) (b : E) :
    LogConcave (Probability.translateLaw μ b) := by
  refine hμ.of_affineIsometry_map (Probability.translateLaw μ b)
    (AffineIsometryEquiv.constVAdd ℝ E (-b)).toAffineIsometry ?_
  have hf : ⇑(AffineIsometryEquiv.constVAdd ℝ E (-b)).toAffineIsometry = fun x ↦ -b + x := by
    funext x
    rfl
  rw [hf]
  exact (Probability.measurePreserving_translate_symm μ b).map_eq
end LogConcave
end KLS
end FunctionalInequalities


