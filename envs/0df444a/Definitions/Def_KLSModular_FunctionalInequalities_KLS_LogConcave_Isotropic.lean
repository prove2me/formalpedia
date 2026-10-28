-- Prove2me | Definitions.Def_KLSModular_FunctionalInequalities_KLS_LogConcave_Isotropic
-- name    : KLSModular_FunctionalInequalities_KLS_LogConcave_Isotropic
-- status  : Definition
-- author  : @Lazyfill
-- created : 2026-10-25T15:40:37.581582+00:00
-- url     : https://prove2.me/theorems/35471368-b77f-4600-8554-699e6845e252
-- title:
--   Isotropic, covariance, and affine KLS bounds
-- statement:
--   `KLS.IsotropicBound K` states that every log-concave probability measure on every finite-dimensional space in universe `u` that is isotropic has intrinsic local-slope Poincaré constant at most the nonnegative constant $K$. `KLS.CovarianceBound K` instead bounds the intrinsic constant for every log-concave probability measure by $K$ times `ENNReal.ofReal ‖Covariance.operator μ‖`, while `KLS.AffineBound K` bounds the intrinsic covariance-gradient constant by $K$; all three are definitions of propositions and do not themselves assert that any such $K$ exists.
--
--   **Original module imports**
--
--   ```lean
--   import FunctionalInequalities.Energy.CovarianceGradient.LinearEquiv
--   import FunctionalInequalities.KLS.Isotropic
--   import FunctionalInequalities.KLS.LogConcave.Translation
--   import FunctionalInequalities.KLS.LogConcave.Density.BorellRepresentation.Moments
--   import FunctionalInequalities.KLS.LogConcave.WeightedGradient.Basic
--   import FunctionalInequalities.KLS.Statement
--   import FunctionalInequalities.Poincare.LipschitzGradient.Comparison
--   import FunctionalInequalities.Poincare.L2.Comparison
--   import FunctionalInequalities.KLS.LogConcave.Poincare
--   import FunctionalInequalities.Probability.Covariance.Whitening
--   import FunctionalInequalities.Probability.Covariance.Intrinsic
--   ```
--
--   **Original declaration excerpt**
--
--   Shown in the original module context.
--
--   ```lean
--   def IsotropicBound (K : NNReal) : Prop :=
--     ∀ (V : Type u) [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
--       [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V] [FiniteDimensional ℝ V]
--       (ν : ProbabilityMeasure V), LogConcave ν → Isotropic ν → Poincare.LocalSlope.Intrinsic.constant ν ≤ (K : ENNReal)
--   ```
--
--   **Module navigation**
--
--   Direct project imports: [`Energy/CovarianceGradient/LinearEquiv`](https://prove2.me/theorems/3edabcc8-b48c-4028-8b8e-560f716da5f0), [`KLS/Isotropic`](https://prove2.me/theorems/b8da0fa3-d27f-46ae-b3b9-8c204df57e02), [`KLS/LogConcave/Translation`](https://prove2.me/theorems/90dffb15-6ccb-4069-ada2-b620f287fe68), [`KLS/LogConcave/Density/BorellRepresentation/Moments`](https://prove2.me/theorems/e5df2dc6-6ebd-4244-bfb5-41d46b1c70d1), [`KLS/LogConcave/WeightedGradient/Basic`](https://prove2.me/theorems/72f5f80b-8a06-4b88-9c28-6818c4e64bc7), [`KLS/Statement`](https://prove2.me/theorems/a8a0c8db-8c01-4ba8-b1c2-6b2fe5d1864a), [`Poincare/LipschitzGradient/Comparison`](https://prove2.me/theorems/2c2b9cea-02c3-4658-a545-11edfb033e0d), [`Poincare/L2/Comparison`](https://prove2.me/theorems/58424fb2-2b30-488c-8ab7-407b091d2a82), [`KLS/LogConcave/Poincare`](https://prove2.me/theorems/22f55d8a-6675-4b7a-ac3b-ac21c6c833d3), [`Probability/Covariance/Whitening`](https://prove2.me/theorems/47b0b944-6abf-4f6e-a39a-7b55e36f44ae), [`Probability/Covariance/Intrinsic`](https://prove2.me/theorems/541d8ad1-e32c-4fe3-bcf1-975d2f57d4f0).
--
--   Theorems in source order:
--
--   - [`of_continuousLinearEquiv_map`](https://prove2.me/theorems/c637e7db-3431-42d0-bb61-ac5baf6882b0)
--   - [`exists_isotropic_localSlope_constant_eq`](https://prove2.me/theorems/5dfc02d9-caf9-4e32-9ec6-e921e0672aed)
--   - [`localSlope_le_mul_intrinsicCovariance`](https://prove2.me/theorems/102edef9-2afb-4d6f-8f68-c39def16f9cf)
--
--   Project result: [The KLS conjecture](https://prove2.me/theorems/c4e9e57c-586c-4945-927e-7f33933f1111).
--
--   [Original module](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/KLS/LogConcave/Isotropic.lean) · `FunctionalInequalities.KLS.LogConcave.Isotropic` · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/KLS/LogConcave/Isotropic.lean#L165-L185 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.KLS.LogConcave.Isotropic`, definition bundle `KLSModular_FunctionalInequalities_KLS_LogConcave_Isotropic`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_Energy_CovarianceGradient_LinearEquiv
import Definitions.Def_KLSModular_FunctionalInequalities_KLS_Isotropic
import Definitions.Def_KLSModular_FunctionalInequalities_KLS_LogConcave_Translation
import Definitions.Def_KLSModular_FunctionalInequalities_KLS_LogConcave_Density_BorellRepresentation_Moments
import Definitions.Def_KLSModular_FunctionalInequalities_KLS_LogConcave_WeightedGradient_Basic
import Definitions.Def_KLSModular_FunctionalInequalities_KLS_Statement
import Definitions.Def_KLSModular_FunctionalInequalities_Poincare_LipschitzGradient_Comparison
import Definitions.Def_KLSModular_FunctionalInequalities_Poincare_L2_Comparison
import Definitions.Def_KLSModular_FunctionalInequalities_KLS_LogConcave_Poincare
import Definitions.Def_KLSModular_FunctionalInequalities_Probability_Covariance_Whitening
import Definitions.Def_KLSModular_FunctionalInequalities_Probability_Covariance_Intrinsic

noncomputable section
open MeasureTheory Filter Topology InnerProductSpace
namespace FunctionalInequalities
open Energy Energy.Euclidean Probability
section Statements
universe u
namespace KLS
/-- Item (1): every isotropic log-concave law on every finite-dimensional Euclidean space of the
universe `u` has literature constant at most `K`. -/
def IsotropicBound (K : NNReal) : Prop :=
  ∀ (V : Type u) [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
    [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V] [FiniteDimensional ℝ V]
    (ν : ProbabilityMeasure V), LogConcave ν → Isotropic ν → Poincare.LocalSlope.Intrinsic.constant ν ≤ (K : ENNReal)
/-- Item (2): every log-concave law on every finite-dimensional Euclidean space of the universe `u`
has literature constant at most `K` times the operator norm of its covariance. -/
def CovarianceBound (K : NNReal) : Prop :=
  ∀ (E : Type u) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] [FiniteDimensional ℝ E]
    (μ : ProbabilityMeasure E), LogConcave μ →
      Poincare.LocalSlope.Intrinsic.constant μ ≤ (K : ENNReal) * ENNReal.ofReal ‖Covariance.operator (μ : Measure E)‖
/-- Item (3): every log-concave law on every finite-dimensional Euclidean space of the universe `u`
has affine covariance Poincaré constant at most `K`. -/
def AffineBound (K : NNReal) : Prop :=
  ∀ (E : Type u) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] [FiniteDimensional ℝ E]
    (μ : ProbabilityMeasure E), LogConcave μ → Poincare.CovarianceGradient.Intrinsic.constant μ ≤ (K : ENNReal)
end KLS
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] [FiniteDimensional ℝ E]
end Statements
end FunctionalInequalities


