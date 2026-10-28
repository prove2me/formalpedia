-- Prove2me | Definitions.Def_KLSModular_FunctionalInequalities_Poincare_LipschitzGradient_Comparison
-- name    : KLSModular_FunctionalInequalities_Poincare_LipschitzGradient_Comparison
-- status  : Definition
-- author  : @Lazyfill
-- created : 2026-10-25T15:38:33.836663+00:00
-- url     : https://prove2.me/theorems/2c2b9cea-02c3-4658-a545-11edfb033e0d
-- title:
--   Identity-weighted Lipschitz-gradient relaxation
-- statement:
--   For a probability measure `ν` on a finite-dimensional, second-countable normed inner-product space $V$, and a Haar measure `m` with $(ν : \text{Measure }V) \ll m$, `Energy.LipschitzGradient.relaxation` is the sequential relaxation on $L^2(ν)$ of the squared gradient energy for globally Lipschitz tests. It is defined using the weighted-gradient operator with the identity map as weight; this bundle only defines the functional and does not assert any Poincaré inequality or finiteness property.
--
--   **Original module imports**
--
--   ```lean
--   import FunctionalInequalities.Energy.WeightedGradient.Core
--   import FunctionalInequalities.Poincare.LocalSlope.SmoothTestComparison
--   import FunctionalInequalities.Poincare.Relaxation
--   import FunctionalInequalities.Probability.Covariance.Factorization
--   ```
--
--   **Original declaration excerpt**
--
--   Shown in the original module context.
--
--   ```lean
--   def relaxation (hac : (ν : Measure V) ≪ m) :
--       Functional (Lp ℝ 2 (ν : Measure V)) :=
--     (PreEnergy.ofLinearPMap (Energy.WeightedGradient.operator ν (ContinuousLinearMap.id ℝ V) hac)).sequentialRelaxation
--   ```
--
--   **Module navigation**
--
--   Direct project imports: [`Energy/WeightedGradient/Core`](https://prove2.me/theorems/f5d86bfc-b82c-47e4-a17b-d1e26078014f), [`Poincare/LocalSlope/SmoothTestComparison`](https://prove2.me/theorems/1ad07877-0369-4792-9877-1dd2997c7c22), [`Poincare/Relaxation`](https://prove2.me/theorems/33b81a93-0d3f-4459-b2f9-a34a6959e52b), [`Probability/Covariance/Factorization`](https://prove2.me/theorems/0d70ddf5-b213-40d4-b84d-6c356995c50e).
--
--   Theorems in source order:
--
--   - [`holds_ofPreEnergy_of_localSlope`](https://prove2.me/theorems/d102feac-ee7b-49ef-9880-953e2bd04ed9)
--   - [`localSlope_holds_of_relaxation`](https://prove2.me/theorems/b98a1acd-890f-4c84-8b2d-782bb9d924ba)
--   - [`constant_eq_lipschitz`](https://prove2.me/theorems/ad3e672a-6889-4720-aee1-47c1405b013e)
--   - [`relaxation_le_mul_lipschitz`](https://prove2.me/theorems/62ed0b65-a0a8-46f7-b7c9-4f855a09ceaf)
--
--   Project result: [The KLS conjecture](https://prove2.me/theorems/c4e9e57c-586c-4945-927e-7f33933f1111).
--
--   [Original module](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Poincare/LipschitzGradient/Comparison.lean) · `FunctionalInequalities.Poincare.LipschitzGradient.Comparison` · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Poincare/LipschitzGradient/Comparison.lean#L52-L56 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Poincare.LipschitzGradient.Comparison`, definition bundle `KLSModular_FunctionalInequalities_Poincare_LipschitzGradient_Comparison`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_Energy_WeightedGradient_Core
import Definitions.Def_KLSModular_FunctionalInequalities_Poincare_LocalSlope_SmoothTestComparison
import Definitions.Def_KLSModular_FunctionalInequalities_Poincare_Relaxation
import Definitions.Def_KLSModular_FunctionalInequalities_Probability_Covariance_Factorization

noncomputable section
open MeasureTheory Filter Topology
open scoped ContDiff
namespace FunctionalInequalities
open Energy.Euclidean
universe u
variable {V : Type u} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V] [FiniteDimensional ℝ V]
variable (ν : ProbabilityMeasure V) (m : Measure V) [m.IsAddHaarMeasure]
namespace Energy
namespace LipschitzGradient
/-- The sequential relaxation of `f ↦ ‖∇f‖²` on the classes of globally Lipschitz `L²(ν)` functions
with square-integrable gradient: the weighted gradient operator with `B = 1`. -/
def relaxation (hac : (ν : Measure V) ≪ m) :
    Functional (Lp ℝ 2 (ν : Measure V)) :=
  (PreEnergy.ofLinearPMap (Energy.WeightedGradient.operator ν (ContinuousLinearMap.id ℝ V) hac)).sequentialRelaxation
end LipschitzGradient
end Energy
end FunctionalInequalities


