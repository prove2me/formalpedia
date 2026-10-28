-- Prove2me | Definitions.Def_KLSModular_FunctionalInequalities_Probability_Posterior_JointRegularity
-- name    : KLSModular_FunctionalInequalities_Probability_Posterior_JointRegularity
-- status  : Definition
-- author  : @Lazyfill
-- created : 2026-10-25T15:24:51.787613+00:00
-- url     : https://prove2.me/theorems/38b44b15-e229-4b35-89b9-63261754a611
-- title:
--   Finite-dimensional coordinates for posterior parameter pairs
-- statement:
--   `Posterior.parameterSpace E` is the Euclidean model indexed by the finite rank of $E\times(E\to_L[\mathbb R]E)$, and `parameterChart` is a continuous linear equivalence from that parameter pair to its coordinate space. `parameterScore` is the continuous linear functional $(c,Q)\mapsto\langle c,x\rangle-\frac12\langle Qx,x\rangle$, `parameterFeature` is its Riesz representative in the chart coordinates, and `parameterRetract` is the adjoint of the c-coordinate block. `featureLaw` pushes a probability measure on E forward through this feature map; the bundle establishes continuity of the score and feature maps but does not define a posterior expectation theorem.
--
--   **Original module imports**
--
--   ```lean
--   import FunctionalInequalities.Probability.Posterior.Exponent
--   import FunctionalInequalities.Probability.Posterior.CompactPrior
--   import FunctionalInequalities.Probability.Posterior.Generator
--   import FunctionalInequalities.Probability.Posterior.CompactDomain
--   import Mathlib.Analysis.InnerProductSpace.Dual
--   import Mathlib.Analysis.InnerProductSpace.Adjoint
--   import Mathlib.Analysis.InnerProductSpace.PiL2
--   import Mathlib.Analysis.InnerProductSpace.LinearMap
--   import Mathlib.Analysis.Normed.Module.FiniteDimension
--   import Mathlib.Analysis.Normed.Operator.Banach
--   ```
--
--   **Original declaration excerpt**
--
--   Shown in the original module context.
--
--   ```lean
--   private abbrev parameterSpace := EuclideanSpace ℝ (Fin (Module.finrank ℝ (E × (E →L[ℝ] E))))
--   ```
--
--   **Module navigation**
--
--   Direct project imports: [`Probability/Posterior/Exponent`](https://prove2.me/theorems/36c30d18-f69a-4499-bf5e-0d0678b5706c), [`Probability/Posterior/CompactPrior`](https://prove2.me/theorems/e9642070-1d94-4ba1-98bc-8d40d5fe9489), [`Probability/Posterior/Generator`](https://prove2.me/theorems/f83f846f-96fd-4858-aa50-76e79f5d2363), [`Probability/Posterior/CompactDomain`](https://prove2.me/theorems/38dd017c-ecae-4018-a0fd-eec5fa1b0dda).
--
--   Theorems in source order:
--
--   - [`contDiff_posteriorExpectation_joint`](https://prove2.me/theorems/26f7270c-a7c7-4be5-ace6-46911a4ce683)
--   - [`contDiff_posteriorMean_joint`](https://prove2.me/theorems/74843a12-a6a2-460d-9106-3e5347056aaa)
--   - [`contDiff_covariance_pair_joint`](https://prove2.me/theorems/f0d416e4-4daa-49f4-9fdf-85bc15992dcb)
--   - [`contDiff_posteriorCovariance_joint`](https://prove2.me/theorems/a52d87ad-7224-4ad7-973f-f486c36649d8)
--
--   Project result: [The KLS conjecture](https://prove2.me/theorems/c4e9e57c-586c-4945-927e-7f33933f1111).
--
--   [Original module](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Probability/Posterior/JointRegularity.lean) · `FunctionalInequalities.Probability.Posterior.JointRegularity` · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Probability/Posterior/JointRegularity.lean#L38-L117 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Probability.Posterior.JointRegularity`, definition bundle `KLSModular_FunctionalInequalities_Probability_Posterior_JointRegularity`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_Probability_Posterior_Exponent
import Definitions.Def_KLSModular_FunctionalInequalities_Probability_Posterior_CompactPrior
import Definitions.Def_KLSModular_FunctionalInequalities_Probability_Posterior_Generator
import Definitions.Def_KLSModular_FunctionalInequalities_Probability_Posterior_CompactDomain
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Normed.Operator.Banach

noncomputable section
open MeasureTheory ProbabilityTheory FunctionalInequalities
open scoped RealInnerProductSpace ContDiff
namespace FunctionalInequalities
namespace Probability
namespace Posterior
section Chart
variable (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
/-- Euclidean model of the parameter space (implementation device). -/
 abbrev parameterSpace := EuclideanSpace ℝ (Fin (Module.finrank ℝ (E × (E →L[ℝ] E))))
/-- Euclidean coordinates of the parameter space `E × (E →L[ℝ] E)`; the operator norm is kept on the
second factor (this is a linear chart, not a whitening). -/
 def parameterChart : (E × (E →L[ℝ] E)) ≃L[ℝ]
    FunctionalInequalities.Probability.Posterior.parameterSpace E :=
  (Module.finBasis ℝ (E × (E →L[ℝ] E))).equivFunL.trans
    (PiLp.continuousLinearEquiv 2 ℝ
      (fun _ : Fin (Module.finrank ℝ (E × (E →L[ℝ] E))) => ℝ)).symm
/-- The exponent of (67) as a continuous linear functional of the parameter pair. -/
 def parameterScore (x : E) : (E × (E →L[ℝ] E)) →L[ℝ] ℝ :=
  (innerSL ℝ x).comp (ContinuousLinearMap.fst ℝ E (E →L[ℝ] E)) -
    (1 / 2 : ℝ) • ((innerSL ℝ x).comp
      ((ContinuousLinearMap.apply ℝ E x).comp (ContinuousLinearMap.snd ℝ E (E →L[ℝ] E))))
omit [FiniteDimensional ℝ E] in
 theorem continuous_parameterScore : Continuous (FunctionalInequalities.Probability.Posterior.parameterScore E) := by
  have hi : Continuous (fun x : E => innerSL ℝ x) := (InnerProductSpace.toDualMap ℝ E).continuous
  have he : Continuous (fun x : E =>
      (ContinuousLinearMap.apply ℝ E x).comp (ContinuousLinearMap.snd ℝ E (E →L[ℝ] E))) :=
    (ContinuousLinearMap.apply ℝ E).continuous.clm_comp_const _
  exact (hi.clm_comp_const _).sub ((hi.clm_comp he).const_smul (1 / 2 : ℝ))
/-- Riesz representative of the score in the chart coordinates. -/
 def parameterFeature (x : E) :
    FunctionalInequalities.Probability.Posterior.parameterSpace E :=
  (InnerProductSpace.toDual ℝ _).symm
    ((FunctionalInequalities.Probability.Posterior.parameterScore E x).comp (FunctionalInequalities.Probability.Posterior.parameterChart E).symm.toContinuousLinearMap)
 theorem continuous_parameterFeature : Continuous (FunctionalInequalities.Probability.Posterior.parameterFeature E) :=
  (InnerProductSpace.toDual ℝ _).symm.continuous.comp
    ((FunctionalInequalities.Probability.Posterior.continuous_parameterScore E).clm_comp_const (FunctionalInequalities.Probability.Posterior.parameterChart E).symm.toContinuousLinearMap)
 def parameterLinearBlock : E →L[ℝ]
    FunctionalInequalities.Probability.Posterior.parameterSpace E :=
  (FunctionalInequalities.Probability.Posterior.parameterChart E).toContinuousLinearMap.comp (ContinuousLinearMap.inl ℝ E (E →L[ℝ] E))
/-- The adjoint of the `c`-block of the chart retracts the feature to the point. -/
 def parameterRetract :
    FunctionalInequalities.Probability.Posterior.parameterSpace E →L[ℝ] E :=
  (FunctionalInequalities.Probability.Posterior.parameterLinearBlock E).adjoint
end Chart
section Expectation
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
/-- The prior pushed forward by the feature map (an internal device, not a new posterior object). -/
 def featureLaw (μ : ProbabilityMeasure E) :
    ProbabilityMeasure (FunctionalInequalities.Probability.Posterior.parameterSpace E) :=
  μ.map (FunctionalInequalities.Probability.Posterior.continuous_parameterFeature E).measurable.aemeasurable
end Expectation
end Posterior
end Probability
end FunctionalInequalities


