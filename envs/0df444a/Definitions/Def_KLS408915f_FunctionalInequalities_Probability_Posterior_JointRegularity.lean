-- Prove2me | Definitions.Def_KLS408915f_FunctionalInequalities_Probability_Posterior_JointRegularity
-- name    : KLS408915f_FunctionalInequalities_Probability_Posterior_JointRegularity
-- status  : Definition
-- author  : @Lazyfill
-- created : 2026-10-23T05:32:44.34841+00:00
-- url     : https://prove2.me/theorems/fe001c31-6033-4365-a489-3cd41058ae77
-- title:
--   Finite-dimensional coordinates for posterior parameter pairs
-- statement:
--   `Posterior.parameterSpace E` is the Euclidean model indexed by the finite rank of $E\times(E\to_L[\mathbb R]E)$, and `parameterChart` is a continuous linear equivalence from that parameter pair to its coordinate space. `parameterScore` is the continuous linear functional $(c,Q)\mapsto\langle c,x\rangle-\frac12\langle Qx,x\rangle$, `parameterFeature` is its Riesz representative in the chart coordinates, and `parameterRetract` is the adjoint of the c-coordinate block. `featureLaw` pushes a probability measure on E forward through this feature map; the bundle establishes continuity of the score and feature maps but does not define a posterior expectation theorem.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Probability/Posterior/JointRegularity.lean#L38-L117 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Probability.Posterior.JointRegularity`, definition bundle `KLS408915f_FunctionalInequalities_Probability_Posterior_JointRegularity`; the repository is private at upload time).

import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Calculus
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_IntegrationByParts_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Laplacian
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Tilt_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Tilt_Local
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Tilt_SquareIntegrable
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Tensor_Coefficients
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Tensor_Coordinate
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Tensor_Multilinear
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Tensor_Symmetrization
import Definitions.Def_KLS408915f_FunctionalInequalities_Probability_AffineSupport
import Definitions.Def_KLS408915f_FunctionalInequalities_Probability_Covariance_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_Probability_Posterior_CompactDomain
import Definitions.Def_KLS408915f_FunctionalInequalities_Probability_Posterior_CompactPrior
import Definitions.Def_KLS408915f_FunctionalInequalities_Probability_Posterior_CompactQuadratic
import Definitions.Def_KLS408915f_FunctionalInequalities_Probability_Posterior_Exponent
import Definitions.Def_KLS408915f_FunctionalInequalities_Probability_Posterior_Generator
import Definitions.Def_KLS408915f_FunctionalInequalities_Probability_Transport
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Analysis.Calculus.ContDiff.FTaylorSeries
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Convex.Function
import Mathlib.Analysis.Convex.Integral
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.InnerProductSpace.Continuous
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.InnerProductSpace.Laplacian
import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import Mathlib.Analysis.InnerProductSpace.Subspace
import Mathlib.Analysis.Normed.Affine.Isometry
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Normed.Module.Multilinear.Curry
import Mathlib.Analysis.Normed.Operator.Banach
import Mathlib.Analysis.Normed.Operator.LinearIsometry
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Data.Fintype.Perm
import Mathlib.Data.Nat.Choose.Central
import Mathlib.Data.Nat.Choose.Vandermonde
import Mathlib.GroupTheory.Perm.Basic
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Measure.Support
import Mathlib.MeasureTheory.Measure.Tilted
import Mathlib.Probability.Moments.Covariance
import Mathlib.Probability.Moments.CovarianceBilin

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


