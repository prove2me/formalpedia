-- Prove2me | Definitions.Def_KLS408915f_FunctionalInequalities_Probability_Posterior_LogPartition
-- name    : KLS408915f_FunctionalInequalities_Probability_Posterior_LogPartition
-- status  : Definition
-- author  : @Lazyfill
-- created : 2026-10-23T11:51:26.642488+00:00
-- url     : https://prove2.me/theorems/8a66578e-0519-4660-8488-2fd564da6921
-- title:
--   Posterior parameterization and log-partition function
-- statement:
--   The private parameter-space constructions identify $E\times(E\toL[\mathbb{R}]E)$ with a Euclidean coordinate space, define the linear score $\langle c,x\rangle-\frac12\langle Qx,x\rangle$, represent it as a parameter-space feature, and push a probability measure forward to `partitionLaw`. The public definition `logPartition μ c Q` is $\psi(c,Q)=\log\int_E\exp(\langle c,x\rangle-\frac12\langle Qx,x\rangle)\,d\mu(x)$ for a probability measure $\mu$ on a finite-dimensional complete real inner-product space. The bundle also proves continuity of the score and feature maps and constructs the associated measurable pushforward.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Probability/Posterior/LogPartition.lean#L24-L129 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Probability.Posterior.LogPartition`, definition bundle `KLS408915f_FunctionalInequalities_Probability_Posterior_LogPartition`; the repository is private at upload time).

import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Calculus
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Cumulant_Basic
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
import Definitions.Def_KLS408915f_FunctionalInequalities_Probability_Posterior_JointRegularity
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
import Mathlib.Probability.Moments.Variance

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace ContDiff
namespace FunctionalInequalities
namespace Probability
namespace Posterior
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
 abbrev partitionParameterSpace :=
  EuclideanSpace ℝ (Fin (Module.finrank ℝ (E × (E →L[ℝ] E))))
 def partitionParameterChart : (E × (E →L[ℝ] E)) ≃L[ℝ]
    FunctionalInequalities.Probability.Posterior.partitionParameterSpace (E := E) :=
  (Module.finBasis ℝ (E × (E →L[ℝ] E))).equivFunL.trans
    (PiLp.continuousLinearEquiv 2 ℝ
      (fun _ : Fin (Module.finrank ℝ (E × (E →L[ℝ] E))) => ℝ)).symm
 def partitionParameterScore (x : E) :
    (E × (E →L[ℝ] E)) →L[ℝ] ℝ :=
  (innerSL ℝ x).comp (ContinuousLinearMap.fst ℝ E (E →L[ℝ] E)) -
    (1 / 2 : ℝ) • ((innerSL ℝ x).comp
      ((ContinuousLinearMap.apply ℝ E x).comp
        (ContinuousLinearMap.snd ℝ E (E →L[ℝ] E))))
omit [CompleteSpace E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] in
 theorem partitionParameterScore_continuous :
    Continuous (FunctionalInequalities.Probability.Posterior.partitionParameterScore (E := E)) := by
  have hi : Continuous (fun x : E => innerSL ℝ x) :=
    (InnerProductSpace.toDualMap ℝ E).continuous
  have he : Continuous (fun x : E =>
      (ContinuousLinearMap.apply ℝ E x).comp
        (ContinuousLinearMap.snd ℝ E (E →L[ℝ] E))) :=
    (ContinuousLinearMap.apply ℝ E).continuous.clm_comp_const _
  exact (hi.clm_comp_const _).sub
    ((hi.clm_comp he).const_smul (1 / 2 : ℝ))
 def partitionParameterFeature (x : E) :
    FunctionalInequalities.Probability.Posterior.partitionParameterSpace (E := E) :=
  (InnerProductSpace.toDual ℝ _).symm
    ((FunctionalInequalities.Probability.Posterior.partitionParameterScore x).comp
      (FunctionalInequalities.Probability.Posterior.partitionParameterChart (E := E)).symm.toContinuousLinearMap)
omit [CompleteSpace E] [MeasurableSpace E] [BorelSpace E] in
 theorem partitionParameterFeature_continuous :
    Continuous (FunctionalInequalities.Probability.Posterior.partitionParameterFeature (E := E)) :=
  (InnerProductSpace.toDual ℝ _).symm.continuous.comp
    ((FunctionalInequalities.Probability.Posterior.partitionParameterScore_continuous (E := E)).clm_comp_const
      (FunctionalInequalities.Probability.Posterior.partitionParameterChart (E := E)).symm.toContinuousLinearMap)
 def partitionLaw (μ : ProbabilityMeasure E) :
    ProbabilityMeasure (FunctionalInequalities.Probability.Posterior.partitionParameterSpace (E := E)) :=
  μ.map (FunctionalInequalities.Probability.Posterior.partitionParameterFeature_continuous (E := E)).measurable.aemeasurable
/-- The log-partition function `ψ(c, Q) = log ∫ e^{⟪c,x⟫ − ½⟪Qx,x⟫} dμ(x)` of the BKL posterior (67). -/
def logPartition (μ : ProbabilityMeasure E) (c : E) (Q : E →L[ℝ] E) : ℝ :=
  Real.log (∫ x, Real.exp (quadraticExponent c Q x) ∂(μ : Measure E))
end Posterior
end Probability
end FunctionalInequalities


