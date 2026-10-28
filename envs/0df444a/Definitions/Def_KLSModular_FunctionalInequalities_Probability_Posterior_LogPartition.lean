-- Prove2me | Definitions.Def_KLSModular_FunctionalInequalities_Probability_Posterior_LogPartition
-- name    : KLSModular_FunctionalInequalities_Probability_Posterior_LogPartition
-- status  : Definition
-- author  : @Lazyfill
-- created : 2026-10-25T15:59:28.688576+00:00
-- url     : https://prove2.me/theorems/b716da65-348c-498f-97a9-23cbe395f8fd
-- title:
--   Posterior parameterization and log-partition function
-- statement:
--   The private parameter-space constructions identify $E\times(E\toL[\mathbb{R}]E)$ with a Euclidean coordinate space, define the linear score $\langle c,x\rangle-\frac12\langle Qx,x\rangle$, represent it as a parameter-space feature, and push a probability measure forward to `partitionLaw`. The public definition `logPartition μ c Q` is $\psi(c,Q)=\log\int_E\exp(\langle c,x\rangle-\frac12\langle Qx,x\rangle)\,d\mu(x)$ for a probability measure $\mu$ on a finite-dimensional complete real inner-product space. The bundle also proves continuity of the score and feature maps and constructs the associated measurable pushforward.
--
--   **Original module imports**
--
--   ```lean
--   import FunctionalInequalities.Probability.Posterior.JointRegularity
--   import FunctionalInequalities.Analysis.BakryEmery.Cumulant.Basic
--   ```
--
--   **Original declaration excerpt**
--
--   Shown in the original module context.
--
--   ```lean
--   private abbrev partitionParameterSpace :=
--     EuclideanSpace ℝ (Fin (Module.finrank ℝ (E × (E →L[ℝ] E))))
--   ```
--
--   **Module navigation**
--
--   Direct project imports: [`Probability/Posterior/JointRegularity`](https://prove2.me/theorems/38b44b15-e229-4b35-89b9-63261754a611), [`Analysis/BakryEmery/Cumulant/Basic`](https://prove2.me/theorems/c2d5b99d-f2d1-47d4-a2c5-2cf685ca2598).
--
--   Theorems in source order:
--
--   - [`contDiff_logPartition_joint`](https://prove2.me/theorems/4f6af24d-bf34-47a4-ab0b-b8f6855e12d6)
--   - [`logLaplace_compactPosterior`](https://prove2.me/theorems/d8a2d036-0686-4a74-b74b-f00a4e04d654)
--   - [`cumulant_compactPosterior`](https://prove2.me/theorems/be65aff1-f18a-49ae-a8b8-b2bf0b7da5d2)
--   - [`fderiv_logPartition_c_apply`](https://prove2.me/theorems/d56dc845-a2d9-42d9-b22a-bbd6ef8df04f)
--
--   Project result: [The KLS conjecture](https://prove2.me/theorems/c4e9e57c-586c-4945-927e-7f33933f1111).
--
--   [Original module](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Probability/Posterior/LogPartition.lean) · `FunctionalInequalities.Probability.Posterior.LogPartition` · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Probability/Posterior/LogPartition.lean#L24-L129 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Probability.Posterior.LogPartition`, definition bundle `KLSModular_FunctionalInequalities_Probability_Posterior_LogPartition`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_Probability_Posterior_JointRegularity
import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_BakryEmery_Cumulant_Basic

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


