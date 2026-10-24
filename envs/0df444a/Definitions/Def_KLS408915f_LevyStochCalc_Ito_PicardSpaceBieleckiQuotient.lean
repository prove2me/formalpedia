-- Prove2me | Definitions.Def_KLS408915f_LevyStochCalc_Ito_PicardSpaceBieleckiQuotient
-- name    : KLS408915f_LevyStochCalc_Ito_PicardSpaceBieleckiQuotient
-- status  : Definition
-- author  : @Lazyfill
-- created : 2026-10-23T10:09:40.597467+00:00
-- url     : https://prove2.me/theorems/4073c4a5-9c31-4a97-b7a1-a70893eb1853
-- title:
--   Bielecki type synonym and separation quotient
-- statement:
--   Vendored from the LevyStochCalc library (https://github.com/cgarryZA/LevyStochCalc). `SBoundedProcess.WithBielecki` is a type synonym for `SBoundedProcess` carrying a phantom weight $\beta$ so distinct Bielecki edist instances can coexist; `of` and `get` are inverse wrappers. Its `PseudoEMetricSpace` edist is `bieleckiEDist`, and `SBoundedProcess.AEQuot` is the `SeparationQuotient` of this pseudo-emetric space, with the induced genuine emetric-space structure. The zero process supplies nonempty instances for both types.
-- source:
--   Lean source: https://github.com/cgarryZA/LevyStochCalc/blob/984dbf0b790031eac05d56fe5a84b65e15e1e932/LevyStochCalc/Ito/PicardSpaceBieleckiQuotient.lean#L37-L365 (repository human-ai-mathematics/kls-lean, commit 408915f, module `LevyStochCalc.Ito.PicardSpaceBieleckiQuotient`, definition bundle `KLS408915f_LevyStochCalc_Ito_PicardSpaceBieleckiQuotient`; the repository is private at upload time). Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (Apache-2.0; upstream copyright notice retained in the Lean text).

import Definitions.Def_KLS408915f_BrownianMotion_Auxiliary_Algebra
import Definitions.Def_KLS408915f_BrownianMotion_Auxiliary_DenseCountable
import Definitions.Def_KLS408915f_BrownianMotion_Auxiliary_ENNReal
import Definitions.Def_KLS408915f_BrownianMotion_Auxiliary_Filtration
import Definitions.Def_KLS408915f_BrownianMotion_Auxiliary_FiniteInf
import Definitions.Def_KLS408915f_BrownianMotion_Auxiliary_Indistinguishable
import Definitions.Def_KLS408915f_BrownianMotion_Auxiliary_LeftLimWithin
import Definitions.Def_KLS408915f_BrownianMotion_Auxiliary_LinearAlgebra
import Definitions.Def_KLS408915f_BrownianMotion_Auxiliary_Martingale
import Definitions.Def_KLS408915f_BrownianMotion_Auxiliary_MeanInequalities
import Definitions.Def_KLS408915f_BrownianMotion_Auxiliary_MeasureTheory
import Definitions.Def_KLS408915f_BrownianMotion_Auxiliary_Metric
import Definitions.Def_KLS408915f_BrownianMotion_Auxiliary_Nat
import Definitions.Def_KLS408915f_BrownianMotion_Auxiliary_StoppedProcess
import Definitions.Def_KLS408915f_BrownianMotion_Auxiliary_Topology
import Definitions.Def_KLS408915f_BrownianMotion_Auxiliary_Upcrossing
import Definitions.Def_KLS408915f_BrownianMotion_Continuity_Chaining
import Definitions.Def_KLS408915f_BrownianMotion_Continuity_CoveringNumber
import Definitions.Def_KLS408915f_BrownianMotion_Continuity_HasBoundedInternalCoveringNumber
import Definitions.Def_KLS408915f_BrownianMotion_Continuity_IsKolmogorovProcess
import Definitions.Def_KLS408915f_BrownianMotion_Continuity_KolmogorovChentsov
import Definitions.Def_KLS408915f_BrownianMotion_Continuity_KolmogorovChentsovInequality
import Definitions.Def_KLS408915f_BrownianMotion_Continuity_LimitModification
import Definitions.Def_KLS408915f_BrownianMotion_Gaussian_BrownianMotion
import Definitions.Def_KLS408915f_BrownianMotion_Gaussian_Moment
import Definitions.Def_KLS408915f_BrownianMotion_Gaussian_ProjectiveLimit
import Definitions.Def_KLS408915f_BrownianMotion_Gaussian_StochasticProcesses
import Definitions.Def_KLS408915f_BrownianMotion_StochasticIntegral_Cadlag
import Definitions.Def_KLS408915f_BrownianMotion_StochasticIntegral_Predictable
import Definitions.Def_KLS408915f_BrownianMotion_StochasticIntegral_Quasimartingale_Basic
import Definitions.Def_KLS408915f_BrownianMotion_StochasticIntegral_Quasimartingale_CadlagModification
import Definitions.Def_KLS408915f_BrownianMotion_StochasticIntegral_Quasimartingale_MaximalInequality
import Definitions.Def_KLS408915f_BrownianMotion_StochasticIntegral_SimpleProcess
import Definitions.Def_KLS408915f_KolmogorovExtension4_CompactSystem
import Definitions.Def_KLS408915f_KolmogorovExtension4_KolmogorovExtension
import Definitions.Def_KLS408915f_KolmogorovExtension4_RegularContent
import Definitions.Def_KLS408915f_LevyStochCalc_Brownian_Construction
import Definitions.Def_KLS408915f_LevyStochCalc_Brownian_ContinuityDyadicChaining
import Definitions.Def_KLS408915f_LevyStochCalc_Brownian_Existence
import Definitions.Def_KLS408915f_LevyStochCalc_Brownian_Filtered
import Definitions.Def_KLS408915f_LevyStochCalc_Brownian_ItoDensityDyadicAverages
import Definitions.Def_KLS408915f_LevyStochCalc_Brownian_ItoDensityPointwise
import Definitions.Def_KLS408915f_LevyStochCalc_Brownian_ItoDensityPredictableL2
import Definitions.Def_KLS408915f_LevyStochCalc_Brownian_ItoDensityShiftedAverages
import Definitions.Def_KLS408915f_LevyStochCalc_Brownian_ItoDensityUnbounded
import Definitions.Def_KLS408915f_LevyStochCalc_Brownian_ItoL2CompletionApi
import Definitions.Def_KLS408915f_LevyStochCalc_Brownian_ItoL2CompletionConvergence
import Definitions.Def_KLS408915f_LevyStochCalc_Brownian_ItoL2CompletionExistence
import Definitions.Def_KLS408915f_LevyStochCalc_Brownian_ItoL2CompletionIncrement
import Definitions.Def_KLS408915f_LevyStochCalc_Brownian_ItoL2CompletionLp
import Definitions.Def_KLS408915f_LevyStochCalc_Brownian_ItoL2CompletionMaster
import Definitions.Def_KLS408915f_LevyStochCalc_Brownian_ItoL2CompletionQuadVar
import Definitions.Def_KLS408915f_LevyStochCalc_Brownian_ItoMartingale
import Definitions.Def_KLS408915f_LevyStochCalc_Brownian_ItoSimpleIntegrand
import Definitions.Def_KLS408915f_LevyStochCalc_Brownian_ItoSimpleIsometry
import Definitions.Def_KLS408915f_LevyStochCalc_Brownian_ItoSimpleMoments
import Definitions.Def_KLS408915f_LevyStochCalc_Brownian_Martingale
import Definitions.Def_KLS408915f_LevyStochCalc_Brownian_MartingaleCondExp
import Definitions.Def_KLS408915f_LevyStochCalc_Brownian_Multidim
import Definitions.Def_KLS408915f_LevyStochCalc_Brownian_MultidimFiltered
import Definitions.Def_KLS408915f_LevyStochCalc_Brownian_MultidimIto
import Definitions.Def_KLS408915f_LevyStochCalc_Brownian_SimplePredictableRefineAppend
import Definitions.Def_KLS408915f_LevyStochCalc_Brownian_SimplePredictableRefineCommon
import Definitions.Def_KLS408915f_LevyStochCalc_Brownian_SimplePredictableRefineInvariance
import Definitions.Def_KLS408915f_LevyStochCalc_Ito_PicardBieleckiNorm
import Definitions.Def_KLS408915f_LevyStochCalc_Ito_PicardSpaceBieleckiEDist
import Definitions.Def_KLS408915f_LevyStochCalc_Ito_PicardSpaceDiscrete
import Definitions.Def_KLS408915f_LevyStochCalc_Ito_PicardStepMap
import Definitions.Def_KLS408915f_LevyStochCalc_Ito_PicardStochasticLipschitz
import Definitions.Def_KLS408915f_LevyStochCalc_Ito_Setting
import Definitions.Def_KLS408915f_LevyStochCalc_Martingale_CadlagModification
import Definitions.Def_KLS408915f_LevyStochCalc_Martingale_RightCont
import Definitions.Def_KLS408915f_LevyStochCalc_Poisson_Compensated
import Definitions.Def_KLS408915f_LevyStochCalc_Poisson_CompensatedApprox
import Definitions.Def_KLS408915f_LevyStochCalc_Poisson_CompensatedDensityBoxIsometry
import Definitions.Def_KLS408915f_LevyStochCalc_Poisson_CompensatedDensityDyadic
import Definitions.Def_KLS408915f_LevyStochCalc_Poisson_CompensatedDensityLimit
import Definitions.Def_KLS408915f_LevyStochCalc_Poisson_CompensatedDensityMarkApprox
import Definitions.Def_KLS408915f_LevyStochCalc_Poisson_CompensatedDensityMarkSum
import Definitions.Def_KLS408915f_LevyStochCalc_Poisson_CompensatedDensityRectSimple
import Definitions.Def_KLS408915f_LevyStochCalc_Poisson_CompensatedDensityRefinement
import Definitions.Def_KLS408915f_LevyStochCalc_Poisson_CompensatedDensityShifted
import Definitions.Def_KLS408915f_LevyStochCalc_Poisson_CompensatedDensityStepIntegral
import Definitions.Def_KLS408915f_LevyStochCalc_Poisson_CompensatedDensityTruncation
import Definitions.Def_KLS408915f_LevyStochCalc_Poisson_CompensatedDiff
import Definitions.Def_KLS408915f_LevyStochCalc_Poisson_CompensatedIsometry
import Definitions.Def_KLS408915f_LevyStochCalc_Poisson_CompensatedMartingaleAdapted
import Definitions.Def_KLS408915f_LevyStochCalc_Poisson_CompensatedMartingaleIncrement
import Definitions.Def_KLS408915f_LevyStochCalc_Poisson_CompensatedMartingaleQuadratic
import Definitions.Def_KLS408915f_LevyStochCalc_Poisson_CompensatedProcess
import Definitions.Def_KLS408915f_LevyStochCalc_Poisson_CompensatedProcessQuadVar
import Definitions.Def_KLS408915f_LevyStochCalc_Poisson_CompensatedSimple
import Definitions.Def_KLS408915f_LevyStochCalc_Poisson_Filtered
import Definitions.Def_KLS408915f_LevyStochCalc_Poisson_MarkStepIncrement
import Definitions.Def_KLS408915f_LevyStochCalc_Poisson_MarkStepIsometry
import Definitions.Def_KLS408915f_LevyStochCalc_Poisson_MarkStepWeight
import Definitions.Def_KLS408915f_LevyStochCalc_Poisson_PoissonSuperposition
import Definitions.Def_KLS408915f_LevyStochCalc_Poisson_RandomMeasure
import Definitions.Def_KLS408915f_LevyStochCalc_Probability_IndepJoin
import Definitions.Def_KLS408915f_LevyStochCalc_Probability_Progressive
import Definitions.Def_KLS408915f_LevyStochCalc_Probability_Transport
import Definitions.Def_KLS408915f_LevyStochCalc_Probability_TrivialSigma
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Convex.Integral
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.InnerProductSpace.GramMatrix
import Mathlib.Analysis.MeanInequalities
import Mathlib.Analysis.Normed.Group.Continuity
import Mathlib.Analysis.Normed.Module.Ball.Pointwise
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Data.Finset.Max
import Mathlib.Data.NNReal.Basic
import Mathlib.Data.Set.Finite.Lattice
import Mathlib.Data.Set.FiniteExhaustion
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.LinearAlgebra.Matrix.BilinearForm
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.SesquilinearForm.Star
import Mathlib.MeasureTheory.Constructions.BorelSpace.ContinuousLinearMap
import Mathlib.MeasureTheory.Constructions.ClosedCompactCylinders
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.MeasureTheory.Constructions.ProjectiveFamilyContent
import Mathlib.MeasureTheory.Covering.DensityTheorem
import Mathlib.MeasureTheory.Function.ConditionalExpectation.CondJensen
import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Real
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.MeasureTheory.Function.Holder
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm
import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Basic
import Mathlib.MeasureTheory.Function.UniformIntegrable
import Mathlib.MeasureTheory.Group.Arithmetic
import Mathlib.MeasureTheory.Integral.Average
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.Layercake
import Mathlib.MeasureTheory.Integral.MeanInequalities
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.MeasurableSpace.Constructions
import Mathlib.MeasureTheory.Measure.AddContent
import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic
import Mathlib.MeasureTheory.Measure.HasOuterApproxClosed
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Measure.RegularityCompacts
import Mathlib.MeasureTheory.OuterMeasure.OfAddContent
import Mathlib.MeasureTheory.SetSemiring
import Mathlib.Order.CompleteLattice.Group
import Mathlib.Order.CompletePartialOrder
import Mathlib.Order.ConditionallyCompleteLattice.Finset
import Mathlib.Order.ConditionallyCompletePartialOrder.Indexed
import Mathlib.Probability.BrownianMotion.Basic
import Mathlib.Probability.ConditionalExpectation
import Mathlib.Probability.Distributions.Gaussian.CharFun
import Mathlib.Probability.Distributions.Gaussian.Fernique
import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Basic
import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Independence
import Mathlib.Probability.Distributions.Gaussian.IsGaussianProcess.Basic
import Mathlib.Probability.Distributions.Gaussian.IsGaussianProcess.Independence
import Mathlib.Probability.Distributions.Gaussian.Multivariate
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Probability.Distributions.Poisson.Basic
import Mathlib.Probability.Independence.Basic
import Mathlib.Probability.Independence.BoundedContinuousFunction
import Mathlib.Probability.Independence.CharacteristicFunction
import Mathlib.Probability.Independence.InfinitePi
import Mathlib.Probability.Independence.Integration
import Mathlib.Probability.Independence.Process.HasIndepIncrements.Basic
import Mathlib.Probability.Independence.ZeroOne
import Mathlib.Probability.Kernel.Defs
import Mathlib.Probability.Martingale.Basic
import Mathlib.Probability.Martingale.OptionalStopping
import Mathlib.Probability.Martingale.Upcrossing
import Mathlib.Probability.Moments.CovarianceBilin
import Mathlib.Probability.Notation
import Mathlib.Probability.Process.Adapted
import Mathlib.Probability.Process.Filtration
import Mathlib.Probability.Process.Kolmogorov
import Mathlib.Probability.Process.Predictable
import Mathlib.Probability.Process.Stopping
import Mathlib.Topology.Algebra.MulAction
import Mathlib.Topology.Bases
import Mathlib.Topology.Compactness.CompactSystem
import Mathlib.Topology.ContinuousMap.SecondCountableSpace
import Mathlib.Topology.EMetricSpace.PairReduction
import Mathlib.Topology.Instances.ENNReal.Lemmas
import Mathlib.Topology.IsClosedRestrict
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Topology.MetricSpace.Bounded
import Mathlib.Topology.MetricSpace.Contracting
import Mathlib.Topology.MetricSpace.Cover
import Mathlib.Topology.MetricSpace.CoveringNumbers
import Mathlib.Topology.MetricSpace.HolderNorm
import Mathlib.Topology.MetricSpace.MetricSeparated
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Order.DenselyOrdered
import Mathlib.Topology.Order.LeftRight
import Mathlib.Topology.Order.LeftRightLim
import Mathlib.Topology.Order.Monotone
import Mathlib.Topology.Order.MonotoneContinuity
import Mathlib.Topology.Separation.Regular
import Mathlib.Topology.UniformSpace.Cauchy
import Mathlib.Topology.UniformSpace.UniformEmbedding

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Ito/PicardSpaceBieleckiQuotient.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
namespace LevyStochCalc
namespace Ito
namespace Picard
universe u v
variable {Ω : Type u} [MeasurableSpace Ω]
/-- **Type synonym for `SBoundedProcess` carrying the Bielecki β-weighted
pseudo-edist instance.** Two `SBoundedProcess`es that agree P-a.s. at
every `t` have Bielecki pseudo-distance zero; this synonym carries the
pseudo-metric, and `SBoundedProcess.AEQuot` (the `SeparationQuotient`)
carries the genuine metric.

The phantom `β` allows different Bielecki β-values to define distinct
typeclass instances on the same underlying type. The `β` parameter is
intentionally unused in the type definition (it only affects the
distinct `EDist` instance that downstream registers on it). -/
def SBoundedProcess.WithBielecki (n : ℕ) (P : Measure Ω)
    [IsProbabilityMeasure P] (ℱ : Filtration ℝ ‹MeasurableSpace Ω›)
    (T β : ℝ) : Type _ :=
  let _ := β  -- silence "unused variable β" — phantom parameter
  SBoundedProcess (n := n) P ℱ T
namespace SBoundedProcess
namespace WithBielecki
variable {n : ℕ} {P : Measure Ω} [IsProbabilityMeasure P]
    {ℱ : Filtration ℝ ‹MeasurableSpace Ω›} {T β : ℝ}
/-- **Constructor.** Wrap a `SBoundedProcess` as the Bielecki-flavored type. -/
def of (X : SBoundedProcess (n := n) P ℱ T) :
    SBoundedProcess.WithBielecki (n := n) P ℱ T β := X
/-- **Underlying `SBoundedProcess` extractor.** -/
def get (X : SBoundedProcess.WithBielecki (n := n) P ℱ T β) :
    SBoundedProcess (n := n) P ℱ T := X
@[simp] lemma get_of (X : SBoundedProcess (n := n) P ℱ T) :
    SBoundedProcess.WithBielecki.get (SBoundedProcess.WithBielecki.of (n := n) (β := β) X) = X
    := rfl
@[simp] lemma of_get (X : SBoundedProcess.WithBielecki (n := n) P ℱ T β) :
    SBoundedProcess.WithBielecki.of (n := n) (β := β)
      (SBoundedProcess.WithBielecki.get X) = X := rfl
end WithBielecki
end SBoundedProcess
noncomputable instance instEDistWithBielecki
    {n : ℕ} {P : Measure Ω} [IsProbabilityMeasure P]
    {ℱ : Filtration ℝ ‹MeasurableSpace Ω›} {T β : ℝ} :
    EDist (SBoundedProcess.WithBielecki (n := n) P ℱ T β) where
  edist X Y := bieleckiEDist β T
    (SBoundedProcess.WithBielecki.get X)
    (SBoundedProcess.WithBielecki.get Y)
@[simp] lemma edist_WithBielecki_def
    {n : ℕ} {P : Measure Ω} [IsProbabilityMeasure P]
    {ℱ : Filtration ℝ ‹MeasurableSpace Ω›} {T β : ℝ}
    (X Y : SBoundedProcess.WithBielecki (n := n) P ℱ T β) :
    edist X Y = bieleckiEDist β T
      (SBoundedProcess.WithBielecki.get X) (SBoundedProcess.WithBielecki.get Y) := rfl
/-- **Slice-AEMeasurability of the Bielecki inner integrand.** From joint
measurability of `(t, ω) ↦ X t ω`, the per-`t` slice `ω ↦ X t ω` is
measurable; composing with the continuous `r ↦ ‖r‖₊²` and finite sum
preserves measurability; the (1/2)-rpow is measurable; pushing through
gives AEMeasurable of the inner Bielecki expression. -/
lemma bieleckiNorm_inner_aemeasurable
    {n : ℕ} {P : Measure Ω} [IsProbabilityMeasure P]
    (X : ℝ → Ω → (Fin n → ℝ))
    (hX_meas : Measurable (Function.uncurry X)) (t : ℝ) :
    AEMeasurable
      (fun ω => (∑ i, (‖X t ω i‖₊ : ℝ≥0∞) ^ 2) ^ ((1 : ℝ) / 2)) P := by
  -- Slice-measurability of `ω ↦ X t ω` via `Measurable.of_uncurry_left`.
  have h_slice : Measurable (fun ω => X t ω) :=
    Measurable.of_uncurry_left hX_meas
  -- Each component `ω ↦ X t ω i` is measurable (composition with
  -- evaluation).
  have h_comp : ∀ i, Measurable (fun ω => X t ω i) := fun i =>
    h_slice.eval
  -- Each summand `ω ↦ ‖X t ω i‖₊²` is measurable.
  have h_summand : ∀ i, Measurable
      (fun ω => ((‖X t ω i‖₊ : ℝ≥0∞)) ^ 2) := by
    intro i
    refine (Measurable.pow_const ?_ _)
    refine (ENNReal.continuous_coe.measurable.comp ?_)
    exact ((h_comp i).nnnorm)
  -- Finite sum is measurable.
  have h_sum : Measurable (fun ω => ∑ i, ((‖X t ω i‖₊ : ℝ≥0∞)) ^ 2) :=
    Finset.measurable_sum _ (fun i _ => h_summand i)
  -- Composing with the continuous `x ↦ x ^ (1/2)`.
  exact (h_sum.pow_const ((1 : ℝ) / 2)).aemeasurable
/-- **AEMeasurability of the Bielecki inner integrand for the path
difference of two `SBoundedProcess`es.** Follows from
`bieleckiNorm_inner_aemeasurable` applied to `X.X - Y.X` after showing
the difference is jointly measurable. -/
lemma SBoundedProcess.pathDiff_aemeasurable
    {n : ℕ} {P : Measure Ω} [IsProbabilityMeasure P]
    {ℱ : Filtration ℝ ‹MeasurableSpace Ω›} {T : ℝ}
    (X Y : SBoundedProcess (n := n) P ℱ T) (t : ℝ) :
    AEMeasurable (fun ω => (∑ i, (‖(X.X t ω - Y.X t ω) i‖₊ : ℝ≥0∞) ^ 2)
        ^ ((1 : ℝ) / 2)) P := by
  -- The pointwise difference `fun t ω => X.X t ω - Y.X t ω` is jointly
  -- measurable as the difference of two jointly measurable functions.
  have h_diff_meas : Measurable
      (Function.uncurry (fun t ω => X.X t ω - Y.X t ω)) := by
    have : Function.uncurry (fun t ω => X.X t ω - Y.X t ω)
        = fun p : ℝ × Ω => X.X p.1 p.2 - Y.X p.1 p.2 := by
      funext p
      rfl
    rw [this]
    exact X.measurable_path.sub Y.measurable_path
  exact bieleckiNorm_inner_aemeasurable
    (fun t ω => X.X t ω - Y.X t ω) h_diff_meas t
/-- **Triangle inequality for the Bielecki β-norm pseudo-edist.**
For `SBoundedProcess`es X, Y, Z, applying `bieleckiNorm_add_le` to
`Y₁ = X.X - Y.X`, `Y₂ = Y.X - Z.X` gives the triangle inequality. -/
lemma bieleckiEDist_triangle
    {n : ℕ} {P : Measure Ω} [IsProbabilityMeasure P]
    {ℱ : Filtration ℝ ‹MeasurableSpace Ω›} {β T : ℝ}
    (X Y Z : SBoundedProcess (n := n) P ℱ T) :
    bieleckiEDist β T X Z
      ≤ bieleckiEDist β T X Y + bieleckiEDist β T Y Z := by
  -- (X.X - Z.X) = (X.X - Y.X) + (Y.X - Z.X) pointwise.
  have h_id : (fun t ω => X.X t ω - Z.X t ω)
      = fun t ω => (X.X t ω - Y.X t ω) + (Y.X t ω - Z.X t ω) := by
    funext t ω
    funext i
    change X.X t ω i - Z.X t ω i = (X.X t ω i - Y.X t ω i) + (Y.X t ω i - Z.X t ω i)
    ring
  -- Apply `bieleckiNorm_add_le`.
  have h := bieleckiNorm_add_le (P := P) β T
    (fun t ω => X.X t ω - Y.X t ω) (fun t ω => Y.X t ω - Z.X t ω)
    (fun t => SBoundedProcess.pathDiff_aemeasurable X Y t)
    (fun t => SBoundedProcess.pathDiff_aemeasurable Y Z t)
  -- Conclude via the pointwise identity.
  change bieleckiNorm (P := P) β T (SBoundedProcess.pathDiff X Z)
    ≤ bieleckiNorm (P := P) β T (SBoundedProcess.pathDiff X Y)
      + bieleckiNorm (P := P) β T (SBoundedProcess.pathDiff Y Z)
  unfold SBoundedProcess.pathDiff
  rw [h_id]
  exact h
noncomputable instance instPseudoEMetricSpaceWithBielecki
    {n : ℕ} {P : Measure Ω} [IsProbabilityMeasure P]
    {ℱ : Filtration ℝ ‹MeasurableSpace Ω›} {T β : ℝ} :
    PseudoEMetricSpace (SBoundedProcess.WithBielecki (n := n) P ℱ T β) where
  edist_self X := by
    change bieleckiEDist β T (SBoundedProcess.WithBielecki.get X)
      (SBoundedProcess.WithBielecki.get X) = 0
    exact bieleckiEDist_self _
  edist_comm X Y := by
    change bieleckiEDist β T (SBoundedProcess.WithBielecki.get X)
        (SBoundedProcess.WithBielecki.get Y)
      = bieleckiEDist β T (SBoundedProcess.WithBielecki.get Y)
        (SBoundedProcess.WithBielecki.get X)
    exact bieleckiEDist_comm _ _
  edist_triangle X Y Z := by
    change bieleckiEDist β T (SBoundedProcess.WithBielecki.get X)
        (SBoundedProcess.WithBielecki.get Z)
      ≤ bieleckiEDist β T (SBoundedProcess.WithBielecki.get X)
        (SBoundedProcess.WithBielecki.get Y)
        + bieleckiEDist β T (SBoundedProcess.WithBielecki.get Y)
          (SBoundedProcess.WithBielecki.get Z)
    exact bieleckiEDist_triangle _ _ _
/-- **AE-quotient of `SBoundedProcess` by P-null-set equivalence.**

  `AEQuot β T := SeparationQuotient (SBoundedProcess.WithBielecki β T)`.

Mathlib's `SeparationQuotient` of a `PseudoEMetricSpace` is automatically
a genuine `EMetricSpace` (separated) — and hence a `MetricSpace` once we
project the edist down to a real-valued distance. This is the literature
Banach space `S²([0, T]; ℝⁿ)` modulo P-null-set equivalence. -/
def SBoundedProcess.AEQuot
    (n : ℕ) (P : Measure Ω) [IsProbabilityMeasure P]
    (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (T β : ℝ) : Type _ :=
  SeparationQuotient (SBoundedProcess.WithBielecki (n := n) P ℱ T β)
/-- Mathlib auto-derives `EMetricSpace` on the `SeparationQuotient`.
Re-export under the project's namespace. -/
noncomputable instance instEMetricSpaceAEQuot
    {n : ℕ} {P : Measure Ω} [IsProbabilityMeasure P]
    {ℱ : Filtration ℝ ‹MeasurableSpace Ω›} {T β : ℝ} :
    EMetricSpace (SBoundedProcess.AEQuot (n := n) P ℱ T β) :=
  instEMetricSpaceSeparationQuotient
end Picard
end Ito
end LevyStochCalc
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
namespace LevyStochCalc
namespace Ito
namespace Picard
universe u v
variable {Ω : Type u} [MeasurableSpace Ω]
variable {E : Type v} [MeasurableSpace E]
/-- **Nonemptiness of `WithBielecki β T`.** The constant-zero
`SBoundedProcess` (from `PicardSpace.lean`) witnesses inhabitedness
of the underlying type, which inhabits the type synonym. -/
noncomputable instance instNonemptyWithBielecki
    {n : ℕ} {P : Measure Ω} [IsProbabilityMeasure P]
    {ℱ : Filtration ℝ ‹MeasurableSpace Ω›} {T β : ℝ} :
    Nonempty (SBoundedProcess.WithBielecki (n := n) P ℱ T β) :=
  ⟨SBoundedProcess.WithBielecki.of (β := β) (constantZeroProcess (n := n) P ℱ T)⟩
/-- **Nonemptiness of `AEQuot β T`.** Lifts from the constant-zero process
via `SeparationQuotient.mk`. -/
noncomputable instance instNonemptyAEQuot
    {n : ℕ} {P : Measure Ω} [IsProbabilityMeasure P]
    {ℱ : Filtration ℝ ‹MeasurableSpace Ω›} {T β : ℝ} :
    Nonempty (SBoundedProcess.AEQuot (n := n) P ℱ T β) :=
  ⟨SeparationQuotient.mk (SBoundedProcess.WithBielecki.of (β := β)
    (constantZeroProcess (n := n) P ℱ T))⟩
end Picard
end Ito
end LevyStochCalc


