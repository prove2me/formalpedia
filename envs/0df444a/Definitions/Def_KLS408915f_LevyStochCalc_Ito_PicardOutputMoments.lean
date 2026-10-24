-- Prove2me | Definitions.Def_KLS408915f_LevyStochCalc_Ito_PicardOutputMoments
-- name    : KLS408915f_LevyStochCalc_Ito_PicardOutputMoments
-- status  : Definition
-- author  : @Lazyfill
-- created : 2026-10-23T10:13:50.599266+00:00
-- url     : https://prove2.me/theorems/d4453c59-c999-4474-9450-416d33f80866
-- title:
--   Second-moment bounds for Picard outputs
-- statement:
--   Vendored from the LevyStochCalc library (https://github.com/cgarryZA/LevyStochCalc). The bundle states the Brownian and compensated-Poisson Itô isometries for nonnegative horizons, including $T=0$, and bounds the second moments of the diffusion, drift, and jump components of `picardStep` using their integrand energies. The drift estimate uses Cauchy–Schwarz on $[0,t]$, while the stochastic terms use their respective isometries; all moment expressions are $\mathbb{R}_{\ge 0}\cup\{\infty\}$-valued lintegrals under a probability measure. Combining the three components gives `bieleckiNorm_picardStep_lt_top` under finite horizon data.
-- source:
--   Lean source: https://github.com/cgarryZA/LevyStochCalc/blob/984dbf0b790031eac05d56fe5a84b65e15e1e932/LevyStochCalc/Ito/PicardOutputMoments.lean#L30-L537 (repository human-ai-mathematics/kls-lean, commit 408915f, module `LevyStochCalc.Ito.PicardOutputMoments`, definition bundle `KLS408915f_LevyStochCalc_Ito_PicardOutputMoments`; the repository is private at upload time). Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (Apache-2.0; upstream copyright notice retained in the Lean text).

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
import Definitions.Def_KLS408915f_LevyStochCalc_Ito_PicardIntegrandBounds
import Definitions.Def_KLS408915f_LevyStochCalc_Ito_PicardIntegrandFrozen
import Definitions.Def_KLS408915f_LevyStochCalc_Ito_PicardSpaceBieleckiEDist
import Definitions.Def_KLS408915f_LevyStochCalc_Ito_PicardSpaceBieleckiQuotient
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
import Definitions.Def_KLS408915f_LevyStochCalc_Probability_ProgressiveCadlag
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
import Mathlib.MeasureTheory.Function.Floor
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
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Ito/PicardOutputMoments.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
namespace LevyStochCalc
namespace Ito
namespace Picard
universe u v
variable {Ω : Type u} [MeasurableSpace Ω]
variable {E : Type v} [MeasurableSpace E]
/-- Cauchy–Schwarz for a finite sum of reals, transported to `ℝ≥0∞`. -/
theorem sq_nnnorm_sum_le {ι : Type*} (s : Finset ι) (f : ι → ℝ) :
    (‖∑ j ∈ s, f j‖₊ : ℝ≥0∞) ^ 2 ≤ (s.card : ℝ≥0∞) * ∑ j ∈ s, (‖f j‖₊ : ℝ≥0∞) ^ 2 := by
  have h1 : (∑ j ∈ s, f j) ^ 2 ≤ (s.card : ℝ) * ∑ j ∈ s, (f j) ^ 2 :=
    sq_sum_le_card_mul_sum_sq
  calc (‖∑ j ∈ s, f j‖₊ : ℝ≥0∞) ^ 2
      = ENNReal.ofReal ((∑ j ∈ s, f j) ^ 2) := sq_coe_nnnorm_real _
    _ ≤ ENNReal.ofReal ((s.card : ℝ) * ∑ j ∈ s, (f j) ^ 2) := ENNReal.ofReal_le_ofReal h1
    _ = (s.card : ℝ≥0∞) * ∑ j ∈ s, (‖f j‖₊ : ℝ≥0∞) ^ 2 := by
        rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_natCast,
          ENNReal.ofReal_sum_of_nonneg (fun _ _ => sq_nonneg _)]
        exact congrArg _ (Finset.sum_congr rfl fun j _ => (sq_coe_nnnorm_real (f j)).symm)
variable {n d : ℕ} {P : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure P]
omit [MeasurableSpace E] in
/-- The Itô isometry at every nonnegative horizon, including `0`. -/
theorem itoIsometry_of_nonneg
    (W : LevyStochCalc.Brownian.BrownianMotion P)
    (ℱ : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›)
    (hℱ : LevyStochCalc.Brownian.IsBrownianFiltration W ℱ)
    (H : Ω → ℝ → ℝ)
    (h_meas : Measurable (Function.uncurry H))
    (h_progMeas : Probability.ProgressivelyMeasurable ℱ H)
    (h_sq : ∀ T : ℝ, 0 < T →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, (‖H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    {T : ℝ} (hT : 0 ≤ T) :
    ∫⁻ ω, (‖LevyStochCalc.Brownian.Ito.stochasticIntegral W ℱ hℱ H h_meas h_progMeas h_sq T ω‖₊
      : ℝ≥0∞) ^ 2 ∂P
      = ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, (‖H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P :=
  LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian_lintegral_sq W ℱ hℱ H h_meas h_progMeas
    h_sq hT
/-- The Itô–Lévy isometry at every nonnegative horizon, including `0`. -/
theorem compensatedIsometry_of_nonneg {ν : MeasureTheory.Measure E}
    [MeasureTheory.SigmaFinite ν]
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν)
    (ℱ : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›)
    (hℱ : LevyStochCalc.Poisson.IsPoissonFiltration N ℱ)
    (φ : Ω → ℝ → E → ℝ)
    (h_meas : Measurable fun p : Ω × ℝ × E => φ p.1 p.2.1 p.2.2)
    (h_progMeas : Probability.MarkedProgressivelyMeasurable ℱ φ)
    (h_sq : ∀ T : ℝ, 0 < T →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e,
        (‖φ ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P < ⊤)
    {T : ℝ} (hT : 0 ≤ T) :
    ∫⁻ ω, (‖LevyStochCalc.Poisson.Compensated.stochasticIntegral N ℱ hℱ φ h_meas h_progMeas
      h_sq T ω‖₊ : ℝ≥0∞) ^ 2 ∂P
      = ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e,
          (‖φ ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P := by
  rw [← LevyStochCalc.Poisson.Compensated.process_lintegral_sq' N ℱ hℱ φ h_meas h_progMeas
    h_sq hT]
  refine lintegral_congr_ae ?_
  filter_upwards [LevyStochCalc.Poisson.Compensated.stochasticIntegral_ae_eq_process N ℱ hℱ φ
    h_meas h_progMeas h_sq T] with ω hω
  rw [hω]
omit [MeasurableSpace E] in
/-- **Second moment of the diffusion component**, by the Itô isometry applied to each of the
`d` component integrals. -/
theorem lintegral_sq_picardStep_diffusion_le
    (W : LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion P d)
    (ℱ : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›)
    (hℱW : ∀ j : Fin d, LevyStochCalc.Brownian.IsBrownianFiltration (W.W j) ℱ)
    (coeffs : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs n d E)
    (X : ℝ → Ω → (Fin n → ℝ))
    (h_meas : ∀ i : Fin n, ∀ j : Fin d,
      Measurable (Function.uncurry (fun ω s => coeffs.σ s (X s ω) i j)))
    (h_progMeas : ∀ i : Fin n, ∀ j : Fin d,
        Probability.ProgressivelyMeasurable ℱ (fun ω s => coeffs.σ s (X s ω) i j))
    (h_sq : ∀ i : Fin n, ∀ j : Fin d, ∀ T : ℝ, 0 < T →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
        (‖coeffs.σ s (X s ω) i j‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    (i : Fin n) {t : ℝ} (ht : 0 ≤ t) :
    ∫⁻ ω, (‖picardStep_diffusion W ℱ hℱW coeffs X h_meas h_progMeas h_sq t ω i‖₊ : ℝ≥0∞) ^ 2 ∂P
      ≤ (d : ℝ≥0∞) * ∑ j : Fin d, ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) t,
          (‖coeffs.σ s (X s ω) i j‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P := by
  set M : Fin d → Ω → ℝ := fun j ω =>
    LevyStochCalc.Brownian.Ito.stochasticIntegral (W.W j) ℱ (hℱW j)
      (fun ω' s => coeffs.σ s (X s ω') i j)
      (h_meas i j) (h_progMeas i j) (h_sq i j) t ω with hM
  have hM_meas : ∀ j : Fin d, Measurable (M j) := by
    intro j
    obtain ⟨Filt, hMart⟩ := LevyStochCalc.Brownian.Ito.martingale_stochasticIntegral
      (W.W j) ℱ (hℱW j) (fun ω' s => coeffs.σ s (X s ω') i j)
      (h_meas i j) (h_progMeas i j) (h_sq i j)
    exact (hMart.stronglyMeasurable t).measurable.mono (Filt.le t) le_rfl
  have hunfold : ∀ ω : Ω,
      picardStep_diffusion W ℱ hℱW coeffs X h_meas h_progMeas h_sq t ω i
        = ∑ j : Fin d, M j ω := by
    intro ω
    simp only [picardStep_diffusion,
      LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.stochasticIntegral, M]
  calc ∫⁻ ω, (‖picardStep_diffusion W ℱ hℱW coeffs X h_meas h_progMeas h_sq t ω i‖₊
        : ℝ≥0∞) ^ 2 ∂P
      = ∫⁻ ω, (‖∑ j : Fin d, M j ω‖₊ : ℝ≥0∞) ^ 2 ∂P :=
        lintegral_congr fun ω => by rw [hunfold ω]
    _ ≤ ∫⁻ ω, (d : ℝ≥0∞) * ∑ j : Fin d, (‖M j ω‖₊ : ℝ≥0∞) ^ 2 ∂P := by
        refine lintegral_mono fun ω => ?_
        simpa using sq_nnnorm_sum_le (Finset.univ : Finset (Fin d)) (fun j => M j ω)
    _ = (d : ℝ≥0∞) * ∑ j : Fin d, ∫⁻ ω, (‖M j ω‖₊ : ℝ≥0∞) ^ 2 ∂P := by
        rw [MeasureTheory.lintegral_const_mul' _ _ (by simp : (d : ℝ≥0∞) ≠ ⊤),
          MeasureTheory.lintegral_finsetSum]
        exact fun j _ => ((hM_meas j).nnnorm.coe_nnreal_ennreal).pow_const 2
    _ = (d : ℝ≥0∞) * ∑ j : Fin d, ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) t,
          (‖coeffs.σ s (X s ω) i j‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P := by
        refine congrArg _ (Finset.sum_congr rfl fun j _ => ?_)
        exact itoIsometry_of_nonneg (W.W j) ℱ (hℱW j)
          (fun ω' s => coeffs.σ s (X s ω') i j)
          (h_meas i j) (h_progMeas i j) (h_sq i j) ht
/-- **Second moment of the jump component**, by the Itô–Lévy isometry. -/
theorem lintegral_sq_picardStep_jump_eq {ν : MeasureTheory.Measure E}
    [MeasureTheory.SigmaFinite ν]
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν)
    (ℱ : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›)
    (hℱN : LevyStochCalc.Poisson.IsPoissonFiltration N ℱ)
    (coeffs : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs n d E)
    (X : ℝ → Ω → (Fin n → ℝ))
    (h_meas : ∀ i : Fin n,
      Measurable (fun p : Ω × ℝ × E => coeffs.γ p.2.1 (X p.2.1 p.1) p.2.2 i))
    (h_progMeas : ∀ i : Fin n,
        Probability.MarkedProgressivelyMeasurable ℱ (fun ω s e => coeffs.γ s (X s ω) e i))
    (h_sq : ∀ i : Fin n, ∀ T : ℝ, 0 < T →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e,
        (‖coeffs.γ s (X s ω) e i‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P < ⊤)
    (i : Fin n) {t : ℝ} (ht : 0 ≤ t) :
    ∫⁻ ω, (‖picardStep_jump N ℱ hℱN coeffs X h_meas h_progMeas h_sq t ω i‖₊ : ℝ≥0∞) ^ 2 ∂P
      = ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) t, ∫⁻ e,
          (‖coeffs.γ s (X s ω) e i‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P :=
  compensatedIsometry_of_nonneg N ℱ hℱN
    (fun ω s e => coeffs.γ s (X s ω) e i) (h_meas i) (h_progMeas i) (h_sq i) ht
/-- The extended norm of a square. -/
theorem enorm_sq_eq (x : ℝ) : ‖x ^ 2‖ₑ = (‖x‖₊ : ℝ≥0∞) ^ 2 := by
  rw [← ENNReal.coe_pow, ← nnnorm_pow]
  rfl
omit [MeasurableSpace E] [MeasureTheory.IsProbabilityMeasure P] in
/-- A function with finite energy on a bounded window is `L²` there. -/
theorem memLp_two_of_lintegral_sq_lt_top {f : ℝ → ℝ} (hf : Measurable f) {b : ℝ}
    (hfin : ∫⁻ s in Set.Icc (0 : ℝ) b, (‖f s‖₊ : ℝ≥0∞) ^ 2 ∂volume < ⊤) :
    MeasureTheory.MemLp f 2 (volume.restrict (Set.Icc (0 : ℝ) b)) := by
  refine (MeasureTheory.memLp_two_iff_integrable_sq hf.aestronglyMeasurable).mpr ?_
  refine ⟨(hf.pow_const 2).aestronglyMeasurable, ?_⟩
  rw [MeasureTheory.hasFiniteIntegral_iff_enorm]
  exact lt_of_le_of_lt (le_of_eq (lintegral_congr fun s => enorm_sq_eq (f s))) hfin
omit [MeasurableSpace E] [MeasureTheory.IsProbabilityMeasure P] in
/-- **Second moment of a time-integral**, by Cauchy–Schwarz on `[0, t]`. -/
theorem lintegral_sq_setIntegral_le {f : Ω → ℝ → ℝ}
    (hf : Measurable (Function.uncurry f)) {t : ℝ} (ht : 0 ≤ t)
    (hfin : ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) t, (‖f ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤) :
    ∫⁻ ω, (‖∫ s in Set.Icc (0 : ℝ) t, f ω s‖₊ : ℝ≥0∞) ^ 2 ∂P
      ≤ ENNReal.ofReal t
        * ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) t, (‖f ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P := by
  haveI : MeasureTheory.IsFiniteMeasure (volume.restrict (Set.Icc (0 : ℝ) t)) :=
    ⟨by rw [MeasureTheory.Measure.restrict_apply_univ, Real.volume_Icc]
        exact ENNReal.ofReal_lt_top⟩
  have hinner_meas : Measurable fun ω : Ω =>
      ∫⁻ s in Set.Icc (0 : ℝ) t, (‖f ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume :=
    (hf.nnnorm.coe_nnreal_ennreal.pow_const 2).lintegral_prod_right'
  have hae : ∀ᵐ ω ∂P, ∫⁻ s in Set.Icc (0 : ℝ) t,
      (‖f ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume < ⊤ :=
    MeasureTheory.ae_lt_top hinner_meas hfin.ne
  have hpt : ∀ᵐ ω ∂P, (‖∫ s in Set.Icc (0 : ℝ) t, f ω s‖₊ : ℝ≥0∞) ^ 2
      ≤ ENNReal.ofReal t * ∫⁻ s in Set.Icc (0 : ℝ) t, (‖f ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume := by
    filter_upwards [hae] with ω hω
    have hslice : Measurable (f ω) := hf.comp (measurable_const.prodMk measurable_id)
    -- `f ω` is `L²` on `[0, t]`
    have hL2 : MeasureTheory.MemLp (f ω) 2 (volume.restrict (Set.Icc (0 : ℝ) t)) :=
      memLp_two_of_lintegral_sq_lt_top hslice hω
    have hint : MeasureTheory.Integrable (f ω) (volume.restrict (Set.Icc (0 : ℝ) t)) :=
      hL2.integrable (by norm_num)
    -- Cauchy–Schwarz against the constant `1`
    have hCS := integral_sq_le_mul_integral_sq_on_Icc (fun s => ‖f ω s‖) t ht
      (Filter.Eventually.of_forall fun _ => norm_nonneg _) hL2.norm
    have habs : |∫ s in Set.Icc (0 : ℝ) t, f ω s| ≤ ∫ s in Set.Icc (0 : ℝ) t, ‖f ω s‖ :=
      MeasureTheory.abs_integral_le_integral_abs.trans_eq
        (MeasureTheory.integral_congr_ae
          (Filter.Eventually.of_forall fun s => (Real.norm_eq_abs (f ω s)).symm))
    have hsq : ∫ s in Set.Icc (0 : ℝ) t, ‖f ω s‖ ^ 2
        = (∫⁻ s in Set.Icc (0 : ℝ) t, (‖f ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume).toReal := by
      rw [MeasureTheory.integral_eq_lintegral_of_nonneg_ae
        (Filter.Eventually.of_forall fun s => by positivity)
        ((hslice.norm.pow_const 2).aestronglyMeasurable)]
      congr 1
      refine lintegral_congr fun s => ?_
      rw [← sq_coe_nnnorm_real ‖f ω s‖, nnnorm_norm]
    have hbound : (∫ s in Set.Icc (0 : ℝ) t, f ω s) ^ 2
        ≤ t * (∫⁻ s in Set.Icc (0 : ℝ) t, (‖f ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume).toReal := by
      have hnn : 0 ≤ ∫ s in Set.Icc (0 : ℝ) t, ‖f ω s‖ :=
        MeasureTheory.integral_nonneg_of_ae
          (Filter.Eventually.of_forall fun s => norm_nonneg (f ω s))
      rw [← hsq]
      refine le_trans ?_ hCS
      nlinarith [habs, abs_nonneg (∫ s in Set.Icc (0 : ℝ) t, f ω s),
        sq_abs (∫ s in Set.Icc (0 : ℝ) t, f ω s), hnn]
    calc (‖∫ s in Set.Icc (0 : ℝ) t, f ω s‖₊ : ℝ≥0∞) ^ 2
        = ENNReal.ofReal ((∫ s in Set.Icc (0 : ℝ) t, f ω s) ^ 2) := sq_coe_nnnorm_real _
      _ ≤ ENNReal.ofReal
            (t * (∫⁻ s in Set.Icc (0 : ℝ) t, (‖f ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume).toReal) :=
          ENNReal.ofReal_le_ofReal hbound
      _ = ENNReal.ofReal t * ∫⁻ s in Set.Icc (0 : ℝ) t, (‖f ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume := by
          rw [ENNReal.ofReal_mul ht, ENNReal.ofReal_toReal hω.ne]
  refine (lintegral_mono_ae hpt).trans ?_
  rw [MeasureTheory.lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
/-- `‖a + b‖² ≤ 2‖a‖² + 2‖b‖²` for reals, in `ℝ≥0∞`. -/
theorem sq_nnnorm_add_le (a b : ℝ) :
    (‖a + b‖₊ : ℝ≥0∞) ^ 2 ≤ 2 * (‖a‖₊ : ℝ≥0∞) ^ 2 + 2 * (‖b‖₊ : ℝ≥0∞) ^ 2 := by
  have hreal : (a + b) ^ 2 ≤ 2 * a ^ 2 + 2 * b ^ 2 := by nlinarith [sq_nonneg (a - b)]
  calc (‖a + b‖₊ : ℝ≥0∞) ^ 2 = ENNReal.ofReal ((a + b) ^ 2) := sq_coe_nnnorm_real _
    _ ≤ ENNReal.ofReal (2 * a ^ 2 + 2 * b ^ 2) := ENNReal.ofReal_le_ofReal hreal
    _ = 2 * (‖a‖₊ : ℝ≥0∞) ^ 2 + 2 * (‖b‖₊ : ℝ≥0∞) ^ 2 := by
        rw [ENNReal.ofReal_add (by positivity) (by positivity),
          ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2),
          ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2), ENNReal.ofReal_ofNat,
          ← sq_coe_nnnorm_real, ← sq_coe_nnnorm_real]
omit [MeasurableSpace E] in
/-- **Second moment of the drift component**, by Cauchy–Schwarz on `[0, t]`. -/
theorem lintegral_sq_picardStep_drift_le
    (coeffs : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs n d E)
    (X : ℝ → Ω → (Fin n → ℝ)) (x₀ : Fin n → ℝ) (i : Fin n)
    (h_μ_meas : Measurable (Function.uncurry fun ω s => coeffs.μ s (X s ω) i))
    {t : ℝ} (ht : 0 ≤ t)
    (hfin : ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) t,
      (‖coeffs.μ s (X s ω) i‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤) :
    ∫⁻ ω, (‖picardStep_drift coeffs X x₀ t ω i‖₊ : ℝ≥0∞) ^ 2 ∂P
      ≤ 2 * (‖x₀ i‖₊ : ℝ≥0∞) ^ 2
        + 2 * (ENNReal.ofReal t * ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) t,
            (‖coeffs.μ s (X s ω) i‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P) := by
  have hunfold : ∀ ω : Ω, picardStep_drift coeffs X x₀ t ω i
      = x₀ i + ∫ s in Set.Icc (0 : ℝ) t, coeffs.μ s (X s ω) i := fun _ => rfl
  calc ∫⁻ ω, (‖picardStep_drift coeffs X x₀ t ω i‖₊ : ℝ≥0∞) ^ 2 ∂P
      = ∫⁻ ω, (‖x₀ i + ∫ s in Set.Icc (0 : ℝ) t, coeffs.μ s (X s ω) i‖₊ : ℝ≥0∞) ^ 2 ∂P :=
        lintegral_congr fun ω => by rw [hunfold ω]
    _ ≤ ∫⁻ ω, (2 * (‖x₀ i‖₊ : ℝ≥0∞) ^ 2
          + 2 * (‖∫ s in Set.Icc (0 : ℝ) t, coeffs.μ s (X s ω) i‖₊ : ℝ≥0∞) ^ 2) ∂P :=
        lintegral_mono fun ω => sq_nnnorm_add_le _ _
    _ = 2 * (‖x₀ i‖₊ : ℝ≥0∞) ^ 2
          + 2 * ∫⁻ ω, (‖∫ s in Set.Icc (0 : ℝ) t, coeffs.μ s (X s ω) i‖₊ : ℝ≥0∞) ^ 2 ∂P := by
        rw [MeasureTheory.lintegral_add_left measurable_const, MeasureTheory.lintegral_const,
          measure_univ, mul_one,
          MeasureTheory.lintegral_const_mul' _ _ (by simp : (2 : ℝ≥0∞) ≠ ⊤)]
    _ ≤ 2 * (‖x₀ i‖₊ : ℝ≥0∞) ^ 2
          + 2 * (ENNReal.ofReal t * ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) t,
              (‖coeffs.μ s (X s ω) i‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P) :=
        add_le_add le_rfl
          (mul_le_mul' le_rfl (lintegral_sq_setIntegral_le h_μ_meas ht hfin))
omit [MeasurableSpace E] [MeasureTheory.IsProbabilityMeasure P] in
/-- The time-integral of a jointly measurable process is measurable in the sample. -/
theorem measurable_setIntegral_slice {f : Ω → ℝ → ℝ}
    (hf : Measurable (Function.uncurry f)) (t : ℝ) :
    Measurable fun ω => ∫ s in Set.Icc (0 : ℝ) t, f ω s := by
  haveI : MeasureTheory.IsFiniteMeasure (volume.restrict (Set.Icc (0 : ℝ) t)) :=
    ⟨by rw [MeasureTheory.Measure.restrict_apply_univ, Real.volume_Icc]
        exact ENNReal.ofReal_lt_top⟩
  exact (hf.stronglyMeasurable.integral_prod_right'
    (ν := volume.restrict (Set.Icc (0 : ℝ) t))).measurable
/-- `‖x + y + z‖² ≤ 3‖x‖² + 3‖y‖² + 3‖z‖²` for reals, in `ℝ≥0∞`. -/
theorem sq_nnnorm_add3_le (x y z : ℝ) :
    (‖x + y + z‖₊ : ℝ≥0∞) ^ 2
      ≤ 3 * (‖x‖₊ : ℝ≥0∞) ^ 2 + 3 * (‖y‖₊ : ℝ≥0∞) ^ 2 + 3 * (‖z‖₊ : ℝ≥0∞) ^ 2 := by
  have hreal : (x + y + z) ^ 2 ≤ 3 * x ^ 2 + 3 * y ^ 2 + 3 * z ^ 2 := by
    nlinarith [sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (x - z)]
  calc (‖x + y + z‖₊ : ℝ≥0∞) ^ 2 = ENNReal.ofReal ((x + y + z) ^ 2) := sq_coe_nnnorm_real _
    _ ≤ ENNReal.ofReal (3 * x ^ 2 + 3 * y ^ 2 + 3 * z ^ 2) := ENNReal.ofReal_le_ofReal hreal
    _ = 3 * (‖x‖₊ : ℝ≥0∞) ^ 2 + 3 * (‖y‖₊ : ℝ≥0∞) ^ 2 + 3 * (‖z‖₊ : ℝ≥0∞) ^ 2 := by
        rw [ENNReal.ofReal_add (by positivity) (by positivity),
          ENNReal.ofReal_add (by positivity) (by positivity),
          ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 3),
          ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 3),
          ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 3), ENNReal.ofReal_ofNat,
          ← sq_coe_nnnorm_real, ← sq_coe_nnnorm_real, ← sq_coe_nnnorm_real]
omit [MeasurableSpace E] [MeasureTheory.IsProbabilityMeasure P] in
/-- Enlarging the time window increases the doubly-integrated energy. -/
theorem lintegral_lintegral_Icc_mono {f : Ω → ℝ → ℝ≥0∞} {t T : ℝ} (h : t ≤ T) :
    ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) t, f ω s ∂volume ∂P
      ≤ ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, f ω s ∂volume ∂P :=
  lintegral_mono fun _ =>
    lintegral_mono' (MeasureTheory.Measure.restrict_mono
      (Set.Icc_subset_Icc le_rfl h) le_rfl) le_rfl
omit [MeasurableSpace E] in
/-- Slice measurability of the drift component. -/
theorem measurable_picardStep_drift
    (coeffs : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs n d E)
    (X : ℝ → Ω → (Fin n → ℝ)) (x₀ : Fin n → ℝ) (i : Fin n)
    (h_μ_meas : Measurable (Function.uncurry fun ω s => coeffs.μ s (X s ω) i)) (t : ℝ) :
    Measurable fun ω => picardStep_drift coeffs X x₀ t ω i :=
  (measurable_setIntegral_slice h_μ_meas t).const_add _
omit [MeasurableSpace E] in
/-- Slice measurability of the diffusion component. -/
theorem measurable_picardStep_diffusion
    (W : LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion P d)
    (ℱ : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›)
    (hℱW : ∀ j : Fin d, LevyStochCalc.Brownian.IsBrownianFiltration (W.W j) ℱ)
    (coeffs : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs n d E)
    (X : ℝ → Ω → (Fin n → ℝ))
    (h_meas : ∀ i : Fin n, ∀ j : Fin d,
      Measurable (Function.uncurry (fun ω s => coeffs.σ s (X s ω) i j)))
    (h_progMeas : ∀ i : Fin n, ∀ j : Fin d,
        Probability.ProgressivelyMeasurable ℱ (fun ω s => coeffs.σ s (X s ω) i j))
    (h_sq : ∀ i : Fin n, ∀ j : Fin d, ∀ T : ℝ, 0 < T →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
        (‖coeffs.σ s (X s ω) i j‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    (i : Fin n) (t : ℝ) :
    Measurable fun ω =>
      picardStep_diffusion W ℱ hℱW coeffs X h_meas h_progMeas h_sq t ω i := by
  have hcomp : ∀ j : Fin d, Measurable fun ω =>
      LevyStochCalc.Brownian.Ito.stochasticIntegral (W.W j) ℱ (hℱW j)
        (fun ω' s => coeffs.σ s (X s ω') i j)
        (h_meas i j) (h_progMeas i j) (h_sq i j) t ω := by
    intro j
    obtain ⟨Filt, hMart⟩ := LevyStochCalc.Brownian.Ito.martingale_stochasticIntegral
      (W.W j) ℱ (hℱW j) (fun ω' s => coeffs.σ s (X s ω') i j)
      (h_meas i j) (h_progMeas i j) (h_sq i j)
    exact (hMart.stronglyMeasurable t).measurable.mono (Filt.le t) le_rfl
  have hunfold : (fun ω => picardStep_diffusion W ℱ hℱW coeffs X h_meas h_progMeas h_sq t ω i)
      = fun ω => ∑ j : Fin d, LevyStochCalc.Brownian.Ito.stochasticIntegral (W.W j) ℱ (hℱW j)
        (fun ω' s => coeffs.σ s (X s ω') i j)
        (h_meas i j) (h_progMeas i j) (h_sq i j) t ω := rfl
  rw [hunfold]
  exact Finset.measurable_sum _ fun j _ => hcomp j
/-- Slice measurability of the jump component. -/
theorem measurable_picardStep_jump {ν : MeasureTheory.Measure E}
    [MeasureTheory.SigmaFinite ν]
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν)
    (ℱ : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›)
    (hℱN : LevyStochCalc.Poisson.IsPoissonFiltration N ℱ)
    (coeffs : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs n d E)
    (X : ℝ → Ω → (Fin n → ℝ))
    (h_meas : ∀ i : Fin n,
      Measurable (fun p : Ω × ℝ × E => coeffs.γ p.2.1 (X p.2.1 p.1) p.2.2 i))
    (h_progMeas : ∀ i : Fin n,
        Probability.MarkedProgressivelyMeasurable ℱ (fun ω s e => coeffs.γ s (X s ω) e i))
    (h_sq : ∀ i : Fin n, ∀ T : ℝ, 0 < T →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e,
        (‖coeffs.γ s (X s ω) e i‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P < ⊤)
    (i : Fin n) (t : ℝ) :
    Measurable fun ω => picardStep_jump N ℱ hℱN coeffs X h_meas h_progMeas h_sq t ω i :=
  ((LevyStochCalc.Poisson.Compensated.stochasticIntegral_adapted N ℱ hℱN
    (fun ω s e => coeffs.γ s (X s ω) e i) (h_meas i) (h_progMeas i) (h_sq i)
      t).stronglyMeasurable).measurable.mono (ℱ.rightCont.le t) le_rfl
section Step
variable {ν : MeasureTheory.Measure E} [MeasureTheory.SigmaFinite ν]
variable (W : LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion P d)
variable (N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν)
variable (ℱ : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›)
variable (hℱW : ∀ j : Fin d, LevyStochCalc.Brownian.IsBrownianFiltration (W.W j) ℱ)
variable (hℱN : LevyStochCalc.Poisson.IsPoissonFiltration N ℱ)
variable (coeffs : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs n d E)
variable (X : ℝ → Ω → (Fin n → ℝ)) (x₀ : Fin n → ℝ)
variable (h_σ_meas : ∀ i : Fin n, ∀ j : Fin d,
  Measurable (Function.uncurry (fun ω s => coeffs.σ s (X s ω) i j)))
variable (h_σ_progMeas : ∀ i : Fin n, ∀ j : Fin d,
  Probability.ProgressivelyMeasurable ℱ (fun ω s => coeffs.σ s (X s ω) i j))
variable (h_σ_sq : ∀ i : Fin n, ∀ j : Fin d, ∀ T : ℝ, 0 < T →
  ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
    (‖coeffs.σ s (X s ω) i j‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
variable (h_γ_meas : ∀ i : Fin n,
  Measurable (fun p : Ω × ℝ × E => coeffs.γ p.2.1 (X p.2.1 p.1) p.2.2 i))
variable (h_γ_progMeas : ∀ i : Fin n,
  Probability.MarkedProgressivelyMeasurable ℱ (fun ω s e => coeffs.γ s (X s ω) e i))
variable (h_γ_sq : ∀ i : Fin n, ∀ T : ℝ, 0 < T →
  ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e,
    (‖coeffs.γ s (X s ω) e i‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P < ⊤)
/-- **Second moment of the Picard step at a time of `[0, T]`, bounded uniformly by data at the
horizon `T`.** -/
theorem lintegral_sq_picardStep_le
    (h_μ_meas : ∀ i : Fin n,
      Measurable (Function.uncurry fun ω s => coeffs.μ s (X s ω) i))
    {T t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) T)
    (hμT : ∀ i : Fin n, ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖coeffs.μ s (X s ω) i‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤) :
    ∫⁻ ω, ∑ i, (‖picardStep W N ℱ hℱW hℱN coeffs X x₀ h_σ_meas h_σ_progMeas h_σ_sq
        h_γ_meas h_γ_progMeas h_γ_sq t ω i‖₊ : ℝ≥0∞) ^ 2 ∂P
      ≤ ∑ i : Fin n,
          (3 * (2 * (‖x₀ i‖₊ : ℝ≥0∞) ^ 2
              + 2 * (ENNReal.ofReal T * ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
                  (‖coeffs.μ s (X s ω) i‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P))
            + 3 * ((d : ℝ≥0∞) * ∑ j : Fin d, ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
                (‖coeffs.σ s (X s ω) i j‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P)
            + 3 * ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e,
                (‖coeffs.γ s (X s ω) e i‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P) := by
  obtain ⟨ht0, htT⟩ := ht
  have hdr : ∀ i : Fin n, Measurable fun ω =>
      (‖picardStep_drift coeffs X x₀ t ω i‖₊ : ℝ≥0∞) ^ 2 := fun i =>
    (((measurable_picardStep_drift coeffs X x₀ i (h_μ_meas i)
      t).nnnorm).coe_nnreal_ennreal).pow_const 2
  have hdf : ∀ i : Fin n, Measurable fun ω =>
      (‖picardStep_diffusion W ℱ hℱW coeffs X h_σ_meas h_σ_progMeas h_σ_sq t ω i‖₊
        : ℝ≥0∞) ^ 2 := fun i =>
    (((measurable_picardStep_diffusion W ℱ hℱW coeffs X h_σ_meas h_σ_progMeas h_σ_sq i
      t).nnnorm).coe_nnreal_ennreal).pow_const 2
  have hjp : ∀ i : Fin n, Measurable fun ω =>
      (‖picardStep_jump N ℱ hℱN coeffs X h_γ_meas h_γ_progMeas h_γ_sq t ω i‖₊
        : ℝ≥0∞) ^ 2 := fun i =>
    (((measurable_picardStep_jump N ℱ hℱN coeffs X h_γ_meas h_γ_progMeas h_γ_sq i
      t).nnnorm).coe_nnreal_ennreal).pow_const 2
  -- pointwise three-term split
  have hpt : ∀ ω : Ω, ∑ i, (‖picardStep W N ℱ hℱW hℱN coeffs X x₀ h_σ_meas h_σ_progMeas
        h_σ_sq h_γ_meas h_γ_progMeas h_γ_sq t ω i‖₊ : ℝ≥0∞) ^ 2
      ≤ ∑ i : Fin n,
          (3 * (‖picardStep_drift coeffs X x₀ t ω i‖₊ : ℝ≥0∞) ^ 2
            + 3 * (‖picardStep_diffusion W ℱ hℱW coeffs X h_σ_meas h_σ_progMeas h_σ_sq
                t ω i‖₊ : ℝ≥0∞) ^ 2
            + 3 * (‖picardStep_jump N ℱ hℱN coeffs X h_γ_meas h_γ_progMeas h_γ_sq
                t ω i‖₊ : ℝ≥0∞) ^ 2) := by
    intro ω
    refine Finset.sum_le_sum fun i _ => ?_
    exact sq_nnnorm_add3_le _ _ _
  have hmeas2 : ∀ i : Fin n, Measurable fun ω =>
      3 * (‖picardStep_drift coeffs X x₀ t ω i‖₊ : ℝ≥0∞) ^ 2
        + 3 * (‖picardStep_diffusion W ℱ hℱW coeffs X h_σ_meas h_σ_progMeas h_σ_sq
            t ω i‖₊ : ℝ≥0∞) ^ 2 :=
    fun i => ((hdr i).const_mul 3).add ((hdf i).const_mul 3)
  have hmeas3 : ∀ i : Fin n, Measurable fun ω =>
      3 * (‖picardStep_drift coeffs X x₀ t ω i‖₊ : ℝ≥0∞) ^ 2
        + 3 * (‖picardStep_diffusion W ℱ hℱW coeffs X h_σ_meas h_σ_progMeas h_σ_sq
            t ω i‖₊ : ℝ≥0∞) ^ 2
        + 3 * (‖picardStep_jump N ℱ hℱN coeffs X h_γ_meas h_γ_progMeas h_γ_sq
            t ω i‖₊ : ℝ≥0∞) ^ 2 :=
    fun i => (hmeas2 i).add ((hjp i).const_mul 3)
  refine (lintegral_mono hpt).trans ?_
  rw [MeasureTheory.lintegral_finsetSum _ (fun i _ => hmeas3 i)]
  refine Finset.sum_le_sum fun i _ => ?_
  rw [MeasureTheory.lintegral_add_left (hmeas2 i),
    MeasureTheory.lintegral_add_left ((hdr i).const_mul 3),
    MeasureTheory.lintegral_const_mul' _ _ (by simp : (3 : ℝ≥0∞) ≠ ⊤),
    MeasureTheory.lintegral_const_mul' _ _ (by simp : (3 : ℝ≥0∞) ≠ ⊤),
    MeasureTheory.lintegral_const_mul' _ _ (by simp : (3 : ℝ≥0∞) ≠ ⊤)]
  have hμt : ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) t,
      (‖coeffs.μ s (X s ω) i‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤ :=
    lt_of_le_of_lt (lintegral_lintegral_Icc_mono htT) (hμT i)
  refine add_le_add (add_le_add (mul_le_mul' le_rfl ?_) (mul_le_mul' le_rfl ?_))
    (mul_le_mul' le_rfl ?_)
  · refine (lintegral_sq_picardStep_drift_le coeffs X x₀ i (h_μ_meas i) ht0 hμt).trans ?_
    exact add_le_add le_rfl (mul_le_mul' le_rfl
      (mul_le_mul' (ENNReal.ofReal_le_ofReal htT) (lintegral_lintegral_Icc_mono htT)))
  · refine (lintegral_sq_picardStep_diffusion_le W ℱ hℱW coeffs X h_σ_meas h_σ_progMeas
      h_σ_sq i ht0).trans ?_
    exact mul_le_mul' le_rfl
      (Finset.sum_le_sum fun j _ => lintegral_lintegral_Icc_mono htT)
  · refine le_of_eq_of_le (lintegral_sq_picardStep_jump_eq N ℱ hℱN coeffs X h_γ_meas
      h_γ_progMeas h_γ_sq i ht0) ?_
    exact lintegral_lintegral_Icc_mono htT
/-- **The Picard step has finite Bielecki norm on `[0, T]`** — the `L²` output field that
`picardStepOnS2` takes as a hypothesis. -/
theorem bieleckiNorm_picardStep_lt_top
    (h_μ_meas : ∀ i : Fin n,
      Measurable (Function.uncurry fun ω s => coeffs.μ s (X s ω) i))
    {T : ℝ}
    (hμT : ∀ i : Fin n, ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖coeffs.μ s (X s ω) i‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    (hσT : ∀ i : Fin n, ∀ j : Fin d, ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖coeffs.σ s (X s ω) i j‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    (hγT : ∀ i : Fin n, ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e,
      (‖coeffs.γ s (X s ω) e i‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P < ⊤) :
    bieleckiNorm (P := P) 0 T
      (fun t ω => picardStep W N ℱ hℱW hℱN coeffs X x₀ h_σ_meas h_σ_progMeas h_σ_sq
        h_γ_meas h_γ_progMeas h_γ_sq t ω) < ⊤ := by
  have hKfin : (∑ i : Fin n,
      (3 * (2 * (‖x₀ i‖₊ : ℝ≥0∞) ^ 2
          + 2 * (ENNReal.ofReal T * ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
              (‖coeffs.μ s (X s ω) i‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P))
        + 3 * ((d : ℝ≥0∞) * ∑ j : Fin d, ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
            (‖coeffs.σ s (X s ω) i j‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P)
        + 3 * ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e,
            (‖coeffs.γ s (X s ω) e i‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P)) < ⊤ := by
    refine ENNReal.sum_lt_top.mpr fun i _ => ?_
    refine ENNReal.add_lt_top.mpr ⟨ENNReal.add_lt_top.mpr ⟨?_, ?_⟩, ?_⟩
    · refine ENNReal.mul_lt_top (by simp) (ENNReal.add_lt_top.mpr ⟨?_, ?_⟩)
      · exact ENNReal.mul_lt_top (by simp) (ENNReal.pow_lt_top ENNReal.coe_lt_top)
      · exact ENNReal.mul_lt_top (by simp)
          (ENNReal.mul_lt_top ENNReal.ofReal_lt_top (hμT i))
    · exact ENNReal.mul_lt_top (by simp) (ENNReal.mul_lt_top (by simp)
        (ENNReal.sum_lt_top.mpr fun j _ => hσT i j))
    · exact ENNReal.mul_lt_top (by simp) (hγT i)
  refine lt_of_le_of_lt (b := _ ^ ((1 : ℝ) / 2)) ?_
    (ENNReal.rpow_lt_top_of_nonneg (by norm_num) hKfin.ne)
  unfold bieleckiNorm
  refine iSup₂_le fun t ht => ?_
  rw [neg_zero, zero_mul, Real.exp_zero, ENNReal.ofReal_one, one_mul]
  exact ENNReal.rpow_le_rpow
    (lintegral_sq_picardStep_le W N ℱ hℱW hℱN coeffs X x₀ h_σ_meas h_σ_progMeas h_σ_sq
      h_γ_meas h_γ_progMeas h_γ_sq h_μ_meas ht hμT) (by norm_num)
end Step
end Picard
end Ito
end LevyStochCalc


