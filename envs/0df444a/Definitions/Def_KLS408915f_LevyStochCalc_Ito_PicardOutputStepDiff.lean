-- Prove2me | Definitions.Def_KLS408915f_LevyStochCalc_Ito_PicardOutputStepDiff
-- name    : KLS408915f_LevyStochCalc_Ito_PicardOutputStepDiff
-- status  : Definition
-- author  : @Lazyfill
-- created : 2026-10-23T10:34:21.286783+00:00
-- url     : https://prove2.me/theorems/c0d328a7-eb2d-44bd-a690-ae37f09bf903
-- title:
--   Per-time and Bielecki difference estimates for Picard steps
-- statement:
--   Vendored from the LevyStochCalc library (https://github.com/cgarryZA/LevyStochCalc). `picardStep_apply_eq` identifies each coordinate of the Picard step with the sum of its drift, diffusion, and compensated-jump components, and `lintegral_sq_sum3_le` combines their separate second-moment bounds using the factor $3$. Under `IsLipschitz` and the full measurability and finite-energy hypotheses for two state processes, `lintegral_sq_picardStep_diff_le` bounds the integrated squared difference of the two Picard steps by the state-difference energy. `bieleckiNorm_picardStep_diff_le` then gives the corresponding weighted estimate with factor $\operatorname{ofReal}(3n(L^2T+dL^2+L^2)/(2\beta))^{1/2}$.
-- source:
--   Lean source: https://github.com/cgarryZA/LevyStochCalc/blob/984dbf0b790031eac05d56fe5a84b65e15e1e932/LevyStochCalc/Ito/PicardOutputStepDiff.lean#L31-L473 (repository human-ai-mathematics/kls-lean, commit 408915f, module `LevyStochCalc.Ito.PicardOutputStepDiff`, definition bundle `KLS408915f_LevyStochCalc_Ito_PicardOutputStepDiff`; the repository is private at upload time). Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (Apache-2.0; upstream copyright notice retained in the Lean text).

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
import Definitions.Def_KLS408915f_LevyStochCalc_Ito_PicardOutputModification
import Definitions.Def_KLS408915f_LevyStochCalc_Ito_PicardOutputMoments
import Definitions.Def_KLS408915f_LevyStochCalc_Ito_PicardOutputWeighting
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
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Ito/PicardOutputStepDiff.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
namespace LevyStochCalc
namespace Ito
namespace Picard
universe u v
variable {Ω : Type u} [MeasurableSpace Ω]
variable {E : Type v} [MeasurableSpace E]
variable {n d : ℕ} {P : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure P]
section Weighting
omit [MeasurableSpace E] [MeasureTheory.IsProbabilityMeasure P] in
/-- **Combining three per-time bounds with a common right-hand side.** For a process that splits
as a sum of three, `‖a + b + c‖² ≤ 3(‖a‖² + ‖b‖² + ‖c‖²)` turns three separate second-moment
bounds into one, with the constants added and tripled. -/
theorem lintegral_sq_sum3_le {U₁ U₂ U₃ : Ω → (Fin n → ℝ)} {c₁ c₂ c₃ R : ℝ≥0∞}
    (hm₁ : ∀ i : Fin n, Measurable fun ω => (‖U₁ ω i‖₊ : ℝ≥0∞) ^ 2)
    (hm₂ : ∀ i : Fin n, Measurable fun ω => (‖U₂ ω i‖₊ : ℝ≥0∞) ^ 2)
    (hm₃ : ∀ i : Fin n, Measurable fun ω => (‖U₃ ω i‖₊ : ℝ≥0∞) ^ 2)
    (h₁ : ∫⁻ ω, ∑ i, (‖U₁ ω i‖₊ : ℝ≥0∞) ^ 2 ∂P ≤ c₁ * R)
    (h₂ : ∫⁻ ω, ∑ i, (‖U₂ ω i‖₊ : ℝ≥0∞) ^ 2 ∂P ≤ c₂ * R)
    (h₃ : ∫⁻ ω, ∑ i, (‖U₃ ω i‖₊ : ℝ≥0∞) ^ 2 ∂P ≤ c₃ * R) :
    ∫⁻ ω, ∑ i, (‖U₁ ω i + U₂ ω i + U₃ ω i‖₊ : ℝ≥0∞) ^ 2 ∂P
      ≤ 3 * (c₁ + c₂ + c₃) * R := by
  have hM₁ : Measurable fun ω => ∑ i, (‖U₁ ω i‖₊ : ℝ≥0∞) ^ 2 :=
    Finset.measurable_sum _ fun i _ => hm₁ i
  have hM₂ : Measurable fun ω => ∑ i, (‖U₂ ω i‖₊ : ℝ≥0∞) ^ 2 :=
    Finset.measurable_sum _ fun i _ => hm₂ i
  have hM₃ : Measurable fun ω => ∑ i, (‖U₃ ω i‖₊ : ℝ≥0∞) ^ 2 :=
    Finset.measurable_sum _ fun i _ => hm₃ i
  have hsum : ∀ ω : Ω, ∑ i, (‖U₁ ω i + U₂ ω i + U₃ ω i‖₊ : ℝ≥0∞) ^ 2
      ≤ 3 * (∑ i, (‖U₁ ω i‖₊ : ℝ≥0∞) ^ 2) + 3 * (∑ i, (‖U₂ ω i‖₊ : ℝ≥0∞) ^ 2)
        + 3 * (∑ i, (‖U₃ ω i‖₊ : ℝ≥0∞) ^ 2) := by
    intro ω
    refine le_trans (Finset.sum_le_sum fun i _ => sq_nnnorm_add3_le _ _ _) (le_of_eq ?_)
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum,
      Finset.mul_sum]
  have hM1' : Measurable fun ω : Ω => 3 * (∑ i, (‖U₁ ω i‖₊ : ℝ≥0∞) ^ 2) := hM₁.const_mul 3
  have hM2' : Measurable fun ω : Ω => 3 * (∑ i, (‖U₂ ω i‖₊ : ℝ≥0∞) ^ 2) := hM₂.const_mul 3
  have hM12 : Measurable fun ω : Ω =>
      3 * (∑ i, (‖U₁ ω i‖₊ : ℝ≥0∞) ^ 2) + 3 * (∑ i, (‖U₂ ω i‖₊ : ℝ≥0∞) ^ 2) := hM1'.add hM2'
  refine (lintegral_mono hsum).trans ?_
  rw [MeasureTheory.lintegral_add_left hM12,
    MeasureTheory.lintegral_add_left hM1',
    MeasureTheory.lintegral_const_mul' _ _ (by simp : (3 : ℝ≥0∞) ≠ ⊤),
    MeasureTheory.lintegral_const_mul' _ _ (by simp : (3 : ℝ≥0∞) ≠ ⊤),
    MeasureTheory.lintegral_const_mul' _ _ (by simp : (3 : ℝ≥0∞) ≠ ⊤)]
  calc 3 * (∫⁻ ω, ∑ i, (‖U₁ ω i‖₊ : ℝ≥0∞) ^ 2 ∂P)
        + 3 * (∫⁻ ω, ∑ i, (‖U₂ ω i‖₊ : ℝ≥0∞) ^ 2 ∂P)
        + 3 * (∫⁻ ω, ∑ i, (‖U₃ ω i‖₊ : ℝ≥0∞) ^ 2 ∂P)
      ≤ 3 * (c₁ * R) + 3 * (c₂ * R) + 3 * (c₃ * R) :=
        add_le_add (add_le_add (mul_le_mul' le_rfl h₁) (mul_le_mul' le_rfl h₂))
          (mul_le_mul' le_rfl h₃)
    _ = 3 * (c₁ + c₂ + c₃) * R := by ring
omit [MeasurableSpace Ω] [MeasureTheory.IsProbabilityMeasure P] in
/-- The `μ` clause of `IsLipschitz`, read on a single coordinate. -/
theorem mu_lip_componentwise {ν : MeasureTheory.Measure E}
    (coeffs : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs n d E) {L : ℝ}
    (hLip : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs.IsLipschitz coeffs ν L)
    (s : ℝ) (x₁ x₂ : Fin n → ℝ) (i : Fin n) :
    |coeffs.μ s x₁ i - coeffs.μ s x₂ i| ≤ L * ‖x₁ - x₂‖ := by
  refine le_trans ?_ (hLip.2.1 s x₁ x₂)
  simpa [Real.norm_eq_abs, Pi.sub_apply] using
    norm_le_pi_norm (coeffs.μ s x₁ - coeffs.μ s x₂) i
omit [MeasurableSpace E] [MeasureTheory.IsProbabilityMeasure P] in
/-- The two shapes of the coordinate second moment agree. -/
theorem lintegral_ofReal_sum_sq_eq (U : Ω → (Fin n → ℝ)) :
    ∫⁻ ω, ENNReal.ofReal (∑ i, (U ω i) ^ 2) ∂P
      = ∫⁻ ω, ∑ i, (‖U ω i‖₊ : ℝ≥0∞) ^ 2 ∂P := by
  refine lintegral_congr fun ω => ?_
  rw [ENNReal.ofReal_sum_of_nonneg (fun _ _ => sq_nonneg _)]
  exact (Finset.sum_congr rfl fun i _ => sq_coe_nnnorm_real (U ω i)).symm
/-- The Picard step is the sum of its three components, coordinatewise. -/
theorem picardStep_apply_eq
    (W : LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion P d)
    {ν : MeasureTheory.Measure E} [MeasureTheory.SigmaFinite ν]
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν)
    (ℱ : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›)
    (hℱW : ∀ j : Fin d, LevyStochCalc.Brownian.IsBrownianFiltration (W.W j) ℱ)
    (hℱN : LevyStochCalc.Poisson.IsPoissonFiltration N ℱ)
    (coeffs : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs n d E)
    (X : ℝ → Ω → (Fin n → ℝ)) (x₀ : Fin n → ℝ)
    (h_σ_meas : ∀ i : Fin n, ∀ j : Fin d,
      Measurable (Function.uncurry (fun ω s => coeffs.σ s (X s ω) i j)))
    (h_σ_progMeas : ∀ i : Fin n, ∀ j : Fin d,
      Probability.ProgressivelyMeasurable ℱ (fun ω s => coeffs.σ s (X s ω) i j))
    (h_σ_sq : ∀ i : Fin n, ∀ j : Fin d, ∀ T' : ℝ, 0 < T' →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T',
        (‖coeffs.σ s (X s ω) i j‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    (h_γ_meas : ∀ i : Fin n,
      Measurable (fun p : Ω × ℝ × E => coeffs.γ p.2.1 (X p.2.1 p.1) p.2.2 i))
    (h_γ_progMeas : ∀ i : Fin n,
      Probability.MarkedProgressivelyMeasurable ℱ (fun ω s e => coeffs.γ s (X s ω) e i))
    (h_γ_sq : ∀ i : Fin n, ∀ T' : ℝ, 0 < T' →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T', ∫⁻ e,
        (‖coeffs.γ s (X s ω) e i‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P < ⊤)
    (t : ℝ) (ω : Ω) (i : Fin n) :
    picardStep W N ℱ hℱW hℱN coeffs X x₀ h_σ_meas h_σ_progMeas h_σ_sq
        h_γ_meas h_γ_progMeas h_γ_sq t ω i
      = picardStep_drift coeffs X x₀ t ω i
        + picardStep_diffusion W ℱ hℱW coeffs X h_σ_meas h_σ_progMeas h_σ_sq t ω i
        + picardStep_jump N ℱ hℱN coeffs X h_γ_meas h_γ_progMeas h_γ_sq t ω i := rfl
/-- The Picard step starts at `x₀`: at time `0` both stochastic components vanish almost surely
and the drift window is a null set. -/
theorem ae_picardStep_zero
    (W : LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion P d)
    {ν : MeasureTheory.Measure E} [MeasureTheory.SigmaFinite ν]
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν)
    (ℱ : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›)
    (hℱW : ∀ j : Fin d, LevyStochCalc.Brownian.IsBrownianFiltration (W.W j) ℱ)
    (hℱN : LevyStochCalc.Poisson.IsPoissonFiltration N ℱ)
    (coeffs : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs n d E)
    (X : ℝ → Ω → (Fin n → ℝ)) (x₀ : Fin n → ℝ)
    (h_σ_meas : ∀ i : Fin n, ∀ j : Fin d,
      Measurable (Function.uncurry (fun ω s => coeffs.σ s (X s ω) i j)))
    (h_σ_progMeas : ∀ i : Fin n, ∀ j : Fin d,
      Probability.ProgressivelyMeasurable ℱ (fun ω s => coeffs.σ s (X s ω) i j))
    (h_σ_sq : ∀ i : Fin n, ∀ j : Fin d, ∀ T' : ℝ, 0 < T' →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T',
        (‖coeffs.σ s (X s ω) i j‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    (h_γ_meas : ∀ i : Fin n,
      Measurable (fun p : Ω × ℝ × E => coeffs.γ p.2.1 (X p.2.1 p.1) p.2.2 i))
    (h_γ_progMeas : ∀ i : Fin n,
      Probability.MarkedProgressivelyMeasurable ℱ (fun ω s e => coeffs.γ s (X s ω) e i))
    (h_γ_sq : ∀ i : Fin n, ∀ T' : ℝ, 0 < T' →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T', ∫⁻ e,
        (‖coeffs.γ s (X s ω) e i‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P < ⊤) :
    ∀ᵐ ω ∂P, ∀ i : Fin n,
      picardStep W N ℱ hℱW hℱN coeffs X x₀ h_σ_meas h_σ_progMeas h_σ_sq
        h_γ_meas h_γ_progMeas h_γ_sq 0 ω i = x₀ i := by
  have hdrift : ∀ (ω : Ω) (i : Fin n), picardStep_drift coeffs X x₀ 0 ω i = x₀ i := by
    intro ω i
    have hzero : (∫ s in Set.Icc (0 : ℝ) 0, coeffs.μ s (X s ω) i ∂volume) = 0 :=
      MeasureTheory.setIntegral_measure_zero _ (by simp)
    change x₀ i + (∫ s in Set.Icc (0 : ℝ) 0, coeffs.μ s (X s ω) i ∂volume) = x₀ i
    rw [hzero, add_zero]
  have hσ : ∀ᵐ ω ∂P, ∀ p : Fin n × Fin d,
      LevyStochCalc.Brownian.Ito.stochasticIntegral (W.W p.2) ℱ (hℱW p.2)
        (fun ω' s => coeffs.σ s (X s ω') p.1 p.2)
        (h_σ_meas p.1 p.2) (h_σ_progMeas p.1 p.2) (h_σ_sq p.1 p.2) 0 ω = 0 :=
    MeasureTheory.ae_all_iff.mpr fun p =>
      LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian_ae_zero_of_nonpos (W.W p.2) ℱ
        (hℱW p.2) (fun ω' s => coeffs.σ s (X s ω') p.1 p.2)
        (h_σ_meas p.1 p.2) (h_σ_progMeas p.1 p.2) (h_σ_sq p.1 p.2) le_rfl
  have hγ : ∀ᵐ ω ∂P, ∀ i : Fin n,
      picardStep_jump N ℱ hℱN coeffs X h_γ_meas h_γ_progMeas h_γ_sq 0 ω i = 0 := by
    refine MeasureTheory.ae_all_iff.mpr fun i => ?_
    filter_upwards [LevyStochCalc.Poisson.Compensated.stochasticIntegral_ae_eq_process N ℱ hℱN
        (fun ω s e => coeffs.γ s (X s ω) e i) (h_γ_meas i) (h_γ_progMeas i) (h_γ_sq i) 0,
      LevyStochCalc.Poisson.Compensated.process_ae_zero_of_nonpos N ℱ hℱN
        (fun ω s e => coeffs.γ s (X s ω) e i) (h_γ_meas i) (h_γ_progMeas i) (h_γ_sq i)
        le_rfl] with ω h1 h2
    change LevyStochCalc.Poisson.Compensated.stochasticIntegral N ℱ hℱN
      (fun ω' s e => coeffs.γ s (X s ω') e i) (h_γ_meas i) (h_γ_progMeas i) (h_γ_sq i) 0 ω = 0
    rw [h1, h2]
    rfl
  filter_upwards [hσ, hγ] with ω hσω hγω i
  rw [picardStep_apply_eq W N ℱ hℱW hℱN coeffs X x₀ h_σ_meas h_σ_progMeas h_σ_sq
    h_γ_meas h_γ_progMeas h_γ_sq 0 ω i, hdrift ω i, hγω i, add_zero]
  have hdiff : picardStep_diffusion W ℱ hℱW coeffs X h_σ_meas h_σ_progMeas h_σ_sq 0 ω i = 0 := by
    change (∑ j : Fin d, LevyStochCalc.Brownian.Ito.stochasticIntegral (W.W j) ℱ (hℱW j)
      (fun ω' s => coeffs.σ s (X s ω') i j)
      (h_σ_meas i j) (h_σ_progMeas i j) (h_σ_sq i j) 0 ω) = 0
    exact Finset.sum_eq_zero fun j _ => hσω (i, j)
  rw [hdiff, add_zero]
attribute [local irreducible] picardStep picardStep_diffusion picardStep_jump
attribute [local irreducible]
  LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.stochasticIntegral
attribute [local irreducible] LevyStochCalc.Brownian.Ito.stochasticIntegral
set_option maxHeartbeats 4000000 in
-- The statement names the full three-component Picard term twice, once along each path, and
-- elaborating the second application exceeds the default budget even with the components sealed.
/-- **The per-time contraction estimate for the Picard step**, with every hypothesis of its three
components discharged from `IsLipschitz`. -/
theorem lintegral_sq_picardStep_diff_le
    (W : LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion P d)
    {ν : MeasureTheory.Measure E} [MeasureTheory.SigmaFinite ν]
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν)
    (ℱ : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›)
    (hℱW : ∀ j : Fin d, LevyStochCalc.Brownian.IsBrownianFiltration (W.W j) ℱ)
    (hℱN : LevyStochCalc.Poisson.IsPoissonFiltration N ℱ)
    (coeffs : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs n d E)
    {L : ℝ} (hLip : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs.IsLipschitz coeffs ν L)
    (X Y : ℝ → Ω → (Fin n → ℝ)) (x₀ : Fin n → ℝ)
    (h_σ_meas_X : ∀ i : Fin n, ∀ j : Fin d,
      Measurable (Function.uncurry (fun ω s => coeffs.σ s (X s ω) i j)))
    (h_σ_progMeas_X : ∀ i : Fin n, ∀ j : Fin d,
      Probability.ProgressivelyMeasurable ℱ (fun ω s => coeffs.σ s (X s ω) i j))
    (h_σ_sq_X : ∀ i : Fin n, ∀ j : Fin d, ∀ T' : ℝ, 0 < T' →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T',
        (‖coeffs.σ s (X s ω) i j‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    (h_γ_meas_X : ∀ i : Fin n,
      Measurable (fun p : Ω × ℝ × E => coeffs.γ p.2.1 (X p.2.1 p.1) p.2.2 i))
    (h_γ_progMeas_X : ∀ i : Fin n,
      Probability.MarkedProgressivelyMeasurable ℱ (fun ω s e => coeffs.γ s (X s ω) e i))
    (h_γ_sq_X : ∀ i : Fin n, ∀ T' : ℝ, 0 < T' →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T', ∫⁻ e,
        (‖coeffs.γ s (X s ω) e i‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P < ⊤)
    (h_σ_meas_Y : ∀ i : Fin n, ∀ j : Fin d,
      Measurable (Function.uncurry (fun ω s => coeffs.σ s (Y s ω) i j)))
    (h_σ_progMeas_Y : ∀ i : Fin n, ∀ j : Fin d,
      Probability.ProgressivelyMeasurable ℱ (fun ω s => coeffs.σ s (Y s ω) i j))
    (h_σ_sq_Y : ∀ i : Fin n, ∀ j : Fin d, ∀ T' : ℝ, 0 < T' →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T',
        (‖coeffs.σ s (Y s ω) i j‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    (h_γ_meas_Y : ∀ i : Fin n,
      Measurable (fun p : Ω × ℝ × E => coeffs.γ p.2.1 (Y p.2.1 p.1) p.2.2 i))
    (h_γ_progMeas_Y : ∀ i : Fin n,
      Probability.MarkedProgressivelyMeasurable ℱ (fun ω s e => coeffs.γ s (Y s ω) e i))
    (h_γ_sq_Y : ∀ i : Fin n, ∀ T' : ℝ, 0 < T' →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T', ∫⁻ e,
        (‖coeffs.γ s (Y s ω) e i‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P < ⊤)
    (hμX : ∀ i : Fin n, Measurable (Function.uncurry fun ω s => coeffs.μ s (X s ω) i))
    (hμY : ∀ i : Fin n, Measurable (Function.uncurry fun ω s => coeffs.μ s (Y s ω) i))
    (hXYm : Measurable (Function.uncurry fun (ω : Ω) (s : ℝ) => ‖X s ω - Y s ω‖))
    (hμXsq : ∀ i : Fin n, ∀ b : ℝ, 0 < b → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) b,
      (‖coeffs.μ s (X s ω) i‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    (hμYsq : ∀ i : Fin n, ∀ b : ℝ, 0 < b → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) b,
      (‖coeffs.μ s (Y s ω) i‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    (hXYsq : ∀ b : ℝ, 0 < b → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) b,
      (‖X s ω - Y s ω‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    {t : ℝ} (ht : 0 < t) :
    ∫⁻ ω, ∑ i : Fin n,
        (‖picardStep W N ℱ hℱW hℱN coeffs X x₀ h_σ_meas_X h_σ_progMeas_X h_σ_sq_X
              h_γ_meas_X h_γ_progMeas_X h_γ_sq_X t ω i
          - picardStep W N ℱ hℱW hℱN coeffs Y x₀ h_σ_meas_Y h_σ_progMeas_Y h_σ_sq_Y
              h_γ_meas_Y h_γ_progMeas_Y h_γ_sq_Y t ω i‖₊ : ℝ≥0∞) ^ 2 ∂P
      ≤ 3 * (ENNReal.ofReal ((n : ℝ) * L ^ 2 * t)
              + ENNReal.ofReal ((n : ℝ) * ((d : ℝ) * L ^ 2))
              + ENNReal.ofReal ((n : ℝ) * L ^ 2))
          * ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) t,
              (∑ i, (‖X s ω i - Y s ω i‖₊ : ℝ≥0∞) ^ 2) ∂volume ∂P := by
  have hbridge : ∀ ω : Ω, ∫⁻ s in Set.Icc (0 : ℝ) t,
        (‖X s ω - Y s ω‖₊ : ℝ≥0∞) ^ 2 ∂volume
      ≤ ∫⁻ s in Set.Icc (0 : ℝ) t, (∑ i, (‖X s ω i - Y s ω i‖₊ : ℝ≥0∞) ^ 2) ∂volume :=
    fun ω => lintegral_mono fun s => by
      simpa [Pi.sub_apply] using sq_coe_nnnorm_le_sum (X s ω - Y s ω)
  have hbridgeR : (∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) t,
        (‖X s ω - Y s ω‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P)
      ≤ ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) t,
          (∑ i, (‖X s ω i - Y s ω i‖₊ : ℝ≥0∞) ^ 2) ∂volume ∂P :=
    lintegral_mono hbridge
  have hbochner : (∫⁻ ω, ENNReal.ofReal
        (∫ s in Set.Icc (0 : ℝ) t, ‖X s ω - Y s ω‖ ^ 2 ∂volume) ∂P)
      ≤ ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) t,
          (∑ i, (‖X s ω i - Y s ω i‖₊ : ℝ≥0∞) ^ 2) ∂volume ∂P := by
    refine lintegral_mono fun ω => ?_
    refine le_trans (lintegral_window_norm_le_sum (Z := fun s ω => X s ω - Y s ω) t ω)
      (lintegral_mono fun s => ?_)
    exact le_of_eq (Finset.sum_congr rfl fun i _ => by rw [Pi.sub_apply])
  have hsplit : ∀ (ω : Ω) (i : Fin n),
      picardStep W N ℱ hℱW hℱN coeffs X x₀ h_σ_meas_X h_σ_progMeas_X h_σ_sq_X
          h_γ_meas_X h_γ_progMeas_X h_γ_sq_X t ω i
        - picardStep W N ℱ hℱW hℱN coeffs Y x₀ h_σ_meas_Y h_σ_progMeas_Y h_σ_sq_Y
            h_γ_meas_Y h_γ_progMeas_Y h_γ_sq_Y t ω i
      = (picardStep_drift coeffs X x₀ t ω i - picardStep_drift coeffs Y x₀ t ω i)
        + (picardStep_diffusion W ℱ hℱW coeffs X h_σ_meas_X h_σ_progMeas_X h_σ_sq_X t ω i
            - picardStep_diffusion W ℱ hℱW coeffs Y h_σ_meas_Y h_σ_progMeas_Y h_σ_sq_Y t ω i)
        + (picardStep_jump N ℱ hℱN coeffs X h_γ_meas_X h_γ_progMeas_X h_γ_sq_X t ω i
            - picardStep_jump N ℱ hℱN coeffs Y h_γ_meas_Y h_γ_progMeas_Y h_γ_sq_Y t ω i) := by
    intro ω i
    rw [picardStep_apply_eq W N ℱ hℱW hℱN coeffs X x₀ h_σ_meas_X h_σ_progMeas_X h_σ_sq_X
      h_γ_meas_X h_γ_progMeas_X h_γ_sq_X t ω i,
      picardStep_apply_eq W N ℱ hℱW hℱN coeffs Y x₀ h_σ_meas_Y h_σ_progMeas_Y h_σ_sq_Y
        h_γ_meas_Y h_γ_progMeas_Y h_γ_sq_Y t ω i]
    ring
  rw [lintegral_congr fun ω => Finset.sum_congr rfl fun i _ => by rw [hsplit ω i]]
  refine lintegral_sq_sum3_le
    (U₁ := fun ω i => picardStep_drift coeffs X x₀ t ω i
      - picardStep_drift coeffs Y x₀ t ω i)
    (U₂ := fun ω i =>
      picardStep_diffusion W ℱ hℱW coeffs X h_σ_meas_X h_σ_progMeas_X h_σ_sq_X t ω i
        - picardStep_diffusion W ℱ hℱW coeffs Y h_σ_meas_Y h_σ_progMeas_Y h_σ_sq_Y t ω i)
    (U₃ := fun ω i =>
      picardStep_jump N ℱ hℱN coeffs X h_γ_meas_X h_γ_progMeas_X h_γ_sq_X t ω i
        - picardStep_jump N ℱ hℱN coeffs Y h_γ_meas_Y h_γ_progMeas_Y h_γ_sq_Y t ω i)
    (fun i => ((((measurable_picardStep_drift coeffs X x₀ i (hμX i) t).sub
      (measurable_picardStep_drift coeffs Y x₀ i (hμY i) t)).nnnorm).coe_nnreal_ennreal).pow_const
        2)
    (fun i => ((((measurable_picardStep_diffusion W ℱ hℱW coeffs X h_σ_meas_X h_σ_progMeas_X
      h_σ_sq_X i t).sub (measurable_picardStep_diffusion W ℱ hℱW coeffs Y h_σ_meas_Y
        h_σ_progMeas_Y h_σ_sq_Y i t)).nnnorm).coe_nnreal_ennreal).pow_const 2)
    (fun i => ((((measurable_picardStep_jump N ℱ hℱN coeffs X h_γ_meas_X h_γ_progMeas_X
      h_γ_sq_X i t).sub (measurable_picardStep_jump N ℱ hℱN coeffs Y h_γ_meas_Y
        h_γ_progMeas_Y h_γ_sq_Y i t)).nnnorm).coe_nnreal_ennreal).pow_const 2)
    ?_ ?_ ?_
  · rw [← lintegral_ofReal_sum_sq_eq]
    exact (drift_diff_lintegral_sq_bound coeffs hLip.1 (mu_lip_componentwise coeffs hLip) X Y x₀
      hμX hμY hXYm hμXsq hμYsq hXYsq ht.le).trans (mul_le_mul' le_rfl hbochner)
  · exact (diffusion_diff_lintegral_sq_bound W ℱ hℱW coeffs hLip.1 hLip.2.2.1 X Y
      h_σ_meas_X h_σ_meas_Y h_σ_progMeas_X h_σ_progMeas_Y h_σ_sq_X h_σ_sq_Y ht).trans
      (mul_le_mul' le_rfl hbridgeR)
  · exact (jump_diff_lintegral_sq_bound N ℱ hℱN coeffs hLip X Y h_γ_meas_X h_γ_progMeas_X
      h_γ_sq_X h_γ_meas_Y h_γ_progMeas_Y h_γ_sq_Y ht).trans (mul_le_mul' le_rfl hbridgeR)
set_option maxHeartbeats 4000000 in
-- Same reason as `lintegral_sq_picardStep_diff_le`: the statement names the full Picard term
-- twice, once along each path.
/-- **The Bielecki contraction estimate for the Picard step.** The rate is
`√(3n(L²T + dL² + L²) / 2β)`, which `picardStep_bielecki_contraction_tight_rate_lt_one` puts
below one once `β` passes its threshold. -/
theorem bieleckiNorm_picardStep_diff_le
    (W : LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion P d)
    {ν : MeasureTheory.Measure E} [MeasureTheory.SigmaFinite ν]
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν)
    (ℱ : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›)
    (hℱW : ∀ j : Fin d, LevyStochCalc.Brownian.IsBrownianFiltration (W.W j) ℱ)
    (hℱN : LevyStochCalc.Poisson.IsPoissonFiltration N ℱ)
    (coeffs : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs n d E)
    {L : ℝ} (hLip : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs.IsLipschitz coeffs ν L)
    (X Y : ℝ → Ω → (Fin n → ℝ)) (x₀ : Fin n → ℝ)
    (h_σ_meas_X : ∀ i : Fin n, ∀ j : Fin d,
      Measurable (Function.uncurry (fun ω s => coeffs.σ s (X s ω) i j)))
    (h_σ_progMeas_X : ∀ i : Fin n, ∀ j : Fin d,
      Probability.ProgressivelyMeasurable ℱ (fun ω s => coeffs.σ s (X s ω) i j))
    (h_σ_sq_X : ∀ i : Fin n, ∀ j : Fin d, ∀ T' : ℝ, 0 < T' →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T',
        (‖coeffs.σ s (X s ω) i j‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    (h_γ_meas_X : ∀ i : Fin n,
      Measurable (fun p : Ω × ℝ × E => coeffs.γ p.2.1 (X p.2.1 p.1) p.2.2 i))
    (h_γ_progMeas_X : ∀ i : Fin n,
      Probability.MarkedProgressivelyMeasurable ℱ (fun ω s e => coeffs.γ s (X s ω) e i))
    (h_γ_sq_X : ∀ i : Fin n, ∀ T' : ℝ, 0 < T' →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T', ∫⁻ e,
        (‖coeffs.γ s (X s ω) e i‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P < ⊤)
    (h_σ_meas_Y : ∀ i : Fin n, ∀ j : Fin d,
      Measurable (Function.uncurry (fun ω s => coeffs.σ s (Y s ω) i j)))
    (h_σ_progMeas_Y : ∀ i : Fin n, ∀ j : Fin d,
      Probability.ProgressivelyMeasurable ℱ (fun ω s => coeffs.σ s (Y s ω) i j))
    (h_σ_sq_Y : ∀ i : Fin n, ∀ j : Fin d, ∀ T' : ℝ, 0 < T' →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T',
        (‖coeffs.σ s (Y s ω) i j‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    (h_γ_meas_Y : ∀ i : Fin n,
      Measurable (fun p : Ω × ℝ × E => coeffs.γ p.2.1 (Y p.2.1 p.1) p.2.2 i))
    (h_γ_progMeas_Y : ∀ i : Fin n,
      Probability.MarkedProgressivelyMeasurable ℱ (fun ω s e => coeffs.γ s (Y s ω) e i))
    (h_γ_sq_Y : ∀ i : Fin n, ∀ T' : ℝ, 0 < T' →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T', ∫⁻ e,
        (‖coeffs.γ s (Y s ω) e i‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P < ⊤)
    (hμX : ∀ i : Fin n, Measurable (Function.uncurry fun ω s => coeffs.μ s (X s ω) i))
    (hμY : ∀ i : Fin n, Measurable (Function.uncurry fun ω s => coeffs.μ s (Y s ω) i))
    (hXYm : Measurable (Function.uncurry fun (ω : Ω) (s : ℝ) => ‖X s ω - Y s ω‖))
    (hμXsq : ∀ i : Fin n, ∀ b : ℝ, 0 < b → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) b,
      (‖coeffs.μ s (X s ω) i‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    (hμYsq : ∀ i : Fin n, ∀ b : ℝ, 0 < b → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) b,
      (‖coeffs.μ s (Y s ω) i‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    (hXYsq : ∀ b : ℝ, 0 < b → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) b,
      (‖X s ω - Y s ω‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    (hZm : Measurable (Function.uncurry fun (ω : Ω) (s : ℝ) => X s ω - Y s ω))
    {β : ℝ} (hβ : 0 < β) {T : ℝ} (hT : 0 < T) :
    bieleckiNorm (P := P) β T (fun t ω i =>
        picardStep W N ℱ hℱW hℱN coeffs X x₀ h_σ_meas_X h_σ_progMeas_X h_σ_sq_X
            h_γ_meas_X h_γ_progMeas_X h_γ_sq_X t ω i
          - picardStep W N ℱ hℱW hℱN coeffs Y x₀ h_σ_meas_Y h_σ_progMeas_Y h_σ_sq_Y
              h_γ_meas_Y h_γ_progMeas_Y h_γ_sq_Y t ω i)
      ≤ (ENNReal.ofReal
            ((3 * ((n : ℝ) * L ^ 2 * T + (n : ℝ) * ((d : ℝ) * L ^ 2) + (n : ℝ) * L ^ 2))
              / (2 * β))) ^ ((1 : ℝ) / 2)
        * bieleckiNorm (P := P) β T (fun t ω i => X t ω i - Y t ω i) := by
  have hnn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  have hdn : (0 : ℝ) ≤ (d : ℝ) := Nat.cast_nonneg d
  have hCnn : (0 : ℝ)
      ≤ 3 * ((n : ℝ) * L ^ 2 * T + (n : ℝ) * ((d : ℝ) * L ^ 2) + (n : ℝ) * L ^ 2) := by
    have h1 : (0 : ℝ) ≤ (n : ℝ) * L ^ 2 * T := by positivity
    have h2 : (0 : ℝ) ≤ (n : ℝ) * ((d : ℝ) * L ^ 2) := by positivity
    have h3 : (0 : ℝ) ≤ (n : ℝ) * L ^ 2 := by positivity
    linarith
  refine bieleckiNorm_le_of_perTime hβ hCnn _ _ hZm fun t ht => ?_
  rw [lintegral_ofReal_sum_sq_eq]
  rcases ht.1.lt_or_eq with ht0 | ht0
  · refine (lintegral_sq_picardStep_diff_le W N ℱ hℱW hℱN coeffs hLip X Y x₀
      h_σ_meas_X h_σ_progMeas_X h_σ_sq_X h_γ_meas_X h_γ_progMeas_X h_γ_sq_X
      h_σ_meas_Y h_σ_progMeas_Y h_σ_sq_Y h_γ_meas_Y h_γ_progMeas_Y h_γ_sq_Y
      hμX hμY hXYm hμXsq hμYsq hXYsq ht0).trans (mul_le_mul' ?_ le_rfl)
    have hstep : ENNReal.ofReal ((n : ℝ) * L ^ 2 * t)
        ≤ ENNReal.ofReal ((n : ℝ) * L ^ 2 * T) := by
      refine ENNReal.ofReal_le_ofReal ?_
      have : (0 : ℝ) ≤ (n : ℝ) * L ^ 2 := by positivity
      nlinarith [ht.2, this]
    calc 3 * (ENNReal.ofReal ((n : ℝ) * L ^ 2 * t)
            + ENNReal.ofReal ((n : ℝ) * ((d : ℝ) * L ^ 2)) + ENNReal.ofReal ((n : ℝ) * L ^ 2))
        ≤ 3 * (ENNReal.ofReal ((n : ℝ) * L ^ 2 * T)
            + ENNReal.ofReal ((n : ℝ) * ((d : ℝ) * L ^ 2)) + ENNReal.ofReal ((n : ℝ) * L ^ 2)) :=
          mul_le_mul' le_rfl (add_le_add (add_le_add hstep le_rfl) le_rfl)
      _ = ENNReal.ofReal
            (3 * ((n : ℝ) * L ^ 2 * T + (n : ℝ) * ((d : ℝ) * L ^ 2) + (n : ℝ) * L ^ 2)) := by
          rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 3),
            ENNReal.ofReal_add (by positivity) (by positivity),
            ENNReal.ofReal_add (by positivity) (by positivity), ENNReal.ofReal_ofNat]
  · have hzero : ∀ᵐ ω ∂P, ∑ i : Fin n,
        (‖picardStep W N ℱ hℱW hℱN coeffs X x₀ h_σ_meas_X h_σ_progMeas_X h_σ_sq_X
              h_γ_meas_X h_γ_progMeas_X h_γ_sq_X t ω i
            - picardStep W N ℱ hℱW hℱN coeffs Y x₀ h_σ_meas_Y h_σ_progMeas_Y h_σ_sq_Y
                h_γ_meas_Y h_γ_progMeas_Y h_γ_sq_Y t ω i‖₊ : ℝ≥0∞) ^ 2 = 0 := by
      filter_upwards [ae_picardStep_zero W N ℱ hℱW hℱN coeffs X x₀ h_σ_meas_X h_σ_progMeas_X
          h_σ_sq_X h_γ_meas_X h_γ_progMeas_X h_γ_sq_X,
        ae_picardStep_zero W N ℱ hℱW hℱN coeffs Y x₀ h_σ_meas_Y h_σ_progMeas_Y
          h_σ_sq_Y h_γ_meas_Y h_γ_progMeas_Y h_γ_sq_Y] with ω hX hY
      simp [← ht0, hX, hY]
    rw [lintegral_congr_ae hzero, MeasureTheory.lintegral_zero]
    exact zero_le
end Weighting
end Picard
end Ito
end LevyStochCalc


