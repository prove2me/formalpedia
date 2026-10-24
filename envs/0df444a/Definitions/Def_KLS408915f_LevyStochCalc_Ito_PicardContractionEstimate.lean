-- Prove2me | Definitions.Def_KLS408915f_LevyStochCalc_Ito_PicardContractionEstimate
-- name    : KLS408915f_LevyStochCalc_Ito_PicardContractionEstimate
-- status  : Definition
-- author  : @Lazyfill
-- created : 2026-10-23T10:57:52.914988+00:00
-- url     : https://prove2.me/theorems/865f1af5-9493-44bf-a287-b1abfdb928b0
-- title:
--   Contraction estimates for the Picard self-map
-- statement:
--   Vendored from the LevyStochCalc library (https://github.com/cgarryZA/LevyStochCalc). The bundle transfers the raw-path Picard difference estimate to frozen `SBoundedProcess` inputs and then to `picardSelfMap`, preserving the Bielecki norm through a.e. modifications. The contraction factor is $\operatorname{ofReal}(3n(L^2T+dL^2+L^2)/(2\beta))^{1/2}$, under $\beta>0$ and $T>0$. It defines `picardIter`, proves geometric bounds on consecutive iterates, and proves convergence to `bieleckiLimit` whenever this factor is strictly less than $1$; auxiliary results establish measurability and finite difference energies.
-- source:
--   Lean source: https://github.com/cgarryZA/LevyStochCalc/blob/984dbf0b790031eac05d56fe5a84b65e15e1e932/LevyStochCalc/Ito/PicardContractionEstimate.lean#L40-L426 (repository human-ai-mathematics/kls-lean, commit 408915f, module `LevyStochCalc.Ito.PicardContractionEstimate`, definition bundle `KLS408915f_LevyStochCalc_Ito_PicardContractionEstimate`; the repository is private at upload time). Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (Apache-2.0; upstream copyright notice retained in the Lean text).

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
import Definitions.Def_KLS408915f_LevyStochCalc_Ito_PicardLimit
import Definitions.Def_KLS408915f_LevyStochCalc_Ito_PicardOutputModification
import Definitions.Def_KLS408915f_LevyStochCalc_Ito_PicardOutputMoments
import Definitions.Def_KLS408915f_LevyStochCalc_Ito_PicardOutputStepDiff
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
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Ito/PicardContractionEstimate.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
namespace LevyStochCalc
namespace Ito
namespace Picard
variable {Ω : Type*} [MeasurableSpace Ω] {E : Type*} [MeasurableSpace E]
variable {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν]
variable {n d : ℕ} {ℱ : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›} {T : ℝ}
/-- The squared norm of a difference is at most twice the sum of the squared norms. -/
theorem sq_nnnorm_sub_le {α : Type*} [SeminormedAddCommGroup α] (a b : α) :
    (‖a - b‖₊ : ℝ≥0∞) ^ 2 ≤ 2 * (‖a‖₊ : ℝ≥0∞) ^ 2 + 2 * (‖b‖₊ : ℝ≥0∞) ^ 2 := by
  have hreal : ‖a - b‖ ^ 2 ≤ 2 * ‖a‖ ^ 2 + 2 * ‖b‖ ^ 2 := by
    have h := norm_sub_le a b
    nlinarith [norm_nonneg a, norm_nonneg b, norm_nonneg (a - b), sq_nonneg (‖a‖ - ‖b‖)]
  calc (‖a - b‖₊ : ℝ≥0∞) ^ 2 = ENNReal.ofReal (‖a - b‖ ^ 2) := sq_coe_nnnorm _
    _ ≤ ENNReal.ofReal (2 * ‖a‖ ^ 2 + 2 * ‖b‖ ^ 2) := ENNReal.ofReal_le_ofReal hreal
    _ = 2 * (‖a‖₊ : ℝ≥0∞) ^ 2 + 2 * (‖b‖₊ : ℝ≥0∞) ^ 2 := by
        rw [ENNReal.ofReal_add (by positivity) (by positivity), sq_coe_nnnorm, sq_coe_nnnorm,
          ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_mul (by norm_num)]
        norm_num
/-- The difference of two frozen processes is jointly measurable. -/
theorem measurable_uncurry_stop_sub (X Y : SBoundedProcess (n := n) P ℱ T) :
    Measurable (Function.uncurry fun (ω : Ω) (s : ℝ) => X.stop.X s ω - Y.stop.X s ω) :=
  (X.stop.measurable_path.comp (measurable_snd.prodMk measurable_fst)).sub
    (Y.stop.measurable_path.comp (measurable_snd.prodMk measurable_fst))
/-- The norm of the difference of two frozen processes is jointly measurable. -/
theorem measurable_uncurry_stop_sub_norm (X Y : SBoundedProcess (n := n) P ℱ T) :
    Measurable (Function.uncurry fun (ω : Ω) (s : ℝ) => ‖X.stop.X s ω - Y.stop.X s ω‖) :=
  (measurable_uncurry_stop_sub X Y).norm
/-- The `ω`-slice of the squared norms of a path map is measurable in time. -/
theorem measurable_sq_slice_time {Z : ℝ → Ω → (Fin n → ℝ)}
    (hZm : Measurable (Function.uncurry Z)) (ω : Ω) :
    Measurable fun s : ℝ => ∑ i, (‖Z s ω i‖₊ : ℝ≥0∞) ^ 2 :=
  Finset.measurable_sum _ fun i _ =>
    (ENNReal.continuous_coe.measurable.comp
      (((measurable_pi_apply i).comp
        (hZm.comp (measurable_id.prodMk measurable_const))).nnnorm)).pow_const 2
/-- The squared norms of a path map are jointly measurable. -/
theorem measurable_uncurry_sq {Z : ℝ → Ω → (Fin n → ℝ)}
    (hZm : Measurable (Function.uncurry Z)) :
    Measurable (Function.uncurry fun (ω : Ω) (s : ℝ) => ∑ i, (‖Z s ω i‖₊ : ℝ≥0∞) ^ 2) :=
  Finset.measurable_sum _ fun i _ =>
    (ENNReal.continuous_coe.measurable.comp
      (((measurable_pi_apply i).comp
        (hZm.comp (measurable_snd.prodMk measurable_fst))).nnnorm)).pow_const 2
/-- The energy of a path map over a window is measurable in the sample point. -/
theorem measurable_lintegral_sq {Z : ℝ → Ω → (Fin n → ℝ)}
    (hZm : Measurable (Function.uncurry Z)) (b : ℝ) :
    Measurable fun ω : Ω =>
      ∫⁻ s in Set.Icc (0 : ℝ) b, ∑ i, (‖Z s ω i‖₊ : ℝ≥0∞) ^ 2 ∂volume :=
  (measurable_uncurry_sq hZm).lintegral_prod_right'
    (ν := volume.restrict (Set.Icc (0 : ℝ) b))
omit [IsProbabilityMeasure P] in
/-- The energy of the difference of two path maps of finite energy is finite. -/
theorem lintegral_sq_sub_lt_top_of_energy {Z₁ Z₂ : ℝ → Ω → (Fin n → ℝ)}
    (hm₁ : Measurable (Function.uncurry Z₁)) (hm₂ : Measurable (Function.uncurry Z₂))
    (h₁ : ∀ b : ℝ, ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) b,
      ∑ i, (‖Z₁ s ω i‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    (h₂ : ∀ b : ℝ, ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) b,
      ∑ i, (‖Z₂ s ω i‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤) (b : ℝ) :
    ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) b,
        (‖Z₁ s ω - Z₂ s ω‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤ := by
  have hpt : ∀ ω : Ω, ∀ s : ℝ, (‖Z₁ s ω - Z₂ s ω‖₊ : ℝ≥0∞) ^ 2
      ≤ 2 * ∑ i, (‖Z₁ s ω i‖₊ : ℝ≥0∞) ^ 2 + 2 * ∑ i, (‖Z₂ s ω i‖₊ : ℝ≥0∞) ^ 2 := by
    intro ω s
    refine (sq_nnnorm_sub_le _ _).trans (add_le_add ?_ ?_)
    · exact mul_le_mul' le_rfl (by rw [sq_coe_nnnorm]; exact ofReal_sq_norm_le_sum _)
    · exact mul_le_mul' le_rfl (by rw [sq_coe_nnnorm]; exact ofReal_sq_norm_le_sum _)
  have hinner : ∀ ω : Ω, ∫⁻ s in Set.Icc (0 : ℝ) b,
        (2 * ∑ i, (‖Z₁ s ω i‖₊ : ℝ≥0∞) ^ 2 + 2 * ∑ i, (‖Z₂ s ω i‖₊ : ℝ≥0∞) ^ 2) ∂volume
      = 2 * (∫⁻ s in Set.Icc (0 : ℝ) b, ∑ i, (‖Z₁ s ω i‖₊ : ℝ≥0∞) ^ 2 ∂volume)
        + 2 * ∫⁻ s in Set.Icc (0 : ℝ) b, ∑ i, (‖Z₂ s ω i‖₊ : ℝ≥0∞) ^ 2 ∂volume := by
    intro ω
    rw [lintegral_add_left ((measurable_sq_slice_time hm₁ ω).const_mul 2),
      lintegral_const_mul _ (measurable_sq_slice_time hm₁ ω),
      lintegral_const_mul _ (measurable_sq_slice_time hm₂ ω)]
  calc ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) b, (‖Z₁ s ω - Z₂ s ω‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P
      ≤ ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) b,
          (2 * ∑ i, (‖Z₁ s ω i‖₊ : ℝ≥0∞) ^ 2
            + 2 * ∑ i, (‖Z₂ s ω i‖₊ : ℝ≥0∞) ^ 2) ∂volume ∂P :=
        lintegral_mono fun ω => lintegral_mono fun s => hpt ω s
    _ = ∫⁻ ω, (2 * (∫⁻ s in Set.Icc (0 : ℝ) b, ∑ i, (‖Z₁ s ω i‖₊ : ℝ≥0∞) ^ 2 ∂volume)
          + 2 * ∫⁻ s in Set.Icc (0 : ℝ) b,
              ∑ i, (‖Z₂ s ω i‖₊ : ℝ≥0∞) ^ 2 ∂volume) ∂P := lintegral_congr fun ω => hinner ω
    _ = 2 * (∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) b,
              ∑ i, (‖Z₁ s ω i‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P)
          + 2 * ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) b,
              ∑ i, (‖Z₂ s ω i‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P := by
        rw [lintegral_add_left ((measurable_lintegral_sq hm₁ b).const_mul 2),
          lintegral_const_mul _ (measurable_lintegral_sq hm₁ b),
          lintegral_const_mul _ (measurable_lintegral_sq hm₂ b)]
    _ < ⊤ := ENNReal.add_lt_top.mpr ⟨ENNReal.mul_lt_top (by norm_num) (h₁ b),
        ENNReal.mul_lt_top (by norm_num) (h₂ b)⟩
/-- The energy of the difference of two frozen processes is finite on every window. -/
theorem lintegral_sq_stop_sub_lt_top (X Y : SBoundedProcess (n := n) P ℱ T) (hT : 0 ≤ T)
    (b : ℝ) :
    ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) b,
        (‖X.stop.X s ω - Y.stop.X s ω‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤ :=
  lintegral_sq_sub_lt_top_of_energy X.stop.measurable_path Y.stop.measurable_path
    (fun c => lt_of_le_of_lt (lintegral_lintegral_sq_stop_le X hT c)
      (ENNReal.mul_lt_top ENNReal.ofReal_lt_top (ENNReal.pow_lt_top X.sup_L2)))
    (fun c => lt_of_le_of_lt (lintegral_lintegral_sq_stop_le Y hT c)
      (ENNReal.mul_lt_top ENNReal.ofReal_lt_top (ENNReal.pow_lt_top Y.sup_L2))) b
/-- Freezing at the horizon does not change the Bielecki norm of a difference. -/
theorem bieleckiNorm_stop_sub (β : ℝ) (X Y : SBoundedProcess (n := n) P ℱ T) :
    bieleckiNorm (P := P) β T (fun t ω i => X.stop.X t ω i - Y.stop.X t ω i)
      = bieleckiNorm (P := P) β T (fun t ω i => X.X t ω i - Y.X t ω i) :=
  bieleckiNorm_min (P := P) β T fun t ω i => X.X t ω i - Y.X t ω i
/-- **The Picard step along frozen processes is a Bielecki contraction**, with the rate of
`bieleckiNorm_picardStep_diff_le`. -/
theorem bieleckiNorm_picardStepOnStop_diff_le
    (W : LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion P d)
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν)
    (hℱW : ∀ j : Fin d, LevyStochCalc.Brownian.IsBrownianFiltration (W.W j) ℱ)
    (hℱN : LevyStochCalc.Poisson.IsPoissonFiltration N ℱ)
    (coeffs : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs n d E)
    (hReg : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs.IsRegular coeffs ν)
    {L : ℝ} (hLip : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs.IsLipschitz coeffs ν L)
    (x₀ : Fin n → ℝ) {β : ℝ} (hβ : 0 < β) (hT : 0 < T)
    (X Y : SBoundedProcess (n := n) P ℱ T) :
    bieleckiNorm (P := P) β T (fun t ω i =>
        picardStepOnStop W N hℱW hℱN coeffs hReg hLip X hT.le x₀ t ω i
          - picardStepOnStop W N hℱW hℱN coeffs hReg hLip Y hT.le x₀ t ω i)
      ≤ (ENNReal.ofReal
            ((3 * ((n : ℝ) * L ^ 2 * T + (n : ℝ) * ((d : ℝ) * L ^ 2) + (n : ℝ) * L ^ 2))
              / (2 * β))) ^ ((1 : ℝ) / 2)
        * bieleckiNorm (P := P) β T (fun t ω i => X.X t ω i - Y.X t ω i) := by
  rw [← bieleckiNorm_stop_sub β X Y]
  exact bieleckiNorm_picardStep_diff_le W N ℱ hℱW hℱN coeffs hLip X.stop.X Y.stop.X x₀
    (fun i j => measurable_sigma_stop coeffs hReg X i j)
    (fun i j => progressivelyMeasurable_sigma_stop coeffs hReg X i j)
    (fun i j _ hT' => lintegral_sq_sigma_stop_lt_top coeffs hReg hLip X hT.le i j hT')
    (fun i => measurable_gamma_stop coeffs hReg X i)
    (fun i => markedProgressivelyMeasurable_gamma_stop coeffs hReg X i)
    (fun i _ hT' => lintegral_sq_gamma_stop_lt_top coeffs hReg hLip X hT.le i hT')
    (fun i j => measurable_sigma_stop coeffs hReg Y i j)
    (fun i j => progressivelyMeasurable_sigma_stop coeffs hReg Y i j)
    (fun i j _ hT' => lintegral_sq_sigma_stop_lt_top coeffs hReg hLip Y hT.le i j hT')
    (fun i => measurable_gamma_stop coeffs hReg Y i)
    (fun i => markedProgressivelyMeasurable_gamma_stop coeffs hReg Y i)
    (fun i _ hT' => lintegral_sq_gamma_stop_lt_top coeffs hReg hLip Y hT.le i hT')
    (fun i => measurable_mu_stop coeffs hReg X i)
    (fun i => measurable_mu_stop coeffs hReg Y i)
    (measurable_uncurry_stop_sub_norm X Y)
    (fun i b hb => lintegral_sq_mu_stop_lt_top coeffs hReg hLip X hT.le i hb)
    (fun i b hb => lintegral_sq_mu_stop_lt_top coeffs hReg hLip Y hT.le i hb)
    (fun b _ => lintegral_sq_stop_sub_lt_top X Y hT.le b)
    (measurable_uncurry_stop_sub X Y) hβ hT
/-- **The Picard self-map is a Bielecki contraction.** The self-map is a modification of the step
along the frozen process, and the Bielecki norm is unchanged under modification. -/
theorem bieleckiNorm_picardSelfMap_diff_le
    (W : LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion P d)
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν)
    (ℱ' : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›) [ℱ'.IsRightContinuous]
    (hℱW : ∀ j : Fin d, LevyStochCalc.Brownian.IsBrownianFiltration (W.W j) ℱ')
    (hℱN : LevyStochCalc.Poisson.IsPoissonFiltration N ℱ')
    (hℱ0 : ∀ t : ℝ, t ≤ 0 → ℱ' 0 ≤ ℱ' t)
    (hnull : ∀ s : Set Ω, MeasurableSet s → P s = 0 → MeasurableSet[ℱ' 0] s)
    (coeffs : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs n d E)
    (hReg : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs.IsRegular coeffs ν)
    {L : ℝ} (hLip : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs.IsLipschitz coeffs ν L)
    (x₀ : Fin n → ℝ) {β : ℝ} (hβ : 0 < β) (hT : 0 < T)
    (X Y : SBoundedProcess (n := n) P ℱ' T) :
    bieleckiNorm (P := P) β T (fun t ω i =>
        (picardSelfMap W N ℱ' hℱW hℱN hℱ0 hnull coeffs hReg hLip x₀ hT X).X t ω i
          - (picardSelfMap W N ℱ' hℱW hℱN hℱ0 hnull coeffs hReg hLip x₀ hT Y).X t ω i)
      ≤ (ENNReal.ofReal
            ((3 * ((n : ℝ) * L ^ 2 * T + (n : ℝ) * ((d : ℝ) * L ^ 2) + (n : ℝ) * L ^ 2))
              / (2 * β))) ^ ((1 : ℝ) / 2)
        * bieleckiNorm (P := P) β T (fun t ω i => X.X t ω i - Y.X t ω i) := by
  have hcongr : bieleckiNorm (P := P) β T (fun t ω i =>
        (picardSelfMap W N ℱ' hℱW hℱN hℱ0 hnull coeffs hReg hLip x₀ hT X).X t ω i
          - (picardSelfMap W N ℱ' hℱW hℱN hℱ0 hnull coeffs hReg hLip x₀ hT Y).X t ω i)
      = bieleckiNorm (P := P) β T (fun t ω i =>
        picardStepOnStop W N hℱW hℱN coeffs hReg hLip X hT.le x₀ t ω i
          - picardStepOnStop W N hℱW hℱN coeffs hReg hLip Y hT.le x₀ t ω i) := by
    refine bieleckiNorm_congr_ae (P := P) β T fun t => ?_
    filter_upwards [picardSelfMap_ae_eq W N ℱ' hℱW hℱN hℱ0 hnull coeffs hReg hLip x₀ hT X t,
      picardSelfMap_ae_eq W N ℱ' hℱW hℱN hℱ0 hnull coeffs hReg hLip x₀ hT Y t] with ω hX hY
    funext i
    rw [hX, hY]
  rw [hcongr]
  exact bieleckiNorm_picardStepOnStop_diff_le W N hℱW hℱN coeffs hReg hLip x₀ hβ hT X Y
/-- A positive Bielecki weight only shrinks the norm on `[0, T]`. -/
theorem bieleckiNorm_le_bieleckiNorm_zero {β : ℝ} (hβ : 0 ≤ β) (T : ℝ)
    (Z : ℝ → Ω → (Fin n → ℝ)) :
    bieleckiNorm (P := P) β T Z ≤ bieleckiNorm (P := P) 0 T Z := by
  refine iSup₂_le fun t ht => ?_
  have hw : ENNReal.ofReal (Real.exp (-β * t)) ≤ ENNReal.ofReal (Real.exp (-0 * t)) := by
    refine ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr ?_)
    have : 0 ≤ β * t := mul_nonneg hβ ht.1
    nlinarith
  exact le_trans (mul_le_mul' hw le_rfl)
    (le_iSup₂ (f := fun u (_ : u ∈ Set.Icc (0 : ℝ) T) =>
      ENNReal.ofReal (Real.exp (-0 * u))
        * (∫⁻ ω, ∑ i, (‖Z u ω i‖₊ : ℝ≥0∞) ^ 2 ∂P) ^ ((1 : ℝ) / 2)) t ht)
variable (W : LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion P d)
  (N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν)
  (ℱ' : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›) [ℱ'.IsRightContinuous]
  (hℱW : ∀ j : Fin d, LevyStochCalc.Brownian.IsBrownianFiltration (W.W j) ℱ')
  (hℱN : LevyStochCalc.Poisson.IsPoissonFiltration N ℱ')
  (hℱ0 : ∀ t : ℝ, t ≤ 0 → ℱ' 0 ≤ ℱ' t)
  (hnull : ∀ s : Set Ω, MeasurableSet s → P s = 0 → MeasurableSet[ℱ' 0] s)
  (coeffs : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs n d E)
  (hReg : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs.IsRegular coeffs ν)
/-- **The Picard iterates** of a starting process under the self-map. -/
noncomputable def picardIter {L : ℝ}
    (hLip : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs.IsLipschitz coeffs ν L)
    (x₀ : Fin n → ℝ) (hT : 0 < T) (X₀ : SBoundedProcess (n := n) P ℱ' T) :
    ℕ → SBoundedProcess (n := n) P ℱ' T
  | 0 => X₀
  | k + 1 => picardSelfMap W N ℱ' hℱW hℱN hℱ0 hnull coeffs hReg hLip x₀ hT
      (picardIter hLip x₀ hT X₀ k)
/-- The Picard iterates are geometrically Bielecki-Cauchy at the contraction rate. -/
theorem bieleckiNorm_picardIter_step_le {L : ℝ}
    (hLip : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs.IsLipschitz coeffs ν L)
    (x₀ : Fin n → ℝ) {β : ℝ} (hβ : 0 < β) (hT : 0 < T)
    (X₀ : SBoundedProcess (n := n) P ℱ' T) (k : ℕ) :
    bieleckiNorm (P := P) β T (fun t ω i =>
        (picardIter W N ℱ' hℱW hℱN hℱ0 hnull coeffs hReg hLip x₀ hT X₀ (k + 1)).X t ω i
          - (picardIter W N ℱ' hℱW hℱN hℱ0 hnull coeffs hReg hLip x₀ hT X₀ k).X t ω i)
      ≤ ((ENNReal.ofReal
            ((3 * ((n : ℝ) * L ^ 2 * T + (n : ℝ) * ((d : ℝ) * L ^ 2) + (n : ℝ) * L ^ 2))
              / (2 * β))) ^ ((1 : ℝ) / 2)) ^ k
        * bieleckiNorm (P := P) β T (fun t ω i =>
            (picardIter W N ℱ' hℱW hℱN hℱ0 hnull coeffs hReg hLip x₀ hT X₀ 1).X t ω i
              - (picardIter W N ℱ' hℱW hℱN hℱ0 hnull coeffs hReg hLip x₀ hT X₀ 0).X t ω i) := by
  induction k with
  | zero => simp
  | succ k ih =>
    refine le_trans (bieleckiNorm_picardSelfMap_diff_le W N ℱ' hℱW hℱN hℱ0 hnull coeffs hReg
      hLip x₀ hβ hT _ _) ?_
    refine le_trans (mul_le_mul' le_rfl ih) (le_of_eq ?_)
    rw [← mul_assoc, ← pow_succ']
omit [ℱ'.IsRightContinuous] in
/-- The Bielecki norm of a difference of two processes of the space is finite. -/
theorem bieleckiNorm_sub_lt_top {β : ℝ} (hβ : 0 ≤ β)
    (X Y : SBoundedProcess (n := n) P ℱ' T) :
    bieleckiNorm (P := P) β T (fun t ω i => X.X t ω i - Y.X t ω i) < ⊤ := by
  have hneg : bieleckiNorm (P := P) 0 T (fun t ω => -(Y.X t ω))
      = bieleckiNorm (P := P) 0 T Y.X := by
    unfold bieleckiNorm
    refine iSup_congr fun t => iSup_congr fun _ => ?_
    congr 2
    exact lintegral_congr fun ω => Finset.sum_congr rfl fun i _ => by simp
  have hEq : (fun t ω i => X.X t ω i - Y.X t ω i)
      = fun t (ω : Ω) => X.X t ω + (fun i => -(Y.X t ω i)) := by
    funext t ω i
    simp [Pi.add_apply, sub_eq_add_neg]
  have hnegm : Measurable (Function.uncurry fun t (ω : Ω) => -(Y.X t ω)) :=
    measurable_neg.comp Y.measurable_path
  have hadd := bieleckiNorm_add_le (P := P) 0 T X.X (fun t ω => -(Y.X t ω))
    (fun t => bieleckiNorm_inner_aemeasurable _ X.measurable_path t)
    (fun t => bieleckiNorm_inner_aemeasurable (fun t ω => -(Y.X t ω)) hnegm t)
  refine lt_of_le_of_lt (bieleckiNorm_le_bieleckiNorm_zero hβ T _) ?_
  rw [hEq]
  refine lt_of_le_of_lt hadd ?_
  rw [hneg]
  exact ENNReal.add_lt_top.mpr ⟨X.sup_L2, Y.sup_L2⟩
/-- **The Picard iterates converge in Bielecki norm.** At a weight making the contraction rate
`< 1`, the iterates converge to `bieleckiLimit` at that rate. -/
theorem bieleckiNorm_picardIter_sub_bieleckiLimit_le {L : ℝ}
    (hLip : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs.IsLipschitz coeffs ν L)
    (x₀ : Fin n → ℝ) {β : ℝ} (hβ : 0 < β) (hT : 0 < T)
    (X₀ : SBoundedProcess (n := n) P ℱ' T)
    (hq : (ENNReal.ofReal
            ((3 * ((n : ℝ) * L ^ 2 * T + (n : ℝ) * ((d : ℝ) * L ^ 2) + (n : ℝ) * L ^ 2))
              / (2 * β))) ^ ((1 : ℝ) / 2) < 1) (k : ℕ) :
    bieleckiNorm (P := P) β T (fun t ω i =>
        (picardIter W N ℱ' hℱW hℱN hℱ0 hnull coeffs hReg hLip x₀ hT X₀ k).X t ω i
          - bieleckiLimit
              (fun m => (picardIter W N ℱ' hℱW hℱN hℱ0 hnull coeffs hReg hLip x₀ hT X₀ m).X)
              t ω i)
      ≤ ((ENNReal.ofReal
            ((3 * ((n : ℝ) * L ^ 2 * T + (n : ℝ) * ((d : ℝ) * L ^ 2) + (n : ℝ) * L ^ 2))
              / (2 * β))) ^ ((1 : ℝ) / 2)) ^ k
        * ((1 - (ENNReal.ofReal
              ((3 * ((n : ℝ) * L ^ 2 * T + (n : ℝ) * ((d : ℝ) * L ^ 2) + (n : ℝ) * L ^ 2))
                / (2 * β))) ^ ((1 : ℝ) / 2))⁻¹
            * bieleckiNorm (P := P) β T (fun t ω i =>
                (picardIter W N ℱ' hℱW hℱN hℱ0 hnull coeffs hReg hLip x₀ hT X₀ 1).X t ω i
                  - (picardIter W N ℱ' hℱW hℱN hℱ0 hnull coeffs hReg hLip x₀ hT X₀ 0).X
                      t ω i)) :=
  bieleckiNorm_sub_bieleckiLimit_geometric (P := P) β T
    (fun m => (picardIter W N ℱ' hℱW hℱN hℱ0 hnull coeffs hReg hLip x₀ hT X₀ m).measurable_path)
    (bieleckiNorm_picardIter_step_le W N ℱ' hℱW hℱN hℱ0 hnull coeffs hReg hLip x₀ hβ hT X₀)
    hq (bieleckiNorm_sub_lt_top ℱ' hβ.le _ _).ne k
omit [IsProbabilityMeasure P] [ℱ'.IsRightContinuous] in
/-- Slice measurability suffices for the Bielecki subadditivity hypothesis. -/
theorem bieleckiNorm_inner_aemeasurable_of_slice {Y : ℝ → Ω → (Fin n → ℝ)}
    (h : ∀ (t : ℝ) (i : Fin n), Measurable fun ω => Y t ω i) (t : ℝ) :
    AEMeasurable (fun ω => (∑ i, (‖Y t ω i‖₊ : ℝ≥0∞) ^ 2) ^ ((1 : ℝ) / 2)) P :=
  ((Finset.measurable_sum _ fun i _ =>
    (ENNReal.continuous_coe.measurable.comp (h t i).nnnorm).pow_const 2).pow_const
      ((1 : ℝ) / 2)).aemeasurable
omit [ℱ'.IsRightContinuous] in
/-- The Bielecki norm of a difference is symmetric. -/
theorem bieleckiNorm_sub_comm (β T : ℝ) (A B : ℝ → Ω → (Fin n → ℝ)) :
    bieleckiNorm (P := P) β T (fun t ω i => A t ω i - B t ω i)
      = bieleckiNorm (P := P) β T (fun t ω i => B t ω i - A t ω i) := by
  unfold bieleckiNorm
  refine iSup_congr fun t => iSup_congr fun _ => ?_
  congr 2
  refine lintegral_congr fun ω => Finset.sum_congr rfl fun i _ => ?_
  simp only [show A t ω i - B t ω i = -(B t ω i - A t ω i) from by ring, nnnorm_neg]
omit [ℱ'.IsRightContinuous] in
/-- The unweighted Bielecki norm is bounded by the weighted one, at the cost of `e^{βT}`. -/
theorem bieleckiNorm_zero_le_mul {β : ℝ} (hβ : 0 ≤ β) {T : ℝ} (Z : ℝ → Ω → (Fin n → ℝ)) :
    bieleckiNorm (P := P) 0 T Z
      ≤ ENNReal.ofReal (Real.exp (β * T)) * bieleckiNorm (P := P) β T Z := by
  refine iSup₂_le fun t ht => ?_
  have hle : ENNReal.ofReal (Real.exp (-β * t))
      * (∫⁻ ω, ∑ i, (‖Z t ω i‖₊ : ℝ≥0∞) ^ 2 ∂P) ^ ((1 : ℝ) / 2)
      ≤ bieleckiNorm (P := P) β T Z :=
    le_iSup₂ (f := fun u (_ : u ∈ Set.Icc (0 : ℝ) T) =>
      ENNReal.ofReal (Real.exp (-β * u))
        * (∫⁻ ω, ∑ i, (‖Z u ω i‖₊ : ℝ≥0∞) ^ 2 ∂P) ^ ((1 : ℝ) / 2)) t ht
  have hexp : ENNReal.ofReal (Real.exp (β * t)) ≤ ENNReal.ofReal (Real.exp (β * T)) :=
    ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr (by nlinarith [ht.2, ht.1]))
  calc ENNReal.ofReal (Real.exp (-0 * t))
        * (∫⁻ ω, ∑ i, (‖Z t ω i‖₊ : ℝ≥0∞) ^ 2 ∂P) ^ ((1 : ℝ) / 2)
      = ENNReal.ofReal (Real.exp (β * t)) * (ENNReal.ofReal (Real.exp (-β * t))
          * (∫⁻ ω, ∑ i, (‖Z t ω i‖₊ : ℝ≥0∞) ^ 2 ∂P) ^ ((1 : ℝ) / 2)) := by
        rw [← mul_assoc, ← ENNReal.ofReal_mul (Real.exp_nonneg _), ← Real.exp_add]
        simp
    _ ≤ ENNReal.ofReal (Real.exp (β * T)) * bieleckiNorm (P := P) β T Z :=
        mul_le_mul' hexp hle
omit [ℱ'.IsRightContinuous] in
/-- A path map at finite Bielecki distance from one of finite Bielecki norm has finite Bielecki
norm. -/
theorem bieleckiNorm_lt_top_of_approx (β T : ℝ) {A Z : ℝ → Ω → (Fin n → ℝ)}
    (hAm : ∀ (t : ℝ) (i : Fin n), Measurable fun ω => A t ω i)
    (hZm : ∀ (t : ℝ) (i : Fin n), Measurable fun ω => Z t ω i)
    (hA : bieleckiNorm (P := P) β T A < ⊤)
    (hd : bieleckiNorm (P := P) β T (fun t ω i => A t ω i - Z t ω i) < ⊤) :
    bieleckiNorm (P := P) β T Z < ⊤ := by
  have hEq : Z = fun t (ω : Ω) => A t ω + fun i => Z t ω i - A t ω i := by
    funext t ω i
    simp [Pi.add_apply]
  have hadd := bieleckiNorm_add_le (P := P) β T A (fun t ω => fun i => Z t ω i - A t ω i)
    (bieleckiNorm_inner_aemeasurable_of_slice hAm)
    (bieleckiNorm_inner_aemeasurable_of_slice fun t i => (hZm t i).sub (hAm t i))
  rw [hEq]
  refine lt_of_le_of_lt hadd (ENNReal.add_lt_top.mpr ⟨hA, ?_⟩)
  rwa [bieleckiNorm_sub_comm (P := P) β T Z A]
end Picard
end Ito
end LevyStochCalc


