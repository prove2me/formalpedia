-- Prove2me | Definitions.Def_KLS408915f_LevyStochCalc_Ito_PicardLimit
-- name    : KLS408915f_LevyStochCalc_Ito_PicardLimit
-- status  : Definition
-- author  : @Lazyfill
-- created : 2026-10-23T10:39:51.567626+00:00
-- url     : https://prove2.me/theorems/014f376b-d9df-4039-80ea-79e87ba78c78
-- title:
--   Limits of Bielecki-Cauchy path-map sequences
-- statement:
--   Vendored from the LevyStochCalc library (https://github.com/cgarryZA/LevyStochCalc). `bieleckiLimit` is the coordinatewise pointwise `limsup` of a sequence of path maps, and the bundle proves its joint and progressive measurability. If the consecutive Bielecki differences are bounded by a summable sequence in $[0,\infty]$, the limit is almost surely the coordinatewise path limit and the Bielecki distance from the $k$th term is bounded by the tail $\sum_j c_{k+j}$. For geometric bounds with rate $q<1$, this tail is expressed as $q^k(1-q)^{-1}C$.
-- source:
--   Lean source: https://github.com/cgarryZA/LevyStochCalc/blob/984dbf0b790031eac05d56fe5a84b65e15e1e932/LevyStochCalc/Ito/PicardLimit.lean#L41-L345 (repository human-ai-mathematics/kls-lean, commit 408915f, module `LevyStochCalc.Ito.PicardLimit`, definition bundle `KLS408915f_LevyStochCalc_Ito_PicardLimit`; the repository is private at upload time). Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (Apache-2.0; upstream copyright notice retained in the Lean text).

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
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Ito/PicardLimit.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal Topology
namespace LevyStochCalc
namespace Ito
namespace Picard
variable {Ω : Type*} [MeasurableSpace Ω] {n : ℕ} {P : Measure Ω} [IsProbabilityMeasure P]
/-- A uniform bound on the weighted `L²` norms over the window bounds the Bielecki norm. -/
theorem bieleckiNorm_le_of_perTime_rpow (β T : ℝ) (Z : ℝ → Ω → (Fin n → ℝ)) (c : ℝ≥0∞)
    (h : ∀ t ∈ Set.Icc (0 : ℝ) T,
      (∫⁻ ω, ∑ i, (‖Z t ω i‖₊ : ℝ≥0∞) ^ 2 ∂P) ^ ((1 : ℝ) / 2)
        ≤ ENNReal.ofReal (Real.exp (β * t)) * c) :
    bieleckiNorm (P := P) β T Z ≤ c := by
  refine iSup₂_le fun t ht => ?_
  refine le_trans (mul_le_mul' le_rfl (h t ht)) (le_of_eq ?_)
  rw [← mul_assoc, ← ENNReal.ofReal_mul (Real.exp_nonneg _), ← Real.exp_add]
  simp
/-- The Bielecki norm bounds the weighted `L²` norm at every time of the window. -/
theorem lintegral_sq_rpow_le_of_bieleckiNorm (β T : ℝ) (Z : ℝ → Ω → (Fin n → ℝ))
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) T) :
    (∫⁻ ω, ∑ i, (‖Z t ω i‖₊ : ℝ≥0∞) ^ 2 ∂P) ^ ((1 : ℝ) / 2)
      ≤ ENNReal.ofReal (Real.exp (β * t)) * bieleckiNorm (P := P) β T Z := by
  have hle : ENNReal.ofReal (Real.exp (-β * t))
      * (∫⁻ ω, ∑ i, (‖Z t ω i‖₊ : ℝ≥0∞) ^ 2 ∂P) ^ ((1 : ℝ) / 2)
      ≤ bieleckiNorm (P := P) β T Z :=
    le_iSup₂ (f := fun u (_ : u ∈ Set.Icc (0 : ℝ) T) =>
      ENNReal.ofReal (Real.exp (-β * u))
        * (∫⁻ ω, ∑ i, (‖Z u ω i‖₊ : ℝ≥0∞) ^ 2 ∂P) ^ ((1 : ℝ) / 2)) t ht
  refine le_trans (le_of_eq ?_) (mul_le_mul' (le_refl (ENNReal.ofReal (Real.exp (β * t)))) hle)
  rw [← mul_assoc, ← ENNReal.ofReal_mul (Real.exp_nonneg _), ← Real.exp_add]
  simp
/-- The pointwise `limsup` of a sequence of path maps. Where the sequence converges this is its
limit; elsewhere it is the `limsup` of a real sequence, whose value is immaterial. -/
noncomputable def bieleckiLimit (X : ℕ → ℝ → Ω → (Fin n → ℝ)) : ℝ → Ω → (Fin n → ℝ) :=
  fun t ω i => Filter.limsup (fun k => X k t ω i) Filter.atTop
/-- The limit path map is jointly measurable. -/
theorem measurable_bieleckiLimit {X : ℕ → ℝ → Ω → (Fin n → ℝ)}
    (h : ∀ k, Measurable (Function.uncurry (X k))) :
    Measurable (Function.uncurry (bieleckiLimit X)) :=
  measurable_pi_iff.mpr fun i =>
    Measurable.limsup fun k => (measurable_pi_apply i).comp (h k)
/-- Each coordinate of the limit path map is progressively measurable. -/
theorem progressivelyMeasurable_bieleckiLimit {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}
    {X : ℕ → ℝ → Ω → (Fin n → ℝ)}
    (h : ∀ k i, Probability.ProgressivelyMeasurable ℱ fun ω s => X k s ω i) (i : Fin n) :
    Probability.ProgressivelyMeasurable ℱ fun ω s => bieleckiLimit X s ω i :=
  Probability.ProgressivelyMeasurable.limsup fun k => h k i
/-- The pointwise difference of two jointly measurable path maps is jointly measurable. -/
theorem measurable_uncurry_sub {X Y : ℝ → Ω → (Fin n → ℝ)}
    (hX : Measurable (Function.uncurry X)) (hY : Measurable (Function.uncurry Y)) :
    Measurable (Function.uncurry fun t ω => fun i => X t ω i - Y t ω i) :=
  measurable_pi_iff.mpr fun i =>
    ((measurable_pi_apply i).comp hX).sub ((measurable_pi_apply i).comp hY)
/-- A path map that vanishes identically has zero Bielecki norm. -/
theorem bieleckiNorm_eq_zero (β T : ℝ) {Z : ℝ → Ω → (Fin n → ℝ)} (h : ∀ t ω i, Z t ω i = 0) :
    bieleckiNorm (P := P) β T Z = 0 := by
  unfold bieleckiNorm
  simp [h, ENNReal.zero_rpow_of_pos]
/-- The Bielecki norm of a difference across a block of steps is at most the sum of the norms of
the steps in the block. -/
theorem bieleckiNorm_sub_le_sum_Ico (β T : ℝ) {X : ℕ → ℝ → Ω → (Fin n → ℝ)}
    (hmeas : ∀ k, Measurable (Function.uncurry (X k))) {c : ℕ → ℝ≥0∞}
    (hstep : ∀ k, bieleckiNorm (P := P) β T (fun t ω i => X (k + 1) t ω i - X k t ω i) ≤ c k)
    (k m : ℕ) (hkm : k ≤ m) :
    bieleckiNorm (P := P) β T (fun t ω i => X m t ω i - X k t ω i)
      ≤ ∑ j ∈ Finset.Ico k m, c j := by
  induction m, hkm using Nat.le_induction with
  | base =>
    rw [Finset.Ico_self, Finset.sum_empty]
    exact le_of_eq (bieleckiNorm_eq_zero (P := P) β T fun _ _ _ => sub_self _)
  | succ m hm ih =>
    have hEq : (fun t ω i => X (m + 1) t ω i - X k t ω i)
        = fun t (ω : Ω) => (fun i => X (m + 1) t ω i - X m t ω i)
            + fun i => X m t ω i - X k t ω i := by
      funext t ω i
      simp [Pi.add_apply, sub_add_sub_cancel]
    have hadd := bieleckiNorm_add_le (P := P) β T
      (fun t ω => fun i => X (m + 1) t ω i - X m t ω i)
      (fun t ω => fun i => X m t ω i - X k t ω i)
      (fun t => bieleckiNorm_inner_aemeasurable _
        (measurable_uncurry_sub (hmeas (m + 1)) (hmeas m)) t)
      (fun t => bieleckiNorm_inner_aemeasurable _
        (measurable_uncurry_sub (hmeas m) (hmeas k)) t)
    rw [hEq, Finset.sum_Ico_succ_top hm]
    exact hadd.trans (by
      refine le_trans (add_le_add (hstep m) ih) (le_of_eq ?_)
      ring)
/-- On a probability measure the integral of a square root is at most the square root of the
integral. -/
theorem lintegral_rpow_half_le {f : Ω → ℝ≥0∞} (hf : AEMeasurable f P) :
    ∫⁻ ω, f ω ^ ((1 : ℝ) / 2) ∂P ≤ (∫⁻ ω, f ω ∂P) ^ ((1 : ℝ) / 2) := by
  have h2 : ∀ ω, (f ω ^ ((1 : ℝ) / 2)) ^ (2 : ℝ) = f ω := by
    intro ω
    rw [← ENNReal.rpow_mul]
    norm_num
  have h := ENNReal.lintegral_mul_le_Lp_mul_Lq P Real.HolderConjugate.two_two
    (f := fun ω => f ω ^ ((1 : ℝ) / 2)) (g := fun _ => (1 : ℝ≥0∞))
    (hf.pow_const _) aemeasurable_const
  simp only [Pi.mul_apply, mul_one, h2, ENNReal.one_rpow, lintegral_const, measure_univ] at h
  exact h
omit [IsProbabilityMeasure P] in
/-- A sequence of non-negative functions with summable integrals is almost surely summable. -/
theorem ae_tsum_ne_top {g : ℕ → Ω → ℝ≥0∞} (hgm : ∀ k, AEMeasurable (g k) P)
    {c : ℕ → ℝ≥0∞} (hb : ∀ k, ∫⁻ ω, g k ω ∂P ≤ c k) (hc : ∑' k, c k ≠ ⊤) :
    ∀ᵐ ω ∂P, ∑' k, g k ω ≠ ⊤ := by
  have hsum : ∫⁻ ω, ∑' k, g k ω ∂P ≤ ∑' k, c k := by
    rw [lintegral_tsum hgm]
    exact ENNReal.tsum_le_tsum hb
  exact (ae_lt_top' (AEMeasurable.tsum hgm)
    (ne_top_of_le_ne_top hc hsum)).mono fun _ h => h.ne
/-- The `ω`-slice of the squared Euclidean norm of a jointly measurable path map is
measurable. -/
theorem measurable_sq_slice {Z : ℝ → Ω → (Fin n → ℝ)} (hZ : Measurable (Function.uncurry Z))
    (t : ℝ) : Measurable fun ω => ∑ i, (‖Z t ω i‖₊ : ℝ≥0∞) ^ 2 := by
  have hs : Measurable fun ω => Z t ω := Measurable.of_uncurry_left hZ
  exact Finset.measurable_sum _ fun i _ =>
    (ENNReal.continuous_coe.measurable.comp (((measurable_pi_apply i).comp hs).nnnorm)).pow_const 2
/-- A single coordinate is dominated by the Euclidean norm of the whole vector. -/
theorem coe_nnnorm_le_rpow_sum {a : Fin n → ℝ} (i : Fin n) :
    (‖a i‖₊ : ℝ≥0∞) ≤ (∑ j, (‖a j‖₊ : ℝ≥0∞) ^ 2) ^ ((1 : ℝ) / 2) := by
  have hle : ((‖a i‖₊ : ℝ≥0∞)) ^ 2 ≤ ∑ j, (‖a j‖₊ : ℝ≥0∞) ^ 2 :=
    Finset.single_le_sum (f := fun j => (‖a j‖₊ : ℝ≥0∞) ^ 2) (fun _ _ => zero_le)
      (Finset.mem_univ i)
  refine le_trans (le_of_eq ?_) (ENNReal.rpow_le_rpow hle (by norm_num : (0 : ℝ) ≤ (1 : ℝ) / 2))
  rw [← ENNReal.rpow_natCast _ 2, ← ENNReal.rpow_mul]
  norm_num
/-- The `L²` slice norm of a Bielecki step at a time of the window. -/
theorem lintegral_step_rpow_le (β T : ℝ) {X : ℕ → ℝ → Ω → (Fin n → ℝ)}
    (hmeas : ∀ k, Measurable (Function.uncurry (X k))) {c : ℕ → ℝ≥0∞}
    (hstep : ∀ k, bieleckiNorm (P := P) β T (fun t ω i => X (k + 1) t ω i - X k t ω i) ≤ c k)
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) T) (k : ℕ) :
    ∫⁻ ω, (∑ i, (‖X (k + 1) t ω i - X k t ω i‖₊ : ℝ≥0∞) ^ 2) ^ ((1 : ℝ) / 2) ∂P
      ≤ ENNReal.ofReal (Real.exp (β * t)) * c k := by
  refine (lintegral_rpow_half_le (P := P)
    (f := fun ω => ∑ i, (‖X (k + 1) t ω i - X k t ω i‖₊ : ℝ≥0∞) ^ 2)
    (measurable_sq_slice (measurable_uncurry_sub (hmeas (k + 1)) (hmeas k)) t).aemeasurable).trans
    ?_
  exact (lintegral_sq_rpow_le_of_bieleckiNorm (P := P) β T
    (fun t ω i => X (k + 1) t ω i - X k t ω i) ht).trans (mul_le_mul' le_rfl (hstep k))
/-- At every time of the window, summable Bielecki steps make the increments almost surely
absolutely summable in every coordinate. -/
theorem ae_summable_steps (β T : ℝ) {X : ℕ → ℝ → Ω → (Fin n → ℝ)}
    (hmeas : ∀ k, Measurable (Function.uncurry (X k))) {c : ℕ → ℝ≥0∞}
    (hstep : ∀ k, bieleckiNorm (P := P) β T (fun t ω i => X (k + 1) t ω i - X k t ω i) ≤ c k)
    (hc : ∑' k, c k ≠ ⊤) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) T) :
    ∀ᵐ ω ∂P, ∀ i, Summable fun k => ‖X (k + 1) t ω i - X k t ω i‖ := by
  have hgm : ∀ k, AEMeasurable
      (fun ω => (∑ i, (‖X (k + 1) t ω i - X k t ω i‖₊ : ℝ≥0∞) ^ 2) ^ ((1 : ℝ) / 2)) P :=
    fun k => bieleckiNorm_inner_aemeasurable _
      (measurable_uncurry_sub (hmeas (k + 1)) (hmeas k)) t
  have hctop : ∑' k, ENNReal.ofReal (Real.exp (β * t)) * c k ≠ ⊤ := by
    rw [ENNReal.tsum_mul_left]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top hc
  have hae := ae_tsum_ne_top (P := P) hgm
    (fun k => lintegral_step_rpow_le (P := P) β T hmeas hstep ht k) hctop
  filter_upwards [hae] with ω hω i
  have hle : ∑' k, ((‖X (k + 1) t ω i - X k t ω i‖₊ : ℝ≥0) : ℝ≥0∞)
      ≤ ∑' k, (∑ j, (‖X (k + 1) t ω j - X k t ω j‖₊ : ℝ≥0∞) ^ 2) ^ ((1 : ℝ) / 2) :=
    ENNReal.tsum_le_tsum fun k =>
      coe_nnnorm_le_rpow_sum (a := fun j => X (k + 1) t ω j - X k t ω j) i
  exact NNReal.summable_coe.mpr
    (ENNReal.tsum_coe_ne_top_iff_summable.mp (ne_top_of_le_ne_top hω hle))
/-- At every time of the window the sequence converges almost surely to the limit path map. -/
theorem ae_tendsto_bieleckiLimit (β T : ℝ) {X : ℕ → ℝ → Ω → (Fin n → ℝ)}
    (hmeas : ∀ k, Measurable (Function.uncurry (X k))) {c : ℕ → ℝ≥0∞}
    (hstep : ∀ k, bieleckiNorm (P := P) β T (fun t ω i => X (k + 1) t ω i - X k t ω i) ≤ c k)
    (hc : ∑' k, c k ≠ ⊤) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) T) :
    ∀ᵐ ω ∂P, ∀ i, Filter.Tendsto (fun k => X k t ω i) Filter.atTop
      (nhds (bieleckiLimit X t ω i)) := by
  filter_upwards [ae_summable_steps (P := P) β T hmeas hstep hc ht] with ω hω i
  have hs : Summable fun k => X (k + 1) t ω i - X k t ω i := Summable.of_norm (hω i)
  have htel : ∀ m, ∑ k ∈ Finset.range m, (X (k + 1) t ω i - X k t ω i)
      = X m t ω i - X 0 t ω i := fun m => Finset.sum_range_sub (fun k => X k t ω i) m
  have hpart : Filter.Tendsto (fun m => X m t ω i - X 0 t ω i) Filter.atTop
      (nhds (∑' k, (X (k + 1) t ω i - X k t ω i))) := by
    have := hs.hasSum.tendsto_sum_nat
    simpa only [htel] using this
  have hL : Filter.Tendsto (fun m => X m t ω i) Filter.atTop
      (nhds ((∑' k, (X (k + 1) t ω i - X k t ω i)) + X 0 t ω i)) := by
    simpa only [sub_add_cancel] using hpart.add_const (X 0 t ω i)
  have hlim : bieleckiLimit X t ω i = (∑' k, (X (k + 1) t ω i - X k t ω i)) + X 0 t ω i :=
    hL.limsup_eq
  rw [hlim]
  exact hL
/-- A finite block of steps is dominated by the tail of the step bounds. -/
theorem sum_Ico_le_tsum_shift {c : ℕ → ℝ≥0∞} (k m : ℕ) :
    ∑ j ∈ Finset.Ico k m, c j ≤ ∑' j, c (k + j) := by
  rw [Finset.sum_Ico_eq_sum_range]
  exact ENNReal.sum_le_tsum _
/-- At every time of the window the weighted `L²` distance to the limit is bounded by the tail of
the step bounds. -/
theorem lintegral_sq_sub_bieleckiLimit_rpow_le (β T : ℝ) {X : ℕ → ℝ → Ω → (Fin n → ℝ)}
    (hmeas : ∀ k, Measurable (Function.uncurry (X k))) {c : ℕ → ℝ≥0∞}
    (hstep : ∀ k, bieleckiNorm (P := P) β T (fun t ω i => X (k + 1) t ω i - X k t ω i) ≤ c k)
    (hc : ∑' k, c k ≠ ⊤) (k : ℕ) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) T) :
    (∫⁻ ω, ∑ i, (‖X k t ω i - bieleckiLimit X t ω i‖₊ : ℝ≥0∞) ^ 2 ∂P) ^ ((1 : ℝ) / 2)
      ≤ ENNReal.ofReal (Real.exp (β * t)) * ∑' j, c (k + j) := by
  set B : ℝ≥0∞ := ENNReal.ofReal (Real.exp (β * t)) * ∑' j, c (k + j) with hB
  have hFm : ∀ m, Measurable fun ω => ∑ i, (‖X k t ω i - X m t ω i‖₊ : ℝ≥0∞) ^ 2 := fun m =>
    measurable_sq_slice (measurable_uncurry_sub (hmeas k) (hmeas m)) t
  -- Fatou against the almost sure limit.
  have hae : ∀ᵐ ω ∂P, Filter.liminf
      (fun m => ∑ i, (‖X k t ω i - X m t ω i‖₊ : ℝ≥0∞) ^ 2) Filter.atTop
      = ∑ i, (‖X k t ω i - bieleckiLimit X t ω i‖₊ : ℝ≥0∞) ^ 2 := by
    filter_upwards [ae_tendsto_bieleckiLimit (P := P) β T hmeas hstep hc ht] with ω hω
    refine Filter.Tendsto.liminf_eq ?_
    refine tendsto_finsetSum _ fun i _ => ?_
    have hnn : Filter.Tendsto (fun m => (‖X k t ω i - X m t ω i‖₊ : ℝ≥0) ^ 2) Filter.atTop
        (nhds ((‖X k t ω i - bieleckiLimit X t ω i‖₊ : ℝ≥0) ^ 2)) :=
      (Filter.Tendsto.const_sub (X k t ω i) (hω i)).nnnorm.pow 2
    simpa only [Function.comp_def, ENNReal.coe_pow] using
      (ENNReal.continuous_coe.tendsto _).comp hnn
  have hfatou : ∫⁻ ω, ∑ i, (‖X k t ω i - bieleckiLimit X t ω i‖₊ : ℝ≥0∞) ^ 2 ∂P
      ≤ Filter.liminf
        (fun m => ∫⁻ ω, ∑ i, (‖X k t ω i - X m t ω i‖₊ : ℝ≥0∞) ^ 2 ∂P) Filter.atTop := by
    calc ∫⁻ ω, ∑ i, (‖X k t ω i - bieleckiLimit X t ω i‖₊ : ℝ≥0∞) ^ 2 ∂P
        = ∫⁻ ω, Filter.liminf
            (fun m => ∑ i, (‖X k t ω i - X m t ω i‖₊ : ℝ≥0∞) ^ 2) Filter.atTop ∂P :=
          (lintegral_congr_ae (hae.mono fun _ h => h)).symm
      _ ≤ _ := lintegral_liminf_le hFm
  -- Each term of the sequence is bounded by `B ^ 2`, eventually.
  have hev : ∀ᶠ m in Filter.atTop,
      ∫⁻ ω, ∑ i, (‖X k t ω i - X m t ω i‖₊ : ℝ≥0∞) ^ 2 ∂P ≤ B ^ (2 : ℕ) := by
    filter_upwards [Filter.eventually_ge_atTop k] with m hm
    have hrev : (fun ω => ∑ i, (‖X k t ω i - X m t ω i‖₊ : ℝ≥0∞) ^ 2)
        = fun ω => ∑ i, (‖X m t ω i - X k t ω i‖₊ : ℝ≥0∞) ^ 2 := by
      funext ω
      exact Finset.sum_congr rfl fun i _ => by
        rw [show X k t ω i - X m t ω i = -(X m t ω i - X k t ω i) by ring, nnnorm_neg]
    have hb : bieleckiNorm (P := P) β T (fun t ω i => X m t ω i - X k t ω i)
        ≤ ∑' j, c (k + j) :=
      (bieleckiNorm_sub_le_sum_Ico (P := P) β T hmeas hstep k m hm).trans
        (sum_Ico_le_tsum_shift k m)
    have hhalf : (∫⁻ ω, ∑ i, (‖X m t ω i - X k t ω i‖₊ : ℝ≥0∞) ^ 2 ∂P) ^ ((1 : ℝ) / 2) ≤ B :=
      (lintegral_sq_rpow_le_of_bieleckiNorm (P := P) β T
        (fun t ω i => X m t ω i - X k t ω i) ht).trans (mul_le_mul' le_rfl hb)
    rw [hrev]
    calc ∫⁻ ω, ∑ i, (‖X m t ω i - X k t ω i‖₊ : ℝ≥0∞) ^ 2 ∂P
        = ((∫⁻ ω, ∑ i, (‖X m t ω i - X k t ω i‖₊ : ℝ≥0∞) ^ 2 ∂P) ^ ((1 : ℝ) / 2)) ^ (2 : ℕ) := by
          rw [← ENNReal.rpow_natCast _ 2, ← ENNReal.rpow_mul]
          norm_num
      _ ≤ B ^ (2 : ℕ) := pow_le_pow_left' hhalf 2
  have hsq : ∫⁻ ω, ∑ i, (‖X k t ω i - bieleckiLimit X t ω i‖₊ : ℝ≥0∞) ^ 2 ∂P ≤ B ^ (2 : ℕ) :=
    hfatou.trans (Filter.liminf_le_of_frequently_le hev.frequently)
  calc (∫⁻ ω, ∑ i, (‖X k t ω i - bieleckiLimit X t ω i‖₊ : ℝ≥0∞) ^ 2 ∂P) ^ ((1 : ℝ) / 2)
      ≤ (B ^ (2 : ℕ)) ^ ((1 : ℝ) / 2) := ENNReal.rpow_le_rpow hsq (by norm_num)
    _ = B := by
        rw [← ENNReal.rpow_natCast B 2, ← ENNReal.rpow_mul]
        norm_num
/-- **The Bielecki limit.** A sequence of jointly measurable path maps whose consecutive Bielecki
differences are summable converges in Bielecki norm to `bieleckiLimit X`, at the rate given by the
tail of the step bounds. -/
theorem bieleckiNorm_sub_bieleckiLimit_le (β T : ℝ) {X : ℕ → ℝ → Ω → (Fin n → ℝ)}
    (hmeas : ∀ k, Measurable (Function.uncurry (X k))) {c : ℕ → ℝ≥0∞}
    (hstep : ∀ k, bieleckiNorm (P := P) β T (fun t ω i => X (k + 1) t ω i - X k t ω i) ≤ c k)
    (hc : ∑' k, c k ≠ ⊤) (k : ℕ) :
    bieleckiNorm (P := P) β T (fun t ω i => X k t ω i - bieleckiLimit X t ω i)
      ≤ ∑' j, c (k + j) :=
  bieleckiNorm_le_of_perTime_rpow (P := P) β T _ _ fun _t ht =>
    lintegral_sq_sub_bieleckiLimit_rpow_le (P := P) β T hmeas hstep hc k ht
/-- The tail of a geometric series of `ℝ≥0∞` step bounds. -/
theorem tsum_geometric_shift {q C : ℝ≥0∞} (k : ℕ) :
    ∑' j, q ^ (k + j) * C = q ^ k * ((1 - q)⁻¹ * C) := by
  calc ∑' j, q ^ (k + j) * C = ∑' j, q ^ k * (q ^ j * C) := by
        refine tsum_congr fun j => ?_
        rw [pow_add, mul_assoc]
    _ = q ^ k * ∑' j, q ^ j * C := ENNReal.tsum_mul_left
    _ = q ^ k * ((1 - q)⁻¹ * C) := by rw [ENNReal.tsum_mul_right, ENNReal.tsum_geometric]
/-- **The Bielecki limit of a geometrically Cauchy sequence.** If the consecutive Bielecki
differences decay geometrically at a rate `< 1`, the sequence converges to `bieleckiLimit` at that
rate. -/
theorem bieleckiNorm_sub_bieleckiLimit_geometric (β T : ℝ) {X : ℕ → ℝ → Ω → (Fin n → ℝ)}
    (hmeas : ∀ k, Measurable (Function.uncurry (X k))) {q C : ℝ≥0∞}
    (hstep : ∀ k, bieleckiNorm (P := P) β T (fun t ω i => X (k + 1) t ω i - X k t ω i)
      ≤ q ^ k * C) (hq : q < 1) (hC : C ≠ ⊤) (k : ℕ) :
    bieleckiNorm (P := P) β T (fun t ω i => X k t ω i - bieleckiLimit X t ω i)
      ≤ q ^ k * ((1 - q)⁻¹ * C) := by
  have hsub : (1 : ℝ≥0∞) - q ≠ 0 := (tsub_pos_of_lt hq).ne'
  have hc : ∑' k, q ^ k * C ≠ ⊤ := by
    rw [ENNReal.tsum_mul_right, ENNReal.tsum_geometric]
    exact ENNReal.mul_ne_top (ENNReal.inv_ne_top.mpr hsub) hC
  refine le_trans (bieleckiNorm_sub_bieleckiLimit_le (P := P) β T hmeas hstep hc k)
    (le_of_eq (tsum_geometric_shift k))
end Picard
end Ito
end LevyStochCalc


