-- Prove2me | Definitions.Def_KLS408915f_LevyStochCalc_Ito_PicardIntegrandBounds
-- name    : KLS408915f_LevyStochCalc_Ito_PicardIntegrandBounds
-- status  : Definition
-- author  : @Lazyfill
-- created : 2026-10-23T10:00:16.492295+00:00
-- url     : https://prove2.me/theorems/1465c9ad-c1d7-4169-a658-e7adb5f1c560
-- title:
--   Energy and measurability bounds for Picard integrands
-- statement:
--   Vendored from the LevyStochCalc library (https://github.com/cgarryZA/LevyStochCalc). The bundle records norm-square identities, coordinate-to-vector inequalities, and linear-growth estimates for $\mu$, $\sigma$, and $\gamma$ obtained from `IsLipschitz` by comparison with the zero state. If a jointly measurable state process has finite integrated coordinate-square energy on every finite horizon, then each drift, diffusion, and jump integrand along that process has finite $[0,\infty]$-valued squared energy on every positive horizon. It also proves that joint and progressive measurability are preserved when these coefficient functions are composed with a state process.
-- source:
--   Lean source: https://github.com/cgarryZA/LevyStochCalc/blob/984dbf0b790031eac05d56fe5a84b65e15e1e932/LevyStochCalc/Ito/PicardIntegrandBounds.lean#L30-L542 (repository human-ai-mathematics/kls-lean, commit 408915f, module `LevyStochCalc.Ito.PicardIntegrandBounds`, definition bundle `KLS408915f_LevyStochCalc_Ito_PicardIntegrandBounds`; the repository is private at upload time). Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (Apache-2.0; upstream copyright notice retained in the Lean text).

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
import Mathlib.Topology.MetricSpace.Bounded
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

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Ito/PicardIntegrandBounds.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
namespace LevyStochCalc
namespace Ito
namespace Picard
universe u v
variable {Ω : Type u} [MeasurableSpace Ω]
variable {E : Type v} [MeasurableSpace E]
/-- The squared extended norm as an extended real. -/
theorem sq_coe_nnnorm {α : Type*} [SeminormedAddGroup α] (v : α) :
    ((‖v‖₊ : ℝ≥0∞)) ^ 2 = ENNReal.ofReal (‖v‖ ^ 2) := by
  have h1 : (‖v‖₊ : ℝ≥0∞) = ENNReal.ofReal ‖v‖ := by
    rw [ENNReal.ofReal_eq_coe_nnreal (norm_nonneg _)]
    exact congrArg _ (NNReal.eq rfl)
  rw [h1, ← ENNReal.ofReal_pow (norm_nonneg _)]
/-- The squared extended norm of a real number as an extended real. -/
theorem sq_coe_nnnorm_real (x : ℝ) : ((‖x‖₊ : ℝ≥0∞)) ^ 2 = ENNReal.ofReal (x ^ 2) := by
  rw [sq_coe_nnnorm, Real.norm_eq_abs, ← abs_pow,
    abs_of_nonneg (by positivity : (0 : ℝ) ≤ x ^ 2)]
/-- The supremum norm on `Fin n → ℝ` is dominated by the Euclidean sum of squares. -/
theorem sq_norm_le_sum_sq {n : ℕ} (x : Fin n → ℝ) : ‖x‖ ^ 2 ≤ ∑ i, (x i) ^ 2 := by
  have hnn : (0 : ℝ) ≤ ∑ i, (x i) ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hb : ‖x‖ ≤ Real.sqrt (∑ i, (x i) ^ 2) := by
    refine (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).mpr fun i => ?_
    rw [Real.norm_eq_abs, ← Real.sqrt_sq_eq_abs]
    exact Real.sqrt_le_sqrt
      (Finset.single_le_sum (fun k _ => sq_nonneg (x k)) (Finset.mem_univ i))
  calc ‖x‖ ^ 2 ≤ (Real.sqrt (∑ i, (x i) ^ 2)) ^ 2 := by
        nlinarith [norm_nonneg x, Real.sqrt_nonneg (∑ i, (x i) ^ 2)]
    _ = ∑ i, (x i) ^ 2 := Real.sq_sqrt hnn
/-- **Linear growth of the diffusion coefficient in the state**, read off the Lipschitz
hypothesis by comparing with the state `0`. -/
theorem sq_sigma_le {n d : ℕ} {ν : MeasureTheory.Measure E}
    (coeffs : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs n d E) {L : ℝ}
    (hLip : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs.IsLipschitz coeffs ν L)
    (s : ℝ) (x : Fin n → ℝ) (i : Fin n) (j : Fin d) :
    (coeffs.σ s x i j) ^ 2
      ≤ 2 * (coeffs.σ s 0 i j) ^ 2 + 2 * (L ^ 2 * ∑ i', (x i') ^ 2) := by
  have hsum := hLip.2.2.1 s x 0
  have hinner : (coeffs.σ s x i j - coeffs.σ s 0 i j) ^ 2
      ≤ ∑ j', (coeffs.σ s x i j' - coeffs.σ s 0 i j') ^ 2 :=
    Finset.single_le_sum (f := fun j' => (coeffs.σ s x i j' - coeffs.σ s 0 i j') ^ 2)
      (fun _ _ => sq_nonneg _) (Finset.mem_univ j)
  have houter : (∑ j', (coeffs.σ s x i j' - coeffs.σ s 0 i j') ^ 2)
      ≤ ∑ i', ∑ j', (coeffs.σ s x i' j' - coeffs.σ s 0 i' j') ^ 2 :=
    Finset.single_le_sum
      (f := fun i' => ∑ j', (coeffs.σ s x i' j' - coeffs.σ s 0 i' j') ^ 2)
      (fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _) (Finset.mem_univ i)
  have hx : ‖x - 0‖ ^ 2 ≤ ∑ i', (x i') ^ 2 := by
    rw [sub_zero]
    exact sq_norm_le_sum_sq x
  have hmul : L ^ 2 * ‖x - 0‖ ^ 2 ≤ L ^ 2 * ∑ i', (x i') ^ 2 :=
    mul_le_mul_of_nonneg_left hx (sq_nonneg L)
  have hAM : (coeffs.σ s x i j) ^ 2
      ≤ 2 * (coeffs.σ s x i j - coeffs.σ s 0 i j) ^ 2 + 2 * (coeffs.σ s 0 i j) ^ 2 := by
    nlinarith [sq_nonneg (coeffs.σ s x i j - 2 * coeffs.σ s 0 i j)]
  linarith [(hinner.trans houter).trans (hsum.trans hmul)]
/-- **The frozen process is square integrable over every horizon**, with the Bielecki norm on
`[0, T]` as the constant. -/
theorem lintegral_lintegral_sq_stop_le {n : ℕ} {P : MeasureTheory.Measure Ω}
    [MeasureTheory.IsProbabilityMeasure P]
    {ℱ : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›} {T : ℝ}
    (Y : SBoundedProcess (n := n) P ℱ T) (hT : 0 ≤ T) (T' : ℝ) :
    ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T',
        ∑ i, (‖Y.stop.X s ω i‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P
      ≤ ENNReal.ofReal T' * (bieleckiNorm (P := P) 0 T Y.X) ^ (2 : ℕ) := by
  have hXi : ∀ i : Fin n, Measurable fun p : Ω × ℝ => Y.stop.X p.2 p.1 i := fun i =>
    (measurable_pi_apply i).comp
      (Y.stop.measurable_path.comp (measurable_snd.prodMk measurable_fst))
  have hjoint : Measurable (Function.uncurry fun (ω : Ω) (s : ℝ) =>
      ∑ i, (‖Y.stop.X s ω i‖₊ : ℝ≥0∞) ^ 2) :=
    Finset.measurable_sum _ fun i _ => ((hXi i).nnnorm.coe_nnreal_ennreal).pow_const 2
  rw [MeasureTheory.lintegral_lintegral_swap (μ := P)
    (ν := volume.restrict (Set.Icc (0 : ℝ) T'))
    (f := fun (ω : Ω) (s : ℝ) => ∑ i, (‖Y.stop.X s ω i‖₊ : ℝ≥0∞) ^ 2) hjoint.aemeasurable]
  calc ∫⁻ s in Set.Icc (0 : ℝ) T',
        (∫⁻ ω, ∑ i, (‖Y.stop.X s ω i‖₊ : ℝ≥0∞) ^ 2 ∂P) ∂volume
      ≤ ∫⁻ _s in Set.Icc (0 : ℝ) T',
          (bieleckiNorm (P := P) 0 T Y.X) ^ (2 : ℕ) ∂volume :=
        MeasureTheory.setLIntegral_mono' measurableSet_Icc
          (fun s hs => Y.lintegral_sq_stop_le hT hs.1)
    _ = (bieleckiNorm (P := P) 0 T Y.X) ^ (2 : ℕ) * volume (Set.Icc (0 : ℝ) T') :=
        MeasureTheory.setLIntegral_const _ _
    _ = ENNReal.ofReal T' * (bieleckiNorm (P := P) 0 T Y.X) ^ (2 : ℕ) := by
        rw [Real.volume_Icc, sub_zero, mul_comm]
/-- **The diffusion integrand along a state process of finite energy is square integrable at
every horizon.** This is the hypothesis `picardStep` asks for. -/
theorem lintegral_sq_sigma_lt_top_of_energy {n d : ℕ} {P : MeasureTheory.Measure Ω}
    [MeasureTheory.IsProbabilityMeasure P] {ν : MeasureTheory.Measure E}
    (coeffs : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs n d E)
    (hReg : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs.IsRegular coeffs ν)
    {L : ℝ} (hLip : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs.IsLipschitz coeffs ν L)
    {Z : ℝ → Ω → (Fin n → ℝ)} (hZm : Measurable (Function.uncurry Z))
    (hZsq : ∀ b : ℝ, ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) b,
      ∑ i', (‖Z s ω i'‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    (i : Fin n) (j : Fin d) {T' : ℝ} (hT' : 0 < T') :
    ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T',
      (‖coeffs.σ s (Z s ω) i j‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤ := by
  have key : ∀ x : ℝ, ((‖x‖₊ : ℝ≥0∞)) ^ 2 = ENNReal.ofReal (x ^ 2) := sq_coe_nnnorm_real
  -- the pointwise linear-growth bound, in extended form
  have hpt : ∀ (ω : Ω) (s : ℝ),
      (‖coeffs.σ s (Z s ω) i j‖₊ : ℝ≥0∞) ^ 2
        ≤ 2 * (‖coeffs.σ s 0 i j‖₊ : ℝ≥0∞) ^ 2
          + ENNReal.ofReal (2 * L ^ 2) * ∑ i', (‖Z s ω i'‖₊ : ℝ≥0∞) ^ 2 := by
    intro ω s
    have h1 : ENNReal.ofReal (2 * (coeffs.σ s 0 i j) ^ 2)
        = 2 * (‖coeffs.σ s 0 i j‖₊ : ℝ≥0∞) ^ 2 := by
      rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2), key, ENNReal.ofReal_ofNat]
    have h2 : ENNReal.ofReal (2 * (L ^ 2 * ∑ i', (Z s ω i') ^ 2))
        = ENNReal.ofReal (2 * L ^ 2) * ∑ i', (‖Z s ω i'‖₊ : ℝ≥0∞) ^ 2 := by
      rw [show 2 * (L ^ 2 * ∑ i', (Z s ω i') ^ 2)
          = (2 * L ^ 2) * ∑ i', (Z s ω i') ^ 2 by ring,
        ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ 2 * L ^ 2),
        ENNReal.ofReal_sum_of_nonneg (fun _ _ => sq_nonneg _)]
      exact congrArg _ (Finset.sum_congr rfl fun i' _ => (key _).symm)
    calc (‖coeffs.σ s (Z s ω) i j‖₊ : ℝ≥0∞) ^ 2
        = ENNReal.ofReal ((coeffs.σ s (Z s ω) i j) ^ 2) := key _
      _ ≤ ENNReal.ofReal (2 * (coeffs.σ s 0 i j) ^ 2
            + 2 * (L ^ 2 * ∑ i', (Z s ω i') ^ 2)) :=
          ENNReal.ofReal_le_ofReal (sq_sigma_le coeffs hLip s _ i j)
      _ = 2 * (‖coeffs.σ s 0 i j‖₊ : ℝ≥0∞) ^ 2
            + ENNReal.ofReal (2 * L ^ 2) * ∑ i', (‖Z s ω i'‖₊ : ℝ≥0∞) ^ 2 := by
          rw [ENNReal.ofReal_add (by positivity) (by positivity), h1, h2]
  refine lt_of_le_of_lt (lintegral_mono fun ω => lintegral_mono fun s => hpt ω s) ?_
  -- measurability of the two pieces
  have hσ0 : Measurable fun s : ℝ => (‖coeffs.σ s 0 i j‖₊ : ℝ≥0∞) ^ 2 := by
    have : Measurable fun s : ℝ => coeffs.σ s 0 i j :=
      ((measurable_pi_apply j).comp ((measurable_pi_apply i).comp
        (hReg.2.1.comp (measurable_id.prodMk measurable_const))))
    exact (this.nnnorm.coe_nnreal_ennreal).pow_const 2
  have hXi : ∀ i' : Fin n, Measurable fun p : Ω × ℝ => Z p.2 p.1 i' := fun i' =>
    (measurable_pi_apply i').comp
      (hZm.comp (measurable_snd.prodMk measurable_fst))
  have hBjoint : Measurable (Function.uncurry fun (ω : Ω) (s : ℝ) =>
      ENNReal.ofReal (2 * L ^ 2) * ∑ i', (‖Z s ω i'‖₊ : ℝ≥0∞) ^ 2) :=
    (Finset.measurable_sum _ fun i' _ =>
      ((hXi i').nnnorm.coe_nnreal_ennreal).pow_const 2).const_mul _
  -- split the sum
  have hinner : ∀ ω : Ω, ∫⁻ s in Set.Icc (0 : ℝ) T',
        (2 * (‖coeffs.σ s 0 i j‖₊ : ℝ≥0∞) ^ 2
          + ENNReal.ofReal (2 * L ^ 2) * ∑ i', (‖Z s ω i'‖₊ : ℝ≥0∞) ^ 2) ∂volume
      = (∫⁻ s in Set.Icc (0 : ℝ) T', 2 * (‖coeffs.σ s 0 i j‖₊ : ℝ≥0∞) ^ 2 ∂volume)
        + ∫⁻ s in Set.Icc (0 : ℝ) T',
            ENNReal.ofReal (2 * L ^ 2) * ∑ i', (‖Z s ω i'‖₊ : ℝ≥0∞) ^ 2 ∂volume :=
    fun ω => MeasureTheory.lintegral_add_left (hσ0.const_mul 2) _
  rw [lintegral_congr hinner,
    MeasureTheory.lintegral_add_left measurable_const _]
  refine ENNReal.add_lt_top.mpr ⟨?_, ?_⟩
  · -- the state-zero term: constant in `ω`, finite by `IsRegular`
    rw [MeasureTheory.lintegral_const, measure_univ, mul_one,
      MeasureTheory.lintegral_const_mul' _ _ (by simp : (2 : ℝ≥0∞) ≠ ⊤)]
    refine ENNReal.mul_lt_top (by simp) ?_
    refine lt_of_le_of_lt (MeasureTheory.setLIntegral_mono' measurableSet_Icc
      fun s _ => ?_) (hReg.2.2.2.2.1 T' hT')
    refine le_trans ?_ (Finset.single_le_sum
      (f := fun i' => ∑ j', (‖coeffs.σ s 0 i' j'‖₊ : ℝ≥0∞) ^ 2)
      (fun _ _ => by simp) (Finset.mem_univ i))
    exact Finset.single_le_sum (f := fun j' => (‖coeffs.σ s 0 i j'‖₊ : ℝ≥0∞) ^ 2)
      (fun _ _ => by simp) (Finset.mem_univ j)
  · -- the state term: the frozen process's horizon bound
    have hconst : ∀ ω : Ω, ∫⁻ s in Set.Icc (0 : ℝ) T',
          ENNReal.ofReal (2 * L ^ 2) * ∑ i', (‖Z s ω i'‖₊ : ℝ≥0∞) ^ 2 ∂volume
        = ENNReal.ofReal (2 * L ^ 2) * ∫⁻ s in Set.Icc (0 : ℝ) T',
            ∑ i', (‖Z s ω i'‖₊ : ℝ≥0∞) ^ 2 ∂volume :=
      fun ω => MeasureTheory.lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    rw [lintegral_congr hconst,
      MeasureTheory.lintegral_const_mul' _ _
        (ENNReal.ofReal_ne_top : ENNReal.ofReal (2 * L ^ 2) ≠ ⊤)]
    refine ENNReal.mul_lt_top ENNReal.ofReal_lt_top ?_
    exact hZsq T'
/-- **The diffusion integrand along the frozen process is square integrable at every horizon.**
This is the hypothesis `picardStep` asks for and that `sup_L2` alone cannot supply. -/
theorem lintegral_sq_sigma_stop_lt_top {n d : ℕ} {P : MeasureTheory.Measure Ω}
    [MeasureTheory.IsProbabilityMeasure P] {ν : MeasureTheory.Measure E}
    {ℱ : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›} {T : ℝ}
    (coeffs : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs n d E)
    (hReg : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs.IsRegular coeffs ν)
    {L : ℝ} (hLip : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs.IsLipschitz coeffs ν L)
    (Y : SBoundedProcess (n := n) P ℱ T) (hT : 0 ≤ T)
    (i : Fin n) (j : Fin d) {T' : ℝ} (hT' : 0 < T') :
    ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T',
      (‖coeffs.σ s (Y.stop.X s ω) i j‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤ :=
  lintegral_sq_sigma_lt_top_of_energy coeffs hReg hLip Y.stop.measurable_path
    (fun b => lt_of_le_of_lt (lintegral_lintegral_sq_stop_le Y hT b)
      (ENNReal.mul_lt_top ENNReal.ofReal_lt_top (ENNReal.pow_lt_top Y.sup_L2))) i j hT'
/-- The Euclidean sum of squares dominates the squared supremum norm, as extended reals. -/
theorem ofReal_sq_norm_le_sum {n : ℕ} (x : Fin n → ℝ) :
    ENNReal.ofReal (‖x‖ ^ 2) ≤ ∑ i, (‖x i‖₊ : ℝ≥0∞) ^ 2 := by
  refine (ENNReal.ofReal_le_ofReal (sq_norm_le_sum_sq x)).trans ?_
  rw [ENNReal.ofReal_sum_of_nonneg (fun _ _ => sq_nonneg _)]
  exact le_of_eq (Finset.sum_congr rfl fun i _ => (sq_coe_nnnorm_real (x i)).symm)
/-- **Linear growth of the jump coefficient in the state**, in the `L²`-in-mark sense, read off
the Lipschitz hypothesis by comparing with the state `0`. -/
theorem lintegral_sq_gamma_le {n d : ℕ} {ν : MeasureTheory.Measure E}
    (coeffs : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs n d E)
    (hReg : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs.IsRegular coeffs ν) {L : ℝ}
    (hLip : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs.IsLipschitz coeffs ν L)
    (s : ℝ) (x : Fin n → ℝ) (i : Fin n) :
    ∫⁻ e, (‖coeffs.γ s x e i‖₊ : ℝ≥0∞) ^ 2 ∂ν
      ≤ 2 * (∫⁻ e, (‖coeffs.γ s 0 e‖₊ : ℝ≥0∞) ^ 2 ∂ν)
        + ENNReal.ofReal (2 * L ^ 2) * ∑ i', (‖x i'‖₊ : ℝ≥0∞) ^ 2 := by
  have hγ0 : Measurable fun e : E => (‖coeffs.γ s 0 e‖₊ : ℝ≥0∞) ^ 2 := by
    have : Measurable fun e : E => coeffs.γ s 0 e :=
      hReg.2.2.1.comp (measurable_const.prodMk (measurable_const.prodMk measurable_id))
    exact (this.nnnorm.coe_nnreal_ennreal).pow_const 2
  -- pointwise: split off the value at the state `0`
  have hpt : ∀ e : E, (‖coeffs.γ s x e i‖₊ : ℝ≥0∞) ^ 2
      ≤ 2 * (‖coeffs.γ s 0 e‖₊ : ℝ≥0∞) ^ 2
        + 2 * (‖coeffs.γ s x e - coeffs.γ s 0 e‖₊ : ℝ≥0∞) ^ 2 := by
    intro e
    have hb : |coeffs.γ s 0 e i| ≤ ‖coeffs.γ s 0 e‖ := by
      simpa [Real.norm_eq_abs] using norm_le_pi_norm (coeffs.γ s 0 e) i
    have hd : |coeffs.γ s x e i - coeffs.γ s 0 e i|
        ≤ ‖coeffs.γ s x e - coeffs.γ s 0 e‖ := by
      simpa [Real.norm_eq_abs, Pi.sub_apply]
        using norm_le_pi_norm (coeffs.γ s x e - coeffs.γ s 0 e) i
    have hreal : (coeffs.γ s x e i) ^ 2
        ≤ 2 * ‖coeffs.γ s 0 e‖ ^ 2 + 2 * ‖coeffs.γ s x e - coeffs.γ s 0 e‖ ^ 2 := by
      have h1 : (coeffs.γ s 0 e i) ^ 2 ≤ ‖coeffs.γ s 0 e‖ ^ 2 := by
        nlinarith [abs_nonneg (coeffs.γ s 0 e i), sq_abs (coeffs.γ s 0 e i), norm_nonneg
          (coeffs.γ s 0 e)]
      have h2 : (coeffs.γ s x e i - coeffs.γ s 0 e i) ^ 2
          ≤ ‖coeffs.γ s x e - coeffs.γ s 0 e‖ ^ 2 := by
        nlinarith [abs_nonneg (coeffs.γ s x e i - coeffs.γ s 0 e i),
          sq_abs (coeffs.γ s x e i - coeffs.γ s 0 e i),
          norm_nonneg (coeffs.γ s x e - coeffs.γ s 0 e)]
      nlinarith [sq_nonneg (coeffs.γ s x e i - 2 * coeffs.γ s 0 e i)]
    calc (‖coeffs.γ s x e i‖₊ : ℝ≥0∞) ^ 2
        = ENNReal.ofReal ((coeffs.γ s x e i) ^ 2) := sq_coe_nnnorm_real _
      _ ≤ ENNReal.ofReal (2 * ‖coeffs.γ s 0 e‖ ^ 2
            + 2 * ‖coeffs.γ s x e - coeffs.γ s 0 e‖ ^ 2) := ENNReal.ofReal_le_ofReal hreal
      _ = 2 * (‖coeffs.γ s 0 e‖₊ : ℝ≥0∞) ^ 2
            + 2 * (‖coeffs.γ s x e - coeffs.γ s 0 e‖₊ : ℝ≥0∞) ^ 2 := by
          rw [ENNReal.ofReal_add (by positivity) (by positivity),
            ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2),
            ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2), ENNReal.ofReal_ofNat,
            ← sq_coe_nnnorm, ← sq_coe_nnnorm]
  -- the Lipschitz clause, converted to the sum of squares
  have hLbound : 2 * ∫⁻ e, (‖coeffs.γ s x e - coeffs.γ s 0 e‖₊ : ℝ≥0∞) ^ 2 ∂ν
      ≤ ENNReal.ofReal (2 * L ^ 2) * ∑ i', (‖x i'‖₊ : ℝ≥0∞) ^ 2 := by
    refine (mul_le_mul' le_rfl (hLip.2.2.2 s x 0)).trans ?_
    rw [show (2 : ℝ≥0∞) = ENNReal.ofReal 2 by simp, ← ENNReal.ofReal_mul (by norm_num),
      show (2 : ℝ) * (L ^ 2 * ‖x - 0‖ ^ 2) = (2 * L ^ 2) * ‖x‖ ^ 2 by rw [sub_zero]; ring,
      ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ 2 * L ^ 2)]
    exact mul_le_mul' le_rfl (ofReal_sq_norm_le_sum x)
  calc ∫⁻ e, (‖coeffs.γ s x e i‖₊ : ℝ≥0∞) ^ 2 ∂ν
      ≤ ∫⁻ e, (2 * (‖coeffs.γ s 0 e‖₊ : ℝ≥0∞) ^ 2
          + 2 * (‖coeffs.γ s x e - coeffs.γ s 0 e‖₊ : ℝ≥0∞) ^ 2) ∂ν := lintegral_mono hpt
    _ = (∫⁻ e, 2 * (‖coeffs.γ s 0 e‖₊ : ℝ≥0∞) ^ 2 ∂ν)
          + ∫⁻ e, 2 * (‖coeffs.γ s x e - coeffs.γ s 0 e‖₊ : ℝ≥0∞) ^ 2 ∂ν :=
        MeasureTheory.lintegral_add_left (hγ0.const_mul 2) _
    _ = 2 * (∫⁻ e, (‖coeffs.γ s 0 e‖₊ : ℝ≥0∞) ^ 2 ∂ν)
          + 2 * ∫⁻ e, (‖coeffs.γ s x e - coeffs.γ s 0 e‖₊ : ℝ≥0∞) ^ 2 ∂ν := by
        rw [MeasureTheory.lintegral_const_mul' _ _ (by simp : (2 : ℝ≥0∞) ≠ ⊤),
          MeasureTheory.lintegral_const_mul' _ _ (by simp : (2 : ℝ≥0∞) ≠ ⊤)]
    _ ≤ 2 * (∫⁻ e, (‖coeffs.γ s 0 e‖₊ : ℝ≥0∞) ^ 2 ∂ν)
          + ENNReal.ofReal (2 * L ^ 2) * ∑ i', (‖x i'‖₊ : ℝ≥0∞) ^ 2 :=
        add_le_add le_rfl hLbound
/-- **The jump integrand along a state process of finite energy is square integrable at every
horizon**, in the `L²`-in-mark sense. -/
theorem lintegral_sq_gamma_lt_top_of_energy {n d : ℕ} {P : MeasureTheory.Measure Ω}
    [MeasureTheory.IsProbabilityMeasure P] {ν : MeasureTheory.Measure E}
    [MeasureTheory.SigmaFinite ν]
    (coeffs : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs n d E)
    (hReg : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs.IsRegular coeffs ν)
    {L : ℝ} (hLip : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs.IsLipschitz coeffs ν L)
    {Z : ℝ → Ω → (Fin n → ℝ)} (hZm : Measurable (Function.uncurry Z))
    (hZsq : ∀ b : ℝ, ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) b,
      ∑ i', (‖Z s ω i'‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    (i : Fin n) {T' : ℝ} (hT' : 0 < T') :
    ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T', ∫⁻ e,
      (‖coeffs.γ s (Z s ω) e i‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P < ⊤ := by
  -- the state-zero jump energy, as a function of time
  have hγ0 : Measurable fun s : ℝ => ∫⁻ e, (‖coeffs.γ s 0 e‖₊ : ℝ≥0∞) ^ 2 ∂ν := by
    have hj : Measurable fun p : ℝ × E => (‖coeffs.γ p.1 0 p.2‖₊ : ℝ≥0∞) ^ 2 := by
      have : Measurable fun p : ℝ × E => coeffs.γ p.1 0 p.2 :=
        hReg.2.2.1.comp (measurable_fst.prodMk (measurable_const.prodMk measurable_snd))
      exact (this.nnnorm.coe_nnreal_ennreal).pow_const 2
    exact hj.lintegral_prod_right'
  refine lt_of_le_of_lt (lintegral_mono fun ω => lintegral_mono fun s =>
    lintegral_sq_gamma_le coeffs hReg hLip s (Z s ω) i) ?_
  have hXi : ∀ i' : Fin n, Measurable fun p : Ω × ℝ => Z p.2 p.1 i' := fun i' =>
    (measurable_pi_apply i').comp
      (hZm.comp (measurable_snd.prodMk measurable_fst))
  have hinner : ∀ ω : Ω, ∫⁻ s in Set.Icc (0 : ℝ) T',
        (2 * (∫⁻ e, (‖coeffs.γ s 0 e‖₊ : ℝ≥0∞) ^ 2 ∂ν)
          + ENNReal.ofReal (2 * L ^ 2) * ∑ i', (‖Z s ω i'‖₊ : ℝ≥0∞) ^ 2) ∂volume
      = (∫⁻ s in Set.Icc (0 : ℝ) T', 2 * (∫⁻ e, (‖coeffs.γ s 0 e‖₊ : ℝ≥0∞) ^ 2 ∂ν) ∂volume)
        + ∫⁻ s in Set.Icc (0 : ℝ) T',
            ENNReal.ofReal (2 * L ^ 2) * ∑ i', (‖Z s ω i'‖₊ : ℝ≥0∞) ^ 2 ∂volume :=
    fun ω => MeasureTheory.lintegral_add_left (hγ0.const_mul 2) _
  rw [lintegral_congr hinner, MeasureTheory.lintegral_add_left measurable_const _]
  refine ENNReal.add_lt_top.mpr ⟨?_, ?_⟩
  · -- the state-zero term: constant in `ω`, finite by `IsRegular`
    rw [MeasureTheory.lintegral_const, measure_univ, mul_one,
      MeasureTheory.lintegral_const_mul' _ _ (by simp : (2 : ℝ≥0∞) ≠ ⊤)]
    exact ENNReal.mul_lt_top (by simp) (hReg.2.2.2.2.2 T' hT')
  · -- the state term: the frozen process's horizon bound
    have hconst : ∀ ω : Ω, ∫⁻ s in Set.Icc (0 : ℝ) T',
          ENNReal.ofReal (2 * L ^ 2) * ∑ i', (‖Z s ω i'‖₊ : ℝ≥0∞) ^ 2 ∂volume
        = ENNReal.ofReal (2 * L ^ 2) * ∫⁻ s in Set.Icc (0 : ℝ) T',
            ∑ i', (‖Z s ω i'‖₊ : ℝ≥0∞) ^ 2 ∂volume :=
      fun ω => MeasureTheory.lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    rw [lintegral_congr hconst,
      MeasureTheory.lintegral_const_mul' _ _
        (ENNReal.ofReal_ne_top : ENNReal.ofReal (2 * L ^ 2) ≠ ⊤)]
    refine ENNReal.mul_lt_top ENNReal.ofReal_lt_top ?_
    exact hZsq T'
/-- **The jump integrand along the frozen process is square integrable at every horizon.**
This is the hypothesis `picardStep` asks for and that `sup_L2` alone cannot supply. -/
theorem lintegral_sq_gamma_stop_lt_top {n d : ℕ} {P : MeasureTheory.Measure Ω}
    [MeasureTheory.IsProbabilityMeasure P] {ν : MeasureTheory.Measure E}
    [MeasureTheory.SigmaFinite ν]
    {ℱ : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›} {T : ℝ}
    (coeffs : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs n d E)
    (hReg : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs.IsRegular coeffs ν)
    {L : ℝ} (hLip : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs.IsLipschitz coeffs ν L)
    (Y : SBoundedProcess (n := n) P ℱ T) (hT : 0 ≤ T)
    (i : Fin n) {T' : ℝ} (hT' : 0 < T') :
    ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T', ∫⁻ e,
      (‖coeffs.γ s (Y.stop.X s ω) e i‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P < ⊤ :=
  lintegral_sq_gamma_lt_top_of_energy coeffs hReg hLip Y.stop.measurable_path
    (fun b => lt_of_le_of_lt (lintegral_lintegral_sq_stop_le Y hT b)
      (ENNReal.mul_lt_top ENNReal.ofReal_lt_top (ENNReal.pow_lt_top Y.sup_L2))) i hT'
/-- Composing a jointly measurable coefficient with a progressively measurable state process
gives a progressively measurable integrand. -/
theorem progressivelyMeasurable_comp_state {n : ℕ}
    {ℱ : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›} {X : ℝ → Ω → (Fin n → ℝ)}
    (hX : ∀ i : Fin n, Probability.ProgressivelyMeasurable ℱ (fun ω s => X s ω i))
    {f : ℝ → (Fin n → ℝ) → ℝ} (hf : Measurable (Function.uncurry f)) :
    Probability.ProgressivelyMeasurable ℱ (fun ω s => f s (X s ω)) := by
  refine Probability.ProgressivelyMeasurable.of_isStronglyProgressive ?_
  intro t
  letI : MeasurableSpace Ω := ℱ t
  have hXm : Measurable fun q : Set.Iic t × Ω => (X (q.1 : ℝ) q.2 : Fin n → ℝ) :=
    measurable_pi_lambda _ fun i => ((hX i).isStronglyProgressive t).measurable
  have hq : Measurable fun q : Set.Iic t × Ω => ((q.1 : ℝ), X (q.1 : ℝ) q.2) :=
    (measurable_subtype_coe.comp measurable_fst).prodMk hXm
  exact (hf.comp hq).stronglyMeasurable
/-- Composing a jointly measurable mark-dependent coefficient with a progressively measurable
state process gives a marked progressively measurable integrand. -/
theorem markedProgressivelyMeasurable_comp_state {n : ℕ}
    {ℱ : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›} {X : ℝ → Ω → (Fin n → ℝ)}
    (hX : ∀ i : Fin n, Probability.ProgressivelyMeasurable ℱ (fun ω s => X s ω i))
    {g : ℝ → (Fin n → ℝ) → E → ℝ}
    (hg : Measurable fun p : ℝ × (Fin n → ℝ) × E => g p.1 p.2.1 p.2.2) :
    Probability.MarkedProgressivelyMeasurable ℱ (fun ω s e => g s (X s ω) e) := by
  intro t
  letI : MeasurableSpace Ω := ℱ t
  have hXm : Measurable fun q : Set.Iic t × Ω => (X (q.1 : ℝ) q.2 : Fin n → ℝ) :=
    measurable_pi_lambda _ fun i => ((hX i).isStronglyProgressive t).measurable
  have hbase : Measurable fun q : (Set.Iic t × Ω) × E =>
      g (q.1.1 : ℝ) (X (q.1.1 : ℝ) q.1.2) q.2 :=
    hg.comp (((measurable_subtype_coe.comp measurable_fst).comp measurable_fst).prodMk
      ((hXm.comp measurable_fst).prodMk measurable_snd))
  have he : Measurable fun p : Ω × ℝ × E =>
      (((⟨min p.2.1 t, Set.mem_Iic.mpr (min_le_right _ _)⟩ : Set.Iic t), p.1), p.2.2) :=
    (((measurable_fst.comp measurable_snd).min measurable_const).subtype_mk.prodMk
      measurable_fst).prodMk (measurable_snd.comp measurable_snd)
  have heq : (fun p : Ω × ℝ × E =>
        (Set.Iic t).indicator (fun s => g s (X s p.1) p.2.2) p.2.1)
      = (Set.univ ×ˢ (Set.Iic t ×ˢ Set.univ)).indicator
          ((fun q : (Set.Iic t × Ω) × E => g (q.1.1 : ℝ) (X (q.1.1 : ℝ) q.1.2) q.2)
            ∘ fun p : Ω × ℝ × E =>
              (((⟨min p.2.1 t, Set.mem_Iic.mpr (min_le_right _ _)⟩ : Set.Iic t), p.1),
                p.2.2)) := by
    funext p
    by_cases hp : p.2.1 ≤ t
    · simp [hp, Function.comp_def]
    · simp [hp, Function.comp_def]
  rw [heq]
  exact (hbase.comp he).stronglyMeasurable.indicator
    (MeasurableSet.univ.prod (measurableSet_Iic.prod MeasurableSet.univ))
/-- Joint measurability of the diffusion integrand along a jointly measurable state process. -/
theorem measurable_sigma_comp_state {n d : ℕ} {ν : MeasureTheory.Measure E}
    (coeffs : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs n d E)
    (hReg : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs.IsRegular coeffs ν)
    {X : ℝ → Ω → (Fin n → ℝ)} (hX : Measurable (Function.uncurry X)) (i : Fin n) (j : Fin d) :
    Measurable (Function.uncurry fun ω s => coeffs.σ s (X s ω) i j) :=
  ((measurable_pi_apply j).comp ((measurable_pi_apply i).comp hReg.2.1)).comp
    (measurable_snd.prodMk (hX.comp (measurable_snd.prodMk measurable_fst)))
/-- Joint measurability of the jump integrand along a jointly measurable state process. -/
theorem measurable_gamma_comp_state {n d : ℕ} {ν : MeasureTheory.Measure E}
    (coeffs : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs n d E)
    (hReg : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs.IsRegular coeffs ν)
    {X : ℝ → Ω → (Fin n → ℝ)} (hX : Measurable (Function.uncurry X)) (i : Fin n) :
    Measurable fun p : Ω × ℝ × E => coeffs.γ p.2.1 (X p.2.1 p.1) p.2.2 i :=
  ((measurable_pi_apply i).comp hReg.2.2.1).comp
    ((measurable_fst.comp measurable_snd).prodMk
      ((hX.comp ((measurable_fst.comp measurable_snd).prodMk measurable_fst)).prodMk
        (measurable_snd.comp measurable_snd)))
/-- **Linear growth of the drift coefficient in the state**, read off the Lipschitz hypothesis
by comparing with the state `0`. -/
theorem sq_mu_le {n d : ℕ} {ν : MeasureTheory.Measure E}
    (coeffs : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs n d E) {L : ℝ}
    (hLip : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs.IsLipschitz coeffs ν L)
    (s : ℝ) (x : Fin n → ℝ) (i : Fin n) :
    (coeffs.μ s x i) ^ 2
      ≤ 2 * ‖coeffs.μ s 0‖ ^ 2 + 2 * (L ^ 2 * ∑ i', (x i') ^ 2) := by
  have hL := hLip.2.1 s x 0
  have hcoord : |coeffs.μ s x i - coeffs.μ s 0 i| ≤ ‖coeffs.μ s x - coeffs.μ s 0‖ := by
    simpa [Real.norm_eq_abs, Pi.sub_apply] using norm_le_pi_norm (coeffs.μ s x - coeffs.μ s 0) i
  have h0 : |coeffs.μ s 0 i| ≤ ‖coeffs.μ s 0‖ := by
    simpa [Real.norm_eq_abs] using norm_le_pi_norm (coeffs.μ s 0) i
  have hx : ‖x - 0‖ ^ 2 ≤ ∑ i', (x i') ^ 2 := by
    rw [sub_zero]; exact sq_norm_le_sum_sq x
  have hnormsq : ‖coeffs.μ s x - coeffs.μ s 0‖ ^ 2 ≤ L ^ 2 * ∑ i', (x i') ^ 2 := by
    have h1 : ‖coeffs.μ s x - coeffs.μ s 0‖ ^ 2 ≤ L ^ 2 * ‖x - 0‖ ^ 2 := by
      nlinarith [norm_nonneg (coeffs.μ s x - coeffs.μ s 0), norm_nonneg (x - 0), hLip.1]
    exact h1.trans (mul_le_mul_of_nonneg_left hx (sq_nonneg L))
  have hdiff : (coeffs.μ s x i - coeffs.μ s 0 i) ^ 2 ≤ L ^ 2 * ∑ i', (x i') ^ 2 := by
    nlinarith [hcoord, abs_nonneg (coeffs.μ s x i - coeffs.μ s 0 i),
      sq_abs (coeffs.μ s x i - coeffs.μ s 0 i), norm_nonneg (coeffs.μ s x - coeffs.μ s 0)]
  have hzero : (coeffs.μ s 0 i) ^ 2 ≤ ‖coeffs.μ s 0‖ ^ 2 := by
    nlinarith [h0, abs_nonneg (coeffs.μ s 0 i), sq_abs (coeffs.μ s 0 i),
      norm_nonneg (coeffs.μ s 0)]
  nlinarith [sq_nonneg (coeffs.μ s x i - 2 * coeffs.μ s 0 i)]
/-- **The drift integrand along a state process of finite energy is square integrable at every
horizon.** -/
theorem lintegral_sq_mu_lt_top_of_energy {n d : ℕ} {P : MeasureTheory.Measure Ω}
    [MeasureTheory.IsProbabilityMeasure P] {ν : MeasureTheory.Measure E}
    (coeffs : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs n d E)
    (hReg : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs.IsRegular coeffs ν)
    {L : ℝ} (hLip : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs.IsLipschitz coeffs ν L)
    {Z : ℝ → Ω → (Fin n → ℝ)}
    (hZsq : ∀ b : ℝ, ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) b,
      ∑ i', (‖Z s ω i'‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    (i : Fin n) {T' : ℝ} (hT' : 0 < T') :
    ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T',
      (‖coeffs.μ s (Z s ω) i‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤ := by
  have hpt : ∀ (ω : Ω) (s : ℝ),
      (‖coeffs.μ s (Z s ω) i‖₊ : ℝ≥0∞) ^ 2
        ≤ 2 * (‖coeffs.μ s 0‖₊ : ℝ≥0∞) ^ 2
          + ENNReal.ofReal (2 * L ^ 2) * ∑ i', (‖Z s ω i'‖₊ : ℝ≥0∞) ^ 2 := by
    intro ω s
    have h1 : ENNReal.ofReal (2 * ‖coeffs.μ s 0‖ ^ 2)
        = 2 * (‖coeffs.μ s 0‖₊ : ℝ≥0∞) ^ 2 := by
      rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2), sq_coe_nnnorm,
        ENNReal.ofReal_ofNat]
    have h2 : ENNReal.ofReal (2 * (L ^ 2 * ∑ i', (Z s ω i') ^ 2))
        = ENNReal.ofReal (2 * L ^ 2) * ∑ i', (‖Z s ω i'‖₊ : ℝ≥0∞) ^ 2 := by
      rw [show 2 * (L ^ 2 * ∑ i', (Z s ω i') ^ 2)
          = (2 * L ^ 2) * ∑ i', (Z s ω i') ^ 2 by ring,
        ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ 2 * L ^ 2),
        ENNReal.ofReal_sum_of_nonneg (fun _ _ => sq_nonneg _)]
      exact congrArg _ (Finset.sum_congr rfl fun i' _ => (sq_coe_nnnorm_real _).symm)
    calc (‖coeffs.μ s (Z s ω) i‖₊ : ℝ≥0∞) ^ 2
        = ENNReal.ofReal ((coeffs.μ s (Z s ω) i) ^ 2) := sq_coe_nnnorm_real _
      _ ≤ ENNReal.ofReal (2 * ‖coeffs.μ s 0‖ ^ 2
            + 2 * (L ^ 2 * ∑ i', (Z s ω i') ^ 2)) :=
          ENNReal.ofReal_le_ofReal (sq_mu_le coeffs hLip s _ i)
      _ = 2 * (‖coeffs.μ s 0‖₊ : ℝ≥0∞) ^ 2
            + ENNReal.ofReal (2 * L ^ 2) * ∑ i', (‖Z s ω i'‖₊ : ℝ≥0∞) ^ 2 := by
          rw [ENNReal.ofReal_add (by positivity) (by positivity), h1, h2]
  refine lt_of_le_of_lt (lintegral_mono fun ω => lintegral_mono fun s => hpt ω s) ?_
  have hμ0 : Measurable fun s : ℝ => (‖coeffs.μ s 0‖₊ : ℝ≥0∞) ^ 2 := by
    have : Measurable fun s : ℝ => coeffs.μ s 0 :=
      hReg.1.comp (measurable_id.prodMk measurable_const)
    exact (this.nnnorm.coe_nnreal_ennreal).pow_const 2
  have hinner : ∀ ω : Ω, ∫⁻ s in Set.Icc (0 : ℝ) T',
        (2 * (‖coeffs.μ s 0‖₊ : ℝ≥0∞) ^ 2
          + ENNReal.ofReal (2 * L ^ 2) * ∑ i', (‖Z s ω i'‖₊ : ℝ≥0∞) ^ 2) ∂volume
      = (∫⁻ s in Set.Icc (0 : ℝ) T', 2 * (‖coeffs.μ s 0‖₊ : ℝ≥0∞) ^ 2 ∂volume)
        + ∫⁻ s in Set.Icc (0 : ℝ) T',
            ENNReal.ofReal (2 * L ^ 2) * ∑ i', (‖Z s ω i'‖₊ : ℝ≥0∞) ^ 2 ∂volume :=
    fun ω => MeasureTheory.lintegral_add_left (hμ0.const_mul 2) _
  rw [lintegral_congr hinner, MeasureTheory.lintegral_add_left measurable_const _]
  refine ENNReal.add_lt_top.mpr ⟨?_, ?_⟩
  · rw [MeasureTheory.lintegral_const, measure_univ, mul_one,
      MeasureTheory.lintegral_const_mul' _ _ (by simp : (2 : ℝ≥0∞) ≠ ⊤)]
    exact ENNReal.mul_lt_top (by simp) (hReg.2.2.2.1 T' hT')
  · have hconst : ∀ ω : Ω, ∫⁻ s in Set.Icc (0 : ℝ) T',
          ENNReal.ofReal (2 * L ^ 2) * ∑ i', (‖Z s ω i'‖₊ : ℝ≥0∞) ^ 2 ∂volume
        = ENNReal.ofReal (2 * L ^ 2) * ∫⁻ s in Set.Icc (0 : ℝ) T',
            ∑ i', (‖Z s ω i'‖₊ : ℝ≥0∞) ^ 2 ∂volume :=
      fun ω => MeasureTheory.lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    rw [lintegral_congr hconst,
      MeasureTheory.lintegral_const_mul' _ _
        (ENNReal.ofReal_ne_top : ENNReal.ofReal (2 * L ^ 2) ≠ ⊤)]
    refine ENNReal.mul_lt_top ENNReal.ofReal_lt_top ?_
    exact hZsq T'
/-- **The drift integrand along the frozen process is square integrable at every horizon.** -/
theorem lintegral_sq_mu_stop_lt_top {n d : ℕ} {P : MeasureTheory.Measure Ω}
    [MeasureTheory.IsProbabilityMeasure P] {ν : MeasureTheory.Measure E}
    {ℱ : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›} {T : ℝ}
    (coeffs : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs n d E)
    (hReg : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs.IsRegular coeffs ν)
    {L : ℝ} (hLip : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs.IsLipschitz coeffs ν L)
    (Y : SBoundedProcess (n := n) P ℱ T) (hT : 0 ≤ T)
    (i : Fin n) {T' : ℝ} (hT' : 0 < T') :
    ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T',
      (‖coeffs.μ s (Y.stop.X s ω) i‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤ :=
  lintegral_sq_mu_lt_top_of_energy coeffs hReg hLip
    (fun b => lt_of_le_of_lt (lintegral_lintegral_sq_stop_le Y hT b)
      (ENNReal.mul_lt_top ENNReal.ofReal_lt_top (ENNReal.pow_lt_top Y.sup_L2))) i hT'
/-- Joint measurability of the drift integrand along a jointly measurable state process. -/
theorem measurable_mu_comp_state {n d : ℕ} {ν : MeasureTheory.Measure E}
    (coeffs : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs n d E)
    (hReg : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs.IsRegular coeffs ν)
    {X : ℝ → Ω → (Fin n → ℝ)} (hX : Measurable (Function.uncurry X)) (i : Fin n) :
    Measurable (Function.uncurry fun ω s => coeffs.μ s (X s ω) i) :=
  ((measurable_pi_apply i).comp hReg.1).comp
    (measurable_snd.prodMk (hX.comp (measurable_snd.prodMk measurable_fst)))
end Picard
end Ito
end LevyStochCalc


