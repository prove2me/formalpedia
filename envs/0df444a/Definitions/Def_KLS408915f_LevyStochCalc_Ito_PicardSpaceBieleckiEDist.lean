-- Prove2me | Definitions.Def_KLS408915f_LevyStochCalc_Ito_PicardSpaceBieleckiEDist
-- name    : KLS408915f_LevyStochCalc_Ito_PicardSpaceBieleckiEDist
-- status  : Definition
-- author  : @Lazyfill
-- created : 2026-10-23T10:08:50.602827+00:00
-- url     : https://prove2.me/theorems/47b8b9ed-f11e-4468-bb88-063e828acd7f
-- title:
--   Bielecki pseudo-distance on bounded processes
-- statement:
--   Vendored from the LevyStochCalc library (https://github.com/cgarryZA/LevyStochCalc). `SBoundedProcess.pathDiff` is the pointwise difference of two process paths, and `bieleckiEDist β T X Y` is `bieleckiNorm β T` applied to that difference. The bundle proves diagonal vanishing, symmetry, and subadditivity of the underlying Bielecki norm, with the required a.e.-measurability of the inner integrands. Thus this is a pseudo-distance in $[0,\infty]$ on process structures, not yet a separated distance.
-- source:
--   Lean source: https://github.com/cgarryZA/LevyStochCalc/blob/984dbf0b790031eac05d56fe5a84b65e15e1e932/LevyStochCalc/Ito/PicardSpaceBieleckiEDist.lean#L38-L344 (repository human-ai-mathematics/kls-lean, commit 408915f, module `LevyStochCalc.Ito.PicardSpaceBieleckiEDist`, definition bundle `KLS408915f_LevyStochCalc_Ito_PicardSpaceBieleckiEDist`; the repository is private at upload time). Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (Apache-2.0; upstream copyright notice retained in the Lean text).

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
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Ito/PicardSpaceBieleckiEDist.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
namespace LevyStochCalc
namespace Ito
namespace Picard
universe u v
variable {Ω : Type u} [MeasurableSpace Ω]
/-- **Pointwise Euclidean Minkowski (ENNReal form).** For NNReal-valued
`a, b : Fin n → NNReal`,
  `(∑ i, ((a i + b i) : ℝ≥0∞)²)^(1/2) ≤ (∑ i, a i²)^(1/2) + (∑ i, b i²)^(1/2)`.

This is the cast-to-`ℝ≥0∞` version of `NNReal.Lp_add_le` at `p = 2`. -/
lemma sum_sq_nnreal_add_le (n : ℕ) (a b : Fin n → NNReal) :
    (∑ i, ((a i + b i : NNReal) : ℝ≥0∞) ^ (2 : ℝ)) ^ ((1 : ℝ) / 2)
      ≤ (∑ i, ((a i : NNReal) : ℝ≥0∞) ^ (2 : ℝ)) ^ ((1 : ℝ) / 2)
        + (∑ i, ((b i : NNReal) : ℝ≥0∞) ^ (2 : ℝ)) ^ ((1 : ℝ) / 2) :=
  ENNReal.Lp_add_le Finset.univ
    (fun i => ((a i : NNReal) : ℝ≥0∞)) (fun i => ((b i : NNReal) : ℝ≥0∞))
    (by norm_num : (1:ℝ) ≤ 2)
/-- **Pointwise difference of path maps.** Subtraction of two
`SBoundedProcess`'s underlying path maps is pointwise subtraction in
`Fin n → ℝ` at each `(t, ω)`. -/
@[simp] noncomputable def SBoundedProcess.pathDiff
    {n : ℕ} {P : Measure Ω} [IsProbabilityMeasure P]
    {ℱ : Filtration ℝ ‹MeasurableSpace Ω›} {T : ℝ}
    (X Y : SBoundedProcess (n := n) P ℱ T) : ℝ → Ω → (Fin n → ℝ) :=
  fun t ω => X.X t ω - Y.X t ω
/-- **The Bielecki β-weighted edist between two `SBoundedProcess`es.**

  `bieleckiEDist β T X Y := bieleckiNorm β T (X.X - Y.X)`,

i.e., `⨆_{t ∈ [0, T]} e^{-βt} · (E[‖X_t - Y_t‖²])^(1/2)`.

This is a **pseudo-edist** on `SBoundedProcess`: two structures with
P-a.s. equal paths at every `t` have `bieleckiEDist = 0` but are not
structurally equal as `SBoundedProcess`es. The genuine `MetricSpace` is
on the AE-quotient (`SBoundedProcess.AEQuot`); this pseudo-edist
descends to a genuine edist on the quotient. -/
noncomputable def bieleckiEDist
    {n : ℕ} {P : Measure Ω} [IsProbabilityMeasure P]
    {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}
    (β T : ℝ) (X Y : SBoundedProcess (n := n) P ℱ T) : ℝ≥0∞ :=
  bieleckiNorm (P := P) β T (SBoundedProcess.pathDiff X Y)
@[simp] lemma bieleckiEDist_self
    {n : ℕ} {P : Measure Ω} [IsProbabilityMeasure P]
    {ℱ : Filtration ℝ ‹MeasurableSpace Ω›} {β T : ℝ}
    (X : SBoundedProcess (n := n) P ℱ T) : bieleckiEDist β T X X = 0 := by
  unfold bieleckiEDist bieleckiNorm SBoundedProcess.pathDiff
  -- The path-difference is identically zero, so the L² norm is zero.
  refine le_antisymm ?_ bot_le
  refine iSup_le (fun t => ?_)
  refine iSup_le (fun _ => ?_)
  -- The integrand is pointwise zero (`X.X t ω - X.X t ω = 0`), so the
  -- lintegral is zero, hence the (1/2)-rpow is zero, multiplying gives zero.
  have h_integrand_zero :
      (fun ω : Ω => ∑ i, ((‖(X.X t ω - X.X t ω) i‖₊ : ℝ≥0∞)) ^ 2)
        = fun _ => 0 := by
    funext ω
    simp
  rw [h_integrand_zero]
  simp
lemma bieleckiEDist_comm
    {n : ℕ} {P : Measure Ω} [IsProbabilityMeasure P]
    {ℱ : Filtration ℝ ‹MeasurableSpace Ω›} {β T : ℝ}
    (X Y : SBoundedProcess (n := n) P ℱ T) :
    bieleckiEDist β T X Y = bieleckiEDist β T Y X := by
  -- It suffices to show, per-`(t, ω, i)`, that the inner summands agree.
  -- ‖X t ω i - Y t ω i‖₊ = ‖-(Y t ω i - X t ω i)‖₊ = ‖Y t ω i - X t ω i‖₊
  -- (by `nnnorm_neg`).
  unfold bieleckiEDist bieleckiNorm SBoundedProcess.pathDiff
  -- The integrand pointwise equality:
  have h_pw : ∀ t : ℝ, ∀ ω : Ω,
      ∑ i, (‖(X.X t ω - Y.X t ω) i‖₊ : ℝ≥0∞) ^ 2
        = ∑ i, (‖(Y.X t ω - X.X t ω) i‖₊ : ℝ≥0∞) ^ 2 := by
    intro t ω
    refine Finset.sum_congr rfl (fun i _ => ?_)
    congr 2
    rw [show (X.X t ω - Y.X t ω) i = -((Y.X t ω - X.X t ω) i) by
      simp [Pi.sub_apply]]
    exact nnnorm_neg _
  -- Lift to lintegral, then to (1/2)-rpow, then to multiplication, then to sup.
  refine iSup_congr (fun t => ?_)
  refine iSup_congr (fun _ => ?_)
  congr 1
  congr 1
  exact lintegral_congr_ae (Filter.Eventually.of_forall (fun ω => h_pw t ω))
/-- **Bielecki β-norm subadditivity.** For any two path maps `Y₁, Y₂`,
  `bieleckiNorm β T (Y₁ + Y₂) ≤ bieleckiNorm β T Y₁ + bieleckiNorm β T Y₂`.

The proof chains four steps:
* Pointwise (in `t, ω`) Euclidean Minkowski on `Fin n → ℝ`.
* L² Minkowski over `ω` (`ENNReal.lintegral_Lp_add_le`).
* Multiplication by the (constant in `ω`) Bielecki weight `e^{-βt}`.
* Sup-subadditivity over `t ∈ [0, T]`. -/
lemma bieleckiNorm_add_le
    {n : ℕ} {P : Measure Ω} [IsProbabilityMeasure P] (β T : ℝ)
    (Y₁ Y₂ : ℝ → Ω → (Fin n → ℝ))
    (hY₁_meas : ∀ t : ℝ, AEMeasurable
      (fun ω => (∑ i, (‖Y₁ t ω i‖₊ : ℝ≥0∞) ^ 2) ^ ((1 : ℝ) / 2)) P)
    (hY₂_meas : ∀ t : ℝ, AEMeasurable
      (fun ω => (∑ i, (‖Y₂ t ω i‖₊ : ℝ≥0∞) ^ 2) ^ ((1 : ℝ) / 2)) P) :
    bieleckiNorm (P := P) β T (fun t ω => Y₁ t ω + Y₂ t ω)
      ≤ bieleckiNorm (P := P) β T Y₁ + bieleckiNorm (P := P) β T Y₂ := by
  unfold bieleckiNorm
  refine iSup_le (fun t => ?_)
  refine iSup_le (fun ht => ?_)
  -- At fixed `t`, show the per-`t` term of the LHS is bounded by the
  -- sum of the per-`t` terms.
  -- Outline:
  --   ofReal(e^{-βt}) · (∫⁻ ω, ∑ i, ‖(Y₁+Y₂) t ω i‖²)^(1/2)
  -- ≤ ofReal(e^{-βt}) · ((∫⁻ ω, ∑ i, ‖Y₁ t ω i‖²)^(1/2)
  --                     + (∫⁻ ω, ∑ i, ‖Y₂ t ω i‖²)^(1/2))
  -- = ofReal(e^{-βt}) · (∫⁻ ω, ∑ i, ‖Y₁ t ω i‖²)^(1/2)
  --   + ofReal(e^{-βt}) · (∫⁻ ω, ∑ i, ‖Y₂ t ω i‖²)^(1/2)
  have h_step :
      (∫⁻ ω, ∑ i, (‖(Y₁ t ω + Y₂ t ω) i‖₊ : ℝ≥0∞) ^ 2 ∂P)
        ^ ((1 : ℝ) / 2)
        ≤ (∫⁻ ω, ∑ i, (‖Y₁ t ω i‖₊ : ℝ≥0∞) ^ 2 ∂P) ^ ((1 : ℝ) / 2)
          + (∫⁻ ω, ∑ i, (‖Y₂ t ω i‖₊ : ℝ≥0∞) ^ 2 ∂P) ^ ((1 : ℝ) / 2) := by
    -- Apply L² Minkowski via ENNReal.lintegral_Lp_add_le. To do so we
    -- need the pointwise (in ω) bound
    --   (∑ i, ‖(Y₁+Y₂) t ω i‖²)^(1/2) ≤ (∑ i, ‖Y₁ t ω i‖²)^(1/2)
    --                                  + (∑ i, ‖Y₂ t ω i‖²)^(1/2),
    -- after which the L² Minkowski on the RHS-as-a-function-of-ω
    -- closes the gap.
    have h_pw : ∀ ω,
        (∑ i, (‖(Y₁ t ω + Y₂ t ω) i‖₊ : ℝ≥0∞) ^ 2) ^ ((1 : ℝ) / 2)
          ≤ (∑ i, (‖Y₁ t ω i‖₊ : ℝ≥0∞) ^ 2) ^ ((1 : ℝ) / 2)
            + (∑ i, (‖Y₂ t ω i‖₊ : ℝ≥0∞) ^ 2) ^ ((1 : ℝ) / 2) := by
      intro ω
      -- Apply `sum_sq_nnreal_add_le` after bounding the L¹ summand pointwise.
      have h_pw_nn : ∀ i,
          (‖(Y₁ t ω + Y₂ t ω) i‖₊ : ℝ≥0∞)
            ≤ (‖Y₁ t ω i‖₊ : ℝ≥0∞) + (‖Y₂ t ω i‖₊ : ℝ≥0∞) := by
        intro i
        rw [show (Y₁ t ω + Y₂ t ω) i = Y₁ t ω i + Y₂ t ω i from rfl]
        exact_mod_cast nnnorm_add_le _ _
      -- Convert sums to the ℝ-power form, apply Minkowski, convert back.
      -- The Bielecki defn uses `^ (2 : ℕ)` but `sum_sq_nnreal_add_le`
      -- and `ENNReal.Lp_add_le` use `^ (2 : ℝ)`. Convert via
      -- `ENNReal.rpow_two = pow_two`.
      have h_conv : ∀ (x : ℝ≥0∞), x ^ (2 : ℝ) = x ^ (2 : ℕ) := by
        intro x
        rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) from by norm_num, ENNReal.rpow_natCast]
      have h_step_A :
          (∑ i, (‖(Y₁ t ω + Y₂ t ω) i‖₊ : ℝ≥0∞) ^ 2) ^ ((1 : ℝ) / 2)
            ≤ (∑ i,
                (((‖Y₁ t ω i‖₊ + ‖Y₂ t ω i‖₊ : NNReal) : ℝ≥0∞)) ^ (2 : ℕ))
                ^ ((1 : ℝ) / 2) := by
        refine ENNReal.rpow_le_rpow ?_ (by norm_num : (0:ℝ) ≤ 1/2)
        refine Finset.sum_le_sum (fun i _ => ?_)
        push_cast
        gcongr
        exact h_pw_nn i
      -- Step B: apply the Euclidean Minkowski, converting ℕ ↔ ℝ exponents.
      refine le_trans h_step_A ?_
      have hMink :=
        sum_sq_nnreal_add_le n (fun i => ‖Y₁ t ω i‖₊) (fun i => ‖Y₂ t ω i‖₊)
      -- Convert all `^ (2 : ℝ)` to `^ (2 : ℕ)` to match the goal shape.
      have h_eq_a :
          (∑ i,
            (((‖Y₁ t ω i‖₊ + ‖Y₂ t ω i‖₊ : NNReal) : ℝ≥0∞)) ^ (2 : ℕ))
          = (∑ i,
            (((‖Y₁ t ω i‖₊ + ‖Y₂ t ω i‖₊ : NNReal) : ℝ≥0∞)) ^ (2 : ℝ))
            := by
        refine Finset.sum_congr rfl (fun i _ => ?_)
        rw [h_conv]
      have h_eq_b : (∑ i, ((‖Y₁ t ω i‖₊ : NNReal) : ℝ≥0∞) ^ (2 : ℝ))
          = (∑ i, ((‖Y₁ t ω i‖₊ : ℝ≥0∞)) ^ 2) := by
        refine Finset.sum_congr rfl (fun i _ => ?_)
        rw [h_conv]
      have h_eq_c : (∑ i, ((‖Y₂ t ω i‖₊ : NNReal) : ℝ≥0∞) ^ (2 : ℝ))
          = (∑ i, ((‖Y₂ t ω i‖₊ : ℝ≥0∞)) ^ 2) := by
        refine Finset.sum_congr rfl (fun i _ => ?_)
        rw [h_conv]
      rw [h_eq_a]
      rw [h_eq_b, h_eq_c] at hMink
      exact hMink
    -- Now apply L² Minkowski (`ENNReal.lintegral_Lp_add_le`) to the
    -- functions `f₁ ω := (∑ i, ‖Y₁ t ω i‖²)^(1/2)` and similarly for `f₂`.
    -- The bound `h_pw` says the function `ω ↦ (∑ i, ‖(Y₁+Y₂) t ω i‖²)^(1/2)`
    -- is pointwise ≤ `f₁ ω + f₂ ω`. Then squaring is monotone on the
    -- pointwise-NN values, then integration is monotone, then taking
    -- the (1/2)-rpow of both sides preserves the inequality.
    -- Setup: define
    --   F  ω := (∑ i, ‖(Y₁+Y₂) t ω i‖²)^(1/2)
    --   f₁ ω := (∑ i, ‖Y₁ t ω i‖²)^(1/2)
    --   f₂ ω := (∑ i, ‖Y₂ t ω i‖²)^(1/2)
    -- Show:   (∫⁻ ω, F ω ^ 2)^(1/2) ≤ (∫⁻ ω, f₁ ω ^ 2)^(1/2)
    --                                  + (∫⁻ ω, f₂ ω ^ 2)^(1/2)
    -- via the chain  (∫⁻ ω, F ω ^ 2)^(1/2)
    --             ≤ (∫⁻ ω, (f₁ ω + f₂ ω) ^ 2)^(1/2)
    --               [monotonicity in F ≤ f₁+f₂]
    --             ≤ (∫⁻ ω, f₁²)^(1/2) + (∫⁻ ω, f₂²)^(1/2) [L² Minkowski]
    set F : Ω → ℝ≥0∞ :=
      fun ω => (∑ i,
        (‖(Y₁ t ω + Y₂ t ω) i‖₊ : ℝ≥0∞) ^ 2) ^ ((1 : ℝ) / 2)
    set f₁ : Ω → ℝ≥0∞ :=
      fun ω => (∑ i, (‖Y₁ t ω i‖₊ : ℝ≥0∞) ^ 2) ^ ((1 : ℝ) / 2)
    set f₂ : Ω → ℝ≥0∞ :=
      fun ω => (∑ i, (‖Y₂ t ω i‖₊ : ℝ≥0∞) ^ 2) ^ ((1 : ℝ) / 2)
    -- The (∫⁻ ω, ∑ i, ‖·‖²) expressions equal (∫⁻ ω, F²),
    --   (∫⁻ ω, f₁²), (∫⁻ ω, f₂²)
    -- via the rpow-cancellation `((x)^(1/2))^2 = x`.
    have h_rpow_half_sq : ∀ (x : ℝ≥0∞), (x ^ ((1 : ℝ) / 2)) ^ (2 : ℝ) = x := by
      intro x
      rw [← ENNReal.rpow_mul]
      norm_num
    have h_F_sq :
        ∀ ω, F ω ^ (2 : ℝ) = ∑ i, (‖(Y₁ t ω + Y₂ t ω) i‖₊ : ℝ≥0∞) ^ 2 :=
      fun ω => h_rpow_half_sq _
    have h_f₁_sq : ∀ ω, f₁ ω ^ (2 : ℝ) = ∑ i, (‖Y₁ t ω i‖₊ : ℝ≥0∞) ^ 2 :=
      fun ω => h_rpow_half_sq _
    have h_f₂_sq : ∀ ω, f₂ ω ^ (2 : ℝ) = ∑ i, (‖Y₂ t ω i‖₊ : ℝ≥0∞) ^ 2 :=
      fun ω => h_rpow_half_sq _
    -- Rewrite LHS and RHS in terms of F, f₁, f₂.
    have h_LHS_eq :
        (∫⁻ ω, ∑ i, (‖(Y₁ t ω + Y₂ t ω) i‖₊ : ℝ≥0∞) ^ 2 ∂P)
            ^ ((1 : ℝ) / 2)
          = (∫⁻ ω, F ω ^ (2 : ℝ) ∂P) ^ ((1 : ℝ) / 2) := by
      congr 1
      refine lintegral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
      exact (h_F_sq ω).symm
    have h_RHS₁_eq :
        (∫⁻ ω, ∑ i, (‖Y₁ t ω i‖₊ : ℝ≥0∞) ^ 2 ∂P) ^ ((1 : ℝ) / 2)
          = (∫⁻ ω, f₁ ω ^ (2 : ℝ) ∂P) ^ ((1 : ℝ) / 2) := by
      congr 1
      refine lintegral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
      exact (h_f₁_sq ω).symm
    have h_RHS₂_eq :
        (∫⁻ ω, ∑ i, (‖Y₂ t ω i‖₊ : ℝ≥0∞) ^ 2 ∂P) ^ ((1 : ℝ) / 2)
          = (∫⁻ ω, f₂ ω ^ (2 : ℝ) ∂P) ^ ((1 : ℝ) / 2) := by
      congr 1
      refine lintegral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
      exact (h_f₂_sq ω).symm
    rw [h_LHS_eq, h_RHS₁_eq, h_RHS₂_eq]
    -- Step 1: bound (∫⁻ F²)^(1/2) ≤ (∫⁻ (f₁+f₂)²)^(1/2) via
    --   monotonicity of LHS in F.
    have h_step1 : (∫⁻ ω, F ω ^ (2 : ℝ) ∂P) ^ ((1 : ℝ) / 2)
        ≤ (∫⁻ ω, (f₁ ω + f₂ ω) ^ (2 : ℝ) ∂P) ^ ((1 : ℝ) / 2) := by
      refine ENNReal.rpow_le_rpow ?_ (by norm_num : (0:ℝ) ≤ 1/2)
      refine lintegral_mono (fun ω => ?_)
      -- F ω ≤ f₁ ω + f₂ ω by h_pw, so F ω ^ 2 ≤ (f₁+f₂) ω ^ 2.
      have h_F_le : F ω ≤ f₁ ω + f₂ ω := h_pw ω
      exact ENNReal.rpow_le_rpow h_F_le (by norm_num : (0:ℝ) ≤ 2)
    -- Step 2: apply L² Minkowski `ENNReal.lintegral_Lp_add_le`.
    -- Need AEMeasurable f₁, f₂.
    have hf₁_meas : AEMeasurable f₁ P := hY₁_meas t
    have hf₂_meas : AEMeasurable f₂ P := hY₂_meas t
    have h_step2 := ENNReal.lintegral_Lp_add_le hf₁_meas hf₂_meas (by norm_num : (1:ℝ) ≤ 2)
    -- h_step2 : (∫⁻ ω, (f₁+f₂)(ω)^2 ∂P)^(1/2)
    --   ≤ (∫⁻ f₁²)^(1/2) + (∫⁻ f₂²)^(1/2)
    -- The `(f₁+f₂) ω` in the lintegral is `Pi.add_apply`-applied;
    -- the goal expression is `(f₁ ω + f₂ ω)`. These are defeq.
    exact le_trans h_step1 h_step2
  -- Multiply by the Bielecki weight `ofReal (e^{-βt})` and split.
  calc ENNReal.ofReal (Real.exp (-β * t)) *
      (∫⁻ ω, ∑ i,
          (‖(fun t ω => Y₁ t ω + Y₂ t ω) t ω i‖₊ : ℝ≥0∞) ^ 2 ∂P)
        ^ ((1 : ℝ) / 2)
      = ENNReal.ofReal (Real.exp (-β * t)) *
          (∫⁻ ω, ∑ i, (‖(Y₁ t ω + Y₂ t ω) i‖₊ : ℝ≥0∞) ^ 2 ∂P)
            ^ ((1 : ℝ) / 2) := rfl
    _ ≤ ENNReal.ofReal (Real.exp (-β * t)) *
          ((∫⁻ ω, ∑ i, (‖Y₁ t ω i‖₊ : ℝ≥0∞) ^ 2 ∂P) ^ ((1 : ℝ) / 2)
            + (∫⁻ ω, ∑ i, (‖Y₂ t ω i‖₊ : ℝ≥0∞) ^ 2 ∂P)
                ^ ((1 : ℝ) / 2)) := by
        gcongr
    _ = ENNReal.ofReal (Real.exp (-β * t)) *
            (∫⁻ ω, ∑ i, (‖Y₁ t ω i‖₊ : ℝ≥0∞) ^ 2 ∂P) ^ ((1 : ℝ) / 2)
        + ENNReal.ofReal (Real.exp (-β * t)) *
            (∫⁻ ω, ∑ i, (‖Y₂ t ω i‖₊ : ℝ≥0∞) ^ 2 ∂P) ^ ((1 : ℝ) / 2) := by
        rw [mul_add]
    _ ≤ (⨆ s ∈ Set.Icc (0 : ℝ) T,
            ENNReal.ofReal (Real.exp (-β * s)) *
              (∫⁻ ω, ∑ i, (‖Y₁ s ω i‖₊ : ℝ≥0∞) ^ 2 ∂P) ^ ((1 : ℝ) / 2))
        + ⨆ s ∈ Set.Icc (0 : ℝ) T,
            ENNReal.ofReal (Real.exp (-β * s)) *
              (∫⁻ ω, ∑ i, (‖Y₂ s ω i‖₊ : ℝ≥0∞) ^ 2 ∂P)
                ^ ((1 : ℝ) / 2) := by
        gcongr
        · refine le_iSup₂ (f := fun s (_ : s ∈ Set.Icc (0:ℝ) T) =>
            ENNReal.ofReal (Real.exp (-β * s)) *
              (∫⁻ ω, ∑ i, (‖Y₁ s ω i‖₊ : ℝ≥0∞) ^ 2 ∂P)
                ^ ((1 : ℝ) / 2)) t ht
        · refine le_iSup₂ (f := fun s (_ : s ∈ Set.Icc (0:ℝ) T) =>
            ENNReal.ofReal (Real.exp (-β * s)) *
              (∫⁻ ω, ∑ i, (‖Y₂ s ω i‖₊ : ℝ≥0∞) ^ 2 ∂P)
                ^ ((1 : ℝ) / 2)) t ht
end Picard
end Ito
end LevyStochCalc


