-- Prove2me | Definitions.Def_KLS408915f_LevyStochCalc_Ito_PicardSpaceDiscrete
-- name    : KLS408915f_LevyStochCalc_Ito_PicardSpaceDiscrete
-- status  : Definition
-- author  : @Lazyfill
-- created : 2026-10-23T10:05:03.410281+00:00
-- url     : https://prove2.me/theorems/d77bc7ec-5afd-4d03-8f5d-4bd53ba3dab7
-- title:
--   Discrete metric and completeness for bounded processes
-- statement:
--   Vendored from the LevyStochCalc library (https://github.com/cgarryZA/LevyStochCalc). `constantZeroProcess` gives a zero element of `SBoundedProcess`, and `discreteDist X Y` is $0$ when $X=Y$ and $1$ otherwise. The supplied pseudo-metric and metric instances use this distance, and the bundle proves that every Cauchy sequence is eventually constant and that the resulting metric space is complete. This discrete metric is separate from the analytic Bielecki norm.
-- source:
--   Lean source: https://github.com/cgarryZA/LevyStochCalc/blob/984dbf0b790031eac05d56fe5a84b65e15e1e932/LevyStochCalc/Ito/PicardSpaceDiscrete.lean#L34-L259 (repository human-ai-mathematics/kls-lean, commit 408915f, module `LevyStochCalc.Ito.PicardSpaceDiscrete`, definition bundle `KLS408915f_LevyStochCalc_Ito_PicardSpaceDiscrete`; the repository is private at upload time). Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (Apache-2.0; upstream copyright notice retained in the Lean text).

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
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Ito/PicardSpaceDiscrete.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
namespace LevyStochCalc
namespace Ito
namespace Picard
universe u v
variable {Ω : Type u} [MeasurableSpace Ω]
/-- **Constant-zero `SBoundedProcess`.** The map `X t ω = 0` (the zero
vector in `Fin n → ℝ`) is the canonical witness of `Nonempty
(SBoundedProcess P T)`:

* **Measurability** — `Function.uncurry (fun _ _ => 0) = fun _ => 0` is the
  zero constant, hence trivially measurable (`Measurable.const 0`).
* **Càdlàg paths** — every constant function is continuous, so the
  right-limit `Filter.Tendsto` is `tendsto_const_nhds`; for the left
  limit, the witness `L = 0` makes the left-limit `Filter.Tendsto` also
  `tendsto_const_nhds`.
* **`sup_L2`** — `bieleckiNorm β T 0 = 0 < ⊤` because the integrand
  `(∑ i, ‖0‖²) = 0` makes the inner `∫⁻` and the outer rpow both zero;
  multiplying by `ENNReal.ofReal (exp (-β·t))` and taking the supremum
  over `t ∈ [0, T]` still gives zero, which is `< ⊤`. -/
noncomputable def constantZeroProcess
    {n : ℕ} (P : Measure Ω) [IsProbabilityMeasure P]
    (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (T : ℝ) :
    SBoundedProcess (n := n) P ℱ T where
  X := fun _ _ => 0
  measurable_path := by
    have : Function.uncurry (fun (_ : ℝ) (_ : Ω) => (0 : Fin n → ℝ)) =
        fun _ => 0 := by
      funext p
      simp [Function.uncurry]
    rw [this]
    exact measurable_const
  adapted := by
    intro i t
    simpa using
      (stronglyMeasurable_const :
        StronglyMeasurable[@Prod.instMeasurableSpace Ω ℝ (ℱ t) inferInstance]
          fun _ : Ω × ℝ => (0 : ℝ))
  cadlag_paths := by
    refine Filter.Eventually.of_forall (fun ω => ?_)
    intro t
    refine ⟨?_, ?_⟩
    · exact tendsto_const_nhds
    · intro _
      exact ⟨0, tendsto_const_nhds⟩
  sup_L2 := by
    unfold bieleckiNorm
    refine lt_of_le_of_lt ?_ ENNReal.zero_lt_top
    refine iSup_le (fun t => ?_)
    refine iSup_le (fun _ => ?_)
    have h_sum_zero : (fun ω : Ω =>
        (∑ i, (‖(fun _ _ => (0 : Fin n → ℝ)) t ω i‖₊ : ℝ≥0∞) ^ 2)) =
        fun _ => 0 := by
      funext ω
      simp
    rw [h_sum_zero]
    simp
/-- `Nonempty` instance: constant zero process. -/
noncomputable instance instNonemptySBoundedProcess
    {n : ℕ} {P : Measure Ω} [IsProbabilityMeasure P]
    {ℱ : Filtration ℝ ‹MeasurableSpace Ω›} {T : ℝ} :
    Nonempty (SBoundedProcess (n := n) P ℱ T) :=
  ⟨constantZeroProcess P ℱ T⟩
section DiscreteMetric
set_option linter.style.openClassical false
open Classical
variable {n : ℕ} {P : Measure Ω} [IsProbabilityMeasure P]
    {ℱ : Filtration ℝ ‹MeasurableSpace Ω›} {T : ℝ}
/-- The discrete distance on `SBoundedProcess`: zero on the diagonal,
one elsewhere. Uses classical decidability of equality (via the
section-local `open Classical`) to make `if X = Y then 0 else 1`
well-typed without needing a `[DecidableEq]` instance. -/
noncomputable def discreteDist
    (X Y : SBoundedProcess (n := n) P ℱ T) : ℝ :=
  if X = Y then 0 else 1
lemma discreteDist_self (X : SBoundedProcess (n := n) P ℱ T) :
    discreteDist X X = 0 := by
  simp [discreteDist]
lemma discreteDist_comm (X Y : SBoundedProcess (n := n) P ℱ T) :
    discreteDist X Y = discreteDist Y X := by
  unfold discreteDist
  by_cases h : X = Y
  · subst h; rfl
  · have h' : ¬ Y = X := fun heq => h heq.symm
    rw [if_neg h, if_neg h']
lemma discreteDist_triangle (X Y Z : SBoundedProcess (n := n) P ℱ T) :
    discreteDist X Z ≤ discreteDist X Y + discreteDist Y Z := by
  unfold discreteDist
  by_cases hXZ : X = Z
  · -- LHS = 0; RHS ≥ 0.
    rw [if_pos hXZ]
    have h₁ : (0 : ℝ) ≤ (if X = Y then (0 : ℝ) else 1) := by
      split_ifs <;> norm_num
    have h₂ : (0 : ℝ) ≤ (if Y = Z then (0 : ℝ) else 1) := by
      split_ifs <;> norm_num
    linarith
  · -- LHS = 1; need 1 ≤ RHS.
    rw [if_neg hXZ]
    by_cases hXY : X = Y
    · by_cases hYZ : Y = Z
      · exact absurd (hXY.trans hYZ) hXZ
      · rw [if_pos hXY, if_neg hYZ]; linarith
    · rw [if_neg hXY]
      have h₂ : (0 : ℝ) ≤ (if Y = Z then (0 : ℝ) else 1) := by
        split_ifs <;> norm_num
      linarith
lemma discreteDist_eq_zero_iff
    (X Y : SBoundedProcess (n := n) P ℱ T) :
    discreteDist X Y = 0 ↔ X = Y := by
  unfold discreteDist
  by_cases h : X = Y
  · simp [h]
  · rw [if_neg h]
    exact ⟨fun h₀ => by linarith, fun heq => absurd heq h⟩
/-- **`PseudoMetricSpace` instance via the discrete distance.** -/
noncomputable instance instPseudoMetricSpaceSBoundedProcess :
    PseudoMetricSpace (SBoundedProcess (n := n) P ℱ T) where
  dist := discreteDist
  dist_self := discreteDist_self
  dist_comm := discreteDist_comm
  dist_triangle := discreteDist_triangle
/-- **`MetricSpace` instance via the discrete distance.** Promotes the
pseudo-metric to a genuine metric by adding the separation axiom
`dist X Y = 0 → X = Y`, which holds for the discrete distance by
construction. -/
noncomputable instance instMetricSpaceSBoundedProcess :
    MetricSpace (SBoundedProcess (n := n) P ℱ T) where
  __ := instPseudoMetricSpaceSBoundedProcess
  eq_of_dist_eq_zero {X Y} h := (discreteDist_eq_zero_iff X Y).mp h
/-- **Cauchy sequence in the discrete metric is eventually constant.** If
`u : ℕ → SBoundedProcess` is Cauchy with respect to the discrete distance
inherited from `instMetricSpaceSBoundedProcess`, then there exists `N`
such that `u n = u N` for all `n ≥ N`. The witness `N` is obtained from
the Cauchy property at scale `ε = 1/2`: any two terms `u m`, `u n` with
`m, n ≥ N` have `dist (u m) (u n) < 1`, hence by the discrete distance
must satisfy `u m = u n`. -/
lemma cauchySeq_eventually_constant
    (u : ℕ → SBoundedProcess (n := n) P ℱ T) (hu : CauchySeq u) :
    ∃ N : ℕ, ∀ n ≥ N, u n = u N := by
  rw [Metric.cauchySeq_iff] at hu
  obtain ⟨N, hN⟩ := hu (1/2) (by norm_num)
  refine ⟨N, ?_⟩
  intro n hn
  have h_dist : dist (u n) (u N) < 1/2 := hN n hn N (le_refl N)
  by_contra hne
  have h_eq : (dist (u n) (u N) : ℝ) = 1 := by
    change discreteDist (u n) (u N) = 1
    unfold discreteDist
    rw [if_neg hne]
  rw [h_eq] at h_dist
  linarith
/-- **`CompleteSpace` instance.** Every Cauchy sequence in the discrete
metric on `SBoundedProcess` is eventually constant and hence converges
to that constant value.

We use `complete_of_cauchySeq_tendsto`: a uniform space with countable
basis of the uniformity (automatic for metric spaces) is complete iff
every Cauchy *sequence* converges. The discrete metric makes every Cauchy
sequence eventually constant (by `cauchySeq_eventually_constant`), and an
eventually-constant sequence converges to its eventual value. -/
noncomputable instance instCompleteSpaceSBoundedProcess :
    CompleteSpace (SBoundedProcess (n := n) P ℱ T) := by
  apply UniformSpace.complete_of_cauchySeq_tendsto
  intro u hu
  obtain ⟨N, hN⟩ := cauchySeq_eventually_constant u hu
  refine ⟨u N, ?_⟩
  rw [Metric.tendsto_atTop]
  intro ε hε
  refine ⟨N, fun n hn => ?_⟩
  rw [hN n hn, dist_self]
  exact hε
end DiscreteMetric
end Picard
end Ito
end LevyStochCalc


