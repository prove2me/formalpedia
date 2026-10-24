-- Prove2me | Definitions.Def_KLS408915f_LevyStochCalc_Poisson_CompensatedProcessQuadVar
-- name    : KLS408915f_LevyStochCalc_Poisson_CompensatedProcessQuadVar
-- status  : Definition
-- author  : @Lazyfill
-- created : 2026-10-23T09:36:06.777485+00:00
-- url     : https://prove2.me/theorems/42e1877d-6f55-4b4c-892b-b66e84c47ec6
-- title:
--   Horizon-measure convergence of dyadic integrands
-- statement:
--   Vendored from the LevyStochCalc library (https://github.com/cgarryZA/LevyStochCalc, commit `984dbf0b790031eac05d56fe5a84b65e15e1e932`). `horizonMeasure` is the product measure $P\otimes(\operatorname{volume}|_{[0,t]}\otimes\nu)$ on $\Omega\times\mathbb R\times E$, and `lintegral_horizonMeasure` rewrites its lintegral as the corresponding nested integral. `memLp_phi_horizon` states that the jointly measurable integrand belongs to `MemLp` exponent $2$ for positive horizons under the global square-integrability assumption. `stageEval` is the stage integrand viewed on the horizon product space, and `stageEval_tendsto` states convergence of its $L^2$ seminorm distance from $\phi$ to $0$ for every time horizon.
-- source:
--   Lean source: https://github.com/cgarryZA/LevyStochCalc/blob/984dbf0b790031eac05d56fe5a84b65e15e1e932/LevyStochCalc/Poisson/CompensatedProcessQuadVar.lean#L46-L167 (repository human-ai-mathematics/kls-lean, commit 408915f, module `LevyStochCalc.Poisson.CompensatedProcessQuadVar`, definition bundle `KLS408915f_LevyStochCalc_Poisson_CompensatedProcessQuadVar`; the repository is private at upload time). Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (Apache-2.0; upstream copyright notice retained in the Lean text).

import Definitions.Def_KLS408915f_BrownianMotion_Auxiliary_Algebra
import Definitions.Def_KLS408915f_BrownianMotion_Auxiliary_DenseCountable
import Definitions.Def_KLS408915f_BrownianMotion_Auxiliary_ENNReal
import Definitions.Def_KLS408915f_BrownianMotion_Auxiliary_FiniteInf
import Definitions.Def_KLS408915f_BrownianMotion_Auxiliary_LinearAlgebra
import Definitions.Def_KLS408915f_BrownianMotion_Auxiliary_MeanInequalities
import Definitions.Def_KLS408915f_BrownianMotion_Auxiliary_MeasureTheory
import Definitions.Def_KLS408915f_BrownianMotion_Auxiliary_Metric
import Definitions.Def_KLS408915f_BrownianMotion_Auxiliary_Nat
import Definitions.Def_KLS408915f_BrownianMotion_Auxiliary_Topology
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
import Definitions.Def_KLS408915f_LevyStochCalc_Brownian_SimplePredictableRefineAppend
import Definitions.Def_KLS408915f_LevyStochCalc_Brownian_SimplePredictableRefineCommon
import Definitions.Def_KLS408915f_LevyStochCalc_Brownian_SimplePredictableRefineInvariance
import Definitions.Def_KLS408915f_LevyStochCalc_Martingale_RightCont
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
import Definitions.Def_KLS408915f_LevyStochCalc_Poisson_CompensatedIsometry
import Definitions.Def_KLS408915f_LevyStochCalc_Poisson_CompensatedMartingaleAdapted
import Definitions.Def_KLS408915f_LevyStochCalc_Poisson_CompensatedMartingaleIncrement
import Definitions.Def_KLS408915f_LevyStochCalc_Poisson_CompensatedMartingaleQuadratic
import Definitions.Def_KLS408915f_LevyStochCalc_Poisson_CompensatedProcess
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
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Convex.Integral
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.InnerProductSpace.GramMatrix
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
import Mathlib.MeasureTheory.Constructions.ClosedCompactCylinders
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.MeasureTheory.Constructions.ProjectiveFamilyContent
import Mathlib.MeasureTheory.Covering.DensityTheorem
import Mathlib.MeasureTheory.Function.ConditionalExpectation.CondJensen
import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Real
import Mathlib.MeasureTheory.Function.Holder
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Basic
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
import Mathlib.Probability.Moments.CovarianceBilin
import Mathlib.Probability.Process.Adapted
import Mathlib.Probability.Process.Filtration
import Mathlib.Probability.Process.Kolmogorov
import Mathlib.Topology.Bases
import Mathlib.Topology.Compactness.CompactSystem
import Mathlib.Topology.ContinuousMap.SecondCountableSpace
import Mathlib.Topology.EMetricSpace.PairReduction
import Mathlib.Topology.IsClosedRestrict
import Mathlib.Topology.MetricSpace.Cover
import Mathlib.Topology.MetricSpace.CoveringNumbers
import Mathlib.Topology.MetricSpace.HolderNorm
import Mathlib.Topology.MetricSpace.MetricSeparated
import Mathlib.Topology.Order.MonotoneContinuity

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Poisson/CompensatedProcessQuadVar.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal
namespace LevyStochCalc
namespace Poisson
namespace Compensated
universe u v
variable {Ω : Type u} [MeasurableSpace Ω]
variable {E : Type v} [MeasurableSpace E]
section Compensator
variable (ν : Measure E) (φ : Ω → ℝ → E → ℝ)
/-- The product measure of `P`, Lebesgue measure on `[0, t]` and `ν` on `Ω × ℝ × E`. -/
noncomputable abbrev horizonMeasure (P : Measure Ω) (t : ℝ) : Measure (Ω × ℝ × E) :=
  P.prod ((volume.restrict (Set.Icc (0 : ℝ) t)).prod ν)
end Compensator
variable {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν]
  (N : PoissonRandomMeasure P ν) (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (hℱ : IsPoissonFiltration
    N ℱ)
  (φ : Ω → ℝ → E → ℝ)
  (h_meas : Measurable (fun p : Ω × ℝ × E => φ p.1 p.2.1 p.2.2))
  (h_progMeas : Probability.MarkedProgressivelyMeasurable ℱ φ)
  (h_sq_int_global : ∀ T : ℝ, 0 < T →
    ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e,
      (‖φ ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P < ⊤)
omit [IsProbabilityMeasure P] in
/-- The nested triple integral over `Ω`, `[0, t]` and `E` as an integral for the horizon
measure. -/
lemma lintegral_horizonMeasure (t : ℝ) (f : Ω → ℝ → E → ℝ≥0∞)
    (hf : Measurable (fun p : Ω × ℝ × E => f p.1 p.2.1 p.2.2)) :
    ∫⁻ p, f p.1 p.2.1 p.2.2 ∂(horizonMeasure ν P t)
      = ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) t, ∫⁻ e, f ω s e ∂ν ∂volume ∂P := by
  rw [horizonMeasure, lintegral_prod _ hf.aemeasurable]
  refine lintegral_congr fun ω => ?_
  rw [lintegral_prod (fun y : ℝ × E => f (ω, y).1 (ω, y).2.1 (ω, y).2.2)
    (hf.comp (measurable_prodMk_left (x := ω))).aemeasurable]
omit [IsProbabilityMeasure P] in
include h_meas h_sq_int_global in
/-- The integrand is square-integrable for the horizon measure. -/
lemma memLp_phi_horizon {t : ℝ} (ht : 0 < t) :
    MemLp (fun p : Ω × ℝ × E => φ p.1 p.2.1 p.2.2) 2 (horizonMeasure ν P t) := by
  refine ⟨h_meas.aestronglyMeasurable, ?_⟩
  refine (ENNReal.rpow_lt_top_iff_of_pos (by norm_num : (0 : ℝ) < 2)).1 ?_
  rw [LevyStochCalc.Brownian.Ito.eLpNorm_sq_eq_lintegral_nnnorm_sq,
    lintegral_horizonMeasure t (fun ω s e => (‖φ ω s e‖₊ : ℝ≥0∞) ^ 2)
      ((ENNReal.continuous_coe.measurable.comp h_meas.nnnorm).pow_const 2)]
  exact h_sq_int_global t ht
/-- The integrand of the stage-`n` approximant as a function on `Ω × ℝ × E`. -/
noncomputable def stageEval (n : ℕ) (p : Ω × ℝ × E) : ℝ :=
  (master N ℱ φ h_meas h_progMeas h_sq_int_global n).2.eval p.2.1 p.2.2 p.1
lemma measurable_stageEval (n : ℕ) :
    Measurable (stageEval N ℱ φ h_meas h_progMeas h_sq_int_global n) :=
  (master N ℱ φ h_meas h_progMeas h_sq_int_global n).2.eval_measurable
/-- The stage integrands converge to `φ` in `L²` of the horizon measure at every time. -/
lemma stageEval_tendsto (t : ℝ) :
    Tendsto (fun n => eLpNorm (stageEval N ℱ φ h_meas h_progMeas h_sq_int_global n
      - fun p : Ω × ℝ × E => φ p.1 p.2.1 p.2.2) 2 (horizonMeasure ν P t)) atTop (𝓝 0) := by
  have hsq : Tendsto (fun n => eLpNorm (stageEval N ℱ φ h_meas h_progMeas h_sq_int_global n
      - fun p : Ω × ℝ × E => φ p.1 p.2.1 p.2.2) 2 (horizonMeasure ν P t) ^ (2 : ℝ))
      atTop (𝓝 0) := by
    obtain ⟨N₀, hN₀⟩ : ∃ N₀ : ℕ, t ≤ stageHorizon N₀ := by
      obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt t (one_lt_two : (1 : ℝ) < 2)
      exact ⟨k, hk.le⟩
    have hbound : ∀ n, N₀ ≤ n → eLpNorm (stageEval N ℱ φ h_meas h_progMeas h_sq_int_global n
        - fun p : Ω × ℝ × E => φ p.1 p.2.1 p.2.2) 2 (horizonMeasure ν P t) ^ (2 : ℝ)
        ≤ stageErr φ P n (master N ℱ φ h_meas h_progMeas h_sq_int_global n).2 := by
      intro n hn
      set G := (master N ℱ φ h_meas h_progMeas h_sq_int_global n).2 with hG
      have hdm : Measurable (fun p : Ω × ℝ × E =>
          (‖φ p.1 p.2.1 p.2.2 - G.eval p.2.1 p.2.2 p.1‖₊ : ℝ≥0∞) ^ 2) :=
        (ENNReal.continuous_coe.measurable.comp (h_meas.sub G.eval_measurable).nnnorm).pow_const 2
      calc eLpNorm (stageEval N ℱ φ h_meas h_progMeas h_sq_int_global n
            - fun p : Ω × ℝ × E => φ p.1 p.2.1 p.2.2) 2 (horizonMeasure ν P t) ^ (2 : ℝ)
          = ∫⁻ p, (‖(stageEval N ℱ φ h_meas h_progMeas h_sq_int_global n
              - fun p : Ω × ℝ × E => φ p.1 p.2.1 p.2.2) p‖₊ : ℝ≥0∞) ^ 2
              ∂(horizonMeasure ν P t) :=
            LevyStochCalc.Brownian.Ito.eLpNorm_sq_eq_lintegral_nnnorm_sq _
        _ = ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) t, ∫⁻ e,
              (‖φ ω s e - G.eval s e ω‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P := by
            rw [← lintegral_horizonMeasure t
              (fun ω s e => (‖φ ω s e - G.eval s e ω‖₊ : ℝ≥0∞) ^ 2) hdm]
            refine lintegral_congr fun q => ?_
            rw [Pi.sub_apply, ← nnnorm_neg, neg_sub]
            rfl
        _ ≤ stageErr φ P n G := lintegral_mono fun ω =>
            lintegral_mono_set (Set.Icc_subset_Icc_right (hN₀.trans (stageHorizon_mono hn)))
    have hinv : Tendsto (fun n : ℕ => ((n : ℝ≥0∞) + 1)⁻¹) atTop (𝓝 0) := by
      have := ENNReal.tendsto_inv_nat_nhds_zero.comp (tendsto_add_atTop_nat 1)
      refine this.congr fun n => ?_
      simp [Function.comp]
    have herr : Tendsto (fun n => stageErr φ P n
        (master N ℱ φ h_meas h_progMeas h_sq_int_global n).2) atTop (𝓝 0) :=
      tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hinv (fun _ => bot_le)
        (fun n => (master_err N ℱ φ h_meas h_progMeas h_sq_int_global n).le)
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds herr
      (Eventually.of_forall fun _ => bot_le) (eventually_atTop.2 ⟨N₀, hbound⟩)
  have h := hsq.ennrpow_const ((1 : ℝ) / 2)
  rw [ENNReal.zero_rpow_of_pos (by norm_num)] at h
  refine h.congr (fun n => ?_)
  rw [← ENNReal.rpow_mul, show (2 : ℝ) * (1 / 2) = 1 by norm_num, ENNReal.rpow_one]
end Compensated
end Poisson
end LevyStochCalc


