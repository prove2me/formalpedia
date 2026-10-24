-- Prove2me | Definitions.Def_KLS408915f_LevyStochCalc_Brownian_ItoAlgebraSimpleIntegrand
-- name    : KLS408915f_LevyStochCalc_Brownian_ItoAlgebraSimpleIntegrand
-- status  : Definition
-- author  : @Lazyfill
-- created : 2026-10-23T11:07:58.156453+00:00
-- url     : https://prove2.me/theorems/0756c6e2-c6f5-4b8f-8f80-53e8e4550970
-- title:
--   Admissibility properties of simple Brownian integrands
-- statement:
--   Vendored from the LevyStochCalc library (https://github.com/cgarryZA/LevyStochCalc). A `SimplePredictable` integrand has a uniform real bound, and its evaluation is progressively measurable when its coefficients are strongly measurable with respect to the corresponding filtration times. Multiplying its evaluation by a jointly measurable process preserves joint measurability, and multiplying by a progressively measurable process preserves progressive measurability. The bundle also proves finite squared $[0,\infty]$-valued energy on every positive horizon when the other factor has finite such energy.
-- source:
--   Lean source: https://github.com/cgarryZA/LevyStochCalc/blob/984dbf0b790031eac05d56fe5a84b65e15e1e932/LevyStochCalc/Brownian/ItoAlgebraSimpleIntegrand.lean#L27-L222 (repository human-ai-mathematics/kls-lean, commit 408915f, module `LevyStochCalc.Brownian.ItoAlgebraSimpleIntegrand`, definition bundle `KLS408915f_LevyStochCalc_Brownian_ItoAlgebraSimpleIntegrand`; the repository is private at upload time). Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (Apache-2.0; upstream copyright notice retained in the Lean text).

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
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Real
import Mathlib.MeasureTheory.Function.Holder
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Basic
import Mathlib.MeasureTheory.Group.Arithmetic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.MeanInequalities
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.MeasurableSpace.Constructions
import Mathlib.MeasureTheory.Measure.AddContent
import Mathlib.MeasureTheory.Measure.HasOuterApproxClosed
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
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
import Mathlib.Probability.Independence.Basic
import Mathlib.Probability.Independence.BoundedContinuousFunction
import Mathlib.Probability.Independence.Integration
import Mathlib.Probability.Independence.Process.HasIndepIncrements.Basic
import Mathlib.Probability.Independence.ZeroOne
import Mathlib.Probability.Kernel.Defs
import Mathlib.Probability.Martingale.Basic
import Mathlib.Probability.Moments.CovarianceBilin
import Mathlib.Probability.Process.Adapted
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
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Brownian/ItoAlgebraSimpleIntegrand.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
namespace LevyStochCalc
namespace Brownian
namespace Ito
open MeasureTheory
open scoped NNReal ENNReal
universe u
variable {Ω : Type u} [MeasurableSpace Ω]
/-- A simple integrand is uniformly bounded in both variables. -/
theorem SimplePredictable.exists_eval_bound {T : ℝ} (G : SimplePredictable Ω T) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ s ω, |G.eval s ω| ≤ B := by
  classical
  choose M hM using G.ξ_bounded
  refine ⟨∑ i : Fin G.N, max (M i) 0, Finset.sum_nonneg fun i _ => le_max_right _ _,
    fun s ω => ?_⟩
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
  by_cases h : G.partition i.castSucc < s ∧ s ≤ G.partition i.succ
  · rw [if_pos h]; exact (hM i ω).trans (le_max_left _ _)
  · rw [if_neg h, abs_zero]; exact le_max_right _ _
/-- A finite sum of step processes `1_{(aᵢ, bᵢ]}(s) · ξᵢ ω`, with `ξᵢ` measurable for
`ℱ (aᵢ)`, is progressively measurable. -/
theorem progressivelyMeasurable_sum_indicator_Ioc
    (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) {n : ℕ} (a b : Fin n → ℝ)
    (ξ : Fin n → Ω → ℝ)
    (hξ : ∀ i, @MeasureTheory.StronglyMeasurable Ω ℝ _ (ℱ (a i)) (ξ i)) :
    Probability.ProgressivelyMeasurable ℱ
      (fun ω s => ∑ i : Fin n, (Set.Ioc (a i) (b i)).indicator (fun _ => ξ i ω) s) := by
  classical
  intro t
  have key : (fun p : Ω × ℝ => (Set.Iic t).indicator
        (fun s => ∑ i : Fin n, (Set.Ioc (a i) (b i)).indicator (fun _ => ξ i p.1) s) p.2)
      = fun p : Ω × ℝ => ∑ i : Fin n,
        (Set.univ ×ˢ (Set.Ioc (a i) (b i) ∩ Set.Iic t)).indicator
          (fun q : Ω × ℝ => ξ i q.1) p := by
    funext p
    by_cases hp : p.2 ≤ t
    · rw [Set.indicator_of_mem (Set.mem_Iic.mpr hp)]
      refine Finset.sum_congr rfl fun i _ => ?_
      by_cases hi : p.2 ∈ Set.Ioc (a i) (b i)
      · have hmem : p ∈ Set.univ ×ˢ (Set.Ioc (a i) (b i) ∩ Set.Iic t) :=
          ⟨Set.mem_univ _, hi, Set.mem_Iic.mpr hp⟩
        rw [Set.indicator_of_mem hi, Set.indicator_of_mem hmem]
      · rw [Set.indicator_of_notMem hi, Set.indicator_of_notMem]
        rintro ⟨-, hmem, -⟩
        exact hi hmem
    · rw [Set.indicator_of_notMem (by simpa using hp)]
      refine (Finset.sum_eq_zero fun i _ => ?_).symm
      rw [Set.indicator_of_notMem]
      rintro ⟨-, -, hmem⟩
      exact hp (Set.mem_Iic.mp hmem)
  letI : MeasurableSpace Ω := ℱ t
  rw [key]
  refine Finset.stronglyMeasurable_fun_sum _ fun i _ => ?_
  by_cases hi : a i < t
  · refine MeasureTheory.StronglyMeasurable.indicator ?_
      (MeasurableSet.univ.prod (measurableSet_Ioc.inter measurableSet_Iic))
    exact ((hξ i).mono (ℱ.mono hi.le)).comp_measurable measurable_fst
  · have hempty : Set.Ioc (a i) (b i) ∩ Set.Iic t = ∅ :=
      Set.eq_empty_iff_forall_notMem.mpr fun s hs =>
        absurd (lt_of_lt_of_le hs.1.1 hs.2) (not_lt.mpr (not_lt.mp hi))
    rw [hempty, Set.prod_empty, Set.indicator_empty]
    exact MeasureTheory.stronglyMeasurable_const
/-- A simple integrand with `ℱ`-adapted coefficients is progressively measurable. -/
theorem SimplePredictable.progressivelyMeasurable_eval {T : ℝ} (G : SimplePredictable Ω T)
    (ℱ : Filtration ℝ ‹MeasurableSpace Ω›)
    (h_adapt : ∀ i : Fin G.N, @MeasureTheory.StronglyMeasurable Ω ℝ _
      (ℱ (G.partition i.castSucc)) (G.ξ i)) :
    Probability.ProgressivelyMeasurable ℱ (fun ω s => G.eval s ω) := by
  have hfun : (fun ω s => G.eval s ω)
      = fun ω s => ∑ i : Fin G.N,
        (Set.Ioc (G.partition i.castSucc) (G.partition i.succ)).indicator
          (fun _ => G.ξ i ω) s := by
    funext ω s; exact eval_eq_sum_indicator G s ω
  rw [hfun]
  exact progressivelyMeasurable_sum_indicator_Ioc ℱ _ _ _ h_adapt
/-- A simple integrand times a jointly measurable process is jointly measurable. -/
theorem SimplePredictable.measurable_uncurry_eval_mul {T : ℝ} (G : SimplePredictable Ω T)
    {H : Ω → ℝ → ℝ} (hm : Measurable (Function.uncurry H)) :
    Measurable (Function.uncurry fun ω s => G.eval s ω * H ω s) :=
  G.eval_jointly_measurable.mul hm
/-- A simple integrand with adapted coefficients times a progressively measurable process is
progressively measurable. -/
theorem SimplePredictable.progressivelyMeasurable_eval_mul {T : ℝ} (G : SimplePredictable Ω T)
    (ℱ : Filtration ℝ ‹MeasurableSpace Ω›)
    (h_adapt : ∀ i : Fin G.N, @MeasureTheory.StronglyMeasurable Ω ℝ _
      (ℱ (G.partition i.castSucc)) (G.ξ i))
    {H : Ω → ℝ → ℝ} (hp : Probability.ProgressivelyMeasurable ℱ H) :
    Probability.ProgressivelyMeasurable ℱ fun ω s => G.eval s ω * H ω s :=
  (G.progressivelyMeasurable_eval ℱ h_adapt).mul hp
/-- A simple integrand times a square-integrable process is square-integrable on every
window. -/
theorem SimplePredictable.lintegral_eval_mul_sq_lt_top {T : ℝ} (G : SimplePredictable Ω T)
    {P : Measure Ω} [IsProbabilityMeasure P] {H : Ω → ℝ → ℝ}
    (hq : ∀ T, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    (T' : ℝ) (hT' : 0 < T') :
    ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T',
      (‖G.eval s ω * H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤ := by
  obtain ⟨B, hB0, hB⟩ := G.exists_eval_bound
  have hbd : ∀ s ω, (‖G.eval s ω‖₊ : ℝ≥0∞) ≤ ENNReal.ofReal B := by
    intro s ω
    calc (‖G.eval s ω‖₊ : ℝ≥0∞)
        = ENNReal.ofReal ‖G.eval s ω‖ := by
          rw [ENNReal.ofReal_eq_coe_nnreal (norm_nonneg _)]; rfl
      _ ≤ ENNReal.ofReal B :=
          ENNReal.ofReal_le_ofReal ((Real.norm_eq_abs _).le.trans (hB s ω))
  have hpt : ∀ s ω, (‖G.eval s ω * H ω s‖₊ : ℝ≥0∞) ^ 2
      ≤ ENNReal.ofReal B ^ 2 * (‖H ω s‖₊ : ℝ≥0∞) ^ 2 := by
    intro s ω
    rw [nnnorm_mul, ENNReal.coe_mul, mul_pow]
    gcongr
    exact hbd s ω
  have hne : ENNReal.ofReal B ^ 2 ≠ ⊤ := (ENNReal.pow_lt_top ENNReal.ofReal_lt_top).ne
  calc ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T',
          (‖G.eval s ω * H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P
      ≤ ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T',
          ENNReal.ofReal B ^ 2 * (‖H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P :=
        lintegral_mono fun ω => lintegral_mono fun s => hpt s ω
    _ = ENNReal.ofReal B ^ 2 * ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T',
          (‖H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P := by
        rw [← MeasureTheory.lintegral_const_mul' _ _ hne]
        exact lintegral_congr fun ω => MeasureTheory.lintegral_const_mul' _ _ hne
    _ < ⊤ := ENNReal.mul_lt_top (lt_top_iff_ne_top.mpr hne) (hq T' hT')
end Ito
end Brownian
end LevyStochCalc


