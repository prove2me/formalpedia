-- Prove2me | Definitions.Def_KLS408915f_LevyStochCalc_Brownian_ItoSimpleIsometry
-- name    : KLS408915f_LevyStochCalc_Brownian_ItoSimpleIsometry
-- status  : Definition
-- author  : @Lazyfill
-- created : 2026-10-23T08:23:03.145826+00:00
-- url     : https://prove2.me/theorems/2b12c3c8-9a8a-4efc-8974-13d664872c52
-- title:
--   Itô isometry for simple predictable integrands
-- statement:
--   Vendored from LevyStochCalc, repository https://github.com/cgarryZA/LevyStochCalc, commit 984dbf0b790031eac05d56fe5a84b65e15e1e932. For a Brownian motion W, a Brownian filtration ℱ, a positive terminal time T, and a simple predictable H whose coefficients are adapted to the left partition times, `simpleIntegral_isometry` states that the lower integral of the squared nonnegative norm of `simpleIntegral W H T` equals the lower integral over Ω and [0,T] of the squared nonnegative norm of `H.eval`. The intermediate `simpleIntegral_sq_lintegral_eq` reduces the left side to the finite sum of interval lengths times coefficient energies, while the embedded private Bochner result reduces the corresponding real integral using diagonal and off-diagonal moment identities.
-- source:
--   Lean source: https://github.com/cgarryZA/LevyStochCalc/blob/984dbf0b790031eac05d56fe5a84b65e15e1e932/LevyStochCalc/Brownian/ItoSimpleIsometry.lean#L28-L196 (repository human-ai-mathematics/kls-lean, commit 408915f, module `LevyStochCalc.Brownian.ItoSimpleIsometry`, definition bundle `KLS408915f_LevyStochCalc_Brownian_ItoSimpleIsometry`; the repository is private at upload time). Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (Apache-2.0; upstream copyright notice retained in the Lean text).

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
import Definitions.Def_KLS408915f_LevyStochCalc_Brownian_ItoSimpleIntegrand
import Definitions.Def_KLS408915f_LevyStochCalc_Brownian_ItoSimpleMoments
import Definitions.Def_KLS408915f_LevyStochCalc_Brownian_Martingale
import Definitions.Def_KLS408915f_LevyStochCalc_Brownian_MartingaleCondExp
import Definitions.Def_KLS408915f_LevyStochCalc_Brownian_Multidim
import Definitions.Def_KLS408915f_LevyStochCalc_Martingale_RightCont
import Definitions.Def_KLS408915f_LevyStochCalc_Probability_IndepJoin
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
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.MeanInequalities
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
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Brownian/ItoSimpleIsometry.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
namespace LevyStochCalc
namespace Brownian
namespace Ito
universe u
variable {Ω : Type u} [MeasurableSpace Ω]
set_option maxHeartbeats 800000 in
-- maxHeartbeats: typechecker budget for proof-heavy goal below.
/-- **Bochner LHS reduction for Brownian.** -/
 lemma simpleIntegral_sq_bochner_eq
    {P : Measure Ω} [IsProbabilityMeasure P]
    (W : LevyStochCalc.Brownian.BrownianMotion P)
    (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (hℱ : IsBrownianFiltration W ℱ)
    {T : ℝ} (H : SimplePredictable Ω T)
    (h_adapt : ∀ i : Fin H.N, @MeasureTheory.StronglyMeasurable Ω ℝ _
      (ℱ (H.partition i.castSucc)) (H.ξ i)) :
    ∫ ω, (∑ i : Fin H.N, H.ξ i ω * (W.W (H.partition i.succ) ω
                                  - W.W (H.partition i.castSucc) ω))^2 ∂P
      = ∑ i : Fin H.N,
        (H.partition i.succ - H.partition i.castSucc) *
        ∫ ω, (H.ξ i ω)^2 ∂P := by
  -- Expand (∑ a_i)² = ∑_{i,j} a_i a_j via Finset.sum_mul_sum.
  have h_expand : ∀ ω,
      (∑ i : Fin H.N, H.ξ i ω * (W.W (H.partition i.succ) ω
                                - W.W (H.partition i.castSucc) ω))^2
      = ∑ i : Fin H.N, ∑ j : Fin H.N,
          (H.ξ i ω * (W.W (H.partition i.succ) ω
                    - W.W (H.partition i.castSucc) ω)) *
          (H.ξ j ω * (W.W (H.partition j.succ) ω
                    - W.W (H.partition j.castSucc) ω)) := by
    intro ω; rw [sq]; exact Finset.sum_mul_sum _ _ _ _
  rw [show (fun ω => (∑ i : Fin H.N, H.ξ i ω * (W.W (H.partition i.succ) ω
                                  - W.W (H.partition i.castSucc) ω))^2)
        = fun ω => ∑ i : Fin H.N, ∑ j : Fin H.N,
            (H.ξ i ω * (W.W (H.partition i.succ) ω
                      - W.W (H.partition i.castSucc) ω)) *
            (H.ξ j ω * (W.W (H.partition j.succ) ω
                      - W.W (H.partition j.castSucc) ω)) from funext h_expand]
  rw [MeasureTheory.integral_finsetSum _
    (fun i _ => MeasureTheory.integrable_finsetSum _
      (fun j _ => cross_sq_integrable W H i j))]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [MeasureTheory.integral_finsetSum _
    (fun j _ => cross_sq_integrable W H i j)]
  rw [Finset.sum_eq_single i]
  · -- j = i: diagonal Bochner
    have h_part_nn : 0 ≤ H.partition i.castSucc := by
      have : H.partition 0 ≤ H.partition i.castSucc :=
        H.partition_strictMono.monotone (Fin.zero_le _)
      rw [H.partition_zero] at this; exact this
    rw [show (fun ω => (H.ξ i ω * (W.W (H.partition i.succ) ω
                                  - W.W (H.partition i.castSucc) ω)) *
                       (H.ξ i ω * (W.W (H.partition i.succ) ω
                                  - W.W (H.partition i.castSucc) ω)))
          = fun ω => (H.ξ i ω * (W.W (H.partition i.succ) ω
                                - W.W (H.partition i.castSucc) ω))^2 from by
      funext ω; ring]
    exact simpleIntegral_diagonal_bochner W ℱ hℱ H i h_part_nn (h_adapt i)
  · -- j ≠ i: offDiagonal (with symmetry)
    intro j _ hj
    rcases lt_or_gt_of_ne hj with h_lt | h_gt
    · rw [show (fun ω => (H.ξ i ω * (W.W (H.partition i.succ) ω
                                  - W.W (H.partition i.castSucc) ω)) *
                         (H.ξ j ω * (W.W (H.partition j.succ) ω
                                  - W.W (H.partition j.castSucc) ω)))
            = fun ω => (H.ξ j ω * (W.W (H.partition j.succ) ω
                                  - W.W (H.partition j.castSucc) ω)) *
                       (H.ξ i ω * (W.W (H.partition i.succ) ω
                                  - W.W (H.partition i.castSucc) ω)) from by
        funext ω; ring]
      exact simpleIntegral_offDiagonal W ℱ hℱ H h_lt (h_adapt j) (h_adapt i)
    · exact simpleIntegral_offDiagonal W ℱ hℱ H h_gt (h_adapt i) (h_adapt j)
  · intro h_not; exact absurd (Finset.mem_univ _) h_not
set_option maxHeartbeats 800000 in
-- maxHeartbeats: typechecker budget for proof-heavy goal below.
/-- **LHS reduction for Brownian Itô isometry on simples.** -/
lemma simpleIntegral_sq_lintegral_eq
    {P : Measure Ω} [IsProbabilityMeasure P]
    (W : LevyStochCalc.Brownian.BrownianMotion P)
    (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (hℱ : IsBrownianFiltration W ℱ)
    {T : ℝ} (H : SimplePredictable Ω T)
    (h_adapt : ∀ i : Fin H.N, @MeasureTheory.StronglyMeasurable Ω ℝ _
      (ℱ (H.partition i.castSucc)) (H.ξ i)) :
    ∫⁻ ω, (‖simpleIntegral W H T ω‖₊ : ℝ≥0∞) ^ 2 ∂P
      = ∑ i : Fin H.N,
        ENNReal.ofReal (H.partition i.succ - H.partition i.castSucc) *
        ∫⁻ ω, (‖H.ξ i ω‖₊ : ℝ≥0∞) ^ 2 ∂P := by
  -- Expand simpleIntegral via simpleIntegral_eq_sum.
  simp_rw [simpleIntegral_eq_sum W H]
  -- Convert (‖x‖)² to ENNReal.ofReal(x²).
  have h_norm_sq_eq : ∀ x : ℝ, (‖x‖₊ : ℝ≥0∞)^2 = ENNReal.ofReal (x^2) := fun x => by
    rw [show (‖x‖₊ : ℝ≥0∞) = ENNReal.ofReal ‖x‖ from ofReal_norm x |>.symm]
    rw [← ENNReal.ofReal_pow (norm_nonneg _)]
    rw [show ‖x‖^2 = x^2 from by rw [Real.norm_eq_abs, sq_abs]]
  rw [show (∫⁻ ω, (‖∑ i : Fin H.N, H.ξ i ω * (W.W (H.partition i.succ) ω
                  - W.W (H.partition i.castSucc) ω)‖₊ : ℝ≥0∞) ^ 2 ∂P)
        = ∫⁻ ω, ENNReal.ofReal
            ((∑ i : Fin H.N, H.ξ i ω * (W.W (H.partition i.succ) ω
                  - W.W (H.partition i.castSucc) ω))^2) ∂P from
    MeasureTheory.lintegral_congr (fun ω => h_norm_sq_eq _)]
  -- Integrability of squared sum.
  have h_int_sum_sq : MeasureTheory.Integrable
      (fun ω => (∑ i : Fin H.N, H.ξ i ω * (W.W (H.partition i.succ) ω
                  - W.W (H.partition i.castSucc) ω))^2) P := by
    have h_eq : ∀ ω, (∑ i : Fin H.N, H.ξ i ω * (W.W (H.partition i.succ) ω
                                  - W.W (H.partition i.castSucc) ω))^2
                = ∑ i : Fin H.N, ∑ j : Fin H.N,
                  (H.ξ i ω * (W.W (H.partition i.succ) ω
                            - W.W (H.partition i.castSucc) ω)) *
                  (H.ξ j ω * (W.W (H.partition j.succ) ω
                            - W.W (H.partition j.castSucc) ω)) := by
      intro ω; rw [sq]; exact Finset.sum_mul_sum _ _ _ _
    rw [show (fun ω => (∑ i, H.ξ i ω * (W.W (H.partition i.succ) ω
                  - W.W (H.partition i.castSucc) ω))^2)
          = fun ω => ∑ i : Fin H.N, ∑ j : Fin H.N,
              (H.ξ i ω * (W.W (H.partition i.succ) ω
                        - W.W (H.partition i.castSucc) ω)) *
              (H.ξ j ω * (W.W (H.partition j.succ) ω
                        - W.W (H.partition j.castSucc) ω)) from funext h_eq]
    refine MeasureTheory.integrable_finsetSum _ (fun i _ => ?_)
    refine MeasureTheory.integrable_finsetSum _ (fun j _ => ?_)
    exact cross_sq_integrable W H i j
  have h_nn_sum_sq :
      0 ≤ᵐ[P] fun ω => (∑ i : Fin H.N, H.ξ i ω * (W.W (H.partition i.succ) ω
                  - W.W (H.partition i.castSucc) ω))^2 := by
    filter_upwards with ω; exact sq_nonneg _
  rw [← MeasureTheory.ofReal_integral_eq_lintegral_ofReal h_int_sum_sq h_nn_sum_sq]
  rw [LevyStochCalc.Brownian.Ito.simpleIntegral_sq_bochner_eq W ℱ hℱ H h_adapt]
  rw [show ENNReal.ofReal (∑ i : Fin H.N,
            (H.partition i.succ - H.partition i.castSucc) * ∫ ω, (H.ξ i ω)^2 ∂P)
        = ∑ i : Fin H.N,
          ENNReal.ofReal
            ((H.partition i.succ - H.partition i.castSucc) * ∫ ω, (H.ξ i ω)^2 ∂P) from by
    rw [ENNReal.ofReal_sum_of_nonneg]
    intro i _
    refine mul_nonneg ?_ (MeasureTheory.integral_nonneg (fun ω => sq_nonneg _))
    have : H.partition i.castSucc < H.partition i.succ :=
      H.partition_strictMono Fin.castSucc_lt_succ
    linarith]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  obtain ⟨M, hM⟩ := H.ξ_bounded i
  have h_xi_sq_bound : ∀ ω : Ω, (H.ξ i ω)^2 ≤ M^2 := fun ω =>
    sq_le_sq' (neg_le_of_abs_le (hM ω)) (le_of_abs_le (hM ω))
  have h_int_xi_sq : MeasureTheory.Integrable (fun ω => (H.ξ i ω)^2) P := by
    refine MeasureTheory.Integrable.mono' (g := fun _ : Ω => M^2)
      (MeasureTheory.integrable_const _) ?_ ?_
    · exact ((H.ξ_measurable i).pow_const 2).aestronglyMeasurable
    · filter_upwards with ω
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      exact h_xi_sq_bound ω
  have h_nn_xi_sq : 0 ≤ᵐ[P] fun ω => (H.ξ i ω)^2 := by
    filter_upwards with ω; positivity
  have h_dt_nn : 0 ≤ H.partition i.succ - H.partition i.castSucc :=
    sub_nonneg.mpr (le_of_lt (H.partition_strictMono Fin.castSucc_lt_succ))
  rw [ENNReal.ofReal_mul h_dt_nn]
  rw [MeasureTheory.ofReal_integral_eq_lintegral_ofReal h_int_xi_sq h_nn_xi_sq]
  rw [show (fun ω => ENNReal.ofReal ((H.ξ i ω)^2))
        = fun ω => (‖H.ξ i ω‖₊ : ℝ≥0∞) ^ 2 from
    funext (fun ω => (h_norm_sq_eq _).symm)]
/-- **Itô isometry on simple integrands.** The L²-norm of the simple integral
equals the L²-norm of the integrand against `dP ⊗ ds`. -/
lemma simpleIntegral_isometry
    {P : Measure Ω} [IsProbabilityMeasure P]
    (W : LevyStochCalc.Brownian.BrownianMotion P)
    (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (hℱ : IsBrownianFiltration W ℱ)
    {T : ℝ} (_hT : 0 < T) (H : SimplePredictable Ω T)
    (h_adapt : ∀ i : Fin H.N, @MeasureTheory.StronglyMeasurable Ω ℝ _
      (ℱ (H.partition i.castSucc)) (H.ξ i)) :
    ∫⁻ ω, (‖simpleIntegral W H T ω‖₊ : ℝ≥0∞) ^ 2 ∂P =
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
        (‖H.eval s ω‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P := by
  rw [simpleIntegral_sq_lintegral_eq W ℱ hℱ H h_adapt]
  rw [lintegral_eval_sq_outer H]
end Ito
end Brownian
end LevyStochCalc


