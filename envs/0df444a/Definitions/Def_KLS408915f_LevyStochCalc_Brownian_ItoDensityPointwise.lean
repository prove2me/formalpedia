-- Prove2me | Definitions.Def_KLS408915f_LevyStochCalc_Brownian_ItoDensityPointwise
-- name    : KLS408915f_LevyStochCalc_Brownian_ItoDensityPointwise
-- status  : Definition
-- author  : @Lazyfill
-- created : 2026-10-23T08:32:14.066486+00:00
-- url     : https://prove2.me/theorems/ae1e6080-5f54-4805-ab83-29019968c1f2
-- title:
--   Pointwise convergence of predictable shifted dyadic approximations
-- statement:
--   Vendored from the LevyStochCalc library (https://github.com/cgarryZA/LevyStochCalc), commit 984dbf0b790031eac05d56fe5a84b65e15e1e932. For a bounded jointly measurable $g:\Omega\times\mathbb R\to\mathbb R$, positive $T$, and fixed $\omega$, `predictable_pointwise_tendsto_per_omega` states that the evaluations of `predictableDyadicSimple_brownian` converge to $g(\omega,s)$ for almost every $s$ with respect to volume restricted to $[0,T]$. The convergence is an a.e. statement on the time interval and uses the left-shifted, preceding-cell averages; no product-measure or $L^2$ conclusion is asserted in this declaration.
-- source:
--   Lean source: https://github.com/cgarryZA/LevyStochCalc/blob/984dbf0b790031eac05d56fe5a84b65e15e1e932/LevyStochCalc/Brownian/ItoDensityPointwise.lean#L408-L584 (repository human-ai-mathematics/kls-lean, commit 408915f, module `LevyStochCalc.Brownian.ItoDensityPointwise`, definition bundle `KLS408915f_LevyStochCalc_Brownian_ItoDensityPointwise`; the repository is private at upload time). Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (Apache-2.0; upstream copyright notice retained in the Lean text).

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
import Definitions.Def_KLS408915f_LevyStochCalc_Brownian_ItoDensityShiftedAverages
import Definitions.Def_KLS408915f_LevyStochCalc_Brownian_ItoSimpleIntegrand
import Definitions.Def_KLS408915f_LevyStochCalc_Brownian_ItoSimpleIsometry
import Definitions.Def_KLS408915f_LevyStochCalc_Brownian_ItoSimpleMoments
import Definitions.Def_KLS408915f_LevyStochCalc_Brownian_Martingale
import Definitions.Def_KLS408915f_LevyStochCalc_Brownian_MartingaleCondExp
import Definitions.Def_KLS408915f_LevyStochCalc_Brownian_Multidim
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
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Brownian/ItoDensityPointwise.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
namespace LevyStochCalc
namespace Brownian
namespace Ito
universe u
variable {Ω : Type u} [MeasurableSpace Ω]
/-- **Pointwise convergence for predictable shifted dyadic.** For each `ω`, the
predictable shifted dyadic SimplePredictable converges to `g(ω, ·)` a.e. on `[0, T]`.

The key difference from `dyadic_pointwise_tendsto_per_omega`: the eval uses the
LEFT-tangent interval `(t_{i-1}, t_i]` instead of the containing interval
`(t_i, t_{i+1}]`. Apply Vitali's differentiation theorem with K = 3 since the
tangent interval is at distance ≤ 3·δ from `s`. -/
lemma predictable_pointwise_tendsto_per_omega
    {T : ℝ} (hT : 0 < T)
    (g : Ω → ℝ → ℝ)
    (h_meas : Measurable (Function.uncurry g))
    (M : ℝ) (h_bound : ∀ ω s, |g ω s| ≤ M)
    (ω : Ω) :
    ∀ᵐ s ∂(volume.restrict (Set.Icc (0 : ℝ) T)),
      Filter.Tendsto
        (fun n => (predictableDyadicSimple_brownian hT g h_meas M h_bound n).eval s ω)
        Filter.atTop (nhds (g ω s)) := by
  -- K = 3 Vitali on g(ω, ·).
  have h_loc_int : MeasureTheory.LocallyIntegrable (g ω) volume :=
    bounded_locallyIntegrable (g ω)
      (h_meas.comp (by fun_prop : Measurable (fun s : ℝ => (ω, s))))
      M (h_bound ω)
  have h_vitali_K3 := IsUnifLocDoublingMeasure.ae_tendsto_average volume h_loc_int 3
  have h_vitali_restrict : ∀ᵐ x ∂(volume.restrict (Set.Icc (0 : ℝ) T)),
      ∀ {ι : Type} {l : Filter ι} (w : ι → ℝ) (δ : ι → ℝ),
        Filter.Tendsto δ l (nhdsWithin 0 (Set.Ioi 0)) →
        (∀ᶠ j in l, x ∈ Metric.closedBall (w j) (3 * δ j)) →
        Filter.Tendsto
          (fun j => ⨍ y in Metric.closedBall (w j) (δ j), g ω y ∂volume) l
            (nhds (g ω x)) :=
    MeasureTheory.ae_restrict_of_ae h_vitali_K3
  -- Exclude {0}.
  have h_pos_ae : ∀ᵐ x ∂(volume : Measure ℝ), x ≠ 0 := by
    rw [MeasureTheory.ae_iff]
    have : {x : ℝ | ¬(x ≠ 0)} = {(0 : ℝ)} := by ext; simp
    rw [this, Real.volume_singleton]
  rw [MeasureTheory.ae_restrict_iff' measurableSet_Icc]
  rw [MeasureTheory.ae_restrict_iff' measurableSet_Icc] at h_vitali_restrict
  filter_upwards [h_vitali_restrict, h_pos_ae] with x h_vitali_at_x hx_ne_zero hx_mem
  have hx_strict_pos : 0 < x := lt_of_le_of_ne hx_mem.1 (Ne.symm hx_ne_zero)
  have hx : 0 < x ∧ x ≤ T := ⟨hx_strict_pos, hx_mem.2⟩
  -- Half-width δ_n = T/2^{n+1}.
  set δ : ℕ → ℝ := fun n => T / (2 * (2 ^ n : ℕ)) with hδ_def
  -- Center w_n = (i - 1/2) * T/2^n.  For i ≥ 1, this is the midpoint of (t_{i-1}, t_i].
  -- For i = 0 (which is eventually false), this is a dummy value.
  set w : ℕ → ℝ := fun n =>
    (((dyadicIndex n T hT x hx).val : ℝ) - 1/2) * (T / ((2 ^ n : ℕ) : ℝ))
    with hw_def
  -- δ → 0 in nhdsWithin 0 (Ioi 0).
  have h_delta_pos : ∀ n, 0 < δ n := fun n => by
    change 0 < T / (2 * (2 ^ n : ℕ))
    have : (0 : ℝ) < 2 * (2 ^ n : ℕ) := by positivity
    exact div_pos hT this
  have h_delta_to_zero : Filter.Tendsto δ Filter.atTop (nhds 0) := by
    have h_2pow : Filter.Tendsto (fun n : ℕ => 2 * ((2 ^ n : ℕ) : ℝ))
        Filter.atTop Filter.atTop := by
      have h_pow_atTop : Filter.Tendsto (fun n : ℕ => ((2 ^ n : ℕ) : ℝ))
          Filter.atTop Filter.atTop := by
        have : Filter.Tendsto (fun n : ℕ => (2 ^ n : ℕ)) Filter.atTop Filter.atTop :=
          tendsto_pow_atTop_atTop_of_one_lt (by norm_num : 1 < 2)
        exact tendsto_natCast_atTop_iff.mpr this
      exact h_pow_atTop.atTop_mul_const' (by norm_num : (0 : ℝ) < 2) |>.congr
        (fun n => by ring)
    exact Filter.Tendsto.div_atTop tendsto_const_nhds h_2pow
  have h_delta_tendsto : Filter.Tendsto δ Filter.atTop (nhdsWithin 0 (Set.Ioi 0)) := by
    rw [tendsto_nhdsWithin_iff]
    refine ⟨h_delta_to_zero, ?_⟩
    exact Filter.Eventually.of_forall h_delta_pos
  -- Eventually 0 < (dyadicIndex n s).val (i.e., for n large, i ≥ 1).
  have h_eventually_i_pos :
      ∀ᶠ n in Filter.atTop, 0 < (dyadicIndex n T hT x hx).val := by
    -- For n large enough, T/2^n < x → t_1 ≤ x → i ≥ 1.
    have h_pow_to_inf : Filter.Tendsto (fun n : ℕ => ((2 ^ n : ℕ) : ℝ))
        Filter.atTop Filter.atTop := by
      have : Filter.Tendsto (fun n : ℕ => (2 ^ n : ℕ)) Filter.atTop Filter.atTop :=
        tendsto_pow_atTop_atTop_of_one_lt (by norm_num : 1 < 2)
      exact tendsto_natCast_atTop_iff.mpr this
    have h_T_div_pow : Filter.Tendsto (fun n : ℕ => T / ((2 ^ n : ℕ) : ℝ))
        Filter.atTop (nhds 0) :=
      Filter.Tendsto.div_atTop tendsto_const_nhds h_pow_to_inf
    have h_evnt : ∀ᶠ n in Filter.atTop, T / ((2 ^ n : ℕ) : ℝ) < x := by
      have := h_T_div_pow.eventually_lt_const hx_strict_pos
      exact this
    filter_upwards [h_evnt] with n hn
    -- (dyadicIndex n T hT x hx).val > 0: from dyadicIndex_mem, t_i < x ≤ t_{i+1}.
    -- If i.val = 0, then t_i = 0 and t_{i+1} = T/2^n. Since t_{i+1} ≥ x means
    -- T/2^n ≥ x, contradicting hn.
    by_contra h_not_pos
    push Not at h_not_pos
    have h_i_zero : (dyadicIndex n T hT x hx).val = 0 := Nat.eq_zero_of_le_zero h_not_pos
    have hi_mem := dyadicIndex_mem n T hT x hx
    have h_x_le : x ≤ T / ((2 ^ n : ℕ) : ℝ) := by
      have := hi_mem.2
      simp only [h_i_zero, Nat.cast_zero, zero_add, one_mul] at this
      exact this
    linarith
  -- For n with i ≥ 1, x ∈ closedBall(w_n, 3 δ_n).
  have h_x_in_ball_eventually : ∀ᶠ n in Filter.atTop,
      x ∈ Metric.closedBall (w n) (3 * δ n) := by
    filter_upwards [h_eventually_i_pos] with n hn_i_pos
    change |x - w n| ≤ 3 * δ n
    have hi_mem := dyadicIndex_mem n T hT x hx
    have h_x_lower : ((dyadicIndex n T hT x hx).val : ℝ) * T / ((2 ^ n : ℕ) : ℝ) < x :=
      hi_mem.1
    have h_x_upper :
        x ≤ (((dyadicIndex n T hT x hx).val : ℝ) + 1) * T / ((2 ^ n : ℕ) : ℝ) := by
      exact_mod_cast hi_mem.2
    set i_val : ℝ := ((dyadicIndex n T hT x hx).val : ℝ) with hi_val
    have h_pos_real : (0 : ℝ) < (2 ^ n : ℕ) := by positivity
    have h_pow_ne : ((2 ^ n : ℕ) : ℝ) ≠ 0 := ne_of_gt h_pos_real
    change |x - (i_val - 1/2) * (T / ((2 ^ n : ℕ) : ℝ))| ≤ 3 * (T / (2 * (2 ^ n : ℕ)))
    rw [abs_le]
    constructor
    · -- Lower bound: x - w_n ≥ -(3 * δ_n).
      have h_x_lower' : i_val * T / ((2 ^ n : ℕ) : ℝ) ≤ x := le_of_lt h_x_lower
      have h_alg : i_val * T / ((2 ^ n : ℕ) : ℝ) - (i_val - 1/2) * (T / ((2 ^ n : ℕ) : ℝ)) =
          T / (2 * ((2 ^ n : ℕ) : ℝ)) := by
        field_simp; ring
      have h_3delta_pos : 0 < 3 * (T / (2 * ((2 ^ n : ℕ) : ℝ))) := by positivity
      linarith
    · -- Upper: x - w_n ≤ 3 δ_n.
      have h_alg :
          (i_val + 1) * T / ((2 ^ n : ℕ) : ℝ)
            - (i_val - 1/2) * (T / ((2 ^ n : ℕ) : ℝ))
            = 3 * (T / (2 * ((2 ^ n : ℕ) : ℝ))) := by
        field_simp; ring
      linarith
  -- Apply Vitali theorem.
  have h_avg_to_g := h_vitali_at_x hx_mem (l := Filter.atTop) w δ
    h_delta_tendsto h_x_in_ball_eventually
  -- Bridge: ⨍ over closedBall = predictable.eval (eventually).
  have h_bridge : ∀ᶠ n in Filter.atTop,
      (predictableDyadicSimple_brownian hT g h_meas M h_bound n).eval x ω =
      ⨍ y in Metric.closedBall (w n) (δ n), g ω y ∂volume := by
    filter_upwards [h_eventually_i_pos] with n hn_i_pos
    rw [predictableDyadicSimple_brownian_eval_eq_shifted hT g h_meas M h_bound n x hx ω]
    -- dyadicAvg_shifted T g n i ω = dyadicAvg_brownian g n ⟨i.val - 1, _⟩ ω (since i ≥ 1)
    -- = ⨍ over closedBall(midpt of (t_{i-1}, t_i], T/2^{n+1}) g(ω, ·)
    unfold dyadicAvg_shifted_brownian
    rw [dif_neg (by omega : ¬ (dyadicIndex n T hT x hx).val = 0)]
    have h_lt : (dyadicIndex n T hT x hx).val - 1 < 2 ^ n := by
      have := (dyadicIndex n T hT x hx).isLt; omega
    set i' : Fin (2 ^ n) := ⟨(dyadicIndex n T hT x hx).val - 1, h_lt⟩
    rw [dyadicAvg_brownian_eq_average_closedBall hT g n i' ω]
    -- Now match w_n and δ_n with the closedBall arguments.
    have h_w_eq : w n =
        (dyadicPartition_brownian T n i'.castSucc +
          dyadicPartition_brownian T n i'.succ) / 2 := by
      change (((dyadicIndex n T hT x hx).val : ℝ) - 1/2) *
          (T / ((2 ^ n : ℕ) : ℝ)) = _
      unfold dyadicPartition_brownian
      simp only [Fin.val_succ, Fin.val_castSucc]
      have h_pow_pos : (0 : ℝ) < ((2 ^ n : ℕ) : ℝ) := by positivity
      have h_pow_ne : ((2 ^ n : ℕ) : ℝ) ≠ 0 := ne_of_gt h_pow_pos
      have h_sub_cast :
          (((dyadicIndex n T hT x hx).val - 1 : ℕ) : ℝ) =
            ((dyadicIndex n T hT x hx).val : ℝ) - 1 := by
        rw [Nat.cast_sub (by omega : 1 ≤ (dyadicIndex n T hT x hx).val)]
        simp
      rw [h_sub_cast]
      have h_add_one_cast :
          ((((dyadicIndex n T hT x hx).val - 1 : ℕ) + 1 : ℕ) : ℝ) =
            ((dyadicIndex n T hT x hx).val : ℝ) := by
        rw [show ((dyadicIndex n T hT x hx).val - 1 : ℕ) + 1 = (dyadicIndex n T hT x hx).val from
          by omega]
      rw [h_add_one_cast]
      field_simp
      ring
    have h_delta_eq : δ n = (dyadicPartition_brownian T n i'.succ -
        dyadicPartition_brownian T n i'.castSucc) / 2 := by
      rw [dyadicPartition_brownian_diff n i']
      change T / (2 * ((2 ^ n : ℕ) : ℝ)) = T / ((2 ^ n : ℕ) : ℝ) / 2
      field_simp
    rw [h_w_eq, h_delta_eq]
  refine Filter.Tendsto.congr' ?_ h_avg_to_g
  filter_upwards [h_bridge] with n hn
  exact hn.symm
end Ito
end Brownian
end LevyStochCalc


