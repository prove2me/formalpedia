-- Prove2me | Definitions.Def_SourceProof_5731c142c22a48f56440eba3
-- name    : SourceProof_5731c142c22a48f56440eba3
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T15:40:57.255643+00:00
-- url     : https://prove2.me/theorems/1f09574e-e5ca-45bf-ae9c-e8bcb23281c1
-- title:
--   LevyStochCalc source module: SourceProof_5731c142c22a48f56440eba3
-- statement:
--   The original source theorem `LevyStochCalc.Brownian.Ito.predictableDyadicSimple_brownian_L2_converges` comes from the `LevyStochCalc.Brownian.ItoDensityPredictableL2` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Batteries.Tactic.OpenPrivate
import Definitions.Def_LevyStochCalc_Brownian_ItoDensityPredictableL2_F000
import Definitions.Def_SourceProof_a308b15a3bf4c276a3bdd5fc

open private predictableDyadicSimple_brownian_ae_tendsto from Definitions.Def_LevyStochCalc_Brownian_ItoDensityPredictableL2_F000
/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# `L²` convergence of the predictable dyadic approximations

For a bounded jointly measurable integrand the left-shifted dyadic simple processes
converge to it in `L²(Ω × [0,T])`, giving density of the simple predictable processes and
of the adapted simple processes in the bounded case, joint measurability of the evaluation
map and the `L²` Cauchy property of the approximating sequence.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
-- `open Classical` is avoided at file scope; explicit decidability is used.

namespace LevyStochCalc.Brownian.Ito

universe u

variable {Ω : Type u} [MeasurableSpace Ω]


theorem _root_.Prove2MeSourceProof.h_5731c142c22a48f56440eba3
    {P : Measure Ω} [IsProbabilityMeasure P]
    {T : ℝ} (hT : 0 < T)
    (g : Ω → ℝ → ℝ)
    (h_meas : Measurable (Function.uncurry g))
    (M : ℝ) (h_bound : ∀ ω s, |g ω s| ≤ M) :
    Filter.Tendsto
      (fun n => ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
        (‖g ω s - (predictableDyadicSimple_brownian hT g h_meas M h_bound n).eval s ω‖₊
          : ℝ≥0∞) ^ 2 ∂volume ∂P)
      Filter.atTop (nhds 0) := by
  haveI h_finite_vol : MeasureTheory.IsFiniteMeasure
      (volume.restrict (Set.Icc (0 : ℝ) T)) := by
    refine ⟨?_⟩
    rw [MeasureTheory.Measure.restrict_apply MeasurableSet.univ, Set.univ_inter,
        Real.volume_Icc]
    exact ENNReal.ofReal_lt_top
  haveI h_finite_prod : MeasureTheory.IsFiniteMeasure
      (P.prod (volume.restrict (Set.Icc (0 : ℝ) T))) := inferInstance
  -- Bound: 2(|M|+1) ≥ |g - eval|.
  set CC : ℝ := 2 * (|M| + 1) with hCC
  have hCC_pos : (0 : ℝ) < CC := by
    have : (0 : ℝ) ≤ |M| := abs_nonneg _
    rw [hCC]; linarith
  have hCC_nn : (0 : ℝ) ≤ CC := le_of_lt hCC_pos
  set F : ℕ → Ω × ℝ → ℝ≥0∞ := fun n p =>
    (‖g p.1 p.2 -
       (LevyStochCalc.Brownian.Ito.predictableDyadicSimple_brownian hT g h_meas M h_bound n).eval p.2 p.1‖₊
        : ℝ≥0∞) ^ 2 with hF_def
  have h_F_bound : ∀ n p, F n p ≤ ENNReal.ofReal (CC ^ 2) := by
    intro n p
    have h_norm_le : ‖g p.1 p.2 -
        (LevyStochCalc.Brownian.Ito.predictableDyadicSimple_brownian hT g h_meas M h_bound n).eval p.2 p.1‖
        ≤ CC := by
      rw [Real.norm_eq_abs]
      have h1 : |g p.1 p.2| ≤ M := h_bound p.1 p.2
      have h2 : |(LevyStochCalc.Brownian.Ito.predictableDyadicSimple_brownian hT g h_meas M h_bound n).eval p.2 p.1|
          ≤ max M 0 :=
        _root_.Prove2MeSourceProof.h_a308b15a3bf4c276a3bdd5fc hT g h_meas M h_bound n p.2 p.1
      have h_abs_M : M ≤ |M| := le_abs_self _
      have h_max_le : max M 0 ≤ |M| + 1 := by
        by_cases hM : M ≤ 0
        · rw [max_eq_right hM]
          have : (0 : ℝ) ≤ |M| := abs_nonneg _
          linarith
        · push Not at hM
          rw [max_eq_left hM.le]
          linarith [le_abs_self M]
      have h12 : |g p.1 p.2 -
          (LevyStochCalc.Brownian.Ito.predictableDyadicSimple_brownian hT g h_meas M h_bound n).eval p.2 p.1|
          ≤ |g p.1 p.2| +
              |(LevyStochCalc.Brownian.Ito.predictableDyadicSimple_brownian hT g h_meas M h_bound n).eval p.2 p.1| :=
        abs_sub _ _
      rw [hCC]; linarith
    have h_norm_nn : 0 ≤ ‖g p.1 p.2 -
        (LevyStochCalc.Brownian.Ito.predictableDyadicSimple_brownian hT g h_meas M h_bound n).eval p.2 p.1‖ :=
      norm_nonneg _
    change (‖g p.1 p.2 -
       (LevyStochCalc.Brownian.Ito.predictableDyadicSimple_brownian hT g h_meas M h_bound n).eval p.2 p.1‖₊
        : ℝ≥0∞) ^ 2 ≤ ENNReal.ofReal (CC ^ 2)
    have : ((‖g p.1 p.2 -
       (LevyStochCalc.Brownian.Ito.predictableDyadicSimple_brownian hT g h_meas M h_bound n).eval p.2 p.1‖₊
        : ℝ≥0∞)) = ENNReal.ofReal ‖g p.1 p.2 -
       (LevyStochCalc.Brownian.Ito.predictableDyadicSimple_brownian hT g h_meas M h_bound n).eval p.2 p.1‖ :=
      (ofReal_norm _).symm
    rw [this, ← ENNReal.ofReal_pow h_norm_nn]
    apply ENNReal.ofReal_le_ofReal
    nlinarith [sq_nonneg (g p.1 p.2 -
       (LevyStochCalc.Brownian.Ito.predictableDyadicSimple_brownian hT g h_meas M h_bound n).eval p.2 p.1)]
  have h_F_meas : ∀ n, Measurable (F n) := by
    intro n
    change Measurable (fun (p : Ω × ℝ) => (‖g p.1 p.2 -
       (LevyStochCalc.Brownian.Ito.predictableDyadicSimple_brownian hT g h_meas M h_bound n).eval p.2 p.1‖₊
        : ℝ≥0∞) ^ 2)
    have h_eval_meas : Measurable (fun p : Ω × ℝ =>
        (LevyStochCalc.Brownian.Ito.predictableDyadicSimple_brownian hT g h_meas M h_bound n).eval p.2 p.1) := by
      unfold LevyStochCalc.Brownian.Ito.SimplePredictable.eval
      refine Finset.measurable_sum _ ?_
      intro i _
      refine Measurable.ite ?_ ?_ measurable_const
      · refine MeasurableSet.inter ?_ ?_
        · exact measurable_snd (measurableSet_Ioi
            (a := (LevyStochCalc.Brownian.Ito.predictableDyadicSimple_brownian hT g h_meas M h_bound n).partition
              i.castSucc))
        · exact measurable_snd (measurableSet_Iic
            (a := (LevyStochCalc.Brownian.Ito.predictableDyadicSimple_brownian hT g h_meas M h_bound n).partition
              i.succ))
      · exact (LevyStochCalc.Brownian.Ito.dyadicAvg_shifted_brownian_measurable T g h_meas n i).comp measurable_fst
    have h_diff : Measurable (fun p : Ω × ℝ =>
        g p.1 p.2 -
        (LevyStochCalc.Brownian.Ito.predictableDyadicSimple_brownian hT g h_meas M h_bound n).eval p.2 p.1) :=
      (h_meas.comp (by fun_prop : Measurable (fun (p : Ω × ℝ) => (p.1, p.2)))).sub
        h_eval_meas
    exact ((ENNReal.continuous_coe.measurable.comp h_diff.nnnorm)).pow_const 2
  have h_bound_integrable : ∫⁻ _ : Ω × ℝ, ENNReal.ofReal (CC ^ 2)
      ∂(P.prod (volume.restrict (Set.Icc (0 : ℝ) T))) ≠ ⊤ := by
    rw [MeasureTheory.lintegral_const]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (MeasureTheory.measure_ne_top _ _)
  have h_F_ae : ∀ᵐ p ∂(P.prod (volume.restrict (Set.Icc (0 : ℝ) T))),
      Filter.Tendsto (fun n => F n p) Filter.atTop (nhds 0) := by
    have h_ae := predictableDyadicSimple_brownian_ae_tendsto (P := P) hT g h_meas M h_bound
    filter_upwards [h_ae] with p hp
    change Filter.Tendsto (fun n => (‖g p.1 p.2 -
       (LevyStochCalc.Brownian.Ito.predictableDyadicSimple_brownian hT g h_meas M h_bound n).eval p.2 p.1‖₊
        : ℝ≥0∞) ^ 2) Filter.atTop (nhds 0)
    have h_diff_zero : Filter.Tendsto
        (fun n => g p.1 p.2 -
       (LevyStochCalc.Brownian.Ito.predictableDyadicSimple_brownian hT g h_meas M h_bound n).eval p.2 p.1)
        Filter.atTop (nhds 0) := by
      have hp' : Filter.Tendsto
        (fun n => (LevyStochCalc.Brownian.Ito.predictableDyadicSimple_brownian hT g h_meas M h_bound n).eval p.2 p.1)
        Filter.atTop (nhds (g p.1 p.2)) := hp
      have h_const : Filter.Tendsto (fun _ : ℕ => g p.1 p.2)
        Filter.atTop (nhds (g p.1 p.2)) := tendsto_const_nhds
      simpa using h_const.sub hp'
    have h_norm_zero : Filter.Tendsto
        (fun n => ‖g p.1 p.2 -
       (LevyStochCalc.Brownian.Ito.predictableDyadicSimple_brownian hT g h_meas M h_bound n).eval p.2 p.1‖₊)
        Filter.atTop (nhds 0) := by
      rw [show (0 : ℝ≥0) = ‖(0 : ℝ)‖₊ from by simp]
      exact (continuous_nnnorm.tendsto _).comp h_diff_zero
    have h_enorm_zero : Filter.Tendsto
        (fun n => ((‖g p.1 p.2 -
       (LevyStochCalc.Brownian.Ito.predictableDyadicSimple_brownian hT g h_meas M h_bound n).eval p.2 p.1‖₊
        : ℝ≥0∞)))
        Filter.atTop (nhds 0) := by
      rw [show (0 : ℝ≥0∞) = ((0 : ℝ≥0) : ℝ≥0∞) from by simp]
      exact (ENNReal.continuous_coe.tendsto _).comp h_norm_zero
    have h_sq_continuous : Continuous (fun x : ℝ≥0∞ => x ^ 2) :=
      ENNReal.continuous_pow 2
    have : Filter.Tendsto (fun n => ((‖g p.1 p.2 -
       (LevyStochCalc.Brownian.Ito.predictableDyadicSimple_brownian hT g h_meas M h_bound n).eval p.2 p.1‖₊
        : ℝ≥0∞)) ^ 2) Filter.atTop (nhds ((0 : ℝ≥0∞) ^ 2)) :=
      (h_sq_continuous.tendsto _).comp h_enorm_zero
    simpa using this
  have h_DCT : Filter.Tendsto
      (fun n => ∫⁻ p, F n p ∂(P.prod (volume.restrict (Set.Icc (0 : ℝ) T))))
      Filter.atTop (nhds 0) := by
    have h_target : Filter.Tendsto (fun n => ∫⁻ p, F n p
          ∂(P.prod (volume.restrict (Set.Icc (0 : ℝ) T))))
        Filter.atTop
        (nhds (∫⁻ _ : Ω × ℝ, (0 : ℝ≥0∞)
          ∂(P.prod (volume.restrict (Set.Icc (0 : ℝ) T))))) := by
      refine MeasureTheory.tendsto_lintegral_of_dominated_convergence'
        (bound := fun _ => ENNReal.ofReal (CC ^ 2))
        (fun n => (h_F_meas n).aemeasurable)
        ?_ h_bound_integrable h_F_ae
      intro n
      exact Filter.Eventually.of_forall (fun p => h_F_bound n p)
    simpa using h_target
  have h_eq : ∀ n, (∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
        (‖g ω s -
          (LevyStochCalc.Brownian.Ito.predictableDyadicSimple_brownian hT g h_meas M h_bound n).eval s ω‖₊
          : ℝ≥0∞) ^ 2 ∂volume ∂P)
      = ∫⁻ p, F n p ∂(P.prod (volume.restrict (Set.Icc (0 : ℝ) T))) := by
    intro n
    rw [MeasureTheory.lintegral_prod _ (h_F_meas n).aemeasurable]
  simp_rw [h_eq]
  exact h_DCT
-- maxHeartbeats: triangle-inequality lift through nested lintegrals + Tonelli.

end LevyStochCalc.Brownian.Ito


