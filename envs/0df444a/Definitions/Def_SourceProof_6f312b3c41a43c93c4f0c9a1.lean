-- Prove2me | Definitions.Def_SourceProof_6f312b3c41a43c93c4f0c9a1
-- name    : SourceProof_6f312b3c41a43c93c4f0c9a1
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T15:11:49.121428+00:00
-- url     : https://prove2.me/theorems/ca79f2e4-62ff-4b26-aab9-4c6164e83fab
-- title:
--   LevyStochCalc source module: SourceProof_6f312b3c41a43c93c4f0c9a1
-- statement:
--   The original source theorem `LevyStochCalc.Brownian.Ito.L2_cauchy_of_L2_tendsto_brownian` comes from the `LevyStochCalc.Brownian.ItoDensityPredictableL2` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Brownian_ItoDensityPointwise_F000
import Definitions.Def_SourceProof_e4a003adac246e81fe5cee0f

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

-- maxHeartbeats: triangle-inequality lift through nested lintegrals + Tonelli.
set_option maxHeartbeats 1600000 in
-- maxHeartbeats: typechecker budget for proof-heavy goal below.

theorem _root_.Prove2MeSourceProof.h_6f312b3c41a43c93c4f0c9a1
    {P : Measure Ω} [IsProbabilityMeasure P]
    {T : ℝ}
    (Hn : ℕ → SimplePredictable Ω T)
    (H : Ω → ℝ → ℝ)
    (h_meas_eval : ∀ n, Measurable (fun (p : Ω × ℝ) => (Hn n).eval p.2 p.1))
    (h_meas_H : Measurable (Function.uncurry H))
    (h_tendsto : Filter.Tendsto
      (fun n => ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
        (‖H ω s - (Hn n).eval s ω‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P)
      Filter.atTop (nhds 0)) :
    ∀ ε : ℝ≥0∞, 0 < ε → ∃ N : ℕ, ∀ n m : ℕ, N ≤ n → N ≤ m →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
        (‖(Hn n).eval s ω - (Hn m).eval s ω‖₊ : ℝ≥0∞) ^ 2
          ∂volume ∂P < ε := by
  intro ε hε_pos
  have hε4_pos : (0 : ℝ≥0∞) < ε / 4 := by
    rw [ENNReal.div_pos_iff]
    refine ⟨hε_pos.ne', ?_⟩
    decide
  have h_eventually := h_tendsto.eventually_lt_const hε4_pos
  rw [Filter.eventually_atTop] at h_eventually
  obtain ⟨N, hN⟩ := h_eventually
  refine ⟨N, fun n m hn hm => ?_⟩
  have h_pointwise : ∀ ω s,
      (‖(Hn n).eval s ω - (Hn m).eval s ω‖₊ : ℝ≥0∞) ^ 2
      ≤ 2 * ((‖(Hn n).eval s ω - H ω s‖₊ : ℝ≥0∞) ^ 2
            + (‖H ω s - (Hn m).eval s ω‖₊ : ℝ≥0∞) ^ 2) := by
    intro ω s
    have h_sum : ((Hn n).eval s ω - H ω s) + (H ω s - (Hn m).eval s ω)
        = (Hn n).eval s ω - (Hn m).eval s ω := by ring
    have := _root_.Prove2MeSourceProof.h_e4a003adac246e81fe5cee0f
      ((Hn n).eval s ω - H ω s) (H ω s - (Hn m).eval s ω)
    rw [h_sum] at this
    exact this
  set A : Ω → ℝ → ℝ≥0∞ :=
    fun ω s => (‖(Hn n).eval s ω - H ω s‖₊ : ℝ≥0∞) ^ 2 with hA
  set B : Ω → ℝ → ℝ≥0∞ :=
    fun ω s => (‖H ω s - (Hn m).eval s ω‖₊ : ℝ≥0∞) ^ 2 with hB
  set C : Ω → ℝ → ℝ≥0∞ :=
    fun ω s => (‖(Hn n).eval s ω - (Hn m).eval s ω‖₊ : ℝ≥0∞) ^ 2 with hC
  have h_A_eq : ∀ ω s, A ω s = (‖H ω s - (Hn n).eval s ω‖₊ : ℝ≥0∞) ^ 2 := by
    intro ω s
    simp only [hA]
    congr 1
    rw [show (Hn n).eval s ω - H ω s = -(H ω s - (Hn n).eval s ω) from by ring]
    rw [nnnorm_neg]
  have h_int_A_lt :
      (∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, A ω s ∂volume ∂P) < ε / 4 := by
    have h_eq : (∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, A ω s ∂volume ∂P)
        = ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
          (‖H ω s - (Hn n).eval s ω‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P := by
      congr 1
      ext ω
      congr 1
      ext s
      exact h_A_eq ω s
    rw [h_eq]
    exact hN n hn
  have h_int_B_lt :
      (∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, B ω s ∂volume ∂P) < ε / 4 := by
    change ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖H ω s - (Hn m).eval s ω‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ε / 4
    exact hN m hm
  have h_meas_A_s : ∀ ω, Measurable (fun s => A ω s) := by
    intro ω
    simp only [hA]
    have h_eval_n_meas : Measurable (fun s => (Hn n).eval s ω) :=
      (h_meas_eval n).comp (by fun_prop : Measurable (fun s : ℝ => ((ω, s) : Ω × ℝ)))
    have h_H_meas : Measurable (fun s : ℝ => H ω s) :=
      h_meas_H.comp (by fun_prop : Measurable (fun s : ℝ => (ω, s)))
    exact ((ENNReal.continuous_coe.measurable.comp
      (h_eval_n_meas.sub h_H_meas).nnnorm)).pow_const 2
  have h_meas_A_outer : Measurable (fun ω =>
      ∫⁻ s in Set.Icc (0 : ℝ) T, A ω s ∂volume) := by
    have h_meas_A_pair : Measurable (fun (q : Ω × ℝ) => A q.1 q.2) := by
      simp only [hA]
      have h_eval_n_pair : Measurable (fun (q : Ω × ℝ) =>
          (Hn n).eval q.2 q.1) := h_meas_eval n
      have h_H_pair : Measurable (fun (q : Ω × ℝ) => H q.1 q.2) :=
        h_meas_H.comp (by fun_prop : Measurable (fun (q : Ω × ℝ) => (q.1, q.2)))
      exact ((ENNReal.continuous_coe.measurable.comp
        (h_eval_n_pair.sub h_H_pair).nnnorm)).pow_const 2
    exact Measurable.lintegral_prod_right'
      (ν := volume.restrict (Set.Icc (0:ℝ) T)) h_meas_A_pair
  have h_C_int_le :
      (∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, C ω s ∂volume ∂P)
      ≤ 2 * ((∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, A ω s ∂volume ∂P)
        + ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, B ω s ∂volume ∂P) := by
    have h_inner : ∀ ω,
        (∫⁻ s in Set.Icc (0 : ℝ) T, C ω s ∂volume) ≤
          2 * ((∫⁻ s in Set.Icc (0 : ℝ) T, A ω s ∂volume)
            + ∫⁻ s in Set.Icc (0 : ℝ) T, B ω s ∂volume) := by
      intro ω
      calc (∫⁻ s in Set.Icc (0 : ℝ) T, C ω s ∂volume)
          ≤ ∫⁻ s in Set.Icc (0 : ℝ) T, 2 * (A ω s + B ω s) ∂volume :=
            MeasureTheory.lintegral_mono (h_pointwise ω)
        _ = 2 * ∫⁻ s in Set.Icc (0 : ℝ) T, (A ω s + B ω s) ∂volume := by
            rw [MeasureTheory.lintegral_const_mul']
            simp
        _ = 2 * ((∫⁻ s in Set.Icc (0 : ℝ) T, A ω s ∂volume)
            + ∫⁻ s in Set.Icc (0 : ℝ) T, B ω s ∂volume) := by
            congr 1
            rw [MeasureTheory.lintegral_add_left']
            exact (h_meas_A_s ω).aemeasurable
    calc (∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, C ω s ∂volume ∂P)
        ≤ ∫⁻ ω,
            2 * ((∫⁻ s in Set.Icc (0 : ℝ) T, A ω s ∂volume)
              + ∫⁻ s in Set.Icc (0 : ℝ) T, B ω s ∂volume) ∂P :=
          MeasureTheory.lintegral_mono h_inner
      _ = 2 * ∫⁻ ω,
            ((∫⁻ s in Set.Icc (0 : ℝ) T, A ω s ∂volume)
              + ∫⁻ s in Set.Icc (0 : ℝ) T, B ω s ∂volume) ∂P := by
          rw [MeasureTheory.lintegral_const_mul']
          simp
      _ = 2 * ((∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, A ω s ∂volume ∂P)
          + ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, B ω s ∂volume ∂P) := by
          congr 1
          rw [MeasureTheory.lintegral_add_left']
          exact h_meas_A_outer.aemeasurable
  have h_AB_sum_lt :
      (∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, A ω s ∂volume ∂P)
      + ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, B ω s ∂volume ∂P < ε / 4 + ε / 4 :=
    ENNReal.add_lt_add h_int_A_lt h_int_B_lt
  have h_2_ne_zero : (2 : ℝ≥0∞) ≠ 0 := by norm_num
  have h_2_ne_top : (2 : ℝ≥0∞) ≠ ⊤ := by norm_num
  have h_2_sum_lt :
      (2 : ℝ≥0∞) * ((∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, A ω s ∂volume ∂P)
      + ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, B ω s ∂volume ∂P) <
      (2 : ℝ≥0∞) * (ε / 4 + ε / 4) :=
    ENNReal.mul_right_strictMono h_2_ne_zero h_2_ne_top h_AB_sum_lt
  have h_eq_ε : (2 : ℝ≥0∞) * (ε / 4 + ε / 4) = ε := by
    rw [← two_mul, ← mul_assoc, show (2 : ℝ≥0∞) * 2 = 4 from by norm_num]
    exact ENNReal.mul_div_cancel (by norm_num : (4 : ℝ≥0∞) ≠ 0) (by norm_num)
  rw [h_eq_ε] at h_2_sum_lt
  exact lt_of_le_of_lt h_C_int_le h_2_sum_lt
end LevyStochCalc.Brownian.Ito


