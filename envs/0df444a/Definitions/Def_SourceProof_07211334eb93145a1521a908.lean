-- Prove2me | Definitions.Def_SourceProof_07211334eb93145a1521a908
-- name    : SourceProof_07211334eb93145a1521a908
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T17:29:51.562875+00:00
-- url     : https://prove2.me/theorems/eef215cf-9233-41d5-b703-ad485feb21e2
-- title:
--   LevyStochCalc source module: SourceProof_07211334eb93145a1521a908
-- statement:
--   The original source theorem `LevyStochCalc.Brownian.Ito.simpleIntegral_intermediate_isometry` comes from the `LevyStochCalc.Brownian.ItoL2CompletionIncrement` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_SourceProof_22c04691b34fae7b7b31973f
import Definitions.Def_SourceProof_be1408ec5fbfc50e70ae1572
import Definitions.Def_SourceProof_c1d1f74b447d0b0c639338c0

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Brownian Itô integral: increment expansions and the intermediate-time isometry

Diagonal and off-diagonal expectations of products of Brownian increments against
adapted weights, the Bochner expansion of the square of a simple integral clamped
at an intermediate time, and the isometry
`∫⁻ ‖simpleIntegral W H t‖₊² = ∫⁻ ∫⁻_{[0, t]} ‖H.eval‖₊²` it gives for every
intermediate time `t`.
-/

namespace LevyStochCalc.Brownian.Ito

open MeasureTheory
open scoped NNReal ENNReal

universe u
variable {Ω : Type u} [MeasurableSpace Ω]


theorem _root_.Prove2MeSourceProof.h_07211334eb93145a1521a908
    {P : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure P]
    (W : LevyStochCalc.Brownian.BrownianMotion P)
    (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (hℱ : IsBrownianFiltration W ℱ)
    {T : ℝ} (H : SimplePredictable Ω T)
    (h_adapt : ∀ i : Fin H.N, @MeasureTheory.StronglyMeasurable Ω ℝ _
      (ℱ (H.partition i.castSucc)) (H.ξ i))
    {t : ℝ} (ht_nn : 0 ≤ t) :
    ∫⁻ ω, (‖simpleIntegral W H t ω‖₊ : ℝ≥0∞) ^ 2 ∂P
      = ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) t, (‖H.eval s ω‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P := by
  have h_part_nn : ∀ i : Fin H.N, 0 ≤ H.partition i.castSucc := fun i => by
    have : H.partition 0 ≤ H.partition i.castSucc :=
      H.partition_strictMono.monotone (Fin.zero_le _)
    rw [H.partition_zero] at this; exact this
  have h_a_le_b : ∀ i : Fin H.N,
      min (H.partition i.castSucc) t ≤ min (H.partition i.succ) t :=
    fun i => min_le_min_right t (le_of_lt (H.partition_strictMono Fin.castSucc_lt_succ))
  have h_norm_sq : ∀ x : ℝ, (‖x‖₊ : ℝ≥0∞) ^ 2 = ENNReal.ofReal (x ^ 2) := fun x => by
    rw [show (‖x‖₊ : ℝ≥0∞) = ENNReal.ofReal ‖x‖ from ofReal_norm x |>.symm,
      ← ENNReal.ofReal_pow (norm_nonneg _), show ‖x‖ ^ 2 = x ^ 2 from by
        rw [Real.norm_eq_abs, sq_abs]]
  have hξsqmeas : ∀ i : Fin H.N, Measurable (fun ω => (‖H.ξ i ω‖₊ : ℝ≥0∞) ^ 2) :=
    fun i => (((H.ξ_measurable i).nnnorm).coe_nnreal_ennreal).pow_const 2
  have hξ_int : ∀ i : Fin H.N, MeasureTheory.Integrable (fun ω => (H.ξ i ω) ^ 2) P := by
    intro i; obtain ⟨M, hM⟩ := H.ξ_bounded i
    refine MeasureTheory.Integrable.mono' (g := fun _ : Ω => M ^ 2)
      (MeasureTheory.integrable_const _) ((H.ξ_measurable i).pow_const 2).aestronglyMeasurable ?_
    filter_upwards with ω
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact sq_le_sq' (neg_le_of_abs_le (hM ω)) (le_of_abs_le (hM ω))
  have hξ_lint : ∀ i : Fin H.N,
      ∫⁻ ω, (‖H.ξ i ω‖₊ : ℝ≥0∞) ^ 2 ∂P = ENNReal.ofReal (∫ ω, (H.ξ i ω) ^ 2 ∂P) := by
    intro i
    rw [show (fun ω => (‖H.ξ i ω‖₊ : ℝ≥0∞) ^ 2) = fun ω => ENNReal.ofReal ((H.ξ i ω) ^ 2) from
      funext (fun ω => h_norm_sq _)]
    rw [← MeasureTheory.ofReal_integral_eq_lintegral_ofReal (hξ_int i)
      (by filter_upwards with ω; positivity)]
  set term : Fin H.N → Ω → ℝ := fun i ω =>
    H.ξ i ω * (W.W (min (H.partition i.succ) t) ω
      - W.W (min (H.partition i.castSucc) t) ω) with hterm
  have h_cross : ∀ i j : Fin H.N,
      MeasureTheory.Integrable (fun ω => term i ω * term j ω) P := by
    intro i j
    obtain ⟨Mi, hMi⟩ := H.ξ_bounded i
    obtain ⟨Mj, hMj⟩ := H.ξ_bounded j
    exact _root_.Prove2MeSourceProof.h_be1408ec5fbfc50e70ae1572 W (le_min (h_part_nn i) ht_nn) (h_a_le_b i)
      (le_min (h_part_nn j) ht_nn) (h_a_le_b j)
      (H.ξ i) (H.ξ j) (H.ξ_measurable i) (H.ξ_measurable j) Mi hMi Mj hMj
  have h_si_int : MeasureTheory.Integrable (fun ω => (LevyStochCalc.Brownian.Ito.simpleIntegral W H t ω) ^ 2) P := by
    rw [show (fun ω => (LevyStochCalc.Brownian.Ito.simpleIntegral W H t ω) ^ 2)
          = fun ω => ∑ i : Fin H.N, ∑ j : Fin H.N, term i ω * term j ω from by
      funext ω
      rw [show LevyStochCalc.Brownian.Ito.simpleIntegral W H t ω = ∑ i : Fin H.N, term i ω from rfl, sq,
        Finset.sum_mul_sum]]
    exact MeasureTheory.integrable_finsetSum _
      (fun i _ => MeasureTheory.integrable_finsetSum _ (fun j _ => h_cross i j))
  rw [show (∫⁻ ω, (‖LevyStochCalc.Brownian.Ito.simpleIntegral W H t ω‖₊ : ℝ≥0∞) ^ 2 ∂P)
        = ∫⁻ ω, ENNReal.ofReal ((LevyStochCalc.Brownian.Ito.simpleIntegral W H t ω) ^ 2) ∂P from
    MeasureTheory.lintegral_congr (fun ω => h_norm_sq _)]
  rw [← MeasureTheory.ofReal_integral_eq_lintegral_ofReal h_si_int
    (by filter_upwards with ω; positivity)]
  rw [_root_.Prove2MeSourceProof.h_c1d1f74b447d0b0c639338c0 W ℱ hℱ H h_adapt ht_nn]
  rw [show (fun ω => ∫⁻ s in Set.Icc (0 : ℝ) t, (‖H.eval s ω‖₊ : ℝ≥0∞) ^ 2 ∂volume)
        = fun ω => ∑ i : Fin H.N,
            ENNReal.ofReal (min (H.partition i.succ) t - min (H.partition i.castSucc) t)
              * (‖H.ξ i ω‖₊ : ℝ≥0∞) ^ 2 from
    funext (fun ω => _root_.Prove2MeSourceProof.h_22c04691b34fae7b7b31973f H ω)]
  rw [MeasureTheory.lintegral_finsetSum _ (fun i _ => (hξsqmeas i).const_mul _)]
  rw [ENNReal.ofReal_sum_of_nonneg (fun i _ => mul_nonneg
    (sub_nonneg.mpr (h_a_le_b i)) (MeasureTheory.integral_nonneg (fun ω => sq_nonneg _)))]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [MeasureTheory.lintegral_const_mul _ (hξsqmeas i),
    ENNReal.ofReal_mul (sub_nonneg.mpr (h_a_le_b i)), hξ_lint i]
end LevyStochCalc.Brownian.Ito


