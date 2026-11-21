-- Prove2me | Definitions.Def_SourceProof_ade4537669e1061d312e165f
-- name    : SourceProof_ade4537669e1061d312e165f
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T07:26:51.687634+00:00
-- url     : https://prove2.me/theorems/677ce7b3-d7f0-4b85-b5d3-6b5f63f6fdcb
-- title:
--   LevyStochCalc source module: SourceProof_ade4537669e1061d312e165f
-- statement:
--   The original source theorem `LevyStochCalc.Brownian.Ito.cross_sq_integrable` comes from the `LevyStochCalc.Brownian.ItoSimpleMoments` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_SourceProof_0d5475ecda5b11387d030812

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Second moments of the terms of the elementary Brownian integral

For an adapted simple predictable integrand the diagonal term satisfies
`E[(ξ_i · ΔW_i) ^ 2] = (t_{i+1} - t_i) · E[ξ_i ^ 2]`, where
`ΔW_i = W_{t_{i+1}} - W_{t_i}`, since `ΔW_i` is independent of `ℱ_{t_i}` and centred Gaussian
with variance `t_{i+1} - t_i`, while for `i < j` the off-diagonal term vanishes,
`E[(ξ_i · ΔW_i) · (ξ_j · ΔW_j)] = 0`. Both rest on the integrability of the squared increments
and of the cross products.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
-- `open Classical` is avoided at file scope; explicit decidability is used.

namespace LevyStochCalc.Brownian.Ito

universe u

variable {Ω : Type u} [MeasurableSpace Ω]


theorem _root_.Prove2MeSourceProof.h_ade4537669e1061d312e165f
    {P : Measure Ω} [IsProbabilityMeasure P]
    (W : LevyStochCalc.Brownian.BrownianMotion P)
    {T : ℝ} (H : SimplePredictable Ω T) (i j : Fin H.N) :
    MeasureTheory.Integrable
      (fun ω => (H.ξ i ω * (W.W (H.partition i.succ) ω
                          - W.W (H.partition i.castSucc) ω)) *
                (H.ξ j ω * (W.W (H.partition j.succ) ω
                          - W.W (H.partition j.castSucc) ω))) P := by
  have h_part_i_nn : 0 ≤ H.partition i.castSucc := by
    have : H.partition 0 ≤ H.partition i.castSucc :=
      H.partition_strictMono.monotone (Fin.zero_le _)
    rw [H.partition_zero] at this; exact this
  have h_part_j_nn : 0 ≤ H.partition j.castSucc := by
    have : H.partition 0 ≤ H.partition j.castSucc :=
      H.partition_strictMono.monotone (Fin.zero_le _)
    rw [H.partition_zero] at this; exact this
  have h_st_i : H.partition i.castSucc < H.partition i.succ :=
    H.partition_strictMono Fin.castSucc_lt_succ
  have h_st_j : H.partition j.castSucc < H.partition j.succ :=
    H.partition_strictMono Fin.castSucc_lt_succ
  have h_int_i_sq := _root_.Prove2MeSourceProof.h_0d5475ecda5b11387d030812 W h_part_i_nn h_st_i
  have h_int_j_sq := _root_.Prove2MeSourceProof.h_0d5475ecda5b11387d030812 W h_part_j_nn h_st_j
  -- Integrability of ΔW_i · ΔW_j via AM-GM.
  have h_meas_i : Measurable (fun ω => W.W (H.partition i.succ) ω
                                     - W.W (H.partition i.castSucc) ω) :=
    (W.measurable_eval _).sub (W.measurable_eval _)
  have h_meas_j : Measurable (fun ω => W.W (H.partition j.succ) ω
                                     - W.W (H.partition j.castSucc) ω) :=
    (W.measurable_eval _).sub (W.measurable_eval _)
  have h_int_ΔW : MeasureTheory.Integrable
      (fun ω => (W.W (H.partition i.succ) ω - W.W (H.partition i.castSucc) ω)
              * (W.W (H.partition j.succ) ω - W.W (H.partition j.castSucc) ω)) P := by
    refine MeasureTheory.Integrable.mono'
      (MeasureTheory.Integrable.add (h_int_i_sq.const_mul (1/2 : ℝ))
        (h_int_j_sq.const_mul (1/2 : ℝ))) (h_meas_i.mul h_meas_j).aestronglyMeasurable ?_
    filter_upwards with ω
    rw [Real.norm_eq_abs, abs_mul]
    have : |W.W (H.partition i.succ) ω - W.W (H.partition i.castSucc) ω| *
           |W.W (H.partition j.succ) ω - W.W (H.partition j.castSucc) ω|
        ≤ (1/2) * (W.W (H.partition i.succ) ω - W.W (H.partition i.castSucc) ω)^2 +
          (1/2) * (W.W (H.partition j.succ) ω - W.W (H.partition j.castSucc) ω)^2 := by
      nlinarith [sq_abs (W.W (H.partition i.succ) ω - W.W (H.partition i.castSucc) ω),
                 sq_abs (W.W (H.partition j.succ) ω - W.W (H.partition j.castSucc) ω),
                 sq_nonneg (|W.W (H.partition i.succ) ω - W.W (H.partition i.castSucc) ω| -
                            |W.W (H.partition j.succ) ω - W.W (H.partition j.castSucc) ω|)]
    exact this
  -- (ξ_i · ΔW_i) · (ξ_j · ΔW_j) = (ξ_i · ξ_j) · (ΔW_i · ΔW_j). Bounded × integrable.
  obtain ⟨M_i, hM_i⟩ := H.ξ_bounded i
  obtain ⟨M_j, hM_j⟩ := H.ξ_bounded j
  have h_eq : ∀ ω, (H.ξ i ω * (W.W (H.partition i.succ) ω
                              - W.W (H.partition i.castSucc) ω)) *
                   (H.ξ j ω * (W.W (H.partition j.succ) ω
                              - W.W (H.partition j.castSucc) ω))
            = (H.ξ i ω * H.ξ j ω) *
              ((W.W (H.partition i.succ) ω - W.W (H.partition i.castSucc) ω) *
              (W.W (H.partition j.succ) ω - W.W (H.partition j.castSucc) ω)) :=
    fun ω => by ring
  rw [show (fun ω => (H.ξ i ω * (W.W (H.partition i.succ) ω
                                 - W.W (H.partition i.castSucc) ω)) *
                     (H.ξ j ω * (W.W (H.partition j.succ) ω
                                 - W.W (H.partition j.castSucc) ω)))
        = fun ω => (H.ξ i ω * H.ξ j ω) *
                   ((W.W (H.partition i.succ) ω - W.W (H.partition i.castSucc) ω) *
                   (W.W (H.partition j.succ) ω - W.W (H.partition j.castSucc) ω)) from
    funext h_eq]
  refine MeasureTheory.Integrable.bdd_mul (c := |M_i| * |M_j|) h_int_ΔW
    ((H.ξ_measurable i).mul (H.ξ_measurable j)).aestronglyMeasurable ?_
  filter_upwards with ω
  rw [Real.norm_eq_abs, abs_mul]
  exact mul_le_mul (le_trans (hM_i ω) (le_abs_self _))
    (le_trans (hM_j ω) (le_abs_self _)) (abs_nonneg _) (abs_nonneg _)
end LevyStochCalc.Brownian.Ito


