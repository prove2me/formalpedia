-- Prove2me | Definitions.Def_SourceProof_ea13c47aab5dc77f7cbb74e3
-- name    : SourceProof_ea13c47aab5dc77f7cbb74e3
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-19T20:39:04.456187+00:00
-- url     : https://prove2.me/theorems/d27c10d5-b133-4ce9-b07e-4784e3aa99fc
-- title:
--   LevyStochCalc source proof: LevyStochCalc.Brownian.Ito.integral_eval_sq
-- statement:
--   Auxiliary theorem proved in the original LevyStochCalc source. Its proof and dependencies are retained verbatim from the certified extraction.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Brownian_ItoSimpleIntegrand_F000
import Definitions.Def_SourceProof_21b3ca7ce373bc4fa5cef462
import Mathlib.MeasureTheory.Group.Arithmetic
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.MeasurableSpace.Constructions
import Mathlib.MeasureTheory.Measure.HasOuterApproxClosed

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# The Itô isometry on simple predictable integrands

Expanding the square of the elementary integral into its diagonal and off-diagonal terms gives,
for an adapted simple predictable integrand `H` and a scalar Brownian motion `W`,
`E[(∫_0^T H dW) ^ 2] = ∑_i (t_{i+1} - t_i) · E[ξ_i ^ 2]`; combined with the energy of the
integrand this is the L²-isometry `E[(∫_0^T H dW) ^ 2] = ∫_0^T E[(H.eval s) ^ 2] ds`, stated
both for the lower integral and for the Bochner integral.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
-- `open Classical` is avoided at file scope; explicit decidability is used.

namespace LevyStochCalc.Brownian.Ito

universe u

variable {Ω : Type u} [MeasurableSpace Ω]


theorem _root_.Prove2MeSourceProof.h_ea13c47aab5dc77f7cbb74e3 {T : ℝ} (H : SimplePredictable Ω T) (ω : Ω) :
    ∫ s in Set.Icc (0 : ℝ) T, (H.eval s ω) ^ 2 ∂volume
      = ∑ i : Fin H.N, (H.partition i.succ - H.partition i.castSucc) * (H.ξ i ω) ^ 2 := by
  -- Real version of `eval_sq_eq_sum_indicator`.
  have h_sq_decomp : ∀ s, (H.eval s ω) ^ 2 = ∑ i : Fin H.N,
      (Set.Ioc (H.partition i.castSucc) (H.partition i.succ)).indicator
        (fun _ => (H.ξ i ω) ^ 2) s := by
    intro s
    rw [LevyStochCalc.Brownian.Ito.eval_eq_sum_indicator]
    by_cases h_any : ∃ i : Fin H.N,
        s ∈ Set.Ioc (H.partition i.castSucc) (H.partition i.succ)
    · obtain ⟨i₀, hi₀⟩ := h_any
      have h_unique : ∀ j : Fin H.N, j ≠ i₀ →
          s ∉ Set.Ioc (H.partition j.castSucc) (H.partition j.succ) := by
        intro j hj hj_mem
        have := _root_.Prove2MeSourceProof.h_21b3ca7ce373bc4fa5cef462 H hj
        exact Set.disjoint_left.mp this hj_mem hi₀
      have h_sum_eq : (∑ i : Fin H.N,
          (Set.Ioc (H.partition i.castSucc) (H.partition i.succ)).indicator
            (fun _ => H.ξ i ω) s) = H.ξ i₀ ω := by
        rw [Finset.sum_eq_single i₀]
        · exact Set.indicator_of_mem hi₀ _
        · intro j _ hj
          exact Set.indicator_of_notMem (h_unique j hj) _
        · intro h_not; exact absurd (Finset.mem_univ _) h_not
      have h_sum_sq_eq : (∑ i : Fin H.N,
          (Set.Ioc (H.partition i.castSucc) (H.partition i.succ)).indicator
            (fun _ => (H.ξ i ω) ^ 2) s) = (H.ξ i₀ ω) ^ 2 := by
        rw [Finset.sum_eq_single i₀]
        · exact Set.indicator_of_mem hi₀ _
        · intro j _ hj
          exact Set.indicator_of_notMem (h_unique j hj) _
        · intro h_not; exact absurd (Finset.mem_univ _) h_not
      rw [h_sum_eq, h_sum_sq_eq]
    · push Not at h_any
      have h_zero_sq : ∀ i : Fin H.N,
          (Set.Ioc (H.partition i.castSucc) (H.partition i.succ)).indicator
            (fun _ => (H.ξ i ω) ^ 2) s = 0 :=
        fun i => Set.indicator_of_notMem (h_any i) _
      have h_zero : ∀ i : Fin H.N,
          (Set.Ioc (H.partition i.castSucc) (H.partition i.succ)).indicator
            (fun _ => H.ξ i ω) s = 0 :=
        fun i => Set.indicator_of_notMem (h_any i) _
      rw [Finset.sum_eq_zero (fun i _ => h_zero i),
          Finset.sum_eq_zero (fun i _ => h_zero_sq i)]
      simp
  simp_rw [h_sq_decomp]
  rw [MeasureTheory.integral_finsetSum]
  · refine Finset.sum_congr rfl (fun i _ => ?_)
    have h_meas_set : MeasurableSet
        (Set.Ioc (H.partition i.castSucc) (H.partition i.succ)) := measurableSet_Ioc
    have h_subset : Set.Ioc (H.partition i.castSucc) (H.partition i.succ)
        ⊆ Set.Icc (0 : ℝ) T := by
      intro x hx
      have h_part_zero_le : 0 ≤ H.partition i.castSucc := by
        have : H.partition 0 ≤ H.partition i.castSucc :=
          H.partition_strictMono.monotone (Fin.zero_le _)
        rw [H.partition_zero] at this; exact this
      have h_part_succ_le_T : H.partition i.succ ≤ T := by
        refine le_trans ?_ H.partition_le_T
        exact H.partition_strictMono.monotone (Fin.le_last _)
      refine ⟨?_, ?_⟩
      · exact h_part_zero_le.trans (le_of_lt hx.1)
      · exact hx.2.trans h_part_succ_le_T
    have h_dt_nn : 0 ≤ H.partition i.succ - H.partition i.castSucc :=
      sub_nonneg.mpr (le_of_lt (H.partition_strictMono Fin.castSucc_lt_succ))
    rw [MeasureTheory.integral_indicator h_meas_set]
    rw [MeasureTheory.setIntegral_const]
    rw [MeasureTheory.measureReal_def]
    rw [MeasureTheory.Measure.restrict_apply h_meas_set]
    rw [Set.inter_eq_left.mpr h_subset]
    rw [Real.volume_Ioc, ENNReal.toReal_ofReal h_dt_nn]
    rw [smul_eq_mul]
  · intro i _
    refine MeasureTheory.Integrable.indicator ?_ measurableSet_Ioc
    exact MeasureTheory.integrable_const _
end LevyStochCalc.Brownian.Ito


