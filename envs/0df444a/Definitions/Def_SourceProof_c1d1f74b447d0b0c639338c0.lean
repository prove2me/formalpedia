-- Prove2me | Definitions.Def_SourceProof_c1d1f74b447d0b0c639338c0
-- name    : SourceProof_c1d1f74b447d0b0c639338c0
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T17:27:33.67551+00:00
-- url     : https://prove2.me/theorems/adc8c261-dbe7-44fb-b914-23ab7929e6e8
-- title:
--   LevyStochCalc source module: SourceProof_c1d1f74b447d0b0c639338c0
-- statement:
--   The original source theorem `LevyStochCalc.Brownian.Ito.simpleIntegral_sq_bochner_clamped` comes from the `LevyStochCalc.Brownian.ItoL2CompletionIncrement` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_SourceProof_246df2546b48a4eab96d1ea1
import Definitions.Def_SourceProof_be1408ec5fbfc50e70ae1572

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


theorem _root_.Prove2MeSourceProof.h_c1d1f74b447d0b0c639338c0
    {P : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure P]
    (W : LevyStochCalc.Brownian.BrownianMotion P)
    (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (hℱ : IsBrownianFiltration W ℱ)
    {T : ℝ} (H : SimplePredictable Ω T)
    (h_adapt : ∀ i : Fin H.N, @MeasureTheory.StronglyMeasurable Ω ℝ _
      (ℱ (H.partition i.castSucc)) (H.ξ i))
    {t : ℝ} (ht_nn : 0 ≤ t) :
    ∫ ω, (simpleIntegral W H t ω) ^ 2 ∂P
      = ∑ i : Fin H.N,
        (min (H.partition i.succ) t - min (H.partition i.castSucc) t)
          * ∫ ω, (H.ξ i ω) ^ 2 ∂P := by
  have h_part_nn : ∀ i : Fin H.N, 0 ≤ H.partition i.castSucc := fun i => by
    have : H.partition 0 ≤ H.partition i.castSucc :=
      H.partition_strictMono.monotone (Fin.zero_le _)
    rw [H.partition_zero] at this; exact this
  set term : Fin H.N → Ω → ℝ := fun i ω =>
    H.ξ i ω * (W.W (min (H.partition i.succ) t) ω
      - W.W (min (H.partition i.castSucc) t) ω) with hterm
  have h_a_le_b : ∀ i : Fin H.N,
      min (H.partition i.castSucc) t ≤ min (H.partition i.succ) t :=
    fun i => min_le_min_right t
      (le_of_lt (H.partition_strictMono Fin.castSucc_lt_succ))
  have h_a_nn : ∀ i : Fin H.N, 0 ≤ min (H.partition i.castSucc) t :=
    fun i => le_min (h_part_nn i) ht_nn
  -- In the genuine case, the lower clamp equals the partition point.
  have h_acs : ∀ i : Fin H.N,
      min (H.partition i.castSucc) t < min (H.partition i.succ) t →
        min (H.partition i.castSucc) t = H.partition i.castSucc := by
    intro i hlt
    refine min_eq_left ?_
    by_contra h
    rw [not_le] at h
    rw [min_eq_right h.le,
      min_eq_right (h.le.trans (le_of_lt (H.partition_strictMono Fin.castSucc_lt_succ)))] at hlt
    exact lt_irrefl t hlt
  -- integrability of every cross product
  have h_cross : ∀ i j : Fin H.N,
      MeasureTheory.Integrable (fun ω => term i ω * term j ω) P := by
    intro i j
    obtain ⟨Mi, hMi⟩ := H.ξ_bounded i
    obtain ⟨Mj, hMj⟩ := H.ξ_bounded j
    exact _root_.Prove2MeSourceProof.h_be1408ec5fbfc50e70ae1572 W (h_a_nn i) (h_a_le_b i) (h_a_nn j) (h_a_le_b j)
      (H.ξ i) (H.ξ j) (H.ξ_measurable i) (H.ξ_measurable j) Mi hMi Mj hMj
  -- off-diagonal vanishing for i < j
  have h_off : ∀ i j : Fin H.N, i < j → ∫ ω, term i ω * term j ω ∂P = 0 := by
    intro i j hij
    rcases eq_or_lt_of_le (h_a_le_b j) with hj_eq | hj_lt
    · -- j-increment degenerate
      rw [show (fun ω => term i ω * term j ω) = fun _ => (0 : ℝ) from by
        funext ω; simp only [hterm]; rw [← hj_eq]; ring]
      exact MeasureTheory.integral_zero _ _
    · rcases eq_or_lt_of_le (h_a_le_b i) with hi_eq | hi_lt
      · -- i-increment degenerate
        rw [show (fun ω => term i ω * term j ω) = fun _ => (0 : ℝ) from by
          funext ω; simp only [hterm]; rw [← hi_eq]; ring]
        exact MeasureTheory.integral_zero _ _
      · -- both genuine: apply the general off-diagonal
        have hbi_le_aj : min (H.partition i.succ) t ≤ H.partition j.castSucc := by
          refine le_trans (min_le_left _ _) ?_
          exact H.partition_strictMono.monotone (Fin.succ_le_castSucc_iff.mpr hij)
        have h := _root_.Prove2MeSourceProof.h_246df2546b48a4eab96d1ea1 W ℱ hℱ (h_part_nn i)
          (by rw [← h_acs i hi_lt]; exact hi_lt)
          hbi_le_aj
          (by rw [← h_acs j hj_lt]; exact hj_lt)
          (H.ξ i) (H.ξ j) (h_adapt i) (h_adapt j)
        rw [show (fun ω => term i ω * term j ω)
              = fun ω => (H.ξ i ω * (W.W (min (H.partition i.succ) t) ω
                  - W.W (H.partition i.castSucc) ω))
                * (H.ξ j ω * (W.W (min (H.partition j.succ) t) ω
                  - W.W (H.partition j.castSucc) ω)) from by
          funext ω; simp only [hterm]; rw [h_acs i hi_lt, h_acs j hj_lt]]
        exact h
  rw [show (fun ω => (LevyStochCalc.Brownian.Ito.simpleIntegral W H t ω) ^ 2)
        = fun ω => ∑ i : Fin H.N, ∑ j : Fin H.N, term i ω * term j ω from by
    funext ω
    rw [show LevyStochCalc.Brownian.Ito.simpleIntegral W H t ω = ∑ i : Fin H.N, term i ω from rfl, sq,
      Finset.sum_mul_sum]]
  rw [MeasureTheory.integral_finsetSum _
    (fun i _ => MeasureTheory.integrable_finsetSum _ (fun j _ => h_cross i j))]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [MeasureTheory.integral_finsetSum _ (fun j _ => h_cross i j),
    Finset.sum_eq_single i]
  · -- diagonal j = i
    rw [show (fun ω => term i ω * term i ω) = fun ω => (term i ω) ^ 2 from by
      funext ω; ring]
    rcases eq_or_lt_of_le (h_a_le_b i) with hi_eq | hi_lt
    · rw [show (fun ω => (term i ω) ^ 2) = fun _ => (0 : ℝ) from by
        funext ω; simp only [hterm]; rw [← hi_eq]; ring, MeasureTheory.integral_zero,
        ← hi_eq]; ring
    · obtain ⟨Mi, hMi⟩ := H.ξ_bounded i
      rw [show (fun ω => (term i ω) ^ 2)
            = fun ω => (H.ξ i ω * (W.W (min (H.partition i.succ) t) ω
                - W.W (H.partition i.castSucc) ω)) ^ 2 from by
        funext ω; simp only [hterm]; rw [h_acs i hi_lt]]
      rw [LevyStochCalc.Brownian.Ito.diagonal_increment_bochner W ℱ hℱ (h_part_nn i)
        (by rw [← h_acs i hi_lt]; exact hi_lt) (H.ξ i) (h_adapt i) Mi hMi]
      rw [h_acs i hi_lt]
  · intro j _ hj
    rcases lt_or_gt_of_ne hj with h_lt | h_gt
    · rw [show (fun ω => term i ω * term j ω) = fun ω => term j ω * term i ω from by
        funext ω; ring]
      exact h_off j i h_lt
    · exact h_off i j h_gt
  · intro h; exact absurd (Finset.mem_univ _) h
end LevyStochCalc.Brownian.Ito


