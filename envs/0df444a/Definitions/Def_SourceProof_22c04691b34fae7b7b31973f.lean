-- Prove2me | Definitions.Def_SourceProof_22c04691b34fae7b7b31973f
-- name    : SourceProof_22c04691b34fae7b7b31973f
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T17:08:39.63632+00:00
-- url     : https://prove2.me/theorems/294267e3-d59d-4c5e-a99f-462a9851133a
-- title:
--   LevyStochCalc source module: SourceProof_22c04691b34fae7b7b31973f
-- statement:
--   The original source theorem `LevyStochCalc.Brownian.Ito.lintegral_eval_sq_clamped` comes from the `LevyStochCalc.Brownian.ItoL2CompletionIncrement` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Brownian_ItoL2CompletionExistence_F000
import Definitions.Def_LevyStochCalc_Brownian_ItoL2CompletionExistence_F001
import Definitions.Def_SourceProof_30124e2fe406762c61b9bb9c

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


theorem _root_.Prove2MeSourceProof.h_22c04691b34fae7b7b31973f {T : ℝ} (H : SimplePredictable Ω T) (ω : Ω)
    {t : ℝ} :
    ∫⁻ s in Set.Icc (0 : ℝ) t, (‖H.eval s ω‖₊ : ℝ≥0∞) ^ 2 ∂volume
      = ∑ i : Fin H.N,
        ENNReal.ofReal (min (H.partition i.succ) t - min (H.partition i.castSucc) t)
          * (‖H.ξ i ω‖₊ : ℝ≥0∞) ^ 2 := by
  have h_part_nn : ∀ i : Fin H.N, 0 ≤ H.partition i.castSucc := fun i => by
    have : H.partition 0 ≤ H.partition i.castSucc :=
      H.partition_strictMono.monotone (Fin.zero_le _)
    rw [H.partition_zero] at this; exact this
  rw [show (fun s => (‖H.eval s ω‖₊ : ℝ≥0∞) ^ 2)
      = (fun s => ∑ i : Fin H.N,
          (Set.Ioc (H.partition i.castSucc) (H.partition i.succ)).indicator
            (fun _ => (‖H.ξ i ω‖₊ : ℝ≥0∞) ^ 2) s) from
    funext (_root_.Prove2MeSourceProof.h_30124e2fe406762c61b9bb9c H · ω)]
  rw [MeasureTheory.lintegral_finsetSum _
    (fun i _ => (Measurable.indicator (by fun_prop) measurableSet_Ioc))]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [MeasureTheory.lintegral_indicator measurableSet_Ioc,
    MeasureTheory.setLIntegral_const,
    MeasureTheory.Measure.restrict_apply measurableSet_Ioc]
  -- volume ((pᵢ, pᵢ₊₁] ∩ [0,t]) = ofReal (pᵢ₊₁∧t − pᵢ∧t)
  have h_inter : Set.Ioc (H.partition i.castSucc) (H.partition i.succ) ∩ Set.Icc 0 t
      = Set.Ioc (H.partition i.castSucc) (min (H.partition i.succ) t) := by
    ext x
    simp only [Set.mem_inter_iff, Set.mem_Ioc, Set.mem_Icc, le_min_iff]
    constructor
    · rintro ⟨⟨h1, h2⟩, _, h4⟩; exact ⟨h1, h2, h4⟩
    · rintro ⟨h1, h2, h3⟩
      exact ⟨⟨h1, h2⟩, le_of_lt (lt_of_le_of_lt (h_part_nn i) h1), h3⟩
  rw [h_inter, Real.volume_Ioc, mul_comm]
  congr 1
  rcases le_or_gt (H.partition i.castSucc) t with h | h
  · rw [min_eq_left h]
  · have hpsucc : min (H.partition i.succ) t = t :=
      min_eq_right (h.le.trans (le_of_lt (H.partition_strictMono Fin.castSucc_lt_succ)))
    rw [hpsucc, min_eq_right h.le,
      ENNReal.ofReal_of_nonpos (by linarith : t - H.partition i.castSucc ≤ 0)]
    simp
end LevyStochCalc.Brownian.Ito


