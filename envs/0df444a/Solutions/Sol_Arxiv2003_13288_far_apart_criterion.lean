-- Prove2me | solution 1 for Arxiv2003_13288.far_apart_criterion
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-25T20:33:40.960701+00:00
-- url     : https://prove2.me/submissions/4d395743-2b50-4b5d-9040-19b0f7a0c745

import Mathlib
import Definitions.Def_Arxiv2003_13288_Basic

open MeasureTheory Filter Topology

open Arxiv2003_13288 in
theorem solution (k δ Cs : ℝ) (hk : 0 < k) (hδ : 0 < δ) (hCs : 0 < Cs) :
    k * scatMeanFreePath (1 / δ ^ 3) Cs = (δ / (Cs / k) ^ (1 / 3 : ℝ)) ^ 3 ∧
    ∀ M : ℝ, 0 < M →
      (M ≤ k * scatMeanFreePath (1 / δ ^ 3) Cs ↔ M ^ (1 / 3 : ℝ) * (Cs / k) ^ (1 / 3 : ℝ) ≤ δ) := by
  have hc : 0 < Cs / k := div_pos hCs hk
  have h3 : ((Cs / k) ^ (1 / 3 : ℝ)) ^ 3 = Cs / k := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hc.le]; norm_num
  have hpos : 0 < (Cs / k) ^ (1 / 3 : ℝ) := Real.rpow_pos_of_pos hc _
  have e : k * scatMeanFreePath (1 / δ ^ 3) Cs = (δ / (Cs / k) ^ (1 / 3 : ℝ)) ^ 3 := by
    rw [div_pow, h3, scatMeanFreePath]; field_simp
  refine ⟨e, fun M hM => ?_⟩
  have hM3 : (M ^ (1 / 3 : ℝ)) ^ 3 = M := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hM.le]; norm_num
  have hMp : 0 < M ^ (1 / 3 : ℝ) := Real.rpow_pos_of_pos hM _
  rw [e, ← le_div_iff₀ hpos]
  constructor
  · intro h
    by_contra hc'
    push_neg at hc'
    have := pow_lt_pow_left₀ hc' (div_pos hδ hpos).le (by norm_num : (3:ℕ) ≠ 0)
    rw [hM3] at this; linarith
  · intro h
    have := pow_le_pow_left₀ hMp.le h 3
    rwa [hM3] at this
