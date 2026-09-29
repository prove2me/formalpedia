-- Prove2me | solution 1 for ABOThreshold.threshold_general_lt_imp_condition
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-23T09:31:26.549453+00:00
-- url     : https://prove2.me/submissions/1a96cd1d-3493-40f1-9e33-35963d7b36b8

import Definitions.Def_ABOThreshold_model

open ABOThreshold Finset

namespace Ag2Aux_ABOCondGen

theorem cond_of_lt (D x : ℝ) (k : ℕ) (hk : 1 ≤ k) (hD : 0 ≤ D) (hx : 0 < x)
    (hlt : x < D ^ (-(1 : ℝ) / (k : ℝ))) : D * x ^ (k + 1) < x := by
  rcases hD.lt_or_eq with hD' | hD'
  · have hk0 : (k : ℝ) ≠ 0 := by exact_mod_cast (by omega : k ≠ 0)
    have h1 : x ^ k < (D ^ (-(1 : ℝ) / (k : ℝ))) ^ k :=
      pow_lt_pow_left₀ hlt hx.le (by omega)
    have h2 : (D ^ (-(1 : ℝ) / (k : ℝ))) ^ k = D⁻¹ := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hD'.le]
      rw [show -(1 : ℝ) / k * k = -1 by field_simp, Real.rpow_neg_one]
    rw [h2] at h1
    have h3 : D * x ^ k < 1 := by
      calc D * x ^ k < D * D⁻¹ := mul_lt_mul_of_pos_left h1 hD'
        _ = 1 := mul_inv_cancel₀ hD'.ne'
    calc D * x ^ (k + 1) = (D * x ^ k) * x := by ring
      _ < 1 * x := mul_lt_mul_of_pos_right h3 hx
      _ = x := one_mul x
  · subst hD'; simpa using hx

end Ag2Aux_ABOCondGen

open Ag2Aux_ABOCondGen

theorem solution (A k : ℕ) (hk : 1 ≤ k) (η : ℝ) (hη : 0 < η)
    (hlt : η < thresholdGeneral A k) : ThresholdConditionGeneral A k η := by
  unfold ThresholdConditionGeneral
  unfold thresholdGeneral at hlt
  exact cond_of_lt _ (2 * η) k hk (by positivity) (by positivity) (by linarith)
