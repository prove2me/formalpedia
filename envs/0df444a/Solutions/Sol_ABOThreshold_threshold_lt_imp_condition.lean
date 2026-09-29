-- Prove2me | solution 1 for ABOThreshold.threshold_lt_imp_condition
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-23T09:31:26.590076+00:00
-- url     : https://prove2.me/submissions/a0ebba62-565b-4758-bf9c-1379d0b62d00

import Definitions.Def_ABOThreshold_model

open ABOThreshold Finset

namespace Ag2Aux_ABOCond

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

end Ag2Aux_ABOCond

open Ag2Aux_ABOCond

theorem solution (A k : ℕ) (hk : 1 ≤ k) (η : ℝ) (hη : 0 < η)
    (hlt : η < thresholdProb A k) : ThresholdCondition A k η :=
  cond_of_lt _ η k hk (Nat.cast_nonneg _) hη hlt
