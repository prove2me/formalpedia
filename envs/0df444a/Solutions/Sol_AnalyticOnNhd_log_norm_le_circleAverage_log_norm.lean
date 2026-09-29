-- Prove2me | solution 1 for AnalyticOnNhd.log_norm_le_circleAverage_log_norm
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.553648+00:00
-- url     : https://prove2.me/submissions/7fb0248d-a51f-5849-9b90-63d7040d59d9

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AnalyticOnNhd_log_norm_le_circleAverage_log_norm

open Real MeasureTheory Metric

theorem solution {F : ℂ → ℂ} {c : ℂ} {R : ℝ}
    (hF : AnalyticOnNhd ℂ F (Metric.closedBall c |R|)) (hc : F c ≠ 0) :
    Real.log ‖F c‖ ≤ Real.circleAverage (fun z ↦ Real.log ‖F z‖) c R := by
  rcases eq_or_ne R 0 with rfl | hR
  · simp [Real.circleAverage_zero]
  rw [AnalyticOnNhd.circleAverage_log_norm hR hF hc]
  refine le_add_of_nonneg_left (finsum_nonneg fun u ↦ ?_)
  by_cases hu : u ∈ Metric.closedBall c |R|
  · refine mul_nonneg ?_ ?_
    · have h0 : (0 : ℤ) ≤ MeromorphicOn.divisor F (Metric.closedBall c |R|) u := by
        simpa using (MeromorphicOn.AnalyticOnNhd.divisor_nonneg hF) u
      exact_mod_cast h0
    · rcases eq_or_ne u c with rfl | huc
      · simp
      · have hpos : 0 < ‖c - u‖ := norm_pos_iff.mpr (sub_ne_zero.mpr huc.symm)
        rw [← Real.log_abs, abs_mul, abs_inv, abs_norm]
        refine Real.log_nonneg ?_
        rw [le_mul_inv_iff₀ hpos, one_mul]
        simpa [dist_eq_norm, norm_sub_rev] using (Metric.mem_closedBall.mp hu)
  · have : (MeromorphicOn.divisor F (Metric.closedBall c |R|)) u = 0 :=
      Function.locallyFinsuppWithin.apply_eq_zero_of_notMem _ hu
    simp [this]

end S_AnalyticOnNhd_log_norm_le_circleAverage_log_norm
end P2MW
export P2MW.S_AnalyticOnNhd_log_norm_le_circleAverage_log_norm (solution)
