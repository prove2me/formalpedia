-- Prove2me | solution 1 for ActuarialValuation.quotaShareCapitalObjective_unique
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-09T16:09:51.574991+00:00
-- url     : https://prove2.me/submissions/c742449a-b657-4055-9463-b42a0e13cd85

import Mathlib
import Definitions.Def_actuarial_quotaShareCapitalObjective
import Definitions.Def_actuarial_quotaShareContinuousOptimum
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution
    (q claim loading capital retention : ℝ)
    (hq0 : 0 < q) (hq1 : q < 1) (hb : claim ≠ 0)
    (hpos : 0 < loading + capital)
    (hEq : quotaShareCapitalObjective q claim retention loading capital =
      quotaShareCapitalObjective q claim
        (quotaShareContinuousOptimum loading capital) loading capital) :
    retention = quotaShareContinuousOptimum loading capital := by
  have hne : loading + capital ≠ 0 := ne_of_gt hpos
  have hcost (r : ℝ) :
      quotaShareCapitalObjective q claim r loading capital =
        q * claim + q * (1 - q) * claim ^ 2 *
          (loading * (1 - r) ^ 2 + capital * r ^ 2) := by
    dsimp [quotaShareCapitalObjective, quotaShareRetainedClaim,
      quotaShareVariancePremium, quotaShareCededClaim]
    ring
  have hquad (r : ℝ) :
      loading * (1 - r) ^ 2 + capital * r ^ 2 =
        loading * capital / (loading + capital) +
        (loading + capital) *
          (r - quotaShareContinuousOptimum loading capital) ^ 2 := by
    dsimp [quotaShareContinuousOptimum]
    field_simp [hne]
    ring
  have hval (r : ℝ) :
      quotaShareCapitalObjective q claim r loading capital =
        q * claim + q * (1 - q) * claim ^ 2 *
          (loading * capital / (loading + capital) +
            (loading + capital) *
              (r - quotaShareContinuousOptimum loading capital) ^ 2) := by
    rw [hcost r, hquad r]
  have hq1p : 0 < 1 - q := sub_pos.mpr hq1
  have hb2 : 0 < claim ^ 2 := by
    have hnn : 0 ≤ claim ^ 2 := sq_nonneg claim
    have hn : claim ^ 2 ≠ 0 := pow_ne_zero 2 hb
    exact lt_of_le_of_ne hnn (Ne.symm hn)
  have hpref : 0 < q * (1 - q) * claim ^ 2 :=
    mul_pos (mul_pos hq0 hq1p) hb2
  rw [hval retention, hval (quotaShareContinuousOptimum loading capital)] at hEq
  have hsqstar :
      (quotaShareContinuousOptimum loading capital -
       quotaShareContinuousOptimum loading capital) ^ 2 = 0 := by ring
  rw [hsqstar] at hEq
  simp only [mul_zero, add_zero] at hEq
  have hzero :
      (q * (1 - q) * claim ^ 2 * (loading + capital)) *
        (retention - quotaShareContinuousOptimum loading capital) ^ 2 = 0 := by
    nlinarith [hEq]
  have hco : q * (1 - q) * claim ^ 2 * (loading + capital) ≠ 0 :=
    ne_of_gt (mul_pos hpref hpos)
  have hsqzero :
      (retention - quotaShareContinuousOptimum loading capital) ^ 2 = 0 :=
    (mul_eq_zero.mp hzero).resolve_left hco
  have hd : retention - quotaShareContinuousOptimum loading capital = 0 := by
    have hmul : (retention - quotaShareContinuousOptimum loading capital) *
        (retention - quotaShareContinuousOptimum loading capital) = 0 := by
      simpa only [pow_two] using hsqzero
    rcases mul_eq_zero.mp hmul with h | h
    · exact h
    · exact h
  exact sub_eq_zero.mp hd
