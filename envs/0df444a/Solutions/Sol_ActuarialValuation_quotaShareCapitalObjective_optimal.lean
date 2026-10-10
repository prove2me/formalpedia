-- Prove2me | solution 1 for ActuarialValuation.quotaShareCapitalObjective_optimal
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-09T16:12:47.156128+00:00
-- url     : https://prove2.me/submissions/73ecee85-80a1-4b17-8f53-2f13f23dc792

import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Definitions.Def_actuarial_quotaShareCapitalObjective
import Definitions.Def_actuarial_quotaShareContinuousOptimum
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution
    (q claim loading capital retention : ℝ)
    (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    (hl : 0 ≤ loading) (hc : 0 ≤ capital)
    (hpos : 0 < loading + capital) :
    quotaShareCapitalObjective q claim
        (quotaShareContinuousOptimum loading capital) loading capital ≤
      quotaShareCapitalObjective q claim retention loading capital := by
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
  have hq : 0 ≤ 1 - q := sub_nonneg.mpr hq1
  have hpref : 0 ≤ q * (1 - q) * claim ^ 2 :=
    mul_nonneg (mul_nonneg hq0 hq) (sq_nonneg claim)
  have hrisk : 0 ≤ (loading + capital) *
      (retention - quotaShareContinuousOptimum loading capital) ^ 2 :=
    mul_nonneg (le_of_lt hpos) (sq_nonneg _)
  have hle :
      q * (1 - q) * claim ^ 2 * (loading * capital / (loading + capital)) ≤
      q * (1 - q) * claim ^ 2 *
        (loading * capital / (loading + capital) +
         (loading + capital) *
           (retention - quotaShareContinuousOptimum loading capital) ^ 2) :=
    mul_le_mul_of_nonneg_left (le_add_of_nonneg_right hrisk) hpref
  calc
    quotaShareCapitalObjective q claim
        (quotaShareContinuousOptimum loading capital) loading capital =
        q * claim + q * (1 - q) * claim ^ 2 *
          (loading * capital / (loading + capital)) := by
            rw [hval]
            ring
    _ ≤ q * claim + q * (1 - q) * claim ^ 2 *
       (loading * capital / (loading + capital) +
        (loading + capital) *
          (retention - quotaShareContinuousOptimum loading capital) ^ 2) :=
      by
        convert add_le_add_left hle (q * claim) using 1 <;> ring
    _ = quotaShareCapitalObjective q claim retention loading capital :=
      (hval retention).symm
