-- Prove2me | solution 1 for ActuarialValuation.finiteReserveLossAtIssue_zero
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-09T09:51:41.925703+00:00
-- url     : https://prove2.me/submissions/e65a731c-a6b1-4189-b8fe-018d671bcc58

import Mathlib
import Definitions.Def_actuarial_finiteReserveLossAtIssue
open MeasureTheory
open ActuarialValuation

theorem solution (K : ℕ) (v : ℝ) (premium benefit reserve : ℕ → ℝ) :
    finiteReserveLossAtIssue K 0 v premium benefit reserve = reserve 0 := by
  simp [finiteReserveLossAtIssue, finiteLifeInForceIndicator, Finset.sum_range_zero,
    pow_zero, Nat.zero_le, zero_add, one_mul, mul_one]
