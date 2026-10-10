-- Prove2me | solution 1 for ActuarialValuation.perClaimDeductibleCeded_zero_attachment
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-10T06:59:23.766531+00:00
-- url     : https://prove2.me/submissions/7ec0620e-7f02-4947-977c-0a2e9f237364

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_perClaimDeductibleCeded
import Definitions.Def_actuarial_aggregateLossTotal

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (x : ℕ → ℕ) (n : ℕ) :
  perClaimDeductibleCeded x n 0 = aggregateLossTotal x n := by
  simp [perClaimDeductibleCeded, aggregateLossTotal]
