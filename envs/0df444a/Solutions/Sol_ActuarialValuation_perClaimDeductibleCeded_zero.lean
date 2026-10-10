-- Prove2me | solution 1 for ActuarialValuation.perClaimDeductibleCeded_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-10T06:57:59.645332+00:00
-- url     : https://prove2.me/submissions/2f63cb95-9189-463c-bb64-6b242df6786a

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_perClaimDeductibleCeded

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (x : ℕ → ℕ) (d : ℕ) :
  perClaimDeductibleCeded x 0 d = 0 := by
  simp [perClaimDeductibleCeded]
