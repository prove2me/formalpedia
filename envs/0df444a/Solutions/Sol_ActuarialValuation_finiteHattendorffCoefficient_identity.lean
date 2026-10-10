-- Prove2me | solution 1 for ActuarialValuation.finiteHattendorffCoefficient_identity
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-10T08:46:25.668453+00:00
-- url     : https://prove2.me/submissions/4a86eb65-fa00-4fb3-95ad-d712bb5016bb

import Mathlib.Data.Real.Basic
import Definitions.Def_actuarial_finiteHattendorffNetAtRisk

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (v : ℝ) (benefit reserve : ℕ → ℝ) (t : ℕ) :
    finiteHattendorffNetAtRisk v benefit reserve t =
      v ^ (t + 1) * (benefit (t + 1) - reserve (t + 1)) := by
  rfl
