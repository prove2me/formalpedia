-- Prove2me | solution 1 for ActuarialValuation.pvLoss_balance
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T11:53:34.693983+00:00
-- url     : https://prove2.me/submissions/07f6240f-3d20-4d32-95e9-4194f212b84f

import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_pvLoss
import Definitions.Def_actuarial_pvPremium

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution {n : ℕ} (benefit annuity : Fin n → ℝ) (premium : ℝ) (i : Fin n) : pvLoss benefit annuity premium i + pvPremium annuity premium i = benefit i := by
  unfold pvLoss
  exact sub_add_cancel (benefit i) (pvPremium annuity premium i)
