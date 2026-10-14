-- Prove2me | solution 1 for ActuarialValuation.pvAdequacy_loss_cdf
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T11:59:38.501294+00:00
-- url     : https://prove2.me/submissions/f9150dd5-8f76-4f6d-a5ff-6fbd7432c31a

import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_pvAdequacy
import Definitions.Def_actuarial_pvCdf
import Definitions.Def_actuarial_pvLoss

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution {n : ℕ} (p benefit annuity : Fin n → ℝ) (premium : ℝ) : pvAdequacy p benefit annuity premium = pvCdf p (pvLoss benefit annuity premium) 0 := by
  simp [pvAdequacy, pvCdf, pvLoss, pvPremium, sub_nonpos]
