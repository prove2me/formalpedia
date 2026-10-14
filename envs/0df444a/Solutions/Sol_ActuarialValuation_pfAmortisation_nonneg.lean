-- Prove2me | solution 1 for ActuarialValuation.pfAmortisation_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T19:31:18.003275+00:00
-- url     : https://prove2.me/submissions/aad7b910-b830-485a-8af4-911916c49772

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_pfAmortisation

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (deficit annuity : ℝ) (hd : 0≤deficit) (ha : 0<annuity) : 0≤pfAmortisation deficit annuity := by
  unfold pfAmortisation
  exact div_nonneg hd ha.le
