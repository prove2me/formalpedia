-- Prove2me | solution 1 for ActuarialValuation.discreteStopLossPremium_mono
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-09T16:21:26.391926+00:00
-- url     : https://prove2.me/submissions/2dd0fa22-ad2e-4b4d-87f8-28dcf070897c

import Mathlib
import Definitions.Def_actuarial_discreteStopLossPremium

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution
  (w : ℕ → ℝ) (bound d e : ℕ)
  (hw : ∀ s, 0 ≤ w s) (hde : d ≤ e) :
  discreteStopLossPremium w bound e ≤
    discreteStopLossPremium w bound d := by
  unfold discreteStopLossPremium
  apply Finset.sum_le_sum
  intro s hs
  have hnat : s - e ≤ s - d := by omega
  apply mul_le_mul_of_nonneg_right _ (hw s)
  exact_mod_cast hnat
