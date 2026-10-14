-- Prove2me | solution 1 for ActuarialValuation.ulShortfallPV_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T14:23:44.816746+00:00
-- url     : https://prove2.me/submissions/2a1ea911-9075-4f7f-a710-444ed5af102d

import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_ulShortfallPV
import Mathlib.Algebra.Order.BigOperators.Group.Finset

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution {m : ℕ} (prob discount account floor : Fin m → ℝ) (hp : ∀ ω, 0≤prob ω) (hd : ∀ ω, 0≤discount ω) : 0≤ulShortfallPV prob discount account floor := by
  unfold ulShortfallPV
  apply Finset.sum_nonneg
  intro ω hω
  have hs : 0 ≤ ulGuaranteeShortfall (account ω) (floor ω) := by
    change 0 ≤ max (floor ω - account ω) 0
    exact le_max_right _ _
  exact mul_nonneg (mul_nonneg (hp ω) (hd ω)) hs
