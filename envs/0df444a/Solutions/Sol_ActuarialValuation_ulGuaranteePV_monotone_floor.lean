-- Prove2me | solution 1 for ActuarialValuation.ulGuaranteePV_monotone_floor
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T14:24:11.852975+00:00
-- url     : https://prove2.me/submissions/c2d9568a-1469-4972-9b5b-711e9975dbf0

import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_ulGuaranteedPV
import Mathlib.Algebra.Order.BigOperators.Group.Finset

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution {m : ℕ} (prob discount account floor1 floor2 : Fin m → ℝ) (hp : ∀ ω,0≤prob ω) (hd : ∀ ω,0≤discount ω) (hfloor : ∀ ω,floor1 ω≤floor2 ω) : ulGuaranteedPV prob discount account floor1 ≤ ulGuaranteedPV prob discount account floor2 := by
  unfold ulGuaranteedPV
  apply Finset.sum_le_sum
  intro ω hω
  have hmax : ulGuaranteePayment (account ω) (floor1 ω) ≤
      ulGuaranteePayment (account ω) (floor2 ω) := by
    change max (account ω) (floor1 ω) ≤ max (account ω) (floor2 ω)
    exact max_le (le_max_left _ _) (le_trans (hfloor ω) (le_max_right _ _))
  exact mul_le_mul_of_nonneg_left hmax (mul_nonneg (hp ω) (hd ω))
