-- Prove2me | solution 1 for ActuarialValuation.irReinflate_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T19:58:39.513989+00:00
-- url     : https://prove2.me/submissions/20633098-c14b-4126-a2b1-6ba1ef249e70

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_irReinflate

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (claim future base : ℝ) (hc : 0≤claim) (hf : 0≤future) (hb : 0<base) : 0≤irReinflate claim future base := by
  unfold irReinflate
  exact div_nonneg (mul_nonneg hc hf) (le_of_lt hb)
