-- Prove2me | solution 1 for ActuarialValuation.dbHMRCMaximumCash_le_gross
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-10T07:18:17.491486+00:00
-- url     : https://prove2.me/submissions/1ffb11dd-18e3-4d04-836b-332324992ac4

import Mathlib.Tactic.Linarith
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_dbHMRCMaximumCash

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (g f : ℝ)
  (hg : 0 ≤ g) (hf : 0 < f) : dbHMRCMaximumCash g f ≤ f * g := by
  unfold dbHMRCMaximumCash
  have hd : (0:ℝ) < 20 + 3*f := by linarith
  apply (div_le_iff₀ hd).2
  have hfg : 0 ≤ f*g := mul_nonneg (le_of_lt hf) hg
  nlinarith [mul_nonneg hfg (le_of_lt hf)]
