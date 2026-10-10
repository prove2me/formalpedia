-- Prove2me | solution 1 for ActuarialValuation.aggregateBernoulliPMF_support
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-09T16:07:40.275984+00:00
-- url     : https://prove2.me/submissions/1dfe944a-4d9a-4845-b1d5-f1f9c34d9731

import Mathlib
import Definitions.Def_actuarial_aggregateBernoulliPMF
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (p : ℝ) (b s : ℕ) (h : b < s) :
    aggregateBernoulliPMF p b s = 0 := by
  have h0 : s ≠ 0 := by omega
  have hb : s ≠ b := by omega
  simp [aggregateBernoulliPMF, h0, hb]
