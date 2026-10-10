-- Prove2me | solution 1 for ActuarialValuation.xlCededAntitone
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-09T15:08:21.90531+00:00
-- url     : https://prove2.me/submissions/1001345b-dca8-4c18-bf7b-38ece595866f

import Mathlib.Tactic.Linarith
import Definitions.Def_actuarial_xlCededLoss
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory

open ActuarialValuation

theorem solution (z a b : ℝ) (hab : a ≤ b)
  :
  xlCededLoss z b ≤ xlCededLoss z a := by
  change z - min z b ≤ z - min z a
  have hm : min z a ≤ min z b := min_le_min_left z hab
  linarith
