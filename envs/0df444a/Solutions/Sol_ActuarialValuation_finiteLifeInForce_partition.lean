-- Prove2me | solution 1 for ActuarialValuation.finiteLifeInForce_partition
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-09T10:04:33.53645+00:00
-- url     : https://prove2.me/submissions/7815cc42-be14-484c-87b2-365d3c6d5464

import Mathlib
import Definitions.Def_actuarial_finiteLifeDeathIndicator
import Definitions.Def_actuarial_finiteLifeInForceIndicator
open MeasureTheory
open ActuarialValuation

theorem solution (K t : ℕ) :
    finiteLifeInForceIndicator K t =
      finiteLifeDeathIndicator K t + finiteLifeInForceIndicator K (t + 1) := by
  unfold finiteLifeInForceIndicator finiteLifeDeathIndicator
  rcases lt_trichotomy t K with h | rfl | h
  · have hle : t ≤ K := le_of_lt h
    have hs : t + 1 ≤ K := Nat.succ_le_of_lt h
    simp [hle, hs, Ne.symm (ne_of_lt h)]
  · have hnot : ¬ t + 1 ≤ t := Nat.not_succ_le_self t
    simp [Nat.le_refl, hnot]
  · have hnot : ¬ t ≤ K := not_le.mpr h
    have hnot2 : ¬ t + 1 ≤ K := by omega
    simp [hnot, hnot2, Ne.symm (ne_of_gt h)]
