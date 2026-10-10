-- Prove2me | solution 1 for ActuarialValuation.decrementRiskPremium_zero_at_risk
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-09T14:50:44.867009+00:00
-- url     : https://prove2.me/submissions/9d082226-ee78-484b-8e35-941003588676

import Mathlib
import Definitions.Def_actuarial_decrementRiskPremium
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory

open ActuarialValuation

theorem solution {J : Type*} [Fintype J] (q : J → ℝ) (v Rnext : ℝ)
  :
  decrementRiskPremium q (fun _ => Rnext) v Rnext = 0 := by
  classical
  simp [decrementRiskPremium]
