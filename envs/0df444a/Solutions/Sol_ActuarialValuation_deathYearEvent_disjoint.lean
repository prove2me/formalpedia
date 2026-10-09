-- Prove2me | solution 1 for ActuarialValuation.deathYearEvent_disjoint
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-08T19:20:47.030983+00:00
-- url     : https://prove2.me/submissions/790e95cb-c063-4983-bd30-198558ace877

import Mathlib
import Definitions.Def_actuarial_deathYearEvent
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation
open MeasureTheory

theorem solution {Ω : Type*} (K : Ω → ℕ)
    (i j : ℕ) (hij : i ≠ j)
    :
    Disjoint (deathYearEvent K i) (deathYearEvent K j) := by
  apply Set.disjoint_left.mpr
  intro ω hi hj
  have hi' : K ω = i := hi
  have hj' : K ω = j := hj
  exact hij (hi'.symm.trans hj')
