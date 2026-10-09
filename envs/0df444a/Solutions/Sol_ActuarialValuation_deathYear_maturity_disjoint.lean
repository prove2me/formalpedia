-- Prove2me | solution 1 for ActuarialValuation.deathYear_maturity_disjoint
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-09T06:13:30.537032+00:00
-- url     : https://prove2.me/submissions/a30fec57-2080-4d04-b668-70c1470a0adb

import Mathlib
import Definitions.Def_actuarial_curtateSurvivalEvent
import Definitions.Def_actuarial_deathYearEvent
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation
open MeasureTheory

theorem solution {Ω : Type*} (K : Ω → ℕ) (k n : ℕ) (hk : k < n)
    : Disjoint (deathYearEvent K k) (curtateSurvivalEvent K n) := by
  apply Set.disjoint_left.mpr
  intro ω hdeath hmaturity
  have heq : K ω = k := hdeath
  have hs : n ≤ K ω := hmaturity
  omega
