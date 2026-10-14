-- Prove2me | solution 1 for ActuarialValuation.ruFirstRuin_unique
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T16:32:03.970656+00:00
-- url     : https://prove2.me/submissions/2629e24c-b551-4a77-8b9a-574929784484

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_ruFirstRuin
import Definitions.Def_actuarial_ruRuinAt

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (u c : ℝ) (x : ℕ → ℝ) (n m : ℕ)
    (hn : ruFirstRuin u c x n) (hm : ruFirstRuin u c x m) :
    n=m := by
  rcases lt_trichotomy n m with hlt | heq | hgt
  · exact False.elim ((hm.2 n hlt) hn.1)
  · exact heq
  · exact False.elim ((hn.2 m hgt) hm.1)
