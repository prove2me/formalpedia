-- Prove2me | solution 1 for ActuarialValuation.ruinProbabilityFinite_succ
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-10T06:51:30.981116+00:00
-- url     : https://prove2.me/submissions/52c905e3-ca86-473a-af46-847549f13110

import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Definitions.Def_actuarial_ruinProbabilityFinite
import Definitions.Def_actuarial_ruinNextSurplus

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution
  (w : ℕ → ℝ) (B c n : ℕ) (u : ℤ) (hu : 0 ≤ u) :
  ruinProbabilityFinite w B c (n + 1) u =
    ∑ k ∈ Finset.range (B + 1),
      w k * ruinProbabilityFinite w B c n
        (ruinNextSurplus u c k) := by
  simp [ruinProbabilityFinite, not_lt_of_ge hu]
