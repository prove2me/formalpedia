-- Prove2me | solution 1 for ActuarialValuation.ipCountPGF_one
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T19:13:28.388153+00:00
-- url     : https://prove2.me/submissions/b9c1ddb5-46e0-4e0a-a0ee-0fbc3864a4e0

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Definitions.Def_actuarial_ipCountPGF

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (p : ℕ → ℝ) :
    ipCountPGF p 1 = (∑' n : ℕ, p n) := by
  simp [ipCountPGF]
