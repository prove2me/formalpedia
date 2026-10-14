-- Prove2me | solution 1 for ActuarialValuation.ipFold_successor
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T19:16:44.240514+00:00
-- url     : https://prove2.me/submissions/8e968881-f13d-4288-b560-2595839d2a35

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Definitions.Def_actuarial_ipConvolve
import Definitions.Def_actuarial_ipFold

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (f : ℕ → ℝ) (n k : ℕ) :
    ipFold f (n+1) k = ipConvolve f (ipFold f n) k := by
  rfl
