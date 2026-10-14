-- Prove2me | solution 1 for ActuarialValuation.pgPanjerRecLaw_one
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T17:47:52.272485+00:00
-- url     : https://prove2.me/submissions/27bce21e-cc29-4f53-b5f4-e4d0654e3cdc

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_pgPanjerRecLaw

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (a b : ℝ) (p : ℕ → ℝ) (m : ℕ) (h : pgPanjerRecLaw a b p m) (hm : 1≤m+1) : p 1 = (a+b)*p 0 := by
  have h1 := h 1 (by decide) hm
  simpa [pgPanjerFactor] using h1
