-- Prove2me | solution 1 for ActuarialValuation.pgConvolve_add
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T17:32:10.933737+00:00
-- url     : https://prove2.me/submissions/fbb44818-8d63-41f0-ade2-493d74650601

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_pgConvolve

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (f g h : ℕ → ℝ) (k : ℕ) : pgConvolve f (fun j => g j+h j) k = pgConvolve f g k+pgConvolve f h k := by
  simp only [pgConvolve, mul_add, Finset.sum_add_distrib]
