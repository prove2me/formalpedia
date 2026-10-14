-- Prove2me | solution 1 for ActuarialValuation.srFirstHit_disjoint
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T19:21:17.088994+00:00
-- url     : https://prove2.me/submissions/5e1c8a76-40c6-432c-be11-80dd5933d378

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Definitions.Def_actuarial_srFirstHit

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution {Ω : Type*} (u c : ℝ) (W Y : ℕ → Ω → ℝ) (n m : ℕ) (h : n≠m) (ω : Ω) : ¬(srFirstHit u c W Y n ω ∧ srFirstHit u c W Y m ω) := by
  rintro ⟨hn, hm⟩
  rcases lt_or_gt_of_ne h with hnm | hmn
  · exact hm.2 n hnm hn.1
  · exact hn.2 m hmn hm.1
