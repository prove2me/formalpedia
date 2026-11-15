-- Prove2me | solution 1 for AppliedSDE.SarkkaSolin.rejection_uniform_slice_mass
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T09:36:15.532361+00:00
-- url     : https://prove2.me/submissions/de610eee-6d91-439c-a0b4-91351ea2ce1f

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory
set_option autoImplicit false
theorem solution
    (w : ℝ) (hw0 : 0 ≤ w) (hw1 : w ≤ 1) :
    ((volume : Measure ℝ).restrict (Set.Icc 0 1)) (Set.Iic w) =
      ENNReal.ofReal w := by
  rw [Measure.restrict_apply measurableSet_Iic]
  have hs : Set.Iic w ∩ Set.Icc (0 : ℝ) 1 =
      Set.Icc 0 w := by
    ext z
    simp only [Set.mem_inter_iff, Set.mem_Iic, Set.mem_Icc]
    constructor
    · intro hz
      exact And.intro hz.2.1 hz.1
    · intro hz
      exact And.intro hz.2 (And.intro hz.1 (le_trans hz.2 hw1))
  rw [hs, Real.volume_Icc, sub_zero]
