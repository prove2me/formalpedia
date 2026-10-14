-- Prove2me | solution 1 for ActuarialValuation.srStoppedExp_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T19:13:30.826954+00:00
-- url     : https://prove2.me/submissions/f31eadfe-ea6e-421a-978d-ade71973bde7

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Definitions.Def_actuarial_srStoppedExp

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution {Ω : Type*} (R u c : ℝ) (W Y : ℕ → Ω → ℝ) (N : ℕ) (ω : Ω) : 0≤srStoppedExp R u c W Y N ω := by
  classical
  unfold srStoppedExp
  apply add_nonneg
  · apply Finset.sum_nonneg
    intro n hn
    split_ifs
    · unfold srExpLoss
      exact (Real.exp_pos _).le
    · exact le_refl 0
  · split_ifs
    · exact le_refl 0
    · unfold srExpLoss
      exact (Real.exp_pos _).le
