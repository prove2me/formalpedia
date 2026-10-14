-- Prove2me | solution 1 for ActuarialValuation.srExpLoss_at_ruin
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T19:19:39.123356+00:00
-- url     : https://prove2.me/submissions/32fb8635-f985-4a97-8738-c17a8449378c

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Definitions.Def_actuarial_srRuinAt
import Definitions.Def_actuarial_srExpLoss

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution {Ω : Type*} (R u c : ℝ) (W Y : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) (hR : 0<R) (h : srRuinAt u c W Y n ω) : Real.exp (R*u)<srExpLoss R c W Y n ω := by
  have hnet : u < srNetLoss c W Y n ω := by
    change u - srNetLoss c W Y n ω < 0 at h
    exact (sub_lt_zero).mp h
  unfold srExpLoss
  exact Real.exp_lt_exp.mpr (mul_lt_mul_of_pos_left hnet hR)
