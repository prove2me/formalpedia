-- Prove2me | solution 1 for ActuarialValuation.gammaPoissonCredibility_fundamental
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-10T06:50:37.202568+00:00
-- url     : https://prove2.me/submissions/ee819e8f-ba38-4e13-87c4-f1d7a3f2e928

import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Definitions.Def_actuarial_gammaPoissonCredibilityBlend
import Definitions.Def_actuarial_gammaPoissonPosteriorMean
import Definitions.Def_actuarial_gammaPoissonPosteriorShape
import Definitions.Def_actuarial_gammaPoissonPosteriorRate
import Definitions.Def_actuarial_gammaPoissonExperienceWeight

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution
  (a b e f : ℝ) (c d : ℕ)
  (hb : 0 < b) (he : 0 < e) (hf : 0 ≤ f) :
  (gammaPoissonCredibilityBlend a b e c =
    gammaPoissonPosteriorMean a b e c) ∧
  (gammaPoissonPosteriorMean
     (gammaPoissonPosteriorShape a c)
     (gammaPoissonPosteriorRate b e) f d =
   gammaPoissonPosteriorMean a b (e + f) (c + d)) ∧
  (0 ≤ gammaPoissonExperienceWeight b e ∧
    gammaPoissonExperienceWeight b e ≤ 1) := by
  constructor
  · unfold gammaPoissonCredibilityBlend gammaPoissonExperienceWeight
      gammaPoissonPosteriorMean gammaPoissonPosteriorShape gammaPoissonPosteriorRate
    have hb0 : b ≠ 0 := ne_of_gt hb
    have he0 : e ≠ 0 := ne_of_gt he
    have hbe : b + e ≠ 0 := ne_of_gt (add_pos hb he)
    field_simp [hb0, he0, hbe] <;> ring
  constructor
  · simp [gammaPoissonPosteriorMean, gammaPoissonPosteriorShape,
      gammaPoissonPosteriorRate, Nat.cast_add, add_assoc]
  constructor
  · change 0 ≤ e / (b + e)
    exact div_nonneg (le_of_lt he) (le_of_lt (add_pos hb he))
  · change e / (b + e) ≤ 1
    apply (div_le_iff₀ (add_pos hb he)).2
    simpa only [one_mul] using
      (show e ≤ b + e from le_add_of_nonneg_left (le_of_lt hb))
