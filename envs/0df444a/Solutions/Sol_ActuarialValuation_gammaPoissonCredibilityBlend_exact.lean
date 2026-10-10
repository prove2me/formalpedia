-- Prove2me | solution 1 for ActuarialValuation.gammaPoissonCredibilityBlend_exact
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-10T06:41:33.538982+00:00
-- url     : https://prove2.me/submissions/97e52f48-775d-41cc-ae09-93723e825eaf

import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Definitions.Def_actuarial_gammaPoissonCredibilityBlend
import Definitions.Def_actuarial_gammaPoissonExperienceWeight
import Definitions.Def_actuarial_gammaPoissonPosteriorMean

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution
  (a b e : ℝ) (c : ℕ)
  (hb : 0 < b) (he : 0 < e) :
  gammaPoissonCredibilityBlend a b e c =
    gammaPoissonPosteriorMean a b e c := by
  unfold gammaPoissonCredibilityBlend gammaPoissonExperienceWeight
    gammaPoissonPosteriorMean gammaPoissonPosteriorShape gammaPoissonPosteriorRate
  have hb0 : b ≠ 0 := ne_of_gt hb
  have he0 : e ≠ 0 := ne_of_gt he
  have hbe : b + e ≠ 0 := ne_of_gt (add_pos hb he)
  field_simp [hb0, he0, hbe] <;> ring
