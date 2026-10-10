-- Prove2me | solution 1 for ActuarialValuation.cm1ReversionaryAnnuity_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-10T07:18:52.939048+00:00
-- url     : https://prove2.me/submissions/ec24bb62-43ce-48e7-94c2-738cc3f16fa4

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Definitions.Def_actuarial_cm1ReversionaryAnnuity
import Mathlib.Algebra.Order.BigOperators.Group.Finset
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (discount pY both : ℕ → ℝ) (n : ℕ) (hd : ∀ t ∈ Finset.range n, 0 ≤ discount t) (hp : ∀ t ∈ Finset.range n, both t ≤ pY t) : 0 ≤ cm1ReversionaryAnnuity discount pY both n := by
  unfold cm1ReversionaryAnnuity
  apply Finset.sum_nonneg
  intro t ht
  apply mul_nonneg (hd t ht)
  unfold cm1ReversionaryIndicator
  exact sub_nonneg.mpr (hp t ht)
