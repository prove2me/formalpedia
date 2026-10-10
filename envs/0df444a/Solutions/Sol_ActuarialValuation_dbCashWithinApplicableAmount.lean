-- Prove2me | solution 1 for ActuarialValuation.dbCashWithinApplicableAmount
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-10T07:30:12.491682+00:00
-- url     : https://prove2.me/submissions/f47bbc63-e17d-41fc-9bc5-e28311fdb7c4

import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Algebra.Order.Ring.Unbundled.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_dbHMRCMaximumCash
import Definitions.Def_actuarial_dbCommutationHeadroom

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (g f L : ℝ)
  (hf : 0 < f) :
  (dbCommutationHeadroom g L f ≥ 0 ↔ L ≤ dbHMRCMaximumCash g f) := by
  have hfn : f ≠ 0 := ne_of_gt hf
  have hd : (0 : ℝ) < 20 + 3*f := by linarith
  have hdn : 20 + 3*f ≠ 0 := ne_of_gt hd
  have hfactor :
      f * dbCommutationHeadroom g L f =
        (20 + 3*f) * (dbHMRCMaximumCash g f - L) := by
    unfold dbCommutationHeadroom dbCommutedPension dbHMRCMaximumCash
    field_simp [hfn, hdn]
    ring
  constructor
  · intro h
    have hm : 0 ≤ f * dbCommutationHeadroom g L f :=
      mul_nonneg (le_of_lt hf) h
    rw [hfactor] at hm
    have hh : 0 ≤ dbHMRCMaximumCash g f - L :=
      (mul_nonneg_iff_of_pos_left hd).mp hm
    linarith
  · intro h
    have hn : 0 ≤ dbHMRCMaximumCash g f - L := sub_nonneg.mpr h
    have hm : 0 ≤ (20 + 3*f) * (dbHMRCMaximumCash g f - L) :=
      (mul_nonneg_iff_of_pos_left hd).mpr hn
    rw [←hfactor] at hm
    exact (mul_nonneg_iff_of_pos_left hf).mp hm
