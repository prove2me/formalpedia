-- Prove2me | solution 1 for ActuarialValuation.wholeLifeTailMass_succ_helperXXIII
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-09T23:07:56.764991+00:00
-- url     : https://prove2.me/submissions/710843fb-a056-4396-8315-e9beded930d8

import Mathlib
import Definitions.Def_actuarial_wholeLifeTailMass

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (w : ℕ → ℝ) (t : ℕ) (hw : Summable w) :
  wholeLifeTailMass w t = w t + wholeLifeTailMass w (t + 1) := by
  have htail (n : ℕ) :
      Summable (fun k : ℕ => if n ≤ k then w k else 0) := by
    apply (hw.norm).of_norm_bounded
    intro k
    split_ifs <;> simp [Real.norm_eq_abs]
  have hsingle :
      Summable (fun k : ℕ => if k = t then w k else 0) := by
    apply (hw.norm).of_norm_bounded
    intro k
    split_ifs <;> simp [Real.norm_eq_abs]
  have hpoint (k : ℕ) :
      (if t ≤ k then w k else 0) =
        (if k = t then w k else 0) +
          (if t + 1 ≤ k then w k else 0) := by
    rcases lt_trichotomy k t with hlt | heq | hgt
    · have hne : k ≠ t := ne_of_lt hlt
      have hnot : ¬ t ≤ k := not_le.mpr hlt
      have hnot' : ¬ t + 1 ≤ k := by omega
      simp [hne, hnot, hnot']
    · subst k
      simp
    · have hne : k ≠ t := ne_of_gt hgt
      have hle : t ≤ k := le_of_lt hgt
      have hnext : t + 1 ≤ k := by omega
      simp [hne, hle, hnext]
  change (∑' k : ℕ, if t ≤ k then w k else 0) =
    w t + (∑' k : ℕ, if t + 1 ≤ k then w k else 0)
  calc
    (∑' k : ℕ, if t ≤ k then w k else 0) =
        ∑' k : ℕ, ((if k = t then w k else 0) +
          (if t + 1 ≤ k then w k else 0)) := by
      exact tsum_congr hpoint
    _ = (∑' k : ℕ, if k = t then w k else 0) +
        (∑' k : ℕ, if t + 1 ≤ k then w k else 0) := by
          rw [hsingle.tsum_add (htail (t + 1))]
    _ = w t + (∑' k : ℕ, if t + 1 ≤ k then w k else 0) := by
      simp
