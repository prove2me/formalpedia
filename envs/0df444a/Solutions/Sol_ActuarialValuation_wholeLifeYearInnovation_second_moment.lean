-- Prove2me | solution 1 for ActuarialValuation.wholeLifeYearInnovation_second_moment
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-09T15:48:32.865607+00:00
-- url     : https://prove2.me/submissions/a0a9ec0a-2cf3-4b13-98dd-a641a1abf54c

import Mathlib
import Definitions.Def_actuarial_wholeLifeYearInnovation
import Definitions.Def_actuarial_wholeLifeTailMass

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (w : ℕ → ℝ) (t : ℕ)
  (hw : Summable w) (hS : 0 < wholeLifeTailMass w t) :
  (∑' k : ℕ, w k * (wholeLifeYearInnovation w t k) ^ 2) =
    w t * (wholeLifeTailMass w (t + 1) / wholeLifeTailMass w t) := by
  let c : ℝ := w t / wholeLifeTailMass w t
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
  have hsplit :
      wholeLifeTailMass w t = w t + wholeLifeTailMass w (t + 1) := by
    change (∑' k : ℕ, if t ≤ k then w k else 0) =
      w t + (∑' k : ℕ, if t + 1 ≤ k then w k else 0)
    calc
      (∑' k : ℕ, if t ≤ k then w k else 0) =
          ∑' k : ℕ, ((if k = t then w k else 0) +
            (if t + 1 ≤ k then w k else 0)) := by
        apply tsum_congr
        intro k
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
      _ = (∑' k : ℕ, if k = t then w k else 0) +
          (∑' k : ℕ, if t + 1 ≤ k then w k else 0) := by
            rw [hsingle.tsum_add (htail (t + 1))]
      _ = w t + (∑' k : ℕ, if t + 1 ≤ k then w k else 0) := by
        simp
  have hsingleq :
      Summable (fun k : ℕ => (if k = t then w k else 0) * (1 - c) ^ 2) :=
    hsingle.mul_right _
  have htailq :
      Summable (fun k : ℕ => c ^ 2 * (if t + 1 ≤ k then w k else 0)) :=
    (htail (t + 1)).mul_left _
  have hpoint (k : ℕ) :
      w k * (wholeLifeYearInnovation w t k) ^ 2 =
        (if k = t then w k else 0) * (1 - c) ^ 2 +
          c ^ 2 * (if t + 1 ≤ k then w k else 0) := by
    rcases lt_trichotomy k t with hlt | heq | hgt
    · have hne : k ≠ t := ne_of_lt hlt
      have hnot : ¬ t ≤ k := not_le.mpr hlt
      have hnot' : ¬ t + 1 ≤ k := by omega
      simp [wholeLifeYearInnovation, c, hne, hnot, hnot']
    · subst k
      simp [wholeLifeYearInnovation, c]
    · have hne : k ≠ t := ne_of_gt hgt
      have hle : t ≤ k := le_of_lt hgt
      have hnext : t + 1 ≤ k := by omega
      simp [wholeLifeYearInnovation, c, hne, hle, hnext]
      ring
  have hcalc :
      (∑' k : ℕ, w k * (wholeLifeYearInnovation w t k) ^ 2) =
        w t * (1 - c) ^ 2 + c ^ 2 * wholeLifeTailMass w (t + 1) := by
    calc
      _ = ∑' k : ℕ, ((if k = t then w k else 0) * (1 - c) ^ 2 +
        c ^ 2 * (if t + 1 ≤ k then w k else 0)) := by
          apply tsum_congr
          intro k
          exact hpoint k
      _ = (∑' k : ℕ, (if k = t then w k else 0) * (1 - c) ^ 2) +
          (∑' k : ℕ, c ^ 2 * (if t + 1 ≤ k then w k else 0)) := by
            rw [hsingleq.tsum_add htailq]
      _ = w t * (1 - c) ^ 2 +
          c ^ 2 * wholeLifeTailMass w (t + 1) := by
            have ha : (∑' k : ℕ,
                (if k = t then w k else 0) * (1 - c) ^ 2) =
                  w t * (1 - c) ^ 2 := by
                    rw [tsum_mul_right]
                    simp
            have hb : (∑' k : ℕ,
                c ^ 2 * (if t + 1 ≤ k then w k else 0)) =
                  c ^ 2 * wholeLifeTailMass w (t + 1) := by
                    rw [tsum_mul_left]
                    rfl
            rw [ha, hb]
  have hsplit' :
      wholeLifeTailMass w (t + 1) =
      wholeLifeTailMass w t - w t := by
    linarith [hsplit]
  rw [hcalc, hsplit']
  dsimp [c]
  have hsne : wholeLifeTailMass w t ≠ 0 := ne_of_gt hS
  field_simp [hsne]
  ring
