-- Prove2me | solution 1 for ActuarialValuation.wholeLifeYearInnovation_orthogonal
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-09T15:52:36.640722+00:00
-- url     : https://prove2.me/submissions/30cb59ad-dcff-4da1-a1f6-b911d8c96503

import Mathlib
import Definitions.Def_actuarial_wholeLifeYearInnovation
import Definitions.Def_actuarial_wholeLifeTailMass

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (w : ℕ → ℝ) (i j : ℕ)
  (hw : Summable w) (hi : i < j)
  (hSi : 0 < wholeLifeTailMass w i)
  (hSj : 0 < wholeLifeTailMass w j) :
  (∑' k : ℕ, w k *
    wholeLifeYearInnovation w i k * wholeLifeYearInnovation w j k) = 0 := by
  have hmean : (∑' k : ℕ, w k * wholeLifeYearInnovation w j k) = 0 := by
    let c : ℝ := w j / wholeLifeTailMass w j
    have hsingle : Summable (fun k : ℕ => if k = j then w k else 0) := by
      apply (hw.norm).of_norm_bounded
      intro k
      split_ifs <;> simp [Real.norm_eq_abs]
    have htail : Summable (fun k : ℕ => if j ≤ k then w k else 0) := by
      apply (hw.norm).of_norm_bounded
      intro k
      split_ifs <;> simp [Real.norm_eq_abs]
    have hctail : Summable (fun k : ℕ => c * (if j ≤ k then w k else 0)) :=
      htail.mul_left c
    have hpoint (k : ℕ) :
        w k * wholeLifeYearInnovation w j k =
          (if k = j then w k else 0) -
            c * (if j ≤ k then w k else 0) := by
      simp [wholeLifeYearInnovation, c, mul_sub, mul_ite, mul_assoc]
      split_ifs <;> ring
    calc
      (∑' k : ℕ, w k * wholeLifeYearInnovation w j k) =
          ∑' k : ℕ, ((if k = j then w k else 0) -
            c * (if j ≤ k then w k else 0)) := by
            apply tsum_congr
            intro k
            exact hpoint k
      _ = (∑' k : ℕ, if k = j then w k else 0) -
          c * (∑' k : ℕ, if j ≤ k then w k else 0) := by
            rw [hsingle.tsum_sub hctail, tsum_mul_left]
      _ = w j - c * wholeLifeTailMass w j := by
            simp [wholeLifeTailMass] <;> ring
      _ = 0 := by
            dsimp [c]
            field_simp [ne_of_gt hSj] <;> ring
  have hpoint (k : ℕ) :
      w k * wholeLifeYearInnovation w i k *
        wholeLifeYearInnovation w j k =
      -(w i / wholeLifeTailMass w i) *
        (w k * wholeLifeYearInnovation w j k) := by
    by_cases hk : k < j
    · have hzero : wholeLifeYearInnovation w j k = 0 := by
        have hkne : k ≠ j := ne_of_lt hk
        have hnot : ¬ j ≤ k := not_le.mpr hk
        simp [wholeLifeYearInnovation, hkne, hnot]
      simp [hzero]
    · have hjk : j ≤ k := le_of_not_gt hk
      have hik : i < k := lt_of_lt_of_le hi hjk
      have hval : wholeLifeYearInnovation w i k =
          -(w i / wholeLifeTailMass w i) := by
        have hkne : k ≠ i := ne_of_gt hik
        have hle : i ≤ k := le_of_lt hik
        simp [wholeLifeYearInnovation, hkne, hle]
      rw [hval]
      ring
  calc
    (∑' k : ℕ, w k * wholeLifeYearInnovation w i k *
      wholeLifeYearInnovation w j k) =
      ∑' k : ℕ, -(w i / wholeLifeTailMass w i) *
        (w k * wholeLifeYearInnovation w j k) := by
      apply tsum_congr
      intro k
      exact hpoint k
    _ = -(w i / wholeLifeTailMass w i) *
      (∑' k : ℕ, w k * wholeLifeYearInnovation w j k) := by
        rw [tsum_mul_left]
    _ = 0 := by
      rw [hmean]
      ring

