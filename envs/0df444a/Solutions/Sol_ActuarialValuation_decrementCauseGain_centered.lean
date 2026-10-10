-- Prove2me | solution 1 for ActuarialValuation.decrementCauseGain_centered
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-10T06:57:53.265994+00:00
-- url     : https://prove2.me/submissions/ecac9c02-9a67-4755-8b30-b22162e09ebf

import Mathlib
import Definitions.Def_actuarial_decrementCauseInnovation
import Definitions.Def_actuarial_decrementTailMass
import Definitions.Def_actuarial_decrementYearMass
import Theorems.Thm_ActuarialValuation_decrementCauseGain_collapse_finite
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution
    {C : Type*} [Fintype C] (w rho : ℕ → C → ℝ) (t : ℕ)
    (hw : Summable (fun k : ℕ => ActuarialValuation.decrementYearMass w k))
    (hn : ∀ k e, 0 ≤ w k e)
    (hS : 0 < ActuarialValuation.decrementTailMass w t) :
    (∑' k : ℕ, ∑ d : C,
      w k d * (∑ c : C,
        rho t c * ActuarialValuation.decrementCauseInnovation w t c k d)) = 0 := by
  classical
  let S := ActuarialValuation.decrementTailMass w t
  let M := ∑ c : C, w t c * rho t c
  have hD (k : ℕ) : 0 ≤ ActuarialValuation.decrementYearMass w k := by
    unfold ActuarialValuation.decrementYearMass
    apply Finset.sum_nonneg
    intro e _
    exact hn k e
  have hsumm : Summable
      (fun k : ℕ => if t ≤ k then ActuarialValuation.decrementYearMass w k else 0) := by
    apply Summable.of_nonneg_of_le
    · intro k
      split_ifs
      · exact hD k
      · exact le_refl 0
    · intro k
      split_ifs
      · exact le_refl _
      · exact hD k
    · exact hw
  have hcollapse (k : ℕ) (d : C) :
      (∑ c : C, rho t c *
        ActuarialValuation.decrementCauseInnovation w t c k d) =
        (if k = t then rho t d else 0) -
          (M / S) * (if t ≤ k then (1 : ℝ) else 0) := by
    simpa only [M, S] using
      ActuarialValuation.decrementCauseGain_collapse_finite w rho t k d
  have hrow (k : ℕ) :
      (∑ d : C, w k d * (∑ c : C, rho t c *
        ActuarialValuation.decrementCauseInnovation w t c k d)) =
      (if k = t then M else 0) -
        (M / S) * (if t ≤ k then ActuarialValuation.decrementYearMass w k else 0) := by
    have hfirst : (∑ d : C, w k d * (if k = t then rho t d else 0)) =
        (if k = t then M else 0) := by
      by_cases hkt : k = t
      · subst k
        simp [M]
      · simp [hkt]
    have hsecond :
        (∑ d : C, w k d * ((M / S) * (if t ≤ k then (1 : ℝ) else 0))) =
        (M / S) * (if t ≤ k then ActuarialValuation.decrementYearMass w k else 0) := by
      by_cases htk : t ≤ k
      · simp only [if_pos htk, mul_one]
        unfold ActuarialValuation.decrementYearMass
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro d _
        ring
      · simp [htk]
    calc
      (∑ d : C, w k d * (∑ c : C, rho t c *
        ActuarialValuation.decrementCauseInnovation w t c k d)) =
        ∑ d : C, w k d *
          ((if k = t then rho t d else 0) -
            (M / S) * (if t ≤ k then (1 : ℝ) else 0)) := by
              apply Finset.sum_congr rfl
              intro d _
              rw [hcollapse]
      _ = (if k = t then M else 0) -
        (M / S) * (if t ≤ k then ActuarialValuation.decrementYearMass w k else 0) := by
          simp_rw [mul_sub]
          rw [Finset.sum_sub_distrib, hfirst, hsecond]
  have hspike : Summable (fun k : ℕ => if k = t then M else 0) := by
    apply summable_of_finite_support
    apply (Set.finite_singleton t).subset
    intro k hk
    by_contra hkt
    exact hk (if_neg hkt)
  have htail := hsumm.mul_left (M / S)
  calc
    (∑' k : ℕ, ∑ d : C, w k d * (∑ c : C, rho t c *
        ActuarialValuation.decrementCauseInnovation w t c k d)) =
      ∑' k : ℕ, ((if k = t then M else 0) -
        (M / S) * (if t ≤ k then ActuarialValuation.decrementYearMass w k else 0)) := by
          apply tsum_congr
          intro k
          exact hrow k
    _ = M - (M / S) * S := by
          rw [hspike.tsum_sub htail]
          simp only [tsum_mul_left, tsum_ite_eq]
          rfl
    _ = 0 := by
          have hSnz : S ≠ 0 := ne_of_gt hS
          field_simp
          ring
