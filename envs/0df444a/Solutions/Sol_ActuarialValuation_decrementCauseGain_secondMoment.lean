-- Prove2me | solution 1 for ActuarialValuation.decrementCauseGain_secondMoment
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-10T06:58:06.604543+00:00
-- url     : https://prove2.me/submissions/f371846a-52cb-40cf-b5bd-42b50ddb7031

import Mathlib
import Definitions.Def_actuarial_decrementCauseInnovation
import Definitions.Def_actuarial_decrementAnnualRisk
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
    (∑' k : ℕ, ∑ d : C, w k d *
      (∑ c : C, rho t c *
        ActuarialValuation.decrementCauseInnovation w t c k d) ^ 2) =
      ActuarialValuation.decrementAnnualRisk w rho t := by
  classical
  let S := ActuarialValuation.decrementTailMass w t
  let M := ∑ c : C, w t c * rho t c
  let A := ∑ c : C, w t c * (rho t c) ^ 2
  have hD (k : ℕ) : 0 ≤ ActuarialValuation.decrementYearMass w k := by
    unfold ActuarialValuation.decrementYearMass
    apply Finset.sum_nonneg
    intro d _
    exact hn k d
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
  have hpoint (k : ℕ) (d : C) :
      (∑ c : C, rho t c *
        ActuarialValuation.decrementCauseInnovation w t c k d) ^ 2 =
      (if k = t then (rho t d) ^ 2 else 0) -
        (2 * (M / S)) * (if k = t then rho t d else 0) +
        (M / S) ^ 2 * (if t ≤ k then (1 : ℝ) else 0) := by
    rw [hcollapse]
    by_cases hk : k = t
    · subst k
      simp
      ring
    · by_cases ht : t ≤ k
      · simp [hk, ht]
      · simp [hk, ht]
  have hrow (k : ℕ) :
      (∑ d : C, w k d * (∑ c : C, rho t c *
        ActuarialValuation.decrementCauseInnovation w t c k d) ^ 2) =
        (if k = t then A else 0) -
          (2 * (M / S)) * (if k = t then M else 0) +
          (M / S) ^ 2 *
            (if t ≤ k then ActuarialValuation.decrementYearMass w k else 0) := by
    have hArow : (∑ d : C, w k d *
        (if k = t then (rho t d) ^ 2 else 0)) =
        (if k = t then A else 0) := by
      by_cases hk : k = t
      · subst k
        simp [A]
      · simp [hk]
    have hMrow : (∑ d : C, w k d *
        (if k = t then rho t d else 0)) =
        (if k = t then M else 0) := by
      by_cases hk : k = t
      · subst k
        simp [M]
      · simp [hk]
    have hDrow : (∑ d : C,
        if t ≤ k then w k d else 0) =
        (if t ≤ k then ActuarialValuation.decrementYearMass w k else 0) := by
      by_cases ht : t ≤ k
      · simp [ht, ActuarialValuation.decrementYearMass]
      · simp [ht]
    calc
      (∑ d : C, w k d * (∑ c : C, rho t c *
        ActuarialValuation.decrementCauseInnovation w t c k d) ^ 2) =
        ∑ d : C, (w k d * (if k = t then (rho t d) ^ 2 else 0) -
          (2 * (M / S)) * (w k d * (if k = t then rho t d else 0)) +
          (M / S) ^ 2 * (if t ≤ k then w k d else 0)) := by
            apply Finset.sum_congr rfl
            intro d _
            rw [hpoint k d]
            by_cases hk : k = t
            · subst k
              simp <;> ring
            · by_cases ht : t ≤ k
              · simp [hk, ht] <;> ring
              · simp [hk, ht]
      _ = (if k = t then A else 0) -
          (2 * (M / S)) * (if k = t then M else 0) +
          (M / S) ^ 2 *
            (if t ≤ k then ActuarialValuation.decrementYearMass w k else 0) := by
              rw [Finset.sum_add_distrib, Finset.sum_sub_distrib]
              rw [← Finset.mul_sum, ← Finset.mul_sum]
              rw [hArow, hMrow, hDrow]
  have hspike (v : ℝ) : Summable (fun k : ℕ => if k = t then v else 0) := by
    apply summable_of_finite_support
    apply (Set.finite_singleton t).subset
    intro k hk
    by_contra hkt
    exact hk (if_neg hkt)
  have hA := hspike A
  have hM := (hspike M).mul_left (2 * (M / S))
  have hT := hsumm.mul_left ((M / S) ^ 2)
  calc
    (∑' k : ℕ, ∑ d : C, w k d * (∑ c : C, rho t c *
      ActuarialValuation.decrementCauseInnovation w t c k d) ^ 2) =
      ∑' k : ℕ, ((if k = t then A else 0) -
        (2 * (M / S)) * (if k = t then M else 0) +
        (M / S) ^ 2 *
          (if t ≤ k then ActuarialValuation.decrementYearMass w k else 0)) := by
            apply tsum_congr
            intro k
            exact hrow k
    _ = A - (2 * (M / S)) * M + (M / S) ^ 2 * S := by
          rw [(hA.sub hM).tsum_add hT, hA.tsum_sub hM]
          simp only [tsum_mul_left, tsum_ite_eq]
          rfl
    _ = ActuarialValuation.decrementAnnualRisk w rho t := by
          unfold ActuarialValuation.decrementAnnualRisk
          dsimp [A, M]
          have hs : S ≠ 0 := ne_of_gt hS
          field_simp
          ring
