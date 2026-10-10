-- Prove2me | solution 1 for ActuarialValuation.decrementAnnualRisk_cause_cross
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-09T15:57:21.746667+00:00
-- url     : https://prove2.me/submissions/ecf4f0f1-b0fa-4eb5-852c-897cbbca99f6

import Mathlib
import Definitions.Def_actuarial_decrementCauseInnovation
import Definitions.Def_actuarial_decrementTailMass
import Definitions.Def_actuarial_decrementYearMass
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution {C : Type*} [Fintype C]
  (w : ℕ → C → ℝ) (t : ℕ) (c d : C)
  (hw : Summable (fun k : ℕ => decrementYearMass w k))
  (hn : ∀ k e, 0 ≤ w k e)
  (hS : 0 < decrementTailMass w t) (hcd : c ≠ d) :
  (∑' k : ℕ, ∑ e : C, w k e *
      decrementCauseInnovation w t c k e *
      decrementCauseInnovation w t d k e) =
    -(w t c * w t d / decrementTailMass w t) := by
  classical
  let S := decrementTailMass w t
  let qc := w t c / S
  let qd := w t d / S
  have hD (k : ℕ) : 0 ≤ decrementYearMass w k := by
    unfold decrementYearMass
    apply Finset.sum_nonneg
    intro e _
    exact hn k e
  have hsumm : Summable (fun k : ℕ => if t ≤ k then decrementYearMass w k else 0) := by
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
  have hpoint (k : ℕ) (e : C) :
      w k e * decrementCauseInnovation w t c k e *
        decrementCauseInnovation w t d k e =
        qc * qd * (if t ≤ k then w k e else 0) -
          qd * (if k = t ∧ e = c then w k e else 0) -
          qc * (if k = t ∧ e = d then w k e else 0) := by
    by_cases hkt : k = t
    · subst k
      by_cases hec : e = c
      · have hed : e ≠ d := by
          intro hed
          exact hcd (hec.symm.trans hed)
        simp [decrementCauseInnovation, qc, qd, S, hec, hed, hcd]
        ring
      · by_cases hed : e = d
        · subst e
          have hdc : d ≠ c := Ne.symm hcd
          simp [decrementCauseInnovation, qc, qd, S, hcd, hdc]
          ring
        · simp [decrementCauseInnovation, qc, qd, S, hec, hed, hcd]
          ring
    · by_cases htk : t ≤ k
      · simp [decrementCauseInnovation, qc, qd, S, hkt, htk]
        ring
      · simp [decrementCauseInnovation, qc, qd, S, hkt, htk]
  have hrow (k : ℕ) :
      (∑ e : C, w k e * decrementCauseInnovation w t c k e *
        decrementCauseInnovation w t d k e) =
        qc * qd * (if t ≤ k then decrementYearMass w k else 0) -
          qd * (if k = t then w t c else 0) -
          qc * (if k = t then w t d else 0) := by
    have hsurv : (∑ e : C, if t ≤ k then w k e else 0) =
        if t ≤ k then decrementYearMass w k else 0 := by
      by_cases ht : t ≤ k
      · simp [ht, decrementYearMass]
      · simp [ht]
    have hevent (a : C) :
        (∑ e : C, if k = t ∧ e = a then w k e else 0) =
        if k = t then w t a else 0 := by
      by_cases hk : k = t
      · subst k
        simp
      · simp [hk]
    calc
      (∑ e : C, w k e * decrementCauseInnovation w t c k e *
        decrementCauseInnovation w t d k e) =
        ∑ e : C, (qc * qd * (if t ≤ k then w k e else 0) -
          qd * (if k = t ∧ e = c then w k e else 0) -
          qc * (if k = t ∧ e = d then w k e else 0)) := by
            apply Finset.sum_congr rfl
            intro e _
            exact hpoint k e
      _ = qc * qd * (if t ≤ k then decrementYearMass w k else 0) -
          qd * (if k = t then w t c else 0) -
          qc * (if k = t then w t d else 0) := by
            rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib]
            rw [← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum]
            rw [hsurv, hevent c, hevent d]
  have hsing (a : C) :
      Summable (fun k : ℕ => if k = t then w t a else 0) := by
    apply summable_of_finite_support
    have hfin : (Function.support (fun k : ℕ => if k = t then w t a else 0)).Finite := by
      apply (Set.finite_singleton t).subset
      intro k hk
      by_contra hkt
      have hz : (if k = t then w t a else 0) = 0 := if_neg hkt
      exact hk hz
    exact hfin
  have hA := hsumm.mul_left (qc * qd)
  have hB := (hsing c).mul_left qd
  have hC := (hsing d).mul_left qc
  calc
    (∑' k : ℕ, ∑ e : C, w k e *
      decrementCauseInnovation w t c k e *
      decrementCauseInnovation w t d k e) =
      ∑' k : ℕ, (qc * qd * (if t ≤ k then decrementYearMass w k else 0) -
        qd * (if k = t then w t c else 0) -
        qc * (if k = t then w t d else 0)) := by
          apply tsum_congr
          intro k
          exact hrow k
    _ = qc * qd * S - qd * w t c - qc * w t d := by
          rw [(hA.sub hB).tsum_sub hC, hA.tsum_sub hB]
          simp only [tsum_mul_left, tsum_ite_eq]
          rfl
    _ = -(w t c * w t d / S) := by
          dsimp [qc, qd]
          have hSnz : S ≠ 0 := ne_of_gt hS
          field_simp
          ring
