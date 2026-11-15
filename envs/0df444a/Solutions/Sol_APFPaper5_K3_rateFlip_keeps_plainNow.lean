-- Prove2me | solution 1 for APFPaper5.K3.rateFlip_keeps_plainNow
-- status  : ACCEPTED   (prove)
-- author  : @FiniteUniverse
-- created : 2026-11-14T06:50:37.293205+00:00
-- url     : https://prove2.me/submissions/3ce9f0b8-4ba1-4be0-91e7-0c8d27ac95db

/-
APF Foundation Ledger — theorem node DRAFT (session EthanBrooke-01WrrBvu, 2026-11-13; not gated, not reviewed)
name: APFPaper5_K3_reversal_on_the_carrier
title: On two held components, the turn of one against the other has a reverse with the same present records, so the present records do not fix the physical object; with no rates no moving hold has one
inputs_revision: 2026-10-04.1
mathlib_rev: 0df444a360eaa60ab8c11dca51a86af692955474
source: Thm_APFB01_reversal_and_the_rate. Paper 5 Supplement v7.33:1617-1650, 1656. FOUNDATION_INPUTS B01.
consumes_inputs: B01 in APFB01.rate_is_held_on_the_carrier only, through its descent form. The others none.
standing: theorems about the supplied MODEL of two held components.
statement: (rateFlip_keeps_plainNow) reversing both rates changes none of the present records.
 (relativeTurn_of_reverse) turning the second component of a reversed state is the reverse of turning it the
 other way.
 (relativeTurn_moves_plainNow) for a turn that is not the identity or the half turn, some state reads
 differently one step earlier and one step later.
 (same_present_records_different_later) so some state and its reverse have the same present records and
 different records after the turn.
 (APFB01.rate_is_held_on_the_carrier) if what the records read after the turn is a physical fact, that state
 and its reverse are different physical objects with the same present records.
 (plainNow_neg2, rateFree_present_records_fix_state) among states with no rate, the present records fix the
 state up to the half turn of both components, which no record sees.
 (rateFree_hold_with_reverse_has_no_direction) so on the states with no rate, a hold that has a reverse reads
 the same one step later as one step earlier.
 (plane_has_no_reverse) and the recombining turn, which does move the records of states with no rate, has
 no reverse there.
 (plainNow_mix, mix_later_fixed_by_present, mix_has_no_reverse) on the full model too, the present records
 fix what they read after the recombining turn, so that turn has no reverse with the same present records.
 A reverse cannot be asked of every hold.
reading: given a hold that moves the present records, "the rate is held" and "the hold has a reverse with
 the same present records" stand or fall together in this model.
not_claimed: that the turn of one component is an admitted hold at any interface; that it has a reverse
 among the held states of an interface; a derivation of the rate from the declared inputs alone.
-/
import Definitions.Def_APFPaper5_K3_PresentRecords
import Definitions.Def_APFPaper5_K3_HeldMaps
import Definitions.Def_APFPaper5_K3_LinearOnTwoComponents
import Definitions.Def_APFPaper5_K4_CompositeOnly
import Theorems.Thm_APFPaper5_K3_no_direction_if_present_records_fix_later
import Theorems.Thm_APFB01_distinct_objects_of_later_record
import Theorems.Thm_APFB01_rate_is_held_of_reversal
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

set_option autoImplicit false

universe uP

namespace APFPaper5.K3

open APFPaper5.K4 (RateFree)

theorem rateFlip_keeps_plainNow (h : Held2) : plainNow (rateFlip h) = plainNow h := by
  have e1 : recA (rateFlip h) = recA h := by dsimp only [recA, rateFlip]; ring
  have e2 : recB (rateFlip h) = recB h := by dsimp only [recB, rateFlip]; ring
  have e3 : recSum (rateFlip h) = recSum h := by dsimp only [recSum, rateFlip]; ring
  show (recA (rateFlip h), recB (rateFlip h), recSum (rateFlip h)) = (recA h, recB h, recSum h)
  rw [e1, e2, e3]

theorem relativeTurn_of_reverse (c s : ℝ) (h : Held2) :
    relativeTurn c s (rateFlip h) = rateFlip (relativeTurn c (-s) h) := by
  apply Held2.ext
  · rfl
  · rfl
  · dsimp only [relativeTurn, rateFlip]; ring
  · dsimp only [relativeTurn, rateFlip]; ring

theorem relativeTurn_moves_plainNow (c s : ℝ) (hs : s ≠ 0) :
    ∃ h : Held2, plainNow (relativeTurn c (-s) h) ≠ plainNow (relativeTurn c s h) := by
  refine ⟨⟨1, 0, 0, 1⟩, fun e => hs ?_⟩
  have e3 := congrArg (fun t : ℝ × ℝ × ℝ => t.2.2) e
  dsimp only [plainNow, recSum, relativeTurn] at e3
  linear_combination (1 / 4) * e3

theorem same_present_records_different_later (c s : ℝ) (hs : s ≠ 0) :
    ∃ h : Held2, plainNow (rateFlip h) = plainNow h ∧
      plainNow (relativeTurn c s (rateFlip h)) ≠ plainNow (relativeTurn c s h) := by
  obtain ⟨h, hh⟩ := relativeTurn_moves_plainNow c s hs
  refine ⟨h, rateFlip_keeps_plainNow h, ?_⟩
  rw [relativeTurn_of_reverse, rateFlip_keeps_plainNow]
  exact hh

theorem plainNow_neg2 (h : Held2) : plainNow (neg2 h) = plainNow h := by
  have e1 : recA (neg2 h) = recA h := by dsimp only [recA, neg2]; ring
  have e2 : recB (neg2 h) = recB h := by dsimp only [recB, neg2]; ring
  have e3 : recSum (neg2 h) = recSum h := by dsimp only [recSum, neg2]; ring
  show (recA (neg2 h), recB (neg2 h), recSum (neg2 h)) = (recA h, recB h, recSum h)
  rw [e1, e2, e3]

theorem rateFree_present_records_fix_state (h k : Held2) (hh : RateFree h) (hk : RateFree k)
    (e : plainNow k = plainNow h) : k = h ∨ k = neg2 h := by
  obtain ⟨p1, p2, p3, p4⟩ := h
  obtain ⟨q1, q2, q3, q4⟩ := k
  obtain ⟨hp2, hp4⟩ := hh
  obtain ⟨hq2, hq4⟩ := hk
  dsimp only at hp2 hp4 hq2 hq4
  have eA := congrArg (fun t : ℝ × ℝ × ℝ => t.1) e
  have eB := congrArg (fun t : ℝ × ℝ × ℝ => t.2.1) e
  have eS := congrArg (fun t : ℝ × ℝ × ℝ => t.2.2) e
  dsimp only [plainNow, recA, recB, recSum] at eA eB eS
  rw [hp2, hq2] at eA
  rw [hp4, hq4] at eB
  rw [hp2, hq2, hp4, hq4] at eS
  have hx : q1 * q3 = p1 * p3 := by linear_combination (1 / 2) * eS - (1 / 2) * eA - (1 / 2) * eB
  have h1 : (q1 - p1) * (q1 + p1) = 0 := by linear_combination eA
  have h3 : (q3 - p3) * (q3 + p3) = 0 := by linear_combination eB
  have same : q1 = p1 → q3 = p3 → (⟨q1, q2, q3, q4⟩ : Held2) = ⟨p1, p2, p3, p4⟩ := by
    intro a b
    rw [a, b, hp2, hq2, hp4, hq4]
  have opp : q1 = -p1 → q3 = -p3 → (⟨q1, q2, q3, q4⟩ : Held2) = neg2 ⟨p1, p2, p3, p4⟩ := by
    intro a b
    rw [a, b, hp2, hq2, hp4, hq4]
    apply Held2.ext
    · rfl
    · show (0 : ℝ) = -0
      ring
    · rfl
    · show (0 : ℝ) = -0
      ring
  rcases mul_eq_zero.mp h1 with a | a
  · rcases mul_eq_zero.mp h3 with b | b
    · exact Or.inl (same (by linarith) (by linarith))
    · have z : p1 * p3 = 0 := by
        linear_combination (1 / 2) * q3 * a + (1 / 2) * p1 * b - (1 / 2) * hx
      rcases mul_eq_zero.mp z with z1 | z3
      · exact Or.inr (opp (by linarith) (by linarith))
      · exact Or.inl (same (by linarith) (by linarith))
  · rcases mul_eq_zero.mp h3 with b | b
    · have z : p1 * p3 = 0 := by
        linear_combination (1 / 2) * q3 * a - (1 / 2) * p1 * b - (1 / 2) * hx
      rcases mul_eq_zero.mp z with z1 | z3
      · exact Or.inl (same (by linarith) (by linarith))
      · exact Or.inr (opp (by linarith) (by linarith))
    · exact Or.inr (opp (by linarith) (by linarith))

theorem rateFree_hold_with_reverse_has_no_direction (D E theta : Held2 → Held2)
    (hodd : ∀ h : Held2, D (neg2 h) = neg2 (D h))
    (hEfree : ∀ h : Held2, RateFree h → RateFree (E h))
    (hfree : ∀ h : Held2, RateFree h → RateFree (theta h))
    (hnow : ∀ h : Held2, RateFree h → plainNow (theta h) = plainNow h)
    (hrev : ∀ h : Held2, RateFree h → D (theta h) = theta (E h))
    (h : Held2) (hh : RateFree h) : plainNow (D h) = plainNow (E h) := by
  have e : plainNow (D (theta h)) = plainNow (E h) := by
    rw [hrev h hh]
    exact hnow (E h) (hEfree h hh)
  rcases rateFree_present_records_fix_state h (theta h) hh (hfree h hh) (hnow h hh) with t | t
  · rw [t] at e
    exact e
  · rw [t, hodd, plainNow_neg2] at e
    exact e

theorem mix_neg2 (c s : ℝ) (h : Held2) : mix c s (neg2 h) = neg2 (mix c s h) := by
  apply Held2.ext
  · dsimp only [mix, neg2]; ring
  · dsimp only [mix, neg2]; ring
  · dsimp only [mix, neg2]; ring
  · dsimp only [mix, neg2]; ring

theorem mix_rateFree (c s : ℝ) (h : Held2) (hh : RateFree h) : RateFree (mix c s h) := by
  obtain ⟨h2, h4⟩ := hh
  refine ⟨?_, ?_⟩
  · show c * h.a2 - s * h.b2 = 0
    rw [h2, h4]; ring
  · show s * h.a2 + c * h.b2 = 0
    rw [h2, h4]; ring

theorem plane_has_no_reverse (c s : ℝ) (hcs : c * s ≠ 0) :
    ¬ ∃ theta : Held2 → Held2, (∀ h : Held2, RateFree h → RateFree (theta h)) ∧
      (∀ h : Held2, RateFree h → plainNow (theta h) = plainNow h) ∧
      (∀ h : Held2, RateFree h → mix c s (theta h) = theta (mix c (-s) h)) := by
  rintro ⟨theta, hfree, hnow, hrev⟩
  have e := rateFree_hold_with_reverse_has_no_direction (mix c s) (mix c (-s)) theta (mix_neg2 c s)
    (mix_rateFree c (-s)) hfree hnow hrev ⟨1, 0, 0, 0⟩ ⟨rfl, rfl⟩
  have e3 := congrArg (fun t : ℝ × ℝ × ℝ => t.2.2) e
  dsimp only [plainNow, recSum, mix] at e3
  exact hcs (by linear_combination (1 / 4) * e3)

theorem plainNow_mix (c s : ℝ) (h : Held2) :
    plainNow (mix c s h) =
      (c * c * recA h + s * s * recB h - c * s * (recSum h - recA h - recB h),
        s * s * recA h + c * c * recB h + c * s * (recSum h - recA h - recB h),
        (c + s) * (c + s) * recA h + (c - s) * (c - s) * recB h +
          (c * c - s * s) * (recSum h - recA h - recB h)) := by
  have e1 : recA (mix c s h) =
      c * c * recA h + s * s * recB h - c * s * (recSum h - recA h - recB h) := by
    dsimp only [recA, recB, recSum, mix]; ring
  have e2 : recB (mix c s h) =
      s * s * recA h + c * c * recB h + c * s * (recSum h - recA h - recB h) := by
    dsimp only [recA, recB, recSum, mix]; ring
  have e3 : recSum (mix c s h) =
      (c + s) * (c + s) * recA h + (c - s) * (c - s) * recB h +
        (c * c - s * s) * (recSum h - recA h - recB h) := by
    dsimp only [recA, recB, recSum, mix]; ring
  show (recA (mix c s h), recB (mix c s h), recSum (mix c s h)) = _
  rw [e1, e2, e3]

theorem mix_later_fixed_by_present (c s : ℝ) (x y : Held2) (e : plainNow x = plainNow y) :
    plainNow (mix c s x) = plainNow (mix c s y) := by
  have eA : recA x = recA y := congrArg (fun t : ℝ × ℝ × ℝ => t.1) e
  have eB : recB x = recB y := congrArg (fun t : ℝ × ℝ × ℝ => t.2.1) e
  have eS : recSum x = recSum y := congrArg (fun t : ℝ × ℝ × ℝ => t.2.2) e
  rw [plainNow_mix, plainNow_mix, eA, eB, eS]

theorem mix_has_no_reverse (c s : ℝ) (hcs : c * s ≠ 0) :
    ¬ ∃ theta : Held2 → Held2, (∀ h : Held2, plainNow (theta h) = plainNow h) ∧
      (∀ h : Held2, mix c s (theta h) = theta (mix c (-s) h)) := by
  rintro ⟨theta, hnow, hrev⟩
  have e := no_direction_if_present_records_fix_later plainNow (mix c s) (mix c (-s)) theta
    (mix_later_fixed_by_present c s) hnow hrev ⟨1, 0, 0, 0⟩
  have e3 := congrArg (fun t : ℝ × ℝ × ℝ => t.2.2) e
  dsimp only [plainNow, recSum, mix] at e3
  exact hcs (by linear_combination (1 / 4) * e3)

end APFPaper5.K3

open APFPaper5.K3 in
theorem APFB01.rate_is_held_on_the_carrier {Process : Type uP} (profile : Held2 → Process → Prop)
    (c s : ℝ) (hs : s ≠ 0)
    (hfact : ∀ r : ℝ × ℝ × ℝ,
      APFB01.Descends profile (fun h => plainNow (relativeTurn c s h) = r)) :
    ∃ h : Held2, plainNow (rateFlip h) = plainNow h ∧
      APFB01.physicalClass profile (rateFlip h) ≠ APFB01.physicalClass profile h := by
  obtain ⟨h, h1, h2⟩ := same_present_records_different_later c s hs
  exact ⟨h, h1, APFB01.distinct_objects_of_later_record profile
    (fun z => plainNow (relativeTurn c s z)) hfact (rateFlip h) h h2⟩


theorem solution :
∀ (h : APFPaper5.K3.Held2),
  @Eq.{1} (Prod.{0, 0} Real (Prod.{0, 0} Real Real)) (APFPaper5.K3.plainNow (APFPaper5.K3.rateFlip h))
    (APFPaper5.K3.plainNow h) := by
  exact @APFPaper5.K3.rateFlip_keeps_plainNow
