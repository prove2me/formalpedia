-- Prove2me | solution 1 for APFPaper5.K3.inner_value_met_twice
-- status  : ACCEPTED   (prove)
-- author  : @FiniteUniverse
-- created : 2026-11-14T07:09:45.712494+00:00
-- url     : https://prove2.me/submissions/e3f0b464-a508-4fbc-84d4-93fc38d7f937

import Theorems.Thm_APFPaper5_K3_cross_norm
/-
APF Foundation Ledger — theorem node DRAFT (session EthanBrooke-01WrrBvu, 2026-11-13; not gated, not reviewed)
name: APFPaper5_K3_relation_and_reverse
title: On two held components, the relation sits strictly between its extremes exactly when the state and its reverse part ways under a turn of one component; one hold carries the relation through its range at fixed costs and meets each inner value twice, at a state and its reverse
inputs_revision: 2026-10-04.1
mathlib_rev: 0df444a360eaa60ab8c11dca51a86af692955474
source: the author's direction of 2026-11-13 ("1 and 2 can be made compatible"), on the two readings put to
 him in NOTE_derivation_pass_17. Thm_APFPaper5_K3_reversal_on_the_carrier,
 Thm_APFPaper5_K3_direction_is_recorded (cross_norm), Thm_APFPaper5_K3_number_alone_cannot_return.
consumes_inputs: none.
standing: theorems about the supplied MODEL of two held components.
statement: (recSum_relativeTurn, crossRe_rateFlip, crossIm_rateFlip) bookkeeping.
 (reverse_differs_iff_rate) for a turn of one component that is not the identity or the half turn, a state
 and its reverse read differently afterwards exactly when the second cross term is not zero.
 (relation_between_iff_rate) the relation sits strictly between its extremes exactly when the second cross
 term is not zero.
 (relation_between_iff_reverse_differs) so the two readings name the same held states.
 (relativeTurn_from_extreme, orbit_costs_and_relation) turning one component of a state with no rate keeps
 both costs and carries the relation to c times its extreme.
 (orbit_reverse, inner_value_met_twice) the reverse of the state at turn (c, s) is the state at turn
 (c, -s); for s not zero the two differ, have the same present records, and sit strictly inside the range.
 (extreme_is_own_reverse) the state at the extreme is its own reverse.
 (present_records_do_not_fix_next) no function of the present records gives the present records after a
 quarter turn of one component.
 (quarter_orbit_closes_and_moves, no_order_keeping_law_for_the_relation) the quarter turn returns after four
 steps and moves the recombination record on the first, so the model-free theorem applies to it.
not_claimed: that an interface is this model; that the turn of one component is an admitted hold; either
 reading as adopted; any K.
-/
import Theorems.Thm_APFPaper5_K3_rateFlip_keeps_plainNow
import Theorems.Thm_APFPaper5_K3_same_present_records_different_later
import Theorems.Thm_APFPaper5_K3_rateFree_present_records_fix_state
import Theorems.Thm_APFPaper5_K3_mix_has_no_reverse
import Theorems.Thm_APFB01_rate_is_held_on_the_carrier
import Theorems.Thm_APFPaper5_K3_profile_preserving_linear_commutes_with_quarter
import Theorems.Thm_APFB01_quarter_record_descends
import Theorems.Thm_APFPaper5_K3_closing_orbit_does_not_move
import Theorems.Thm_APFPaper5_K3_number_alone_does_not_fix_next
import Theorems.Thm_APFPaper5_K3_retracing_orbit_same_now_different_later
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

set_option autoImplicit false
namespace APFPaper5.K3

theorem recSum_relativeTurn (c s : ℝ) (h : Held2) :
    recSum (relativeTurn c s h) =
      recA h + (c * c + s * s) * recB h + 2 * (c * crossRe h + s * crossIm h) := by
  dsimp only [recSum, recA, recB, crossRe, crossIm, relativeTurn]
  ring

theorem crossRe_rateFlip (h : Held2) : crossRe (rateFlip h) = crossRe h := by
  dsimp only [crossRe, rateFlip]
  ring

theorem crossIm_rateFlip (h : Held2) : crossIm (rateFlip h) = -crossIm h := by
  dsimp only [crossIm, rateFlip]
  ring

theorem reverse_differs_iff_rate (c s : ℝ) (hs : s ≠ 0) (h : Held2) :
    plainNow (relativeTurn c s (rateFlip h)) ≠ plainNow (relativeTurn c s h) ↔ crossIm h ≠ 0 := by
  have key : recSum (relativeTurn c s (rateFlip h)) - recSum (relativeTurn c s h) =
      -4 * s * crossIm h := by
    dsimp only [recSum, relativeTurn, rateFlip, crossIm]
    ring
  constructor
  · intro hne h0
    apply hne
    have e1 : recA (relativeTurn c s (rateFlip h)) = recA (relativeTurn c s h) := by
      dsimp only [recA, relativeTurn, rateFlip]; ring
    have e2 : recB (relativeTurn c s (rateFlip h)) = recB (relativeTurn c s h) := by
      dsimp only [recB, relativeTurn, rateFlip]; ring
    have e3 : recSum (relativeTurn c s (rateFlip h)) = recSum (relativeTurn c s h) := by
      linear_combination key + (-4 * s) * h0
    show (recA (relativeTurn c s (rateFlip h)), recB (relativeTurn c s (rateFlip h)),
      recSum (relativeTurn c s (rateFlip h))) = (recA (relativeTurn c s h),
      recB (relativeTurn c s h), recSum (relativeTurn c s h))
    rw [e1, e2, e3]
  · intro hne e
    have e3 : recSum (relativeTurn c s (rateFlip h)) = recSum (relativeTurn c s h) :=
      congrArg (fun t : ℝ × ℝ × ℝ => t.2.2) e
    have z : s * crossIm h = 0 := by linear_combination (1 / 4) * key - (1 / 4) * e3
    rcases mul_eq_zero.mp z with z1 | z2
    · exact hs z1
    · exact hne z2

theorem relation_between_iff_rate (h : Held2) :
    crossRe h * crossRe h < recA h * recB h ↔ crossIm h ≠ 0 := by
  have e := cross_norm h
  constructor
  · intro hlt h0
    rw [h0] at e
    linarith
  · intro hne
    have t : 0 < crossIm h * crossIm h := mul_self_pos.mpr hne
    linarith

theorem relation_between_iff_reverse_differs (c s : ℝ) (hs : s ≠ 0) (h : Held2) :
    crossRe h * crossRe h < recA h * recB h ↔
      plainNow (relativeTurn c s (rateFlip h)) ≠ plainNow (relativeTurn c s h) :=
  (relation_between_iff_rate h).trans (reverse_differs_iff_rate c s hs h).symm

theorem relativeTurn_from_extreme (a b c s : ℝ) :
    relativeTurn c s ⟨a, 0, b, 0⟩ = ⟨a, 0, c * b, s * b⟩ := by
  apply Held2.ext
  · rfl
  · rfl
  · dsimp only [relativeTurn]; ring
  · dsimp only [relativeTurn]; ring

theorem orbit_costs_and_relation (a b c s : ℝ) (hcs : c * c + s * s = 1) :
    recA ⟨a, 0, c * b, s * b⟩ = a * a ∧ recB ⟨a, 0, c * b, s * b⟩ = b * b ∧
      crossRe ⟨a, 0, c * b, s * b⟩ = c * (a * b) ∧
      crossIm ⟨a, 0, c * b, s * b⟩ = -(s * (a * b)) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · dsimp only [recA]; ring
  · dsimp only [recB]; linear_combination (b * b) * hcs
  · dsimp only [crossRe]; ring
  · dsimp only [crossIm]; ring

theorem orbit_reverse (a b c s : ℝ) :
    rateFlip ⟨a, 0, c * b, s * b⟩ = ⟨a, 0, c * b, -s * b⟩ := by
  apply Held2.ext
  · rfl
  · dsimp only [rateFlip]; ring
  · rfl
  · dsimp only [rateFlip]; ring

theorem inner_value_met_twice (a b c s : ℝ) (hcs : c * c + s * s = 1) (hs : s ≠ 0)
    (hab : a * b ≠ 0) :
    plainNow (⟨a, 0, c * b, -s * b⟩ : Held2) = plainNow ⟨a, 0, c * b, s * b⟩ ∧
      (⟨a, 0, c * b, -s * b⟩ : Held2) ≠ ⟨a, 0, c * b, s * b⟩ ∧
      crossRe ⟨a, 0, c * b, s * b⟩ * crossRe ⟨a, 0, c * b, s * b⟩ <
        recA ⟨a, 0, c * b, s * b⟩ * recB ⟨a, 0, c * b, s * b⟩ := by
  have hy : crossIm ⟨a, 0, c * b, s * b⟩ ≠ 0 := by
    rw [(orbit_costs_and_relation a b c s hcs).2.2.2]
    exact neg_ne_zero.mpr (mul_ne_zero hs hab)
  refine ⟨?_, ?_, (relation_between_iff_rate _).mpr hy⟩
  · rw [← orbit_reverse]
    exact rateFlip_keeps_plainNow _
  · intro e
    have e4 : -s * b = s * b := congrArg Held2.b2 e
    have hb : b ≠ 0 := fun hb0 => hab (by rw [hb0]; ring)
    have z : s * b = 0 := by linear_combination (-1 / 2) * e4
    rcases mul_eq_zero.mp z with z1 | z2
    · exact hs z1
    · exact hb z2

theorem extreme_is_own_reverse (a b : ℝ) : rateFlip ⟨a, 0, b, 0⟩ = ⟨a, 0, b, 0⟩ := by
  apply Held2.ext
  · rfl
  · dsimp only [rateFlip]; ring
  · rfl
  · dsimp only [rateFlip]; ring

theorem present_records_do_not_fix_next :
    ¬ ∃ f : ℝ × ℝ × ℝ → ℝ × ℝ × ℝ, ∀ h : Held2, plainNow (relativeTurn 0 1 h) = f (plainNow h) := by
  rintro ⟨f, hf⟩
  have e1 := hf ⟨1, 0, 0, 1⟩
  have e2 := hf ⟨1, 0, 0, -1⟩
  have same : plainNow (⟨1, 0, 0, -1⟩ : Held2) = plainNow ⟨1, 0, 0, 1⟩ := by
    have t := rateFlip_keeps_plainNow ⟨1, 0, 0, 1⟩
    have r : rateFlip ⟨1, 0, 0, 1⟩ = ⟨1, 0, 0, -1⟩ := by
      apply Held2.ext
      · rfl
      · dsimp only [rateFlip]; ring
      · rfl
      · rfl
    rw [r] at t
    exact t
  rw [same, ← e1] at e2
  have e3 := congrArg (fun t : ℝ × ℝ × ℝ => t.2.2) e2
  dsimp only [plainNow, recSum, relativeTurn] at e3
  linarith

theorem quarter_orbit_closes_and_moves (a b : ℝ) (hab : a * b ≠ 0) :
    ∃ o : ℕ → Held2, (∀ n : ℕ, o (n + 1) = relativeTurn 0 1 (o n)) ∧ o (3 + 1) = o 0 ∧
      recSum (o 1) ≠ recSum (o 0) := by
  refine ⟨fun n => (relativeTurn 0 1)^[n] ⟨a, 0, b, 0⟩,
    fun n => Function.iterate_succ_apply' _ n _, ?_, ?_⟩
  · show relativeTurn 0 1 (relativeTurn 0 1 (relativeTurn 0 1 (relativeTurn 0 1 ⟨a, 0, b, 0⟩))) =
      ⟨a, 0, b, 0⟩
    apply Held2.ext
    · rfl
    · rfl
    · dsimp only [relativeTurn]; ring
    · dsimp only [relativeTurn]; ring
  · show recSum (relativeTurn 0 1 ⟨a, 0, b, 0⟩) ≠ recSum ⟨a, 0, b, 0⟩
    intro e
    dsimp only [recSum, relativeTurn] at e
    exact hab (by linear_combination (-1 / 2) * e)

theorem no_order_keeping_law_for_the_relation :
    ¬ ∃ f : ℝ → ℝ, (∀ x y : ℝ, x < y → f x < f y) ∧
      ∀ h : Held2, recSum (relativeTurn 0 1 h) = f (recSum h) := by
  obtain ⟨o, ho, hclose, hmove⟩ := quarter_orbit_closes_and_moves 1 1 (by norm_num)
  exact number_alone_does_not_fix_next recSum (relativeTurn 0 1) o ho 3 hclose hmove

end APFPaper5.K3


theorem solution :
∀ (a b c s : Real)
  (hcs :
    @Eq.{1} Real
      (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) c c)
        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) s s))
      (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)))
  (hs : @Ne.{1} Real s (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)))
  (hab :
    @Ne.{1} Real (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) a b)
      (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))),
  And
    (@Eq.{1} (Prod.{0, 0} Real (Prod.{0, 0} Real Real))
      (APFPaper5.K3.plainNow
        (APFPaper5.K3.Held2.mk a (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
          (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) c b)
          (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) (@Neg.neg.{0} Real Real.instNeg s) b)))
      (APFPaper5.K3.plainNow
        (APFPaper5.K3.Held2.mk a (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
          (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) c b)
          (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) s b))))
    (And
      (@Ne.{1} APFPaper5.K3.Held2
        (APFPaper5.K3.Held2.mk a (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
          (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) c b)
          (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) (@Neg.neg.{0} Real Real.instNeg s) b))
        (APFPaper5.K3.Held2.mk a (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
          (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) c b)
          (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) s b)))
      (@LT.lt.{0} Real Real.instLT
        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
          (APFPaper5.K3.crossRe
            (APFPaper5.K3.Held2.mk a (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
              (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) c b)
              (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) s b)))
          (APFPaper5.K3.crossRe
            (APFPaper5.K3.Held2.mk a (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
              (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) c b)
              (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) s b))))
        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
          (APFPaper5.K3.recA
            (APFPaper5.K3.Held2.mk a (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
              (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) c b)
              (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) s b)))
          (APFPaper5.K3.recB
            (APFPaper5.K3.Held2.mk a (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
              (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) c b)
              (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) s b)))))) := by
  exact @APFPaper5.K3.inner_value_met_twice
