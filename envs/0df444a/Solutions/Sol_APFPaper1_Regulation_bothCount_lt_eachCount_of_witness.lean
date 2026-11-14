-- Prove2me | solution 1 for APFPaper1.Regulation.bothCount_lt_eachCount_of_witness
-- status  : ACCEPTED   (prove)
-- author  : @FiniteUniverse
-- created : 2026-11-13T17:26:48.896631+00:00
-- url     : https://prove2.me/submissions/cd6f471b-83fb-4fb5-82a8-d666d71ee3c6

/-
APF Foundation Ledger — theorem node DRAFT (session EthanBrooke-01WrrBvu, 2026-11-12; not gated, not reviewed)
name: APFPaper1_Regulation_count_strict
title: One irreducibly joint disturbance in the list makes the count ratio drop below one
inputs_revision: 2026-10-04.1
mathlib_rev: 0df444a360eaa60ab8c11dca51a86af692955474
source: as Def_APFPaper1_Regulation.
consumes_inputs: none as a hypothesis (see Thm_APFPaper1_Regulation_pair).
statement: (countP_lt_of_witness) for Boolean tests p and q on a list, if p implies q on the list and some
 listed element passes q and fails p, then fewer elements pass p than q. (bothCount_lt_eachCount_of_witness)
 if some listed disturbance is irreducibly joint for the pair, the number of listed disturbances where one
 response saves both marks is strictly less than the number where each can be saved.
not_claimed: any value of the ratio; that the ratio is a score.
-/
import Theorems.Thm_APFPaper1_Regulation_holdable_left_of_jointlyHoldable
import Theorems.Thm_APFPaper1_Regulation_holdable_right_of_jointlyHoldable
import Theorems.Thm_APFPaper1_Regulation_bothCount_le_eachCount
import Theorems.Thm_APFPaper1_Regulation_bothCount_eq_eachCount_of_none

set_option autoImplicit false
namespace APFPaper1.Regulation

open APFPaper1.Continuation
open Classical

universe uA uC uF uX uR uM

theorem countP_lt_of_witness {α : Type uA} (p q : α → Bool) :
    ∀ l : List α, (∀ x ∈ l, p x = true → q x = true) →
      (∃ x ∈ l, q x = true ∧ p x = false) → l.countP p < l.countP q
  | [], _, ⟨_, hx, _⟩ => by cases hx
  | a :: t, hpq, ⟨x, hx, hq, hp⟩ => by
      have hle : t.countP p ≤ t.countP q :=
        List.countP_mono_left (fun y hy h => hpq y (List.mem_cons_of_mem _ hy) h)
      rcases List.mem_cons.mp hx with h | hxt
      · subst h
        have hpx : ¬ (p x = true) := by rw [hp]; exact Bool.false_ne_true
        rw [List.countP_cons_of_pos hq, List.countP_cons_of_neg hpx]
        omega
      · have ih := countP_lt_of_witness p q t
          (fun y hy h => hpq y (List.mem_cons_of_mem _ hy) h) ⟨x, hxt, hq, hp⟩
        by_cases hpa : p a = true
        · rw [List.countP_cons_of_pos hpa,
            List.countP_cons_of_pos (hpq a (List.mem_cons.mpr (Or.inl rfl)) hpa)]
          omega
        · rw [List.countP_cons_of_neg hpa]
          by_cases hqa : q a = true
          · rw [List.countP_cons_of_pos hqa]
            omega
          · rw [List.countP_cons_of_neg hqa]
            exact ih

variable {Context : Type uC} {Frag : Context → Context → Type uF} {Raw : Context → Type uX}
  {R : Context → Type uR} {M : Type uM}
  (step : (g h : Context) → Frag g h → Raw g → Raw h → Prop)
  (resource : (g : Context) → WordFrom Frag g → R g)
  (calibration : (g : Context) → R g → NNReal) (C : Context → NNReal)
  (reads : (h : Context) → Raw h → M → Bool)

theorem bothCount_lt_eachCount_of_witness (g : Context) (xs : List (Raw g)) (m1 m2 : M)
    (x0 : Raw g) (hx0 : x0 ∈ xs)
    (hirr : IrreduciblyJointAt step resource calibration C reads g x0 m1 m2) :
    bothCount step resource calibration C reads g xs m1 m2 <
      eachCount step resource calibration C reads g xs m1 m2 := by
  unfold bothCount eachCount
  apply countP_lt_of_witness
  · intro x _ hx
    have hj := of_decide_eq_true hx
    exact decide_eq_true
      ⟨holdable_left_of_jointlyHoldable step resource calibration C reads g x m1 m2 hj,
        holdable_right_of_jointlyHoldable step resource calibration C reads g x m1 m2 hj⟩
  · exact ⟨x0, hx0, decide_eq_true ⟨hirr.1, hirr.2.1⟩, decide_eq_false hirr.2.2⟩

end APFPaper1.Regulation


universe apfNative_uC apfNative_uF apfNative_uX apfNative_uR apfNative_uM
theorem solution :
∀ {Context : Type apfNative_uC} {Frag : Context → Context → Type apfNative_uF} {Raw : Context → Type apfNative_uX}
  {R : Context → Type apfNative_uR} {M : Type apfNative_uM} (step : (g h : Context) → Frag g h → Raw g → Raw h → Prop)
  (resource : (g : Context) → @APFPaper1.Continuation.WordFrom.{apfNative_uC, apfNative_uF} Context Frag g → R g)
  (calibration : (g : Context) → R g → NNReal) (C : Context → NNReal) (reads : (h : Context) → Raw h → M → Bool)
  (g : Context) (xs : List.{apfNative_uX} (Raw g)) (m1 m2 : M) (x0 : Raw g)
  (hx0 :
    @Membership.mem.{apfNative_uX, apfNative_uX} (Raw g) (List.{apfNative_uX} (Raw g))
      (@List.instMembership.{apfNative_uX} (Raw g)) xs x0)
  (hirr :
    @APFPaper1.Regulation.IrreduciblyJointAt.{apfNative_uC, apfNative_uF, apfNative_uX, apfNative_uR, apfNative_uM}
      Context Frag Raw R M step resource calibration C reads g x0 m1 m2),
  @LT.lt.{0} Nat instLTNat
    (@APFPaper1.Regulation.bothCount.{apfNative_uC, apfNative_uF, apfNative_uX, apfNative_uR, apfNative_uM} Context Frag
      Raw R M step resource calibration C reads g xs m1 m2)
    (@APFPaper1.Regulation.eachCount.{apfNative_uC, apfNative_uF, apfNative_uX, apfNative_uR, apfNative_uM} Context Frag
      Raw R M step resource calibration C reads g xs m1 m2) := by
  exact @APFPaper1.Regulation.bothCount_lt_eachCount_of_witness
