-- Prove2me | solution 1 for APFPaper1.Regulation.holdable_left_of_jointlyHoldable
-- status  : ACCEPTED   (prove)
-- author  : @FiniteUniverse
-- created : 2026-11-13T17:23:55.884799+00:00
-- url     : https://prove2.me/submissions/2d6ca2de-51a1-4c3e-82c5-e19369564f3c

/-
APF Foundation Ledger — theorem node DRAFT (session EthanBrooke-01WrrBvu, 2026-11-12; not gated, not reviewed)
name: APFPaper1_Regulation_pair
title: The pair under regulation: member threats, the two branches, and the count ratio
inputs_revision: 2026-10-04.1
mathlib_rev: 0df444a360eaa60ab8c11dca51a86af692955474
source: as Def_APFPaper1_Regulation.
consumes_inputs: none as a hypothesis. The budget C and the continuation class Cont are the ledger's own
 objects (B04 supplies the capacity in the source; Cont is the corrected definition), so the statements are
 about ledger data plus the supplied reading `reads`.
statement: (saves_cont) a saving response is a budgeted continuation of the disturbance.
 (holdable_left_of_jointlyHoldable, _right) if one response saves both marks, each mark is holdable; so a
 disturbance against which a member cannot be held is one against which the pair cannot be held.
 (jointlyHoldable_or_irreduciblyJointAt, not_both) where each mark is holdable, exactly one of jointly
 holdable and irreducibly joint holds. (bothCount_le_eachCount) over any finite list of disturbances, the
 number where both can be saved by one response is at most the number where each can be saved.
 (bothCount_eq_eachCount_of_none) the two numbers are equal when no disturbance in the list is irreducibly
 joint.
not_claimed: strict inequality of the counts when an irreducibly joint disturbance is in the list (true, not
 proved here); that the ratio of the counts is a score or a probability; any continuum of values.
-/
import Definitions.Def_APFPaper1_Regulation
import Definitions.Def_APFPaper1_RegulationCounts
import Mathlib.Data.NNReal.Basic

set_option autoImplicit false
namespace APFPaper1.Regulation

open APFPaper1.Continuation
open Classical

universe uC uF uX uR uM
variable {Context : Type uC} {Frag : Context → Context → Type uF} {Raw : Context → Type uX}
  {R : Context → Type uR} {M : Type uM}
  (step : (g h : Context) → Frag g h → Raw g → Raw h → Prop)
  (resource : (g : Context) → WordFrom Frag g → R g)
  (calibration : (g : Context) → R g → NNReal) (C : Context → NNReal)
  (reads : (h : Context) → Raw h → M → Bool)

theorem saves_cont (g : Context) (x : Raw g) (w : WordFrom Frag g) (m : M)
    (h : Saves step resource calibration C reads g x w m) :
    Cont step resource calibration C g x w := by
  obtain ⟨hbill, y, hy, _⟩ := h
  exact ⟨⟨y, hy⟩, hbill⟩

theorem holdable_left_of_jointlyHoldable (g : Context) (x : Raw g) (m1 m2 : M)
    (h : JointlyHoldable step resource calibration C reads g x m1 m2) :
    Holdable step resource calibration C reads g x m1 := by
  obtain ⟨w, hbill, y, hy, h1, _⟩ := h
  exact ⟨w, hbill, y, hy, h1⟩

theorem holdable_right_of_jointlyHoldable (g : Context) (x : Raw g) (m1 m2 : M)
    (h : JointlyHoldable step resource calibration C reads g x m1 m2) :
    Holdable step resource calibration C reads g x m2 := by
  obtain ⟨w, hbill, y, hy, _, h2⟩ := h
  exact ⟨w, hbill, y, hy, h2⟩

theorem jointlyHoldable_or_irreduciblyJointAt (g : Context) (x : Raw g) (m1 m2 : M)
    (h1 : Holdable step resource calibration C reads g x m1)
    (h2 : Holdable step resource calibration C reads g x m2) :
    JointlyHoldable step resource calibration C reads g x m1 m2 ∨
      IrreduciblyJointAt step resource calibration C reads g x m1 m2 := by
  by_cases h : JointlyHoldable step resource calibration C reads g x m1 m2
  · exact Or.inl h
  · exact Or.inr ⟨h1, h2, h⟩

theorem not_jointlyHoldable_of_irreduciblyJointAt (g : Context) (x : Raw g) (m1 m2 : M)
    (h : IrreduciblyJointAt step resource calibration C reads g x m1 m2) :
    ¬ JointlyHoldable step resource calibration C reads g x m1 m2 := h.2.2

theorem bothCount_le_eachCount (g : Context) (xs : List (Raw g)) (m1 m2 : M) :
    bothCount step resource calibration C reads g xs m1 m2 ≤
      eachCount step resource calibration C reads g xs m1 m2 := by
  unfold bothCount eachCount
  apply List.countP_mono_left
  intro x _ hx
  have hj := of_decide_eq_true hx
  exact decide_eq_true
    ⟨holdable_left_of_jointlyHoldable step resource calibration C reads g x m1 m2 hj,
      holdable_right_of_jointlyHoldable step resource calibration C reads g x m1 m2 hj⟩

theorem bothCount_eq_eachCount_of_none (g : Context) (xs : List (Raw g)) (m1 m2 : M)
    (hnone : ∀ x ∈ xs, ¬ IrreduciblyJointAt step resource calibration C reads g x m1 m2) :
    bothCount step resource calibration C reads g xs m1 m2 =
      eachCount step resource calibration C reads g xs m1 m2 := by
  unfold bothCount eachCount
  apply List.countP_congr
  intro x hx
  simp only [decide_eq_true_eq]
  constructor
  · intro hj
    exact ⟨holdable_left_of_jointlyHoldable step resource calibration C reads g x m1 m2 hj,
      holdable_right_of_jointlyHoldable step resource calibration C reads g x m1 m2 hj⟩
  · rintro ⟨h1, h2⟩
    rcases jointlyHoldable_or_irreduciblyJointAt step resource calibration C reads g x m1 m2 h1 h2
      with h | h
    · exact h
    · exact absurd h (hnone x hx)

end APFPaper1.Regulation


universe uC uF uX uR uM
theorem solution :
∀ {Context : Type uC} {Frag : Context → Context → Type uF} {Raw : Context → Type uX} {R : Context → Type uR}
  {M : Type uM} (step : (g h : Context) → Frag g h → Raw g → Raw h → Prop)
  (resource : (g : Context) → APFPaper1.Continuation.WordFrom.{uC, uF} Frag g → R g)
  (calibration : (g : Context) → R g → NNReal) (C : Context → NNReal) (reads : (h : Context) → Raw h → M → Bool)
  (g : Context) (x : Raw g) (m1 m2 : M),
  APFPaper1.Regulation.JointlyHoldable.{uC, uF, uX, uR, uM} step resource calibration C reads g x m1 m2 →
    APFPaper1.Regulation.Holdable.{uC, uF, uX, uR, uM} step resource calibration C reads g x m1 := by
  exact @APFPaper1.Regulation.holdable_left_of_jointlyHoldable
