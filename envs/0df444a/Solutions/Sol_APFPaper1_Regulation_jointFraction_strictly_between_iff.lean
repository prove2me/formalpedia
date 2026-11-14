-- Prove2me | solution 1 for APFPaper1.Regulation.jointFraction_strictly_between_iff
-- status  : ACCEPTED   (prove)
-- author  : @FiniteUniverse
-- created : 2026-11-13T17:39:50.824705+00:00
-- url     : https://prove2.me/submissions/bc9cbc41-c4a2-45b5-a78e-0fd83e01bf2e

/-
APF Foundation Ledger — theorem node DRAFT (session EthanBrooke-01WrrBvu, 2026-11-12; not gated, not reviewed)
name: APFPaper1_joint_fraction
title: The joint fraction is symmetric, lies from 0 to 1, is 1 for a mark with itself, and is strictly between when the list is mixed
inputs_revision: 2026-10-04.1
mathlib_rev: 0df444a360eaa60ab8c11dca51a86af692955474
source: as Def_APFPaper1_JointFraction; Thm_APFPaper1_Regulation_pair and Thm_APFPaper1_Regulation_overflow.
consumes_inputs: none as a hypothesis. The objects are ledger words, the budget and the readings.
statement: (jointlyHoldable_comm, bothCount_symm, eachCount_symm, jointFraction_symm) exchanging the two marks
 changes nothing. (jointFraction_mem) the fraction lies from 0 to 1. (jointFraction_self) for a mark with
 itself it is 1, given one listed disturbance against which the mark can be saved.
 (jointFraction_strictly_between) if one listed disturbance lets one response save both, and another lets each
 be saved but not both, the fraction is strictly between 0 and 1.
 (jointFraction_strictly_between_iff) and conversely: the fraction is strictly between 0 and 1 exactly when
 the list holds a disturbance of each kind.
not_claimed: that the fraction is the pair number of an algebra; that it takes every value in an interval (on
 a list of n disturbances it takes at most n + 1 values); any independence from the supplied list.
-/
import Definitions.Def_APFPaper1_JointFraction
import Theorems.Thm_APFPaper1_Regulation_irreduciblyJointAt_iff_overflow
import Theorems.Thm_APFPaper1_Regulation_eachCount_pos_of_mem
import Theorems.Thm_APFPaper1_Regulation_count_ratio_strictly_between

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

theorem jointlyHoldable_comm (g : Context) (x : Raw g) (m1 m2 : M) :
    JointlyHoldable step resource calibration C reads g x m1 m2 ↔
      JointlyHoldable step resource calibration C reads g x m2 m1 := by
  constructor
  · rintro ⟨w, hc, y, hex, h1, h2⟩
    exact ⟨w, hc, y, hex, h2, h1⟩
  · rintro ⟨w, hc, y, hex, h1, h2⟩
    exact ⟨w, hc, y, hex, h2, h1⟩

theorem jointlyHoldable_self_iff (g : Context) (x : Raw g) (m : M) :
    JointlyHoldable step resource calibration C reads g x m m ↔
      (Holdable step resource calibration C reads g x m ∧
        Holdable step resource calibration C reads g x m) := by
  constructor
  · rintro ⟨w, hc, y, hex, h1, _⟩
    exact ⟨⟨w, hc, y, hex, h1⟩, ⟨w, hc, y, hex, h1⟩⟩
  · rintro ⟨⟨w, hc, y, hex, h1⟩, _⟩
    exact ⟨w, hc, y, hex, h1, h1⟩

theorem bothCount_symm (g : Context) (xs : List (Raw g)) (m1 m2 : M) :
    bothCount step resource calibration C reads g xs m1 m2 =
      bothCount step resource calibration C reads g xs m2 m1 := by
  unfold bothCount
  apply List.countP_congr
  intro x _
  simp only [decide_eq_true_eq]
  exact jointlyHoldable_comm step resource calibration C reads g x m1 m2

theorem eachCount_symm (g : Context) (xs : List (Raw g)) (m1 m2 : M) :
    eachCount step resource calibration C reads g xs m1 m2 =
      eachCount step resource calibration C reads g xs m2 m1 := by
  unfold eachCount
  apply List.countP_congr
  intro x _
  simp only [decide_eq_true_eq]
  exact and_comm

theorem jointFraction_symm (g : Context) (xs : List (Raw g)) (m1 m2 : M) :
    jointFraction step resource calibration C reads g xs m1 m2 =
      jointFraction step resource calibration C reads g xs m2 m1 := by
  unfold jointFraction
  rw [bothCount_symm step resource calibration C reads g xs m1 m2,
    eachCount_symm step resource calibration C reads g xs m1 m2]

theorem jointFraction_mem (g : Context) (xs : List (Raw g)) (m1 m2 : M) :
    0 ≤ jointFraction step resource calibration C reads g xs m1 m2 ∧
      jointFraction step resource calibration C reads g xs m1 m2 ≤ 1 := by
  unfold jointFraction
  have hle := bothCount_le_eachCount step resource calibration C reads g xs m1 m2
  have hle' : (bothCount step resource calibration C reads g xs m1 m2 : ℝ) ≤
      (eachCount step resource calibration C reads g xs m1 m2 : ℝ) := by exact_mod_cast hle
  refine ⟨div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _), ?_⟩
  by_cases h0 : eachCount step resource calibration C reads g xs m1 m2 = 0
  · rw [h0, Nat.cast_zero, div_zero]
    exact zero_le_one
  · have hpos : (0 : ℝ) < (eachCount step resource calibration C reads g xs m1 m2 : ℝ) :=
      Nat.cast_pos.mpr (Nat.pos_of_ne_zero h0)
    exact (div_le_one hpos).mpr hle'

theorem jointFraction_self (g : Context) (xs : List (Raw g)) (m : M) (x0 : Raw g)
    (hx0 : x0 ∈ xs) (h : Holdable step resource calibration C reads g x0 m) :
    jointFraction step resource calibration C reads g xs m m = 1 := by
  have hjh : JointlyHoldable step resource calibration C reads g x0 m m :=
    (jointlyHoldable_self_iff step resource calibration C reads g x0 m).mpr ⟨h, h⟩
  have hpos := eachCount_pos_of_mem step resource calibration C reads g xs m m x0 hx0 hjh
  have heq : bothCount step resource calibration C reads g xs m m =
      eachCount step resource calibration C reads g xs m m := by
    unfold bothCount eachCount
    apply List.countP_congr
    intro x _
    simp only [decide_eq_true_eq]
    exact jointlyHoldable_self_iff step resource calibration C reads g x m
  unfold jointFraction
  rw [heq]
  exact div_self (ne_of_gt (Nat.cast_pos.mpr hpos))

theorem jointFraction_strictly_between (g : Context) (xs : List (Raw g)) (m1 m2 : M)
    (x0 x1 : Raw g) (hx0 : x0 ∈ xs) (hx1 : x1 ∈ xs)
    (hheld : JointlyHoldable step resource calibration C reads g x0 m1 m2)
    (hirr : IrreduciblyJointAt step resource calibration C reads g x1 m1 m2) :
    0 < jointFraction step resource calibration C reads g xs m1 m2 ∧
      jointFraction step resource calibration C reads g xs m1 m2 < 1 := by
  obtain ⟨hb, hlt⟩ := count_ratio_strictly_between step resource calibration C reads g xs m1 m2
    x0 x1 hx0 hx1 hheld hirr
  unfold jointFraction
  have hb' : (0 : ℝ) < (bothCount step resource calibration C reads g xs m1 m2 : ℝ) :=
    Nat.cast_pos.mpr hb
  have hlt' : (bothCount step resource calibration C reads g xs m1 m2 : ℝ) <
      (eachCount step resource calibration C reads g xs m1 m2 : ℝ) := by exact_mod_cast hlt
  have hpos : (0 : ℝ) < (eachCount step resource calibration C reads g xs m1 m2 : ℝ) :=
    lt_trans hb' hlt'
  exact ⟨div_pos hb' hpos, (div_lt_one hpos).mpr hlt'⟩

theorem jointFraction_strictly_between_iff (g : Context) (xs : List (Raw g)) (m1 m2 : M) :
    (0 < jointFraction step resource calibration C reads g xs m1 m2 ∧
      jointFraction step resource calibration C reads g xs m1 m2 < 1) ↔
    ((∃ x0 ∈ xs, JointlyHoldable step resource calibration C reads g x0 m1 m2) ∧
      (∃ x1 ∈ xs, IrreduciblyJointAt step resource calibration C reads g x1 m1 m2)) := by
  constructor
  · rintro ⟨hpos, hlt⟩
    have hb : 0 < bothCount step resource calibration C reads g xs m1 m2 := by
      by_contra hb0
      have hz : bothCount step resource calibration C reads g xs m1 m2 = 0 :=
        Nat.eq_zero_of_not_pos hb0
      unfold jointFraction at hpos
      rw [hz, Nat.cast_zero, zero_div] at hpos
      exact lt_irrefl 0 hpos
    constructor
    · have hb2 := hb
      unfold bothCount at hb2
      obtain ⟨x0, hx0, hdec⟩ := List.countP_pos_iff.mp hb2
      exact ⟨x0, hx0, of_decide_eq_true hdec⟩
    · by_contra hnone
      have hnone' : ∀ x ∈ xs, ¬ IrreduciblyJointAt step resource calibration C reads g x m1 m2 :=
        fun x hx hirr => hnone ⟨x, hx, hirr⟩
      have heq := bothCount_eq_eachCount_of_none step resource calibration C reads g xs m1 m2 hnone'
      have hpos' : (0 : ℝ) < (eachCount step resource calibration C reads g xs m1 m2 : ℝ) := by
        rw [← heq]
        exact Nat.cast_pos.mpr hb
      unfold jointFraction at hlt
      rw [heq, div_self (ne_of_gt hpos')] at hlt
      exact lt_irrefl 1 hlt
  · rintro ⟨⟨x0, hx0, hheld⟩, ⟨x1, hx1, hirr⟩⟩
    exact jointFraction_strictly_between step resource calibration C reads g xs m1 m2 x0 x1 hx0 hx1
      hheld hirr

end APFPaper1.Regulation


universe apfNative_uC apfNative_uF apfNative_uX apfNative_uR apfNative_uM
theorem solution :
∀ {Context : Type apfNative_uC} {Frag : Context → Context → Type apfNative_uF} {Raw : Context → Type apfNative_uX}
  {R : Context → Type apfNative_uR} {M : Type apfNative_uM} (step : (g h : Context) → Frag g h → Raw g → Raw h → Prop)
  (resource : (g : Context) → @APFPaper1.Continuation.WordFrom.{apfNative_uC, apfNative_uF} Context Frag g → R g)
  (calibration : (g : Context) → R g → NNReal) (C : Context → NNReal) (reads : (h : Context) → Raw h → M → Bool)
  (g : Context) (xs : List.{apfNative_uX} (Raw g)) (m1 m2 : M),
  Iff
    (And
      (@LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
        (@APFPaper1.Regulation.jointFraction.{apfNative_uC, apfNative_uF, apfNative_uX, apfNative_uR, apfNative_uM}
          Context Frag Raw R M step resource calibration C reads g xs m1 m2))
      (@LT.lt.{0} Real Real.instLT
        (@APFPaper1.Regulation.jointFraction.{apfNative_uC, apfNative_uF, apfNative_uX, apfNative_uR, apfNative_uM}
          Context Frag Raw R M step resource calibration C reads g xs m1 m2)
        (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))))
    (And
      (@Exists.{apfNative_uX + 1} (Raw g) fun (x0 : Raw g) =>
        And
          (@Membership.mem.{apfNative_uX, apfNative_uX} (Raw g) (List.{apfNative_uX} (Raw g))
            (@List.instMembership.{apfNative_uX} (Raw g)) xs x0)
          (@APFPaper1.Regulation.JointlyHoldable.{apfNative_uC, apfNative_uF, apfNative_uX, apfNative_uR, apfNative_uM}
            Context Frag Raw R M step resource calibration C reads g x0 m1 m2))
      (@Exists.{apfNative_uX + 1} (Raw g) fun (x1 : Raw g) =>
        And
          (@Membership.mem.{apfNative_uX, apfNative_uX} (Raw g) (List.{apfNative_uX} (Raw g))
            (@List.instMembership.{apfNative_uX} (Raw g)) xs x1)
          (@APFPaper1.Regulation.IrreduciblyJointAt.{apfNative_uC, apfNative_uF, apfNative_uX, apfNative_uR,
                apfNative_uM}
            Context Frag Raw R M step resource calibration C reads g x1 m1 m2))) := by
  exact @APFPaper1.Regulation.jointFraction_strictly_between_iff
