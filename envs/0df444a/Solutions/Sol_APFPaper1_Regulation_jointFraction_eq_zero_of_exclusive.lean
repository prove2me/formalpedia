-- Prove2me | solution 1 for APFPaper1.Regulation.jointFraction_eq_zero_of_exclusive
-- status  : ACCEPTED   (prove)
-- author  : @FiniteUniverse
-- created : 2026-11-13T17:34:33.42562+00:00
-- url     : https://prove2.me/submissions/50875818-d3e5-4a98-bdc9-2ff950a165f4

/-
APF Foundation Ledger — theorem node DRAFT (session EthanBrooke-01WrrBvu, 2026-11-12; not gated, not reviewed)
name: APFPaper1_joint_fraction_exclusive
title: The joint fraction of two marks that never read true together is zero
inputs_revision: 2026-10-04.1
mathlib_rev: 0df444a360eaa60ab8c11dca51a86af692955474
source: as Def_APFPaper1_JointFraction. The test announced in NOTE_derivation_pass_2_2026-11-12.
consumes_inputs: none.
statement: (not_jointlyHoldable_of_exclusive) if no state reads both marks true, no response saves both.
 (bothCount_eq_zero_of_exclusive, jointFraction_eq_zero_of_exclusive) so the count of jointly saved
 disturbances is 0 and the joint fraction is 0, on every list.
consequence: in a model where a state carries one single mark, two different single marks never read true
 together. There the joint fraction is 0 for different single marks and 1 for a mark with itself. It cannot
 return the square of the two-mark model. The joint fraction measures whether two readings can be held
 together. It is NOT the turn number.
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

theorem not_jointlyHoldable_of_exclusive (m1 m2 : M)
    (hexcl : ∀ (h : Context) (y : Raw h), ¬ (reads h y m1 = true ∧ reads h y m2 = true))
    (g : Context) (x : Raw g) :
    ¬ JointlyHoldable step resource calibration C reads g x m1 m2 := by
  rintro ⟨w, _, y, _, h1, h2⟩
  exact hexcl w.1 y ⟨h1, h2⟩

theorem bothCount_eq_zero_of_exclusive (m1 m2 : M)
    (hexcl : ∀ (h : Context) (y : Raw h), ¬ (reads h y m1 = true ∧ reads h y m2 = true))
    (g : Context) (xs : List (Raw g)) :
    bothCount step resource calibration C reads g xs m1 m2 = 0 := by
  by_contra hne
  have hpos : 0 < bothCount step resource calibration C reads g xs m1 m2 := Nat.pos_of_ne_zero hne
  unfold bothCount at hpos
  obtain ⟨x0, _, hdec⟩ := List.countP_pos_iff.mp hpos
  exact not_jointlyHoldable_of_exclusive step resource calibration C reads m1 m2 hexcl g x0
    (of_decide_eq_true hdec)

theorem jointFraction_eq_zero_of_exclusive (m1 m2 : M)
    (hexcl : ∀ (h : Context) (y : Raw h), ¬ (reads h y m1 = true ∧ reads h y m2 = true))
    (g : Context) (xs : List (Raw g)) :
    jointFraction step resource calibration C reads g xs m1 m2 = 0 := by
  unfold jointFraction
  rw [bothCount_eq_zero_of_exclusive step resource calibration C reads m1 m2 hexcl g xs,
    Nat.cast_zero, zero_div]

end APFPaper1.Regulation


universe apfNative_uC apfNative_uF apfNative_uX apfNative_uR apfNative_uM
theorem solution :
∀ {Context : Type apfNative_uC} {Frag : Context → Context → Type apfNative_uF} {Raw : Context → Type apfNative_uX}
  {R : Context → Type apfNative_uR} {M : Type apfNative_uM} (step : (g h : Context) → Frag g h → Raw g → Raw h → Prop)
  (resource : (g : Context) → @APFPaper1.Continuation.WordFrom.{apfNative_uC, apfNative_uF} Context Frag g → R g)
  (calibration : (g : Context) → R g → NNReal) (C : Context → NNReal) (reads : (h : Context) → Raw h → M → Bool)
  (m1 m2 : M)
  (hexcl :
    ∀ (h : Context) (y : Raw h),
      Not (And (@Eq.{1} Bool (reads h y m1) Bool.true) (@Eq.{1} Bool (reads h y m2) Bool.true)))
  (g : Context) (xs : List.{apfNative_uX} (Raw g)),
  @Eq.{1} Real
    (@APFPaper1.Regulation.jointFraction.{apfNative_uC, apfNative_uF, apfNative_uX, apfNative_uR, apfNative_uM} Context
      Frag Raw R M step resource calibration C reads g xs m1 m2)
    (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) := by
  exact @APFPaper1.Regulation.jointFraction_eq_zero_of_exclusive
