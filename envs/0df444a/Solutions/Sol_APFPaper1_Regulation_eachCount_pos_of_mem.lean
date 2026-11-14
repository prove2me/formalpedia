-- Prove2me | solution 1 for APFPaper1.Regulation.eachCount_pos_of_mem
-- status  : ACCEPTED   (prove)
-- author  : @FiniteUniverse
-- created : 2026-11-13T17:30:08.020869+00:00
-- url     : https://prove2.me/submissions/275c0ef0-5d26-431e-a60c-34c0b695be6a

/-
APF Foundation Ledger — theorem node DRAFT (session EthanBrooke-01WrrBvu, 2026-11-12; not gated, not reviewed)
name: APFPaper1_Regulation_overflow
title: Irreducibly joint means budget overflow; and when the count ratio is strictly between 0 and 1
inputs_revision: 2026-10-04.1
mathlib_rev: 0df444a360eaa60ab8c11dca51a86af692955474
source: as Def_APFPaper1_Regulation. Paper 1 Supplement v9.28:1224-1235 (the budget clause of Cont).
consumes_inputs: none as a hypothesis. The capacity C is the ledger's own object (B04 in the source).
statement: (irreduciblyJointAt_iff_overflow) a pair is irreducibly joint at a disturbance exactly when each
 mark is holdable there and every response having a run that ends where both marks read true has a bill
 above the context capacity. (bothCount_pos_of_mem, eachCount_pos_of_mem) a listed disturbance at which one
 response saves both marks makes both counts positive. (count_ratio_strictly_between) a list containing one
 such disturbance and one irreducibly joint disturbance has 0 < bothCount < eachCount.
not_claimed: that either kind of disturbance exists; that the ratio is a score or the pair number of any
 algebra. The second clause of the first statement is satisfied vacuously when no response at any bill
 reaches a state where both marks read true.
-/
import Theorems.Thm_APFPaper1_Regulation_bothCount_lt_eachCount_of_witness

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

theorem irreduciblyJointAt_iff_overflow (g : Context) (x : Raw g) (m1 m2 : M) :
    IrreduciblyJointAt step resource calibration C reads g x m1 m2 ↔
      Holdable step resource calibration C reads g x m1 ∧
      Holdable step resource calibration C reads g x m2 ∧
      ∀ w : WordFrom Frag g,
        (∃ y : Raw w.1, Executes step w.2 x y ∧ reads w.1 y m1 = true ∧ reads w.1 y m2 = true) →
          C g < calibration g (resource g w) := by
  constructor
  · rintro ⟨h1, h2, hn⟩
    refine ⟨h1, h2, fun w hw => ?_⟩
    by_contra hlt
    exact hn ⟨w, not_lt.mp hlt, hw⟩
  · rintro ⟨h1, h2, hov⟩
    refine ⟨h1, h2, ?_⟩
    rintro ⟨w, hbill, hw⟩
    exact absurd hbill (not_le.mpr (hov w hw))

theorem bothCount_pos_of_mem (g : Context) (xs : List (Raw g)) (m1 m2 : M) (x0 : Raw g)
    (hx0 : x0 ∈ xs) (hj : JointlyHoldable step resource calibration C reads g x0 m1 m2) :
    0 < bothCount step resource calibration C reads g xs m1 m2 := by
  unfold bothCount
  exact List.countP_pos_iff.mpr ⟨x0, hx0, decide_eq_true hj⟩

theorem eachCount_pos_of_mem (g : Context) (xs : List (Raw g)) (m1 m2 : M) (x0 : Raw g)
    (hx0 : x0 ∈ xs) (hj : JointlyHoldable step resource calibration C reads g x0 m1 m2) :
    0 < eachCount step resource calibration C reads g xs m1 m2 :=
  lt_of_lt_of_le (bothCount_pos_of_mem step resource calibration C reads g xs m1 m2 x0 hx0 hj)
    (bothCount_le_eachCount step resource calibration C reads g xs m1 m2)

theorem count_ratio_strictly_between (g : Context) (xs : List (Raw g)) (m1 m2 : M)
    (x0 x1 : Raw g) (hx0 : x0 ∈ xs) (hx1 : x1 ∈ xs)
    (hheld : JointlyHoldable step resource calibration C reads g x0 m1 m2)
    (hirr : IrreduciblyJointAt step resource calibration C reads g x1 m1 m2) :
    0 < bothCount step resource calibration C reads g xs m1 m2 ∧
      bothCount step resource calibration C reads g xs m1 m2 <
        eachCount step resource calibration C reads g xs m1 m2 :=
  ⟨bothCount_pos_of_mem step resource calibration C reads g xs m1 m2 x0 hx0 hheld,
    bothCount_lt_eachCount_of_witness step resource calibration C reads g xs m1 m2 x1 hx1 hirr⟩

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
  (hj :
    @APFPaper1.Regulation.JointlyHoldable.{apfNative_uC, apfNative_uF, apfNative_uX, apfNative_uR, apfNative_uM} Context
      Frag Raw R M step resource calibration C reads g x0 m1 m2),
  @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
    (@APFPaper1.Regulation.eachCount.{apfNative_uC, apfNative_uF, apfNative_uX, apfNative_uR, apfNative_uM} Context Frag
      Raw R M step resource calibration C reads g xs m1 m2) := by
  exact @APFPaper1.Regulation.eachCount_pos_of_mem
