-- Prove2me | solution 1 for APFPaper1.Regulation.forced_choice_of_irreduciblyJointAt
-- status  : ACCEPTED   (prove)
-- author  : @FiniteUniverse
-- created : 2026-11-13T17:27:11.221827+00:00
-- url     : https://prove2.me/submissions/67937117-fdcd-4118-b455-39f24d3615e0

/-
APF Foundation Ledger — theorem node DRAFT (session EthanBrooke-01WrrBvu, 2026-11-12; not gated, not reviewed)
name: APFPaper1_Regulation_forced_choice
title: An irreducibly joint disturbance forces a choice between the two marks
inputs_revision: 2026-10-04.1
mathlib_rev: 0df444a360eaa60ab8c11dca51a86af692955474
source: as Def_APFPaper1_Regulation. Author's question of 2026-11-12, "this would force collapse?".
consumes_inputs: none as a hypothesis.
statement: if a pair is irreducibly joint at a disturbance x, then some budgeted response saves the first
 mark, some budgeted response saves the second, and every run of every budgeted response from x that ends
 where the first mark reads true ends where the second reads false.
not_claimed: which mark is kept; that the kept mark is selected by cost (A2) or that the selection is unique
 (BW); that the lost mark cannot be recovered by a later response; any probability for either outcome.
-/
import Theorems.Thm_APFPaper1_Regulation_holdable_left_of_jointlyHoldable
import Theorems.Thm_APFPaper1_Regulation_holdable_right_of_jointlyHoldable
import Theorems.Thm_APFPaper1_Regulation_bothCount_le_eachCount
import Theorems.Thm_APFPaper1_Regulation_bothCount_eq_eachCount_of_none

set_option autoImplicit false
namespace APFPaper1.Regulation

open APFPaper1.Continuation

universe uC uF uX uR uM
variable {Context : Type uC} {Frag : Context → Context → Type uF} {Raw : Context → Type uX}
  {R : Context → Type uR} {M : Type uM}
  (step : (g h : Context) → Frag g h → Raw g → Raw h → Prop)
  (resource : (g : Context) → WordFrom Frag g → R g)
  (calibration : (g : Context) → R g → NNReal) (C : Context → NNReal)
  (reads : (h : Context) → Raw h → M → Bool)

theorem forced_choice_of_irreduciblyJointAt (g : Context) (x : Raw g) (m1 m2 : M)
    (h : IrreduciblyJointAt step resource calibration C reads g x m1 m2) :
    (∃ w : WordFrom Frag g, Saves step resource calibration C reads g x w m1) ∧
    (∃ w : WordFrom Frag g, Saves step resource calibration C reads g x w m2) ∧
    ∀ (w : WordFrom Frag g) (y : Raw w.1), calibration g (resource g w) ≤ C g →
      Executes step w.2 x y → reads w.1 y m1 = true → reads w.1 y m2 = false := by
  obtain ⟨h1, h2, hn⟩ := h
  refine ⟨h1, h2, fun w y hbill hy hm1 => ?_⟩
  cases hm2 : reads w.1 y m2 with
  | false => rfl
  | true => exact absurd ⟨w, hbill, y, hy, hm1, hm2⟩ hn

end APFPaper1.Regulation


universe apfNative_uC apfNative_uF apfNative_uX apfNative_uR apfNative_uM
theorem solution :
∀ {Context : Type apfNative_uC} {Frag : Context → Context → Type apfNative_uF} {Raw : Context → Type apfNative_uX}
  {R : Context → Type apfNative_uR} {M : Type apfNative_uM} (step : (g h : Context) → Frag g h → Raw g → Raw h → Prop)
  (resource : (g : Context) → @APFPaper1.Continuation.WordFrom.{apfNative_uC, apfNative_uF} Context Frag g → R g)
  (calibration : (g : Context) → R g → NNReal) (C : Context → NNReal) (reads : (h : Context) → Raw h → M → Bool)
  (g : Context) (x : Raw g) (m1 m2 : M)
  (h :
    @APFPaper1.Regulation.IrreduciblyJointAt.{apfNative_uC, apfNative_uF, apfNative_uX, apfNative_uR, apfNative_uM}
      Context Frag Raw R M step resource calibration C reads g x m1 m2),
  And
    (@Exists.{max (apfNative_uC + 1) (apfNative_uF + 1)}
      (@APFPaper1.Continuation.WordFrom.{apfNative_uC, apfNative_uF} Context Frag g)
      fun (w : @APFPaper1.Continuation.WordFrom.{apfNative_uC, apfNative_uF} Context Frag g) =>
      @APFPaper1.Regulation.Saves.{apfNative_uC, apfNative_uF, apfNative_uX, apfNative_uR, apfNative_uM} Context Frag
        Raw R M step resource calibration C reads g x w m1)
    (And
      (@Exists.{max (apfNative_uC + 1) (apfNative_uF + 1)}
        (@APFPaper1.Continuation.WordFrom.{apfNative_uC, apfNative_uF} Context Frag g)
        fun (w : @APFPaper1.Continuation.WordFrom.{apfNative_uC, apfNative_uF} Context Frag g) =>
        @APFPaper1.Regulation.Saves.{apfNative_uC, apfNative_uF, apfNative_uX, apfNative_uR, apfNative_uM} Context Frag
          Raw R M step resource calibration C reads g x w m2)
      (∀ (w : @APFPaper1.Continuation.WordFrom.{apfNative_uC, apfNative_uF} Context Frag g)
        (y :
          Raw
            (@Sigma.fst.{apfNative_uC, max apfNative_uC apfNative_uF} Context
              (fun (h : Context) => @APFPaper1.Continuation.Word.{apfNative_uC, apfNative_uF} Context Frag g h) w)),
        @LE.le.{0} NNReal (@Preorder.toLE.{0} NNReal (@PartialOrder.toPreorder.{0} NNReal NNReal.instPartialOrder))
            (calibration g (resource g w)) (C g) →
          @APFPaper1.Continuation.Executes.{apfNative_uC, apfNative_uF, apfNative_uX} Context Frag Raw step g
              (@Sigma.fst.{apfNative_uC, max apfNative_uC apfNative_uF} Context
                (fun (h : Context) => @APFPaper1.Continuation.Word.{apfNative_uC, apfNative_uF} Context Frag g h) w)
              (@Sigma.snd.{apfNative_uC, max apfNative_uC apfNative_uF} Context
                (fun (h : Context) => @APFPaper1.Continuation.Word.{apfNative_uC, apfNative_uF} Context Frag g h) w)
              x y →
            @Eq.{1} Bool
                (reads
                  (@Sigma.fst.{apfNative_uC, max apfNative_uC apfNative_uF} Context
                    (fun (h : Context) => @APFPaper1.Continuation.Word.{apfNative_uC, apfNative_uF} Context Frag g h) w)
                  y m1)
                Bool.true →
              @Eq.{1} Bool
                (reads
                  (@Sigma.fst.{apfNative_uC, max apfNative_uC apfNative_uF} Context
                    (fun (h : Context) => @APFPaper1.Continuation.Word.{apfNative_uC, apfNative_uF} Context Frag g h) w)
                  y m2)
                Bool.false)) := by
  exact @APFPaper1.Regulation.forced_choice_of_irreduciblyJointAt
