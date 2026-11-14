-- Prove2me | solution 1 for APFPaper1.Continuation.cont_again_iff
-- status  : ACCEPTED   (prove)
-- author  : @FiniteUniverse
-- created : 2026-11-14T05:49:49.18632+00:00
-- url     : https://prove2.me/submissions/a8c6fbb0-7c04-411f-83e8-5b25b4292100

/-
APF Foundation Ledger — theorem node DRAFT (session EthanBrooke-01WrrBvu, 2026-11-13; not gated, not reviewed)
name: APFPaper1_Cont_step_again
title: By the definition of the continuation class, a step can be taken again from a state exactly when it runs from where it ended and the whole bill is at most the capacity
inputs_revision: 2026-10-04.1
mathlib_rev: 0df444a360eaa60ab8c11dca51a86af692955474
source: the author's statements of 2026-11-13, 16:27 HST ("The step - any step - can be taken again if the
 budget alows and it is selected by a2") and 16:29 HST ("This goes to the definition of what a continuation
 profile is"). Def_APFPaper1_ContinuationWords: Cont, "the whole-word budgeted continuation class (author
 ruling 2026-11-12)": a word belongs to Cont g x when it executes from x and its calibrated whole resource is
 at most the capacity of g. FOUNDATION_INPUTS B01, B04.
consumes_inputs: none as a predicate. These are consequences of the definition of the continuation class.
statement: (uses executes_append of the definition module: a word followed by a word executes from x to z
 exactly when the first executes from x to some y and the second from y to z.)
 (cont_then_iff) v followed by u is in the continuation class of x exactly when v runs from x to some state,
 u runs from that state, and the bill of the whole word is at most the capacity.
 (cont_again_iff) so a step u that returns to its own context can be taken again from x exactly when u runs
 from x to some state, runs again from that state, and the bill of the two together is at most the capacity.
reading: "can be taken again" is read off the continuation profile, which is what B01 says a physical
 object is. It is two conditions, running and budget, and no further assumption. Which admissible
 continuation is the realized one is A2's part.
not_claimed: that any step runs again from where it ended; anything about how the bill of a repeated step
 grows (that is supplied in Thm_APFB04_steps_again); any identification with the occupant.
-/
import Definitions.Def_APFPaper1_ContinuationWords

set_option autoImplicit false
namespace APFPaper1.Continuation

universe uC uF uX uR

variable {Context : Type uC} {Frag : Context → Context → Type uF} {Raw : Context → Type uX}
  {R : Context → Type uR}

theorem cont_then_iff (step : (g h : Context) → Frag g h → Raw g → Raw h → Prop)
    (resource : (g : Context) → WordFrom Frag g → R g)
    (calibration : (g : Context) → R g → NNReal) (C : Context → NNReal)
    {g h k : Context} (x : Raw g) (v : Word Frag g h) (u : Word Frag h k) :
    Cont step resource calibration C g x ⟨k, v.append u⟩ ↔
      (∃ y : Raw h, Executes step v x y ∧ ∃ z : Raw k, Executes step u y z) ∧
        calibration g (resource g ⟨k, v.append u⟩) ≤ C g := by
  constructor
  · rintro ⟨⟨z, hz⟩, hb⟩
    obtain ⟨y, h1, h2⟩ := (executes_append step v u x z).mp hz
    exact ⟨⟨y, h1, z, h2⟩, hb⟩
  · rintro ⟨⟨y, h1, z, h2⟩, hb⟩
    exact ⟨⟨z, (executes_append step v u x z).mpr ⟨y, h1, h2⟩⟩, hb⟩

theorem cont_again_iff (step : (g h : Context) → Frag g h → Raw g → Raw h → Prop)
    (resource : (g : Context) → WordFrom Frag g → R g)
    (calibration : (g : Context) → R g → NNReal) (C : Context → NNReal)
    (g : Context) (x : Raw g) (u : Word Frag g g) :
    Cont step resource calibration C g x ⟨g, u.append u⟩ ↔
      (∃ y : Raw g, Executes step u x y ∧ ∃ z : Raw g, Executes step u y z) ∧
        calibration g (resource g ⟨g, u.append u⟩) ≤ C g :=
  cont_then_iff step resource calibration C x u u

end APFPaper1.Continuation


universe apfNative_uC apfNative_uF apfNative_uX apfNative_uR
theorem solution :
∀ {Context : Type apfNative_uC} {Frag : Context → Context → Type apfNative_uF} {Raw : Context → Type apfNative_uX}
  {R : Context → Type apfNative_uR} (step : (g h : Context) → Frag g h → Raw g → Raw h → Prop)
  (resource : (g : Context) → @APFPaper1.Continuation.WordFrom.{apfNative_uC, apfNative_uF} Context Frag g → R g)
  (calibration : (g : Context) → R g → NNReal) (C : Context → NNReal) (g : Context) (x : Raw g)
  (u : @APFPaper1.Continuation.Word.{apfNative_uC, apfNative_uF} Context Frag g g),
  Iff
    (@APFPaper1.Continuation.Cont.{apfNative_uC, apfNative_uF, apfNative_uX, apfNative_uR} Context Frag Raw R step
      resource calibration C g x
      (@Sigma.mk.{apfNative_uC, max apfNative_uC apfNative_uF} Context
        (fun (h : Context) => @APFPaper1.Continuation.Word.{apfNative_uC, apfNative_uF} Context Frag g h) g
        (@APFPaper1.Continuation.Word.append.{apfNative_uC, apfNative_uF} Context Frag g g g u u)))
    (And
      (@Exists.{apfNative_uX + 1} (Raw g) fun (y : Raw g) =>
        And
          (@APFPaper1.Continuation.Executes.{apfNative_uC, apfNative_uF, apfNative_uX} Context Frag Raw step g g u x y)
          (@Exists.{apfNative_uX + 1} (Raw g) fun (z : Raw g) =>
            @APFPaper1.Continuation.Executes.{apfNative_uC, apfNative_uF, apfNative_uX} Context Frag Raw step g g u y
              z))
      (@LE.le.{0} NNReal (@Preorder.toLE.{0} NNReal (@PartialOrder.toPreorder.{0} NNReal NNReal.instPartialOrder))
        (calibration g
          (resource g
            (@Sigma.mk.{apfNative_uC, max apfNative_uC apfNative_uF} Context
              (fun (h : Context) => @APFPaper1.Continuation.Word.{apfNative_uC, apfNative_uF} Context Frag g h) g
              (@APFPaper1.Continuation.Word.append.{apfNative_uC, apfNative_uF} Context Frag g g g u u))))
        (C g))) := by
  exact @APFPaper1.Continuation.cont_again_iff
