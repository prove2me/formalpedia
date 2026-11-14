-- Prove2me | solution 1 for APFPaper1.Continuation.cont_at_another_state_iff_runs
-- status  : ACCEPTED   (prove)
-- author  : @FiniteUniverse
-- created : 2026-11-14T05:50:24.894212+00:00
-- url     : https://prove2.me/submissions/e0f514fd-f35e-43a1-bb2b-b92d223394f0

/-
APF Foundation Ledger — theorem node DRAFT (session EthanBrooke-01WrrBvu, 2026-11-13; not gated, not reviewed)
name: APFPaper1_Cont_budget_is_state_free
title: In the continuation class the budget test of a word does not depend on the state it starts from; a step admitted at one state of a context is admitted at another exactly when it runs from it
inputs_revision: 2026-10-04.1
mathlib_rev: 0df444a360eaa60ab8c11dca51a86af692955474
source: Def_APFPaper1_ContinuationWords (Cont, author ruling 2026-11-12). The author's statements of
 2026-11-13 16:27 and 16:29 HST.
consumes_inputs: none. A consequence of the definition of the continuation class.
statement: (cont_at_another_state_iff_runs) if a word is in the continuation class of x, it is in the
 continuation class of another raw state of the same context exactly when it executes from that state.
reading: for the same step taken again from where it ended, "the budget allows" is already settled by its
 having been admitted once. What remains is whether it runs from there.
not_claimed: that the two-step word is in budget from the first state (that is cont_again_iff, and it is a
 different question); that the step runs from where it ended.
-/
import Definitions.Def_APFPaper1_ContinuationWords

set_option autoImplicit false
namespace APFPaper1.Continuation

universe uC uF uX uR

variable {Context : Type uC} {Frag : Context → Context → Type uF} {Raw : Context → Type uX}
  {R : Context → Type uR}

theorem cont_at_another_state_iff_runs
    (step : (g h : Context) → Frag g h → Raw g → Raw h → Prop)
    (resource : (g : Context) → WordFrom Frag g → R g)
    (calibration : (g : Context) → R g → NNReal) (C : Context → NNReal)
    (g : Context) (x x' : Raw g) (w : WordFrom Frag g)
    (hx : Cont step resource calibration C g x w) :
    Cont step resource calibration C g x' w ↔ ∃ z : Raw w.1, Executes step w.2 x' z :=
  ⟨fun h => h.1, fun h => ⟨h, hx.2⟩⟩

end APFPaper1.Continuation


universe apfNative_uC apfNative_uF apfNative_uX apfNative_uR
theorem solution :
∀ {Context : Type apfNative_uC} {Frag : Context → Context → Type apfNative_uF} {Raw : Context → Type apfNative_uX}
  {R : Context → Type apfNative_uR} (step : (g h : Context) → Frag g h → Raw g → Raw h → Prop)
  (resource : (g : Context) → @APFPaper1.Continuation.WordFrom.{apfNative_uC, apfNative_uF} Context Frag g → R g)
  (calibration : (g : Context) → R g → NNReal) (C : Context → NNReal) (g : Context) (x x' : Raw g)
  (w : @APFPaper1.Continuation.WordFrom.{apfNative_uC, apfNative_uF} Context Frag g)
  (hx :
    @APFPaper1.Continuation.Cont.{apfNative_uC, apfNative_uF, apfNative_uX, apfNative_uR} Context Frag Raw R step
      resource calibration C g x w),
  Iff
    (@APFPaper1.Continuation.Cont.{apfNative_uC, apfNative_uF, apfNative_uX, apfNative_uR} Context Frag Raw R step
      resource calibration C g x' w)
    (@Exists.{apfNative_uX + 1}
      (Raw
        (@Sigma.fst.{apfNative_uC, max apfNative_uC apfNative_uF} Context
          (fun (h : Context) => @APFPaper1.Continuation.Word.{apfNative_uC, apfNative_uF} Context Frag g h) w))
      fun
        (z :
          Raw
            (@Sigma.fst.{apfNative_uC, max apfNative_uC apfNative_uF} Context
              (fun (h : Context) => @APFPaper1.Continuation.Word.{apfNative_uC, apfNative_uF} Context Frag g h) w)) =>
      @APFPaper1.Continuation.Executes.{apfNative_uC, apfNative_uF, apfNative_uX} Context Frag Raw step g
        (@Sigma.fst.{apfNative_uC, max apfNative_uC apfNative_uF} Context
          (fun (h : Context) => @APFPaper1.Continuation.Word.{apfNative_uC, apfNative_uF} Context Frag g h) w)
        (@Sigma.snd.{apfNative_uC, max apfNative_uC apfNative_uF} Context
          (fun (h : Context) => @APFPaper1.Continuation.Word.{apfNative_uC, apfNative_uF} Context Frag g h) w)
        x' z) := by
  exact @APFPaper1.Continuation.cont_at_another_state_iff_runs
