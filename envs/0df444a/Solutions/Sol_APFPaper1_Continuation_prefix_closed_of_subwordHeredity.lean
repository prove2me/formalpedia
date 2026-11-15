-- Prove2me | solution 1 for APFPaper1.Continuation.prefix_closed_of_subwordHeredity
-- status  : ACCEPTED   (prove)
-- author  : @FiniteUniverse
-- created : 2026-11-15T02:41:35.717942+00:00
-- url     : https://prove2.me/submissions/15c9e645-e6eb-4763-b7aa-866ed2e2f402

/-
APF Foundation Ledger — theorem node DRAFT (Claude seat, session EthanBrooke-01WrrBvv, 2026-11-14; not
 gated, not reviewed, not released, not built in the ledger repo)
name: APFPaper1_Cont_subword_gives_prefix
title: For the whole-word continuation class, contiguous-subword heredity gives prefix restriction
inputs_revision: 2026-11-14.1
mathlib_rev: 0df444a360eaa60ab8c11dca51a86af692955474
source: Paper 1 Supplement v9.28:1231 (C3, prefix restriction), 3301 (W-her, contiguous-subword heredity:
 "The continuation axioms deliver this only for execution-initial segments"). Def_APFPaper1_ContinuationWords
 and Def_APFPaper1_ContextualEquivalence (seat 01WrrBvu): Cont, IsPrefix, sandwich, SubwordHeredity.
 Codebank: no statement of prefix restriction or of subword heredity for continuation words was found
 (apf/continuation_calculus.py uses "hereditary" for set systems, a different notion).
consumes_inputs: none. Ordinary mathematics on the definitions.
statement: take the whole-word class Cont as the definedness predicate, and call a word admissible when it
 is in Cont from some raw possibility. If every contiguous subword of a defined word is admissible (W-her),
 then every initial segment of a member of Cont g x is a member of Cont g x (C3).
reading: with the whole-word budget, W-her is at least as strong as C3. The budget does not depend on the
 raw possibility, and an initial segment of an executing word executes from the same possibility.
not_claimed: the converse, which fails (Thm_APFPaper1_Cont_load_worlds); that either clause holds.
-/
import Definitions.Def_APFPaper1_ContextualEquivalence

set_option autoImplicit false
namespace APFPaper1.Continuation

universe uC uF uX uR
variable {Context : Type uC} {Frag : Context → Context → Type uF} {Raw : Context → Type uX}
  {R : Context → Type uR}

theorem prefix_closed_of_subwordHeredity
    (step : (g h : Context) → Frag g h → Raw g → Raw h → Prop)
    (resource : (g : Context) → WordFrom Frag g → R g)
    (calibration : (g : Context) → R g → NNReal) (C : Context → NNReal)
    (hher : SubwordHeredity (Cont step resource calibration C)
      (fun g h M => ∃ x : Raw g, Cont step resource calibration C g x ⟨h, M⟩))
    (g : Context) (x : Raw g) (v w : WordFrom Frag g) (hpre : IsPrefix v w)
    (hw : Cont step resource calibration C g x w) :
    Cont step resource calibration C g x v := by
  obtain ⟨u, hu⟩ := hpre
  have hw' : Cont step resource calibration C g x (sandwich (Word.nil g) v.2 u) := by
    show Cont step resource calibration C g x ⟨w.1, v.2.append u⟩
    rw [← hu]
    exact hw
  obtain ⟨_, _, hb⟩ := hher g g v.1 w.1 (Word.nil g) v.2 u x hw'
  exact ⟨isPrefix_executes step v w ⟨u, hu⟩ x hw.1, hb⟩

end APFPaper1.Continuation

#print axioms APFPaper1.Continuation.prefix_closed_of_subwordHeredity


universe apfNative_uC apfNative_uF apfNative_uX apfNative_uR
theorem solution :
∀ {Context : Type apfNative_uC} {Frag : Context → Context → Type apfNative_uF} {Raw : Context → Type apfNative_uX}
  {R : Context → Type apfNative_uR} (step : (g h : Context) → Frag g h → Raw g → Raw h → Prop)
  (resource : (g : Context) → @APFPaper1.Continuation.WordFrom.{apfNative_uC, apfNative_uF} Context Frag g → R g)
  (calibration : (g : Context) → R g → NNReal) (C : Context → NNReal)
  (hher :
    @APFPaper1.Continuation.SubwordHeredity.{apfNative_uC, apfNative_uF, apfNative_uX} Context Frag Raw
      (@APFPaper1.Continuation.Cont.{apfNative_uC, apfNative_uF, apfNative_uX, apfNative_uR} Context Frag Raw R step
        resource calibration C)
      fun (g h : Context) (M : @APFPaper1.Continuation.Word.{apfNative_uC, apfNative_uF} Context Frag g h) =>
      @Exists.{apfNative_uX + 1} (Raw g) fun (x : Raw g) =>
        @APFPaper1.Continuation.Cont.{apfNative_uC, apfNative_uF, apfNative_uX, apfNative_uR} Context Frag Raw R step
          resource calibration C g x
          (@Sigma.mk.{apfNative_uC, max apfNative_uC apfNative_uF} Context
            (fun (h : Context) => @APFPaper1.Continuation.Word.{apfNative_uC, apfNative_uF} Context Frag g h) h M))
  (g : Context) (x : Raw g) (v w : @APFPaper1.Continuation.WordFrom.{apfNative_uC, apfNative_uF} Context Frag g)
  (hpre : @APFPaper1.Continuation.IsPrefix.{apfNative_uC, apfNative_uF} Context Frag g v w)
  (hw :
    @APFPaper1.Continuation.Cont.{apfNative_uC, apfNative_uF, apfNative_uX, apfNative_uR} Context Frag Raw R step
      resource calibration C g x w),
  @APFPaper1.Continuation.Cont.{apfNative_uC, apfNative_uF, apfNative_uX, apfNative_uR} Context Frag Raw R step resource
    calibration C g x v := by
  exact @APFPaper1.Continuation.prefix_closed_of_subwordHeredity
