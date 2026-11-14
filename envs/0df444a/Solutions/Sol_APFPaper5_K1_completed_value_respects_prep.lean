-- Prove2me | solution 1 for APFPaper5.K1.completed_value_respects_prep
-- status  : ACCEPTED   (prove)
-- author  : @FiniteUniverse
-- created : 2026-11-13T17:25:36.301612+00:00
-- url     : https://prove2.me/submissions/15b44400-770f-4945-bd70-cbe7874aab14

/-
APF — support theorem for Paper 5 obligation K1.a. DRAFT for author and cold review. Not gated, not released.
name: APFPaper5.K1.completed_value_respects_classes
title: A value read off completed runs is constant on contextual classes of the preparation and of the terminal test
inputs_revision: 2026-10-04.1 (consumes no declared input)
mathlib_rev: 0df444a360eaa60ab8c11dca51a86af692955474
source: Paper 5 Technical Supplement v7.33:353-362 ("s respects the strong contextual quotient"), 746-760; Paper 1
  Technical Supplement v9.28:3239-3250.
statement: With contextual equivalence taken over all ambient words (author ruling 2026-11-12), if two preparations
  are equivalent then, for every terminal test and raw input, the completed run is defined for one exactly when it
  is for the other, and the values agree when defined. Likewise for two equivalent terminal tests after a fixed
  preparation.
label: BY DEFINITION OF ContextEq. Each statement is the definition instantiated at an empty prefix or suffix. It
  says a score that IS the value of completed runs respects the quotient. It does not say any physical score is
  such a value.
-/
import Definitions.Def_APFPaper1_ContextualEquivalence

set_option autoImplicit false
namespace APFPaper5.K1
open APFPaper1.Continuation

universe uC uF uX uV
variable {Context : Type uC} {Frag : Context → Context → Type uF} {Raw : Context → Type uX}
  {Val : Type uV}

/-- Equivalent preparations, same terminal test. -/
theorem completed_value_respects_prep (Defd : (g : Context) → Raw g → WordFrom Frag g → Prop)
    (value : (g : Context) → WordFrom Frag g → Raw g → Val)
    {g a c : Context} (W W' : Word Frag g a) (S : Word Frag a c) (x : Raw g)
    (h : ContextEq Defd value (fun _ _ _ => True) W W') :
    (Defd g x (sandwich (Word.nil g) W S) ↔ Defd g x (sandwich (Word.nil g) W' S)) ∧
    (Defd g x (sandwich (Word.nil g) W S) → Defd g x (sandwich (Word.nil g) W' S) →
      value g (sandwich (Word.nil g) W S) x = value g (sandwich (Word.nil g) W' S) x) :=
  h g c (Word.nil g) S x trivial trivial

/-- Equivalent terminal tests, same preparation. -/
theorem completed_value_respects_test (Defd : (g : Context) → Raw g → WordFrom Frag g → Prop)
    (value : (g : Context) → WordFrom Frag g → Raw g → Val)
    {g a c : Context} (W : Word Frag g a) (S S' : Word Frag a c) (x : Raw g)
    (h : ContextEq Defd value (fun _ _ _ => True) S S') :
    (Defd g x (sandwich W S (Word.nil c)) ↔ Defd g x (sandwich W S' (Word.nil c))) ∧
    (Defd g x (sandwich W S (Word.nil c)) → Defd g x (sandwich W S' (Word.nil c)) →
      value g (sandwich W S (Word.nil c)) x = value g (sandwich W S' (Word.nil c)) x) :=
  h g c W (Word.nil c) x trivial trivial

end APFPaper5.K1


universe apfNative_uC apfNative_uF apfNative_uX apfNative_uV
theorem solution :
∀ {Context : Type apfNative_uC} {Frag : Context → Context → Type apfNative_uF} {Raw : Context → Type apfNative_uX}
  {Val : Type apfNative_uV}
  (Defd : (g : Context) → Raw g → @APFPaper1.Continuation.WordFrom.{apfNative_uC, apfNative_uF} Context Frag g → Prop)
  (value : (g : Context) → @APFPaper1.Continuation.WordFrom.{apfNative_uC, apfNative_uF} Context Frag g → Raw g → Val)
  {g a c : Context} (W W' : @APFPaper1.Continuation.Word.{apfNative_uC, apfNative_uF} Context Frag g a)
  (S : @APFPaper1.Continuation.Word.{apfNative_uC, apfNative_uF} Context Frag a c) (x : Raw g)
  (h :
    @APFPaper1.Continuation.ContextEq.{apfNative_uC, apfNative_uF, apfNative_uX, apfNative_uV} Context Frag Raw Val Defd
      value
      (fun (x x_1 : Context) (x_2 : @APFPaper1.Continuation.Word.{apfNative_uC, apfNative_uF} Context Frag x x_1) =>
        True)
      g a W W'),
  And
    (Iff
      (Defd g x
        (@APFPaper1.Continuation.sandwich.{apfNative_uC, apfNative_uF} Context Frag g g a c
          (@APFPaper1.Continuation.Word.nil.{apfNative_uC, apfNative_uF} Context Frag g) W S))
      (Defd g x
        (@APFPaper1.Continuation.sandwich.{apfNative_uC, apfNative_uF} Context Frag g g a c
          (@APFPaper1.Continuation.Word.nil.{apfNative_uC, apfNative_uF} Context Frag g) W' S)))
    (Defd g x
        (@APFPaper1.Continuation.sandwich.{apfNative_uC, apfNative_uF} Context Frag g g a c
          (@APFPaper1.Continuation.Word.nil.{apfNative_uC, apfNative_uF} Context Frag g) W S) →
      Defd g x
          (@APFPaper1.Continuation.sandwich.{apfNative_uC, apfNative_uF} Context Frag g g a c
            (@APFPaper1.Continuation.Word.nil.{apfNative_uC, apfNative_uF} Context Frag g) W' S) →
        @Eq.{apfNative_uV + 1} Val
          (value g
            (@APFPaper1.Continuation.sandwich.{apfNative_uC, apfNative_uF} Context Frag g g a c
              (@APFPaper1.Continuation.Word.nil.{apfNative_uC, apfNative_uF} Context Frag g) W S)
            x)
          (value g
            (@APFPaper1.Continuation.sandwich.{apfNative_uC, apfNative_uF} Context Frag g g a c
              (@APFPaper1.Continuation.Word.nil.{apfNative_uC, apfNative_uF} Context Frag g) W' S)
            x)) := by
  exact @APFPaper5.K1.completed_value_respects_prep
