-- Prove2me | solution 1 for APFB01.unseen_turn_changes_no_fact
-- status  : ACCEPTED   (prove)
-- author  : @FiniteUniverse
-- created : 2026-11-13T17:14:40.385147+00:00
-- url     : https://prove2.me/submissions/cb5fd1a0-5152-49a9-9c59-a332a9d31c71

/-
APF Foundation Ledger — theorem node DRAFT (session EthanBrooke-01WrrBvu, 2026-11-13; not gated, not reviewed)
name: APFB01_unseen_turn
title: Under B01, a turn that changes no continuation profile changes no physical fact
inputs_revision: 2026-10-04.1
mathlib_rev: 0df444a360eaa60ab8c11dca51a86af692955474
source: FOUNDATION_INPUTS B01 ("A physical object is its admissible continuation profile. Physical facts are
 fixed by that structure."), in its designated descent form. Paper 5 Supplement v7.33:1808-1823 (the common
 held orientation is killed by the record functor) and 1953 (multiplicity without a distinguishing completion
 is quotient-null).
consumes_inputs: B01, as the hypothesis that the fact in question descends to the continuation quotient.
statement: (APFB01.fact_agrees_of_same_profile) if a fact descends and x and y have the same profile, the fact
 holds at x exactly when it holds at y. (APFB01.unseen_turn_changes_no_fact) so if T leaves every profile
 unchanged, the fact holds at T x exactly when it holds at x.
not_claimed: that a common turn leaves every profile unchanged. That needs the profile to be made of records
 the turn does not move.
-/
import Definitions.Def_APF_B01_DeclaredInput

set_option autoImplicit false

universe uX uP

theorem APFB01.fact_agrees_of_same_profile {X : Type uX} {Process : Type uP}
    (profile : X → Process → Prop) (fact : X → Prop) (hd : APFB01.Descends profile fact)
    (x y : X) (hprof : profile x = profile y) : fact x ↔ fact y := by
  obtain ⟨descended, hdesc⟩ := hd
  have hclass : APFB01.physicalClass profile x = APFB01.physicalClass profile y :=
    Quot.sound hprof
  rw [hdesc x, hdesc y, hclass]

theorem APFB01.unseen_turn_changes_no_fact {X : Type uX} {Process : Type uP}
    (profile : X → Process → Prop) (T : X → X) (hunseen : ∀ x : X, profile (T x) = profile x)
    (fact : X → Prop) (hd : APFB01.Descends profile fact) (x : X) : fact (T x) ↔ fact x :=
  APFB01.fact_agrees_of_same_profile profile fact hd (T x) x (hunseen x)


universe apfNative_uX apfNative_uP
theorem solution :
∀ {X : Type apfNative_uX} {Process : Type apfNative_uP} (profile : X → Process → Prop) (T : X → X)
  (hunseen : ∀ (x : X), @Eq.{apfNative_uP + 1} (Process → Prop) (profile (T x)) (profile x)) (fact : X → Prop)
  (hd : @APFB01.Descends.{apfNative_uX, apfNative_uP} X Process profile fact) (x : X), Iff (fact (T x)) (fact x) := by
  exact @APFB01.unseen_turn_changes_no_fact
