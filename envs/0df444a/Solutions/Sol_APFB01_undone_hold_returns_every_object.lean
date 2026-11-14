-- Prove2me | solution 1 for APFB01.undone_hold_returns_every_object
-- status  : ACCEPTED   (prove)
-- author  : @FiniteUniverse
-- created : 2026-11-14T05:54:33.695954+00:00
-- url     : https://prove2.me/submissions/1b686798-b2e4-4f93-90c0-a74ed6859902

/-
APF Foundation Ledger — theorem node DRAFT (session EthanBrooke-01WrrBvu, 2026-11-13; not gated, not reviewed)
name: APFB01_undone_hold_returns
title: With finitely many processes there are finitely many physical objects, and a hold on them that loses nothing brings every object back
inputs_revision: 2026-10-04.1
mathlib_rev: 0df444a360eaa60ab8c11dca51a86af692955474
source: FOUNDATION_INPUTS B01 (the quotient by continuation profile, APFB01.PhysicalState). The B02 input
 node's reading of its context: "Q its full finite process universe" (Def_APF_B02_DeclaredInput, comment;
 the Lean predicate itself does not carry the finiteness).
consumes_inputs: B01's quotient only. No input predicate is assumed.
statement: (APFB01.physicalState_finite) if the process universe is finite, the physical objects are
 finitely many.
 (undone_hold_returns) an injective map of a finite set to itself brings every point back after some
 positive number of steps.
 (APFB01.undone_hold_returns_every_object) so a hold on physical objects that loses nothing brings every
 object back.
reading: "and back" in the relation sentence follows from "can be undone" where the process universe is
 finite.
not_claimed: that a hold acts on physical objects at an interface; that it loses nothing; anything about
 held states of a continuum model, where exact return can fail.
-/
import Definitions.Def_APF_B01_DeclaredInput
import Mathlib.Data.Fintype.Pigeonhole
import Mathlib.Data.Finite.Prod
import Mathlib.Logic.Function.Iterate

set_option autoImplicit false

universe uX uP

theorem APFB01.physicalState_finite {X : Type uX} {Process : Type uP} [Finite Process]
    (profile : X → Process → Prop) : Finite (APFB01.PhysicalState profile) := by
  have hinj : Function.Injective
      (Quot.lift (fun x : X => profile x) (fun _ _ h => h) :
        APFB01.PhysicalState profile → Process → Prop) := by
    intro a b
    induction a using Quot.ind
    induction b using Quot.ind
    intro h
    exact Quot.sound h
  exact Finite.of_injective _ hinj

namespace APFPaper5.K3

theorem undone_hold_returns {S : Type*} [Finite S] (D : S → S) (hD : Function.Injective D)
    (x : S) : ∃ n : ℕ, 0 < n ∧ D^[n] x = x := by
  obtain ⟨i, j, hij, e⟩ := Finite.exists_ne_map_eq_of_infinite (fun n : ℕ => D^[n] x)
  have key : ∀ a b : ℕ, a < b → D^[a] x = D^[b] x → ∃ n : ℕ, 0 < n ∧ D^[n] x = x := by
    intro a b hab hab'
    refine ⟨b - a, Nat.sub_pos_of_lt hab, ?_⟩
    have t : D^[a] (D^[b - a] x) = D^[a] x := by
      rw [← Function.iterate_add_apply, Nat.add_sub_cancel' hab.le]
      exact hab'.symm
    exact (hD.iterate a) t
  rcases Nat.lt_or_gt_of_ne hij with h | h
  · exact key i j h e
  · exact key j i h e.symm

end APFPaper5.K3

theorem APFB01.undone_hold_returns_every_object {X : Type uX} {Process : Type uP} [Finite Process]
    (profile : X → Process → Prop)
    (D : APFB01.PhysicalState profile → APFB01.PhysicalState profile)
    (hD : Function.Injective D) (s : APFB01.PhysicalState profile) :
    ∃ n : ℕ, 0 < n ∧ D^[n] s = s :=
  haveI := APFB01.physicalState_finite profile
  APFPaper5.K3.undone_hold_returns D hD s


universe apfNative_uX apfNative_uP
theorem solution :
∀ {X : Type apfNative_uX} {Process : Type apfNative_uP} [Finite.{apfNative_uP + 1} Process]
  (profile : X → Process → Prop)
  (D :
    @APFB01.PhysicalState.{apfNative_uX, apfNative_uP} X Process profile →
      @APFB01.PhysicalState.{apfNative_uX, apfNative_uP} X Process profile)
  (hD :
    @Function.Injective.{apfNative_uX + 1, apfNative_uX + 1}
      (@APFB01.PhysicalState.{apfNative_uX, apfNative_uP} X Process profile)
      (@APFB01.PhysicalState.{apfNative_uX, apfNative_uP} X Process profile) D)
  (s : @APFB01.PhysicalState.{apfNative_uX, apfNative_uP} X Process profile),
  @Exists.{1} Nat fun (n : Nat) =>
    And (@LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) n)
      (@Eq.{apfNative_uX + 1} (@APFB01.PhysicalState.{apfNative_uX, apfNative_uP} X Process profile)
        (@Nat.iterate.{apfNative_uX + 1} (@APFB01.PhysicalState.{apfNative_uX, apfNative_uP} X Process profile) D n s)
        s) := by
  exact @APFB01.undone_hold_returns_every_object
