-- Prove2me | solution 1 for APFB01.hold_is_a_rearrangement
-- status  : ACCEPTED   (prove)
-- author  : @FiniteUniverse
-- created : 2026-11-14T07:15:23.569323+00:00
-- url     : https://prove2.me/submissions/ed6a3b7a-f265-46ae-b508-04a6b95e1ab6

/-
APF Foundation Ledger — theorem node DRAFT (session EthanBrooke-01WrrBvu, 2026-11-13; not gated, not reviewed)
name: APFB01_hold_rearranges
title: A hold read forward from the continuation relation draws no distinction; if it also erases none, then with finitely many processes it rearranges the physical objects, brings each one back, and is undone by repeating
inputs_revision: 2026-10-04.1
mathlib_rev: 0df444a360eaa60ab8c11dca51a86af692955474
source: the author's wording of 2026-11-13 15:39 HST ("Distinctions are drawn or erased, just rearranged",
 read as: not drawn, not erased, just rearranged, by a hold). FOUNDATION_INPUTS B01 ("A physical object is
 its admissible continuation profile"). Thm_APFB01_undone_hold_returns, Thm_APFPaper5_K3_held_states_and_undo.
consumes_inputs: B01's quotient. No input predicate is assumed.
statement: (hold_draws_nothing_of_derivative) processes are words. If the state after an admitted word
 admits exactly what the earlier state admitted after that word, then two raw states with the same
 continuation relation, at which the word is admitted, have the same continuation relation after it. The
 hold makes no difference where there was none.
 (APFB01.hold_is_a_rearrangement) a hold on raw states that makes no difference where there was none
 ("draws nothing") and loses no difference that was there ("erases nothing") acts on the physical objects.
 With finitely many processes that action is one to one and onto, every object is brought back after some
 positive number of steps, and one step from it is undone by repeating.
reading: of "not drawn, not erased, just rearranged", the first follows from B01 once "after" is the
 continuation relation read forward; the third follows from the second and finiteness. The second is the
 hypothesis.
not_claimed: that a hold erases nothing at any interface; that the hold is defined at every state (it is
 taken here as a map of all raw states, which is where "can be taken again" sits); that anything moves.
-/
import Theorems.Thm_APFPaper5_K3_undo_is_a_repeat
import Theorems.Thm_APFPaper5_K3_kept_along_the_hold
import Theorems.Thm_APFPaper5_K3_every_state_comes_to_return
import Theorems.Thm_APFPaper5_K3_occupant_settles
import Theorems.Thm_APFPaper5_K3_finite_of_separating_family
import Theorems.Thm_APFB01_every_object_comes_to_return

set_option autoImplicit false

universe uX uP uA

namespace APFPaper5.K3

theorem hold_draws_nothing_of_derivative {X : Type uX} {A : Type uA}
    (Cont : X → List A → Prop) (after : X → List A → X) (u : List A)
    (hder : ∀ (x : X) (w : List A), Cont x u → (Cont (after x u) w ↔ Cont x (u ++ w)))
    (x y : X) (hxy : Cont x = Cont y) (hx : Cont x u) :
    Cont (after x u) = Cont (after y u) := by
  have hy : Cont y u := by
    rw [← hxy]
    exact hx
  funext w
  apply propext
  rw [hder x w hx, hder y w hy, hxy]

end APFPaper5.K3

theorem APFB01.hold_is_a_rearrangement {X : Type uX} {Process : Type uP} [Finite Process]
    (profile : X → Process → Prop) (hold : X → X)
    (hnodraw : ∀ x y : X, APFB01.physicalClass profile x = APFB01.physicalClass profile y →
      APFB01.physicalClass profile (hold x) = APFB01.physicalClass profile (hold y))
    (hnoerase : ∀ x y : X,
      APFB01.physicalClass profile (hold x) = APFB01.physicalClass profile (hold y) →
      APFB01.physicalClass profile x = APFB01.physicalClass profile y) :
    ∃ D : APFB01.PhysicalState profile → APFB01.PhysicalState profile,
      (∀ x : X, D (APFB01.physicalClass profile x) = APFB01.physicalClass profile (hold x)) ∧
      Function.Bijective D ∧
      ∀ s : APFB01.PhysicalState profile, ∃ n : ℕ, 0 < n ∧ D^[n] s = s ∧ D^[n - 1] (D s) = s := by
  let D : APFB01.PhysicalState profile → APFB01.PhysicalState profile :=
    Quot.lift (fun x => APFB01.physicalClass profile (hold x))
      (fun x y h => hnodraw x y (Quot.sound h))
  have hinj : Function.Injective D := by
    intro a b
    induction a using Quot.ind
    induction b using Quot.ind
    intro h
    exact hnoerase _ _ h
  have := APFB01.physicalState_finite profile
  refine ⟨D, fun x => rfl, ⟨hinj, Finite.injective_iff_surjective.mp hinj⟩, fun s => ?_⟩
  obtain ⟨n, hn, h⟩ := APFPaper5.K3.undone_hold_returns D hinj s
  exact ⟨n, hn, h, APFPaper5.K3.undo_is_a_repeat D s n hn h⟩


universe apfNative_uX apfNative_uP
theorem solution :
∀ {X : Type apfNative_uX} {Process : Type apfNative_uP} [Finite.{apfNative_uP + 1} Process]
  (profile : X → Process → Prop) (hold : X → X)
  (hnodraw :
    ∀ (x y : X),
      @Eq.{apfNative_uX + 1} (@APFB01.PhysicalState.{apfNative_uX, apfNative_uP} X Process profile)
          (@APFB01.physicalClass.{apfNative_uX, apfNative_uP} X Process profile x)
          (@APFB01.physicalClass.{apfNative_uX, apfNative_uP} X Process profile y) →
        @Eq.{apfNative_uX + 1} (@APFB01.PhysicalState.{apfNative_uX, apfNative_uP} X Process profile)
          (@APFB01.physicalClass.{apfNative_uX, apfNative_uP} X Process profile (hold x))
          (@APFB01.physicalClass.{apfNative_uX, apfNative_uP} X Process profile (hold y)))
  (hnoerase :
    ∀ (x y : X),
      @Eq.{apfNative_uX + 1} (@APFB01.PhysicalState.{apfNative_uX, apfNative_uP} X Process profile)
          (@APFB01.physicalClass.{apfNative_uX, apfNative_uP} X Process profile (hold x))
          (@APFB01.physicalClass.{apfNative_uX, apfNative_uP} X Process profile (hold y)) →
        @Eq.{apfNative_uX + 1} (@APFB01.PhysicalState.{apfNative_uX, apfNative_uP} X Process profile)
          (@APFB01.physicalClass.{apfNative_uX, apfNative_uP} X Process profile x)
          (@APFB01.physicalClass.{apfNative_uX, apfNative_uP} X Process profile y)),
  @Exists.{apfNative_uX + 1}
    (@APFB01.PhysicalState.{apfNative_uX, apfNative_uP} X Process profile →
      @APFB01.PhysicalState.{apfNative_uX, apfNative_uP} X Process profile)
    fun
      (D :
        @APFB01.PhysicalState.{apfNative_uX, apfNative_uP} X Process profile →
          @APFB01.PhysicalState.{apfNative_uX, apfNative_uP} X Process profile) =>
    And
      (∀ (x : X),
        @Eq.{apfNative_uX + 1} (@APFB01.PhysicalState.{apfNative_uX, apfNative_uP} X Process profile)
          (D (@APFB01.physicalClass.{apfNative_uX, apfNative_uP} X Process profile x))
          (@APFB01.physicalClass.{apfNative_uX, apfNative_uP} X Process profile (hold x)))
      (And
        (@Function.Bijective.{apfNative_uX + 1, apfNative_uX + 1}
          (@APFB01.PhysicalState.{apfNative_uX, apfNative_uP} X Process profile)
          (@APFB01.PhysicalState.{apfNative_uX, apfNative_uP} X Process profile) D)
        (∀ (s : @APFB01.PhysicalState.{apfNative_uX, apfNative_uP} X Process profile),
          @Exists.{1} Nat fun (n : Nat) =>
            And (@LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) n)
              (And
                (@Eq.{apfNative_uX + 1} (@APFB01.PhysicalState.{apfNative_uX, apfNative_uP} X Process profile)
                  (@Nat.iterate.{apfNative_uX + 1}
                    (@APFB01.PhysicalState.{apfNative_uX, apfNative_uP} X Process profile) D n s)
                  s)
                (@Eq.{apfNative_uX + 1} (@APFB01.PhysicalState.{apfNative_uX, apfNative_uP} X Process profile)
                  (@Nat.iterate.{apfNative_uX + 1}
                    (@APFB01.PhysicalState.{apfNative_uX, apfNative_uP} X Process profile) D
                    (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat) n
                      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                    (D s))
                  s)))) := by
  exact @APFB01.hold_is_a_rearrangement
