-- Prove2me | solution 1 for APFB01.turn_between_same_profile_of_declaredInput
-- status  : ACCEPTED   (prove)
-- author  : @FiniteUniverse
-- created : 2026-11-13T17:11:55.436134+00:00
-- url     : https://prove2.me/submissions/a96da313-b039-4c5e-b515-673f21375c0d

/-
APF Foundation Ledger — theorem node DRAFT (session EthanBrooke-01WrrBvu, 2026-11-12; not gated, not reviewed)
name: APFB01_turn_between_same_profile
title: Under B01, two raw objects with the same continuation profile are joined by an admissible turn, if reachability by an admissible turn is an admission fact
inputs_revision: 2026-10-04.1
mathlib_rev: 0df444a360eaa60ab8c11dca51a86af692955474
source: FOUNDATION_INPUTS B01 ("A physical object is its admissible continuation profile. Physical facts are
 fixed by that structure."), in the designated form APF_B01_DeclaredInput and its descent predicate. Author's
 direction of 2026-10-04: every physical fact, including admission, descends to the continuation quotient.
consumes_inputs: B01, as a hypothesis. The first theorem takes one descent instance; the second takes the full
 declared input with the admission facts chosen as "w is reachable from x by an admissible turn".
statement: (APFB01.turn_between_same_profile) if the identity is an admissible turn, the fact "w is reachable
 from x by an admissible turn" descends to the continuation quotient, and x and y have the same profile, then
 some admissible turn carries x to y. (APFB01.turn_between_same_profile_of_declaredInput) the same from the
 full declared input.
not_claimed: that reachability by an admissible turn is an admission fact of the source; that two pairs of
 marks with the same number have the same profile. They do not once a third mark is present
 (Thm_APFPaper5_K3_exchange_test, third_mark_sees_handedness), so this theorem does not give the two-point
 clause.
-/
import Definitions.Def_APF_B01_DeclaredInput
import Mathlib.Data.Set.Defs

set_option autoImplicit false

universe uX uP uF uR uO

theorem APFB01.turn_between_same_profile {X : Type uX} {Process : Type uP}
    (profile : X → Process → Prop) (Adm : Set (X → X)) (hid : (fun w : X => w) ∈ Adm)
    (x y : X) (hprof : profile x = profile y)
    (hdescends : APFB01.Descends profile (fun w : X => ∃ T ∈ Adm, T x = w)) :
    ∃ T ∈ Adm, T x = y := by
  obtain ⟨descended, hdesc⟩ := hdescends
  have hx : ∃ T ∈ Adm, T x = x := ⟨fun w => w, hid, rfl⟩
  have hclass : APFB01.physicalClass profile x = APFB01.physicalClass profile y :=
    Quot.sound hprof
  have h1 := (hdesc x).mp hx
  rw [hclass] at h1
  exact (hdesc y).mpr h1

theorem APFB01.turn_between_same_profile_of_declaredInput {X : Type uX} {Process : Type uP}
    {PhysicalFact : Type uF} {ReadoutFact : Type uR} {ResultFact : Type uO}
    (profile : X → Process → Prop) (truth : PhysicalFact → X → Prop)
    (readoutTruth : ReadoutFact → X → Prop) (resultTruth : ResultFact → X → Prop)
    (Adm : Set (X → X)) (hid : (fun w : X => w) ∈ Adm)
    (hB01 : APF_B01_DeclaredInput profile truth readoutTruth resultTruth
      (fun (x : X) (w : X) => ∃ T ∈ Adm, T x = w))
    (x y : X) (hprof : profile x = profile y) : ∃ T ∈ Adm, T x = y :=
  APFB01.turn_between_same_profile profile Adm hid x y hprof (hB01.2.2.2 x)


universe apfNative_uX apfNative_uP apfNative_uF apfNative_uR apfNative_uO
theorem solution :
∀ {X : Type apfNative_uX} {Process : Type apfNative_uP} {PhysicalFact : Type apfNative_uF}
  {ReadoutFact : Type apfNative_uR} {ResultFact : Type apfNative_uO} (profile : X → Process → Prop)
  (truth : PhysicalFact → X → Prop) (readoutTruth : ReadoutFact → X → Prop) (resultTruth : ResultFact → X → Prop)
  (Adm : Set.{apfNative_uX} (X → X))
  (hid :
    @Membership.mem.{apfNative_uX, apfNative_uX} ((w : X) → X) (Set.{apfNative_uX} (X → X))
      (@Set.instMembership.{apfNative_uX} (X → X)) Adm fun (w : X) => w)
  (hB01 :
    @APF_B01_DeclaredInput.{apfNative_uX, apfNative_uP, apfNative_uF, apfNative_uR, apfNative_uO, apfNative_uX} X
      Process PhysicalFact ReadoutFact ResultFact X profile truth readoutTruth resultTruth fun (x w : X) =>
      @Exists.{apfNative_uX + 1} (X → X) fun (T : X → X) =>
        And
          (@Membership.mem.{apfNative_uX, apfNative_uX} (X → X) (Set.{apfNative_uX} (X → X))
            (@Set.instMembership.{apfNative_uX} (X → X)) Adm T)
          (@Eq.{apfNative_uX + 1} X (T x) w))
  (x y : X) (hprof : @Eq.{apfNative_uP + 1} (Process → Prop) (profile x) (profile y)),
  @Exists.{apfNative_uX + 1} (X → X) fun (T : X → X) =>
    And
      (@Membership.mem.{apfNative_uX, apfNative_uX} (X → X) (Set.{apfNative_uX} (X → X))
        (@Set.instMembership.{apfNative_uX} (X → X)) Adm T)
      (@Eq.{apfNative_uX + 1} X (T x) y) := by
  exact @APFB01.turn_between_same_profile_of_declaredInput
