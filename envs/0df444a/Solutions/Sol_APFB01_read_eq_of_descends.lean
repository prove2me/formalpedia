-- Prove2me | solution 1 for APFB01.read_eq_of_descends
-- status  : ACCEPTED   (prove)
-- author  : @FiniteUniverse
-- created : 2026-11-14T05:46:15.417929+00:00
-- url     : https://prove2.me/submissions/165a403a-c3d6-475a-8660-aca66e39fcf7

/-
APF Foundation Ledger — theorem node DRAFT (Claude seat, phone session 2026-11-13; not gated, not reviewed,
 not released). Compiled in a cloud sandbox against the frozen v15 bytes of Def_APF_B01_DeclaredInput
 (sha256 9dd8c7f2…5258) with Lean 4.33.1 and no Mathlib; not built on the build box.
name: APFB01_readout_binding
title: A reading that descends is a Boolean function on the physical quotient
inputs_revision: 2026-10-04.1
source: Paper 1 Supplement v9.28:1313-1322 (physical descent of a distinction; "equivalently, x ~ y implies
 d(x) = d(y)"); Def_APF_B01_DeclaredInput.
consumes_inputs: B01 only in `exists_distinction_of_declaredInput`; the first three results are ordinary
 mathematics on the B01 vocabulary.
overlap: the forward direction of `descends_iff_respects` is the existing K3 reference node
 APFB01.fact_agrees_of_same_profile (Thm_APFB01_unseen_turn); reuse it when this is built on the build box.
named_hypothesis: hf, that the Boolean reading is one of the original readout propositions of the full B01
 readout family. This is a source identification, not a law.
statement: (1) a raw predicate descends exactly when profile-equal raw states agree on it; (2) a Boolean
 reading whose truth descends agrees at profile-equal raw states; (3) a family of such readings is a family of
 Boolean functions on the physical quotient, read at the class of the raw state; (4) under B01 and hf the same
 holds for a single reading.
not_claimed: that any particular reading is physical; that a reading in one context is a distinction in another.
-/
import Definitions.Def_APF_B01_DeclaredInput

set_option autoImplicit false
universe uX uP uF uR uO uA uM

namespace APFB01

/-- Supplement v9.28:1322. A raw predicate descends exactly when profile-equal raw states agree on it. -/
theorem descends_iff_respects {X : Type uX} {Process : Type uP}
    (profile : X → Process → Prop) (fact : X → Prop) :
    Descends profile fact ↔ ∀ x y : X, profile x = profile y → (fact x ↔ fact y) := by
  constructor
  · rintro ⟨desc, h⟩ x y hxy
    have hq : physicalClass profile x = physicalClass profile y := Quot.sound hxy
    exact (h x).trans (by rw [hq]; exact (h y).symm)
  · intro h
    exact ⟨Quot.lift fact (fun x y hxy => propext (h x y hxy)), fun _ => Iff.rfl⟩

/-- A Boolean reading whose truth descends takes equal values at profile-equal raw states. -/
theorem read_eq_of_descends {X : Type uX} {Process : Type uP}
    (profile : X → Process → Prop) (read : X → Bool)
    (hd : Descends profile (fun x => read x = true))
    (x y : X) (hxy : profile x = profile y) : read x = read y := by
  have h := (descends_iff_respects profile (fun x => read x = true)).1 hd x y hxy
  cases hx : read x <;> cases hy : read y <;> simp [hx, hy] at h ⊢

/-- A family of Boolean readings whose truths descend is a family of Boolean functions on the physical
quotient, read at the class of the raw state. -/
theorem exists_distinctions_of_descends {X : Type uX} {Process : Type uP} {M : Type uM}
    (profile : X → Process → Prop) (reads : X → M → Bool)
    (hd : ∀ m : M, Descends profile (fun x => reads x m = true)) :
    ∃ d : M → PhysicalState profile → Bool,
      ∀ (x : X) (m : M), reads x m = d m (physicalClass profile x) :=
  ⟨fun m => Quot.lift (fun x => reads x m)
      (fun x y hxy => read_eq_of_descends profile (fun x => reads x m) (hd m) x y hxy),
    fun _ _ => rfl⟩

/-- Under the declared input B01, a Boolean reading that is one of the original readout propositions is a
Boolean function on the physical quotient. -/
theorem exists_distinction_of_declaredInput
    {X : Type uX} {Process : Type uP} {PhysicalFact : Type uF}
    {ReadoutFact : Type uR} {ResultFact : Type uO} {AdmissionFact : Type uA}
    (profile : X → Process → Prop) (truth : PhysicalFact → X → Prop)
    (readoutTruth : ReadoutFact → X → Prop) (resultTruth : ResultFact → X → Prop)
    (admissionTruth : AdmissionFact → X → Prop)
    (hB01 : APF_B01_DeclaredInput profile truth readoutTruth resultTruth admissionTruth)
    (read : X → Bool) (f : ReadoutFact) (hf : ∀ x : X, readoutTruth f x ↔ read x = true) :
    ∃ d : PhysicalState profile → Bool, ∀ x : X, read x = d (physicalClass profile x) := by
  obtain ⟨desc, h⟩ := hB01.2.1 f
  have hd : Descends profile (fun x => read x = true) :=
    ⟨desc, fun x => (hf x).symm.trans (h x)⟩
  exact ⟨Quot.lift read (fun x y hxy => read_eq_of_descends profile read hd x y hxy), fun _ => rfl⟩

/-- Every physical state has a raw representative, and a Boolean function on the quotient that is true at
the state is true when read at that representative. -/
theorem exists_rep_reading_true {X : Type uX} {Process : Type uP}
    (profile : X → Process → Prop) (c : PhysicalState profile)
    (d1 d2 : PhysicalState profile → Bool) (h1 : d1 c = true) (h2 : d2 c = true) :
    ∃ x : X, physicalClass profile x = c ∧
      d1 (physicalClass profile x) = true ∧ d2 (physicalClass profile x) = true := by
  obtain ⟨x, hx⟩ := Quot.exists_rep c
  exact ⟨x, hx, by rw [show physicalClass profile x = c from hx]; exact h1,
    by rw [show physicalClass profile x = c from hx]; exact h2⟩

end APFB01

#print axioms APFB01.descends_iff_respects
#print axioms APFB01.read_eq_of_descends
#print axioms APFB01.exists_distinctions_of_descends
#print axioms APFB01.exists_distinction_of_declaredInput
#print axioms APFB01.exists_rep_reading_true


universe apfNative_uX apfNative_uP
theorem solution :
∀ {X : Type apfNative_uX} {Process : Type apfNative_uP} (profile : X → Process → Prop) (read : X → Bool)
  (hd : @APFB01.Descends.{apfNative_uX, apfNative_uP} X Process profile fun (x : X) => @Eq.{1} Bool (read x) Bool.true)
  (x y : X) (hxy : @Eq.{apfNative_uP + 1} (Process → Prop) (profile x) (profile y)), @Eq.{1} Bool (read x) (read y) := by
  exact @APFB01.read_eq_of_descends
