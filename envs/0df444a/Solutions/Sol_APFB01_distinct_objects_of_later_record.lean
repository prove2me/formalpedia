-- Prove2me | solution 1 for APFB01.distinct_objects_of_later_record
-- status  : ACCEPTED   (prove)
-- author  : @FiniteUniverse
-- created : 2026-11-14T05:53:28.806264+00:00
-- url     : https://prove2.me/submissions/ce03e3af-7e05-4c34-b62f-6ce0c565a91c

/-
APF Foundation Ledger — theorem node DRAFT (session EthanBrooke-01WrrBvu, 2026-11-13; not gated, not reviewed)
name: APFB01_reversal_and_the_rate
title: If a hold has a reverse with the same present records and something moves, two different physical objects have the same present records; if present records fix the state, a reversible hold has no direction
inputs_revision: 2026-10-04.1
mathlib_rev: 0df444a360eaa60ab8c11dca51a86af692955474
source: FOUNDATION_INPUTS B01 ("A physical object is its admissible continuation profile. Physical facts are
 fixed by that structure"). The author's adopted sentence of 2026-11-12 ("smooth reversible held states").
 Paper 5 Supplement v7.33:1617-1650, 1656 ("their reverses are admitted in the same record-free component").
consumes_inputs: B01 in the theorems named APFB01, through its descent form: the hypothesis hfact says that
 what the records read after the hold is a physical fact. The other theorems consume none.
statement: X is a space of held states, now reads the present records, D is the hold for one step, E undoes
 it, and theta sends a held state to its reverse.
 (reversed_hold_reads_earlier) if theta keeps the present records and the hold of a reverse is the reverse
 of the undone hold, then after the hold the reverse reads what the state read one step earlier.
 (present_records_do_not_fix_state) if moreover some state reads differently one step earlier and one step
 later, two held states have the same present records and different records after the hold.
 (no_direction_if_present_records_fix_later, no_direction_if_present_records_fix_state) if instead the
 present records fix what the records read after the hold, or fix the held state, every state reads the same
 one step later as one step earlier.
 (APFB01.distinct_objects_of_later_record, APFB01.present_records_do_not_fix_object) two states that read
 differently after the hold are different physical objects, and if they have the same present records no
 function of the present records gives the physical object.
 (APFB01.rate_is_held_of_reversal) so reversal and motion give two different physical objects with the same
 present records.
not_claimed: that a hold has a reverse among the held states of the same context; that anything moves under
 a hold; hence no derivation of the rate from the declared inputs alone.
-/
import Definitions.Def_APF_B01_DeclaredInput

set_option autoImplicit false

universe uX uP uR uS

namespace APFPaper5.K3

theorem reversed_hold_reads_earlier {X : Type uX} {R : Type uR} (now : X → R) (D E theta : X → X)
    (hnow : ∀ x : X, now (theta x) = now x) (hrev : ∀ x : X, D (theta x) = theta (E x)) (x : X) :
    now (D (theta x)) = now (E x) := by
  rw [hrev, hnow]

theorem present_records_do_not_fix_state {X : Type uX} {R : Type uR} (now : X → R) (D E theta : X → X)
    (hnow : ∀ x : X, now (theta x) = now x) (hrev : ∀ x : X, D (theta x) = theta (E x))
    (hmotion : ∃ x : X, now (E x) ≠ now (D x)) :
    ∃ x y : X, now x = now y ∧ now (D x) ≠ now (D y) := by
  obtain ⟨x, hx⟩ := hmotion
  refine ⟨theta x, x, hnow x, ?_⟩
  rw [reversed_hold_reads_earlier now D E theta hnow hrev x]
  exact hx

theorem no_direction_if_present_records_fix_later {X : Type uX} {R : Type uR} (now : X → R)
    (D E theta : X → X) (hdet : ∀ x y : X, now x = now y → now (D x) = now (D y))
    (hnow : ∀ x : X, now (theta x) = now x) (hrev : ∀ x : X, D (theta x) = theta (E x)) (x : X) :
    now (D x) = now (E x) := by
  rw [← reversed_hold_reads_earlier now D E theta hnow hrev x]
  exact (hdet (theta x) x (hnow x)).symm

theorem no_direction_if_present_records_fix_state {X : Type uX} {R : Type uR} (now : X → R)
    (D E theta : X → X) (hinj : ∀ x y : X, now x = now y → x = y)
    (hnow : ∀ x : X, now (theta x) = now x) (hrev : ∀ x : X, D (theta x) = theta (E x)) (x : X) :
    now (D x) = now (E x) :=
  no_direction_if_present_records_fix_later now D E theta
    (fun x y h => by rw [hinj x y h]) hnow hrev x

end APFPaper5.K3

theorem APFB01.distinct_objects_of_later_record {X : Type uX} {Process : Type uP} {R : Type uR}
    (profile : X → Process → Prop) (later : X → R)
    (hfact : ∀ r : R, APFB01.Descends profile (fun x => later x = r)) (x y : X)
    (hne : later x ≠ later y) :
    APFB01.physicalClass profile x ≠ APFB01.physicalClass profile y := by
  obtain ⟨descended, hd⟩ := hfact (later x)
  intro hc
  have hx := (hd x).mp rfl
  rw [hc] at hx
  exact hne ((hd y).mpr hx).symm

theorem APFB01.present_records_do_not_fix_object {X : Type uX} {Process : Type uP} {R : Type uR} {S : Type uS}
    (profile : X → Process → Prop) (now : X → S) (later : X → R)
    (hfact : ∀ r : R, APFB01.Descends profile (fun x => later x = r)) (x y : X)
    (hnow : now x = now y) (hne : later x ≠ later y) :
    ¬ ∃ f : S → APFB01.PhysicalState profile,
      ∀ z : X, APFB01.physicalClass profile z = f (now z) := by
  rintro ⟨f, hf⟩
  exact APFB01.distinct_objects_of_later_record profile later hfact x y hne
    (by rw [hf x, hf y, hnow])

theorem APFB01.rate_is_held_of_reversal {X : Type uX} {Process : Type uP} {R : Type uR}
    (profile : X → Process → Prop) (now : X → R) (D E theta : X → X)
    (hfact : ∀ r : R, APFB01.Descends profile (fun x => now (D x) = r))
    (hnow : ∀ x : X, now (theta x) = now x) (hrev : ∀ x : X, D (theta x) = theta (E x))
    (hmotion : ∃ x : X, now (E x) ≠ now (D x)) :
    ∃ x y : X, now x = now y ∧
      APFB01.physicalClass profile x ≠ APFB01.physicalClass profile y := by
  obtain ⟨x, y, hxy, hne⟩ :=
    APFPaper5.K3.present_records_do_not_fix_state now D E theta hnow hrev hmotion
  exact ⟨x, y, hxy,
    APFB01.distinct_objects_of_later_record profile (fun z => now (D z)) hfact x y hne⟩


universe apfNative_uX apfNative_uP apfNative_uR
theorem solution :
∀ {X : Type apfNative_uX} {Process : Type apfNative_uP} {R : Type apfNative_uR} (profile : X → Process → Prop)
  (later : X → R)
  (hfact :
    ∀ (r : R),
      @APFB01.Descends.{apfNative_uX, apfNative_uP} X Process profile fun (x : X) =>
        @Eq.{apfNative_uR + 1} R (later x) r)
  (x y : X) (hne : @Ne.{apfNative_uR + 1} R (later x) (later y)),
  @Ne.{apfNative_uX + 1} (@APFB01.PhysicalState.{apfNative_uX, apfNative_uP} X Process profile)
    (@APFB01.physicalClass.{apfNative_uX, apfNative_uP} X Process profile x)
    (@APFB01.physicalClass.{apfNative_uX, apfNative_uP} X Process profile y) := by
  exact @APFB01.distinct_objects_of_later_record
