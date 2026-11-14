-- Prove2me | solution 1 for APFB05.relation_strictly_dearer
-- status  : ACCEPTED   (prove)
-- author  : @FiniteUniverse
-- created : 2026-11-13T17:15:00.556827+00:00
-- url     : https://prove2.me/submissions/610db48f-c8b4-4e6d-a5a0-f75a0e710dc8

/-
APF Foundation Ledger — theorem node DRAFT (session EthanBrooke-01WrrBvu, 2026-11-12; not gated, not reviewed)
name: APFB05_no_free_rider
title: A relation that needs a new record is never carried by the cheapest admissible family unless demanded
inputs_revision: 2026-10-04.1
mathlib_rev: 0df444a360eaa60ab8c11dca51a86af692955474
source: FOUNDATION_INPUTS B05 (marginal floor) and B07a (A2, realization at the admissible cost minimum).
 Author ruling of 2026-11-12 on the meaning of "irreducibly joint" (the relation is a tested task needing a
 new record).
consumes_inputs: B05 as the hypothesis hB05. B07a in the form hA2, which is the archive predicate
 APFPaper1.Foundation.A2Selection candidates (familyCost ...) realized written out: realized is a candidate
 and no candidate is cheaper. FOUNDATION_INPUTS records that A2's Lean form is NOT yet certified against its
 source, so this theorem's use of A2 carries that same caveat. First theorem on the ledger to consume A2.
statement: (relation_strictly_dearer) under B05, a tested, support-novel r with S and insert r S both
 admissible makes insert r S strictly dearer than S. (no_free_rider) if moreover S is among the candidate
 families and the realized family is a cheapest candidate, the realized family is not insert r S.
not_claimed: which family is realized; that the realized family is unique (that would need B07b); any
 process by which a dearer family is replaced. A2's scope note says it locates the realized configuration and
 posits no search or optimization process.
-/
import Theorems.Thm_APFPaper1_Source_not_supportNovel_of_carried
import Theorems.Thm_APFB05_relation_task_third_charge
import Theorems.Thm_APFB05_mark_mark_relation_three_floors
import Theorems.Thm_APFB05_relation_excluded_in_window

set_option autoImplicit false
open APFPaper1.Source

section
variable {Context : Type*} {D P R Record : Context → Type*} [∀ g, DecidableEq (D g)]
  (wholeResource : (g : Context) → P g → R g)
  (calibration : (g : Context) → R g → NNReal)
  (maintained : (g : Context) → P g → Set (Record g))
  (sufficient : (g : Context) → P g → Set (Record g) → D g → Prop)
  (usesToRealize : (g : Context) → P g → D g → Set (Record g) → Prop)
  (tested : (g : Context) → D g → Prop)
  (C epsilon : Context → ℝ)

theorem APFB05.relation_strictly_dearer
    (hB05 : APFB05.MarginalFloor wholeResource calibration maintained sufficient usesToRealize
      tested C epsilon)
    (g : Context) (S : Finset (D g)) (r : D g)
    (htested : tested g r)
    (hS : familyAdmissible (wholeResource g) (calibration g) (maintained g)
      (sufficient g) (usesToRealize g) (C g) S)
    (hSr : familyAdmissible (wholeResource g) (calibration g) (maintained g)
      (sufficient g) (usesToRealize g) (C g) (insert r S))
    (hnew : supportNovel (wholeResource g) (calibration g) (maintained g)
      (sufficient g) (usesToRealize g) S r) :
    familyCost (wholeResource g) (calibration g) (maintained g)
        (sufficient g) (usesToRealize g) S <
      familyCost (wholeResource g) (calibration g) (maintained g)
        (sufficient g) (usesToRealize g) (insert r S) := by
  have h := APFB05.relation_task_third_charge wholeResource calibration maintained sufficient
    usesToRealize tested C epsilon hB05 g S r htested hS hSr hnew
  have heps := (hB05 g).1
  linarith

theorem APFB05.no_free_rider
    (hB05 : APFB05.MarginalFloor wholeResource calibration maintained sufficient usesToRealize
      tested C epsilon)
    (g : Context) (S : Finset (D g)) (r : D g)
    (htested : tested g r)
    (hS : familyAdmissible (wholeResource g) (calibration g) (maintained g)
      (sufficient g) (usesToRealize g) (C g) S)
    (hSr : familyAdmissible (wholeResource g) (calibration g) (maintained g)
      (sufficient g) (usesToRealize g) (C g) (insert r S))
    (hnew : supportNovel (wholeResource g) (calibration g) (maintained g)
      (sufficient g) (usesToRealize g) S r)
    (candidates : Set (Finset (D g))) (realized : Finset (D g))
    (hScand : S ∈ candidates)
    (hA2 : realized ∈ candidates ∧ ∀ T ∈ candidates,
      familyCost (wholeResource g) (calibration g) (maintained g)
          (sufficient g) (usesToRealize g) realized ≤
        familyCost (wholeResource g) (calibration g) (maintained g)
          (sufficient g) (usesToRealize g) T) :
    realized ≠ insert r S := by
  intro hreal
  have hlt := APFB05.relation_strictly_dearer wholeResource calibration maintained sufficient
    usesToRealize tested C epsilon hB05 g S r htested hS hSr hnew
  have hmin := hA2.2 S hScand
  rw [hreal] at hmin
  linarith

end


universe apfNative_u_1 apfNative_u_2 apfNative_u_3 apfNative_u_4 apfNative_u_5
theorem solution :
∀ {Context : Type apfNative_u_1} {D : Context → Type apfNative_u_2} {P : Context → Type apfNative_u_3}
  {R : Context → Type apfNative_u_4} {Record : Context → Type apfNative_u_5}
  [inst : (g : Context) → DecidableEq.{apfNative_u_2 + 1} (D g)] (wholeResource : (g : Context) → P g → R g)
  (calibration : (g : Context) → R g → NNReal) (maintained : (g : Context) → P g → Set.{apfNative_u_5} (Record g))
  (sufficient : (g : Context) → P g → Set.{apfNative_u_5} (Record g) → D g → Prop)
  (usesToRealize : (g : Context) → P g → D g → Set.{apfNative_u_5} (Record g) → Prop)
  (tested : (g : Context) → D g → Prop) (C epsilon : Context → Real)
  (hB05 :
    @APFB05.MarginalFloor.{apfNative_u_1, apfNative_u_2, apfNative_u_3, apfNative_u_4, apfNative_u_5} Context D P R
      Record inst wholeResource calibration maintained sufficient usesToRealize tested C epsilon)
  (g : Context) (S : Finset.{apfNative_u_2} (D g)) (r : D g) (htested : tested g r)
  (hS :
    @APFPaper1.Source.familyAdmissible.{apfNative_u_2, apfNative_u_3, apfNative_u_4, apfNative_u_5} (D g) (P g) (R g)
      (Record g) (wholeResource g) (calibration g) (maintained g) (sufficient g) (usesToRealize g) (C g) S)
  (hSr :
    @APFPaper1.Source.familyAdmissible.{apfNative_u_2, apfNative_u_3, apfNative_u_4, apfNative_u_5} (D g) (P g) (R g)
      (Record g) (wholeResource g) (calibration g) (maintained g) (sufficient g) (usesToRealize g) (C g)
      (@Insert.insert.{apfNative_u_2, apfNative_u_2} (D g) (Finset.{apfNative_u_2} (D g))
        (@Finset.instInsert.{apfNative_u_2} (D g) (inst g)) r S))
  (hnew :
    @APFPaper1.Source.supportNovel.{apfNative_u_2, apfNative_u_3, apfNative_u_4, apfNative_u_5} (D g) (P g) (R g)
      (Record g) (wholeResource g) (calibration g) (maintained g) (sufficient g) (usesToRealize g) S r),
  @LT.lt.{0} Real Real.instLT
    (@APFPaper1.Source.familyCost.{apfNative_u_2, apfNative_u_3, apfNative_u_4, apfNative_u_5} (D g) (P g) (R g)
      (Record g) (wholeResource g) (calibration g) (maintained g) (sufficient g) (usesToRealize g) S)
    (@APFPaper1.Source.familyCost.{apfNative_u_2, apfNative_u_3, apfNative_u_4, apfNative_u_5} (D g) (P g) (R g)
      (Record g) (wholeResource g) (calibration g) (maintained g) (sufficient g) (usesToRealize g)
      (@Insert.insert.{apfNative_u_2, apfNative_u_2} (D g) (Finset.{apfNative_u_2} (D g))
        (@Finset.instInsert.{apfNative_u_2} (D g) (inst g)) r S)) := by
  exact @APFB05.relation_strictly_dearer
