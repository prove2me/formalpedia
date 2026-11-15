-- Prove2me | solution 1 for APFPaper5.K3.reading_after_map_needs_own_record
-- status  : ACCEPTED   (prove)
-- author  : @FiniteUniverse
-- created : 2026-11-14T08:16:27.095782+00:00
-- url     : https://prove2.me/submissions/b56458d7-0df6-46e8-978d-dc8e62dee5a6

import Theorems.Thm_APFPaper5_K3_cross_norm
import Theorems.Thm_APFPaper5_K3_rateFlip_preserves_plain_records
/-
APF Foundation Ledger — theorem node DRAFT (session EthanBrooke-01WrrBvu, 2026-11-13; not gated, not reviewed)
name: APFPaper5_K3_economy_instances
title: What needs a record of its own on the carrier: a reading after a map that shows the common turn, a reading of the mirror sheet, and the rate
inputs_revision: 2026-10-04.1
mathlib_rev: 0df444a360eaa60ab8c11dca51a86af692955474
source: Thm_APFPaper5_K1_record_model_bridge; the author's direction of 2026-11-13 ("Let's get this").
consumes_inputs: none. CONDITIONAL INSTANCES: a record model over the held states of the supplied models,
 with hsound (the records a distinction needs fix its verdict).
statement: (reading_after_map_needs_own_record) if every record held for S is fixed by the continuation
 profile, and the common turn is seen after T, some reading of the continuation profile after T needs a
 record that S does not hold.
 (number_extreme_without_rate, number_between_needs_rate) with no rate, the number between the two
 components is fixed by their two costs up to sign; a number strictly between needs a rate.
 (rate_needs_own_record) if every record held for S is fixed by the two costs and the plain recombination,
 some reading of the quarter-turned recombination needs a record that S does not hold.
 (APFPaper5.K4.mirror_reading_needs_own_record) if every record held for S is fixed by the first sheet, some
 reading of the two-sheet record book needs a record that S does not hold.
reading: economy removes what the required records do not need. That covers the map that shows the common
 turn and the mirror sheet. It covers the rate as well: the rate is carried only if a record after a turn
 of one component is among those required.
not_claimed: which records are required at an interface; hsound; any K.
-/
import Definitions.Def_APFPaper5_K4_TwoSheets
import Theorems.Thm_APFPaper5_K1_needs_own_record_of_separates
import Theorems.Thm_APFPaper5_K1_recordModel_supportNovel_of_needs_own_record
import Theorems.Thm_APFPaper5_K1_recordModel_economy_of_separation
import Theorems.Thm_APFPaper5_K3_firstOrder_of_two_directions
import Theorems.Thm_APFPaper5_K3_two_directions_needed
import Theorems.Thm_APFPaper5_K3_seen_common_turn_splits_an_object
import Theorems.Thm_APFPaper5_K4_two_sheets_separate_more
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

set_option autoImplicit false

namespace APFPaper5.K3

open APFPaper5.K1

universe u v
variable {ι : Type u} {Rec : Type v} [DecidableEq Rec]

theorem reading_after_map_needs_own_record {Val : Type*} (fam : ι → Finset Rec)
    (reads : Rec → Held2 → Val) (verdict : ι → Held2 → Prop) (S : Finset ι)
    (hS : ∀ r ∈ S.biUnion fam, ∀ x y : Held2, plainAfterTurn x = plainAfterTurn y →
      reads r x = reads r y)
    (T : Held2 → Held2) (hseen : ¬ CommonTurnUnseenAfter T)
    (dAfter : (ℝ × ℝ × (ℝ × ℝ × ℝ) → Prop) → ι)
    (hverdict : ∀ (Q : ℝ × ℝ × (ℝ × ℝ × ℝ) → Prop) (h : Held2),
      verdict (dAfter Q) h ↔ plainAfterTurn (T h) = Q)
    (hsound : ∀ (Q : ℝ × ℝ × (ℝ × ℝ × ℝ) → Prop) (x y : Held2),
      (∀ r ∈ fam (dAfter Q), reads r x = reads r y) →
        (verdict (dAfter Q) x ↔ verdict (dAfter Q) y)) :
    ∃ Q : ℝ × ℝ × (ℝ × ℝ × ℝ) → Prop, ¬ fam (dAfter Q) ⊆ S.biUnion fam := by
  obtain ⟨x, y, hxy, hne⟩ := seen_common_turn_splits_an_object T hseen
  refine ⟨plainAfterTurn (T x), needs_own_record_of_separates fam reads verdict S _ (hsound _) x y
    (fun r hr => hS r hr x y hxy) ?_⟩
  rw [hverdict, hverdict]
  intro hiff
  exact hne (hiff.mp rfl).symm

theorem number_extreme_without_rate (h : Held2) (hreal : crossIm h = 0) :
    crossRe h * crossRe h = recA h * recB h := by
  have e := cross_norm h
  rw [hreal] at e
  linarith

theorem number_between_needs_rate (h : Held2) (hlt : crossRe h * crossRe h < recA h * recB h) :
    crossIm h ≠ 0 := by
  intro h0
  have e := number_extreme_without_rate h h0
  linarith

theorem rate_needs_own_record {Val : Type*} (fam : ι → Finset Rec)
    (reads : Rec → Held2 → Val) (verdict : ι → Held2 → Prop) (S : Finset ι)
    (hS : ∀ r ∈ S.biUnion fam, ∀ x y : Held2, recA x = recA y → recB x = recB y →
      recSum x = recSum y → reads r x = reads r y)
    (dQuarter : ℝ → ι) (hverdict : ∀ (t : ℝ) (h : Held2), verdict (dQuarter t) h ↔ recQuarter h = t)
    (hsound : ∀ (t : ℝ) (x y : Held2), (∀ r ∈ fam (dQuarter t), reads r x = reads r y) →
      (verdict (dQuarter t) x ↔ verdict (dQuarter t) y)) :
    ∃ t : ℝ, ¬ fam (dQuarter t) ⊆ S.biUnion fam := by
  obtain ⟨hA, hB, hSum⟩ := rateFlip_preserves_plain_records ⟨1, 0, 0, 1⟩
  obtain ⟨h0, h4⟩ := rateFlip_seen_by_quarter_record
  refine ⟨0, needs_own_record_of_separates fam reads verdict S _ (hsound 0) ⟨1, 0, 0, 1⟩
    (rateFlip ⟨1, 0, 0, 1⟩) (fun r hr => hS r hr _ _ hA.symm hB.symm hSum.symm) ?_⟩
  rw [hverdict, hverdict, h4]
  intro hiff
  have := hiff.mp h0
  norm_num at this

end APFPaper5.K3

namespace APFPaper5.K4

open APFPaper5.K1 APFPaper5.K3

universe u v
variable {ι : Type u} {Rec : Type v} [DecidableEq Rec]

theorem mirror_reading_needs_own_record {Val : Type*} (fam : ι → Finset Rec)
    (reads : Rec → Sheets → Val) (verdict : ι → Sheets → Prop) (S : Finset ι)
    (hS : ∀ r ∈ S.biUnion fam, ∀ p q : Sheets, p.sync = q.sync → reads r p = reads r q)
    (dReading : RecordWeights → RecordWeights → ℝ → ι)
    (hverdict : ∀ (w w' : RecordWeights) (t : ℝ) (p : Sheets),
      verdict (dReading w w' t) p ↔ sheetsReading w w' p = t)
    (hsound : ∀ (w w' : RecordWeights) (t : ℝ) (p q : Sheets),
      (∀ r ∈ fam (dReading w w' t), reads r p = reads r q) →
        (verdict (dReading w w' t) p ↔ verdict (dReading w w' t) q)) :
    ∃ (w w' : RecordWeights) (t : ℝ), ¬ fam (dReading w w' t) ⊆ S.biUnion fam := by
  obtain ⟨p, q, hsync, w, w', hne⟩ := two_sheets_separate_more
  refine ⟨w, w', sheetsReading w w' p, needs_own_record_of_separates fam reads verdict S _
    (hsound w w' _) p q (fun r hr => hS r hr p q hsync) ?_⟩
  rw [hverdict, hverdict]
  intro hiff
  exact hne (hiff.mp rfl).symm

end APFPaper5.K4


universe apfNative_u apfNative_v apfNative_u_1
theorem solution :
∀ {ι : Type apfNative_u} {Rec : Type apfNative_v} [inst : DecidableEq.{apfNative_v + 1} Rec] {Val : Type apfNative_u_1}
  (fam : ι → Finset.{apfNative_v} Rec) (reads : Rec → APFPaper5.K3.Held2 → Val)
  (verdict : ι → APFPaper5.K3.Held2 → Prop) (S : Finset.{apfNative_u} ι)
  (hS :
    ∀ (r : Rec),
      @Membership.mem.{apfNative_v, apfNative_v} Rec (Finset.{apfNative_v} Rec)
          (@SetLike.instMembership.{apfNative_v, apfNative_v} (Finset.{apfNative_v} Rec) Rec
            (@Finset.instSetLike.{apfNative_v} Rec))
          (@Finset.biUnion.{apfNative_u, apfNative_v} ι Rec inst S fam) r →
        ∀ (x y : APFPaper5.K3.Held2),
          @Eq.{1} ((x : Prod.{0, 0} Real (Prod.{0, 0} Real (Prod.{0, 0} Real (Prod.{0, 0} Real Real)))) → Prop)
              (APFPaper5.K3.plainAfterTurn x) (APFPaper5.K3.plainAfterTurn y) →
            @Eq.{apfNative_u_1 + 1} Val (reads r x) (reads r y))
  (T : APFPaper5.K3.Held2 → APFPaper5.K3.Held2) (hseen : Not (APFPaper5.K3.CommonTurnUnseenAfter T))
  (dAfter : (Prod.{0, 0} Real (Prod.{0, 0} Real (Prod.{0, 0} Real (Prod.{0, 0} Real Real))) → Prop) → ι)
  (hverdict :
    ∀ (Q : Prod.{0, 0} Real (Prod.{0, 0} Real (Prod.{0, 0} Real (Prod.{0, 0} Real Real))) → Prop)
      (h : APFPaper5.K3.Held2),
      Iff (verdict (dAfter Q) h)
        (@Eq.{1} ((x : Prod.{0, 0} Real (Prod.{0, 0} Real (Prod.{0, 0} Real (Prod.{0, 0} Real Real)))) → Prop)
          (APFPaper5.K3.plainAfterTurn (T h)) Q))
  (hsound :
    ∀ (Q : Prod.{0, 0} Real (Prod.{0, 0} Real (Prod.{0, 0} Real (Prod.{0, 0} Real Real))) → Prop)
      (x y : APFPaper5.K3.Held2),
      (∀ (r : Rec),
          @Membership.mem.{apfNative_v, apfNative_v} Rec (Finset.{apfNative_v} Rec)
              (@SetLike.instMembership.{apfNative_v, apfNative_v} (Finset.{apfNative_v} Rec) Rec
                (@Finset.instSetLike.{apfNative_v} Rec))
              (fam (dAfter Q)) r →
            @Eq.{apfNative_u_1 + 1} Val (reads r x) (reads r y)) →
        Iff (verdict (dAfter Q) x) (verdict (dAfter Q) y)),
  @Exists.{1} (Prod.{0, 0} Real (Prod.{0, 0} Real (Prod.{0, 0} Real (Prod.{0, 0} Real Real))) → Prop)
    fun (Q : Prod.{0, 0} Real (Prod.{0, 0} Real (Prod.{0, 0} Real (Prod.{0, 0} Real Real))) → Prop) =>
    Not
      (@LE.le.{apfNative_v} (Finset.{apfNative_v} Rec)
        (@Preorder.toLE.{apfNative_v} (Finset.{apfNative_v} Rec)
          (@PartialOrder.toPreorder.{apfNative_v} (Finset.{apfNative_v} Rec)
            (@Finset.instPartialOrder.{apfNative_v} Rec)))
        (fam (dAfter Q)) (@Finset.biUnion.{apfNative_u, apfNative_v} ι Rec inst S fam)) := by
  exact @APFPaper5.K3.reading_after_map_needs_own_record
