-- Prove2me | solution 1 for APFPaper5.K1.orientationForm_zero_of_symm
-- status  : ACCEPTED   (prove)
-- author  : @FiniteUniverse
-- created : 2026-11-16T17:49:43.5042+00:00
-- url     : https://prove2.me/submissions/93f92077-72c5-437a-a491-43330083a4c4

import Definitions.Def_APFPaper5_K1_identity_exchange_Vocabulary
/-
APF Foundation Ledger — theorem node DRAFT (Claude seat, session EthanBrooke-01WrrBvv, 2026-11-15; not
 gated, not reviewed, not released, not built in the ledger repo)
name: APFPaper5_K1_identity_exchange
title: A recorded distinction is the same thing held and read, so every typed hypothesis of K1 holds for the ruled score of a counted family, with the identity as exchange and a zero orientation part
inputs_revision: 2026-11-14.1
mathlib_rev: 0df444a360eaa60ab8c11dca51a86af692955474
source: the author, 2026-11-15 09:39 HST: "It is the same", in answer to this seat's question "is a recorded
 distinction the same thing held and read, so that the exchange of the two roles is the identity?"
 (TEE_UP_K1_ordered_score_2026-11-15, option A). RULING_recorded_distinction_held_and_read_2026-11-15.
 Paper 5 Supplement v7.33:312-334 (the scalar ledger does not determine the ordered score), 353-382 (the
 ordered-score theorem; the alternating part "may be nonzero"), 3038-3041 (K1), 70 and 3101-3104 (the ledger
 does not depend on Held orientation). The builder seat's Def_APFPaper5_K1_OrderedScore (the typed
 hypotheses), Thm_APFPaper5_K1_bilinearization and Thm_APFPaper5_K1_record_book_table.
standing:
 - The identification is the author's ruling. It is carried here in two places and nowhere else: one
   vector, markClass, is the class of a distinction held and of the same distinction read; and the exchange
   of the two roles is the identity map.
 - The score is the author's ruling B and "counted" is the author's ruling A, as typed in
   Def_APFPaper5_K1_SourcePartyScore.
consumes_inputs: none. No declared input is used as a hypothesis and none is proved.
theorems:
 - (tableForm_markClass, table_linearizes) the form of a table reproduces the table on the classes of the
   marks: the first typed hypothesis of K1.
 - (nondegenerate_of_faithful_identity) with the identity as exchange, a faithful diagonal gives a
   nondegenerate pairing, so there is no radical to quotient by.
 - (orientationForm_zero_of_symm, ledgerForm_eq_of_symm) for a symmetric table the orientation part is zero
   and the ledger form is the form itself.
 - (sourcePartyScore_symm) the ruled score of two distinctions is the same in either order.
 - (source_counted_family_meets_all_of_K1_with_identity_exchange) all of the above for the ruled score of a
   counted family on any source data of the declared forms, for any cost of records that is never negative.
not claimed:
 - An ordered score with a nonzero orientation part. Under the ruling K1 hands K3 no orientation.
 - That the score is separately additive under a coarse-graining of classes, or the construction of the
   classes from a score table by linearization. The classes here are the combinations of the counted
   distinctions, taken as given.
 - That a region's distinctions are counted, or what a record costs.
 - Anything about a hold, a turn, reversal or K3. No lane. No claim that the transfer is forced, that the
   carrier gap is closed or narrowed, or that Born is derived.
axioms: within propext, Classical.choice, Quot.sound. No sorry.
-/
import Theorems.Thm_APFPaper5_K1_sourceNeeds_mono
import Theorems.Thm_APFPaper5_K1_source_own_record_of_alone_not_rest
import Theorems.Thm_APFPaper5_K1_source_party_score_meets_K1
import Theorems.Thm_APFPaper5_K1_source_counted_family_meets_K1
import Theorems.Thm_APFPaper5_K1_leastBill_nonneg
import Theorems.Thm_APFPaper5_K1_leastBill_le_bill
import Theorems.Thm_APFPaper5_K1_le_leastBill
import Theorems.Thm_APFPaper5_K1_leastBill_pos_iff
import Theorems.Thm_APFPaper5_K1_source_counted_family_meets_K1_leastBill
import Theorems.Thm_APFPaper5_K1_familyNeeds_eq_sourceNeeds
import Theorems.Thm_APFPaper5_K1_cost_le_leastBill
import Theorems.Thm_APFPaper5_K1_leastBill_eq_cost_of_kept_alone
import Theorems.Thm_APFPaper5_K1_ledgerPartyScore_eq_source
import Theorems.Thm_APFPaper5_K1_counted_iff_sourceCounted
import Theorems.Thm_APFPaper5_K1_sourceCounted_leastBill_of_counted
import Theorems.Thm_APFPaper5_K1_PaidPair_source_counted_pair_meets_K1
import Theorems.Thm_APFPaper5_K1_exchanged_eq_ledger_add_orientation
import Theorems.Thm_APFPaper5_K1_ledgerForm_posDef
import Theorems.Thm_APFPaper5_K1_diagonal_parallelogram
import Theorems.Thm_APFPaper5_K1_atomTable_symm
import Theorems.Thm_APFPaper5_K1_atomTable_form
import Theorems.Thm_APFPaper5_K1_atomTable_nonneg
import Theorems.Thm_APFPaper5_K1_record_book_table_satisfies_K1

set_option autoImplicit false

open APFPaper1 APFPaper1.Source

namespace APFPaper5.K1

section Table

variable {ι : Type*} [Fintype ι] [DecidableEq ι]



/-- The form of a table, on the classes of two marks, is the table's entry. -/
theorem tableForm_markClass_p2mProof (G : ι → ι → ℝ) (i j : ι) :
    tableForm G (markClass i) (markClass j) = G i j := by
  unfold tableForm markClass
  rw [Finset.sum_eq_single i]
  · rw [Finset.sum_eq_single j]
    · simp
    · intro l _ hl
      simp [hl]
    · intro h
      exact absurd (Finset.mem_univ j) h
  · intro k _ hk
    simp [hk]
  · intro h
    exact absurd (Finset.mem_univ i) h

/-- K1's first clause in the builder seat's typing: the form of a table reproduces the table on the
classes of the marks. -/
theorem table_linearizes_p2mProof (G : ι → ι → ℝ) :
    Linearizes (VP := ι → ℝ) (VE := ι → ℝ) (fun e p : ι => G e p) markClass markClass
      (tableForm G) :=
  fun e p => tableForm_markClass_p2mProof G e p

omit [DecidableEq ι] in
/-- With the identity as exchange, a faithful diagonal leaves no combination paired to zero with
everything. -/
theorem nondegenerate_of_faithful_identity_p2mProof (G : ι → ι → ℝ)
    (h : FaithfulNonnegDiagonal (tableForm G) (LinearEquiv.refl ℝ (ι → ℝ))) :
    IsNondegenerate (VP := ι → ℝ) (VE := ι → ℝ) (tableForm G) :=
  ⟨fun e he => h.2 e (he e), fun p hp => h.2 p (hp p)⟩

omit [DecidableEq ι] in
/-- With the identity as exchange, the orientation part of a symmetric table is zero. -/
theorem orientationForm_zero_of_symm_p2mProof (G : ι → ι → ℝ) (hG : ∀ i j, G i j = G j i) (x y : ι → ℝ) :
    orientationForm (tableForm G) (LinearEquiv.refl ℝ (ι → ℝ)) x y = 0 := by
  unfold orientationForm
  have h : tableForm G ((LinearEquiv.refl ℝ (ι → ℝ)) x) y =
      tableForm G ((LinearEquiv.refl ℝ (ι → ℝ)) y) x := tableForm_symm G hG x y
  rw [h]
  ring

omit [DecidableEq ι] in
/-- With the identity as exchange, the ledger form of a symmetric table is the table's own form. -/
theorem ledgerForm_eq_of_symm_p2mProof (G : ι → ι → ℝ) (hG : ∀ i j, G i j = G j i) (x y : ι → ℝ) :
    ledgerForm (tableForm G) (LinearEquiv.refl ℝ (ι → ℝ)) x y = tableForm G x y := by
  unfold ledgerForm
  have h : tableForm G ((LinearEquiv.refl ℝ (ι → ℝ)) y) x =
      tableForm G ((LinearEquiv.refl ℝ (ι → ℝ)) x) y := tableForm_symm G hG y x
  rw [h]
  show (tableForm G x y + tableForm G x y) / 2 = tableForm G x y
  ring

end Table

section Source

variable {D P R Record : Type*} {ι : Type*} [Fintype ι] [DecidableEq ι] [DecidableEq D]
  [Fintype Record]

/-- The score of two distinctions is the same in either order. -/
theorem sourcePartyScore_symm_p2mProof (w : Record → ℝ) (maintained : P → Set Record)
    (sufficient : P → Set Record → D → Prop) (usesToRealize : P → D → Set Record → Prop)
    (dist : ι → D) (i j : ι) :
    sourcePartyScore w maintained sufficient usesToRealize dist i j =
      sourcePartyScore w maintained sufficient usesToRealize dist j i :=
  atomTable_symm w (partyMark (sourceKeeps maintained sufficient usesToRealize dist)) i j

/-- If a distinction recorded is the same thing held and read, so that the exchange of the two roles is
the identity, every typed hypothesis of K1 holds for the ruled score of a counted family on source data
of the declared forms: the form reproduces the score, is bilinear and nondegenerate, and has a faithful
nonnegative diagonal. Its orientation part is zero and its ledger form is the form itself. -/
theorem source_counted_family_meets_all_of_K1_with_identity_exchange_p2mProof (w : Record → ℝ)
    (hw : ∀ a, 0 ≤ w a) (wholeResource : P → R) (calibration : R → NNReal)
    (maintained : P → Set Record) (sufficient : P → Set Record → D → Prop)
    (usesToRealize : P → D → Set Record → Prop) (tested : D → Prop) (C : ℝ) (dist : ι → D)
    (h : SourceCounted w wholeResource calibration maintained sufficient usesToRealize tested C
      dist) :
    Linearizes (VP := ι → ℝ) (VE := ι → ℝ)
        (fun e p : ι => sourcePartyScore w maintained sufficient usesToRealize dist e p)
        markClass markClass
        (tableForm (sourcePartyScore w maintained sufficient usesToRealize dist)) ∧
      IsBilinear (VP := ι → ℝ) (VE := ι → ℝ)
        (tableForm (sourcePartyScore w maintained sufficient usesToRealize dist)) ∧
      IsNondegenerate (VP := ι → ℝ) (VE := ι → ℝ)
        (tableForm (sourcePartyScore w maintained sufficient usesToRealize dist)) ∧
      FaithfulNonnegDiagonal
        (tableForm (sourcePartyScore w maintained sufficient usesToRealize dist))
        (LinearEquiv.refl ℝ (ι → ℝ)) ∧
      (∀ x y : ι → ℝ,
        orientationForm (tableForm (sourcePartyScore w maintained sufficient usesToRealize dist))
          (LinearEquiv.refl ℝ (ι → ℝ)) x y = 0) ∧
      ∀ x y : ι → ℝ,
        ledgerForm (tableForm (sourcePartyScore w maintained sufficient usesToRealize dist))
          (LinearEquiv.refl ℝ (ι → ℝ)) x y =
        tableForm (sourcePartyScore w maintained sufficient usesToRealize dist) x y := by
  have hK := source_counted_family_meets_K1 w hw wholeResource calibration maintained sufficient
    usesToRealize tested C dist h
  have hsymm := sourcePartyScore_symm_p2mProof w maintained sufficient usesToRealize dist
  exact ⟨table_linearizes_p2mProof _, hK.1, nondegenerate_of_faithful_identity_p2mProof _ hK.2, hK.2,
    orientationForm_zero_of_symm_p2mProof _ hsymm, ledgerForm_eq_of_symm_p2mProof _ hsymm⟩

end Source

end APFPaper5.K1


universe apfNative_u_1
theorem solution :
∀ {ι : Type apfNative_u_1} [inst : Fintype.{apfNative_u_1} ι] (G : ι → ι → Real)
  (hG : ∀ (i j : ι), @Eq.{1} Real (G i j) (G j i)) (x y : ι → Real),
  @Eq.{1} Real
    (@APFPaper5.K1.orientationForm.{apfNative_u_1, apfNative_u_1} (ι → Real) (ι → Real)
      (@Pi.addCommGroup.{apfNative_u_1, 0} ι (fun (a : ι) => Real) fun (i : ι) => Real.instAddCommGroup)
      (@Pi.Function.module.{apfNative_u_1, 0, 0} ι Real Real Real.semiring Real.instAddCommMonoid
        (@Semiring.toModule.{0} Real Real.semiring))
      (@Pi.addCommGroup.{apfNative_u_1, 0} ι (fun (a : ι) => Real) fun (i : ι) => Real.instAddCommGroup)
      (@Pi.Function.module.{apfNative_u_1, 0, 0} ι Real Real Real.semiring Real.instAddCommMonoid
        (@Semiring.toModule.{0} Real Real.semiring))
      (@APFPaper5.K1.tableForm.{apfNative_u_1} ι inst G)
      (@LinearEquiv.refl.{0, apfNative_u_1} Real (ι → Real) Real.semiring
        (@Pi.addCommMonoid.{apfNative_u_1, 0} ι (fun (a : ι) => Real) fun (i : ι) => Real.instAddCommMonoid)
        (@Pi.Function.module.{apfNative_u_1, 0, 0} ι Real Real Real.semiring Real.instAddCommMonoid
          (@Semiring.toModule.{0} Real Real.semiring)))
      x y)
    (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) := by
  exact @APFPaper5.K1.orientationForm_zero_of_symm_p2mProof
