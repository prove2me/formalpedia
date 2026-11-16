-- Prove2me | solution 1 for APFPaper5.K1.Book.book_meets_hypotheses
-- status  : ACCEPTED   (prove)
-- author  : @FiniteUniverse
-- created : 2026-11-16T00:06:59.673+00:00
-- url     : https://prove2.me/submissions/297b4dfd-9887-4b7a-b9f1-3d762a729f0e

import Definitions.Def_APFPaper5_K1_ledger_bridge_Vocabulary
/-
APF Foundation Ledger — theorem node DRAFT (Claude seat, session EthanBrooke-01WrrBvv, 2026-11-14; not
 gated, not reviewed, not released, not built in the ledger repo)
name: APFPaper5_K1_ledger_bridge
title: On finite restricted record-ledger data, guarded B05, availability and a counted-family hypothesis imply a bilinear score table with a faithful nonnegative diagonal
inputs_revision: 2026-11-14.1
mathlib_rev: 0df444a360eaa60ab8c11dca51a86af692955474
source: the author's "Go" of 2026-11-14 20:09 HST (restate the bridge over the ledger and needs).
 Def_APFPaper1_RecordLedger, Def_APFPaper5_K1_LedgerScore, Thm_APFPaper1_RecordLedger_laws,
 Thm_APFPaper5_K1_interface_bridge and _families (this seat). Declared input B05 in its declared form
 APFB05.MarginalFloor (Def_APF_B05_DeclaredInput_r2). Builder seat: recordModel_satisfies_K1,
 APFB05.weighted_record_model_satisfies_floor, recordModel_supportNovel_of_needs_own_record.
standing: THEOREMS ON RESTRICTED RECORD-LEDGER DATA. The K1 statement supplies finite Record and
 finite index types, hcounted (admissibility, testing and novelty over the other indices), guarded B05
 read over the ledger's own data, and LedgerAvailable. The additive bill is built into RecordLedger;
 defining that representation does not establish it for the original physical source. Defining
 LedgerCounted likewise does not establish that a family meets its obligations. LedgerAvailable is
 a hypothesis, not an installed input. Reading the eight inputs over this restricted representation
 is not installed. These are conditional reference theorems, not Foundation consequences.
what this file says:
 1. ledger_familyCost_eq_needs, ledger_score_eq_shared_needs.
 2. ledger_counted_family_satisfies_K1.
 3. Book: a ledger with one record all distinctions need and one private record each. book_needsFin (its
    needs are what was put in), book_meets_hypotheses (B05, availability and "counted" hold together on
    it). So the K1 statement is not empty.
what this file does NOT say: that the role exchange is anything but the identity; anything about
 orientation, K2 to K6, or the K3 models. No lane. No claim that the transfer is forced, that the carrier
 gap is closed or narrowed, or that Born is derived.
axioms: within propext, Classical.choice, Quot.sound. No sorry.
-/
import Definitions.Def_APFPaper5_K1_LedgerScore
import Theorems.Thm_APFPaper1_RecordLedger_bill_eq_sum
import Theorems.Thm_APFPaper1_RecordLedger_maintained_eq_kept
import Theorems.Thm_APFPaper1_RecordLedger_needsFin_subset_of_sufficient
import Theorems.Thm_APFPaper5_K1_interface_sharedCost_families
import Definitions.Def_APFPaper5_K1_interface_bridge_witness_Vocabulary
import Theorems.Thm_APFPaper5_K1_BridgeWitness_exactly_served

set_option autoImplicit false

open APFPaper1 APFPaper1.Source

namespace APFPaper5.K1

section
variable {D P Record : Type*} [DecidableEq Record]

/-- The ledger's family cost is the total cost of the records the family needs. -/
theorem ledger_familyCost_eq_needs (L : RecordLedger D P Record) (S : Finset D)
    (hS : ∃ p : P, L.kept p = S.biUnion L.needsFin ∧ ∀ d ∈ S, ∃ sigma : Set Record,
      sigma ⊆ L.maintained p ∧ L.sufficient p sigma d ∧ L.usesToRealize p d sigma) :
    L.familyCost S = ∑ a ∈ S.biUnion L.needsFin, (L.cost a : ℝ) :=
  familyCost_eq_sum_of_available L.wholeResource L.calibration L.maintained L.sufficient
    L.usesToRealize L.kept L.needsFin L.cost L.bill_eq_sum L.maintained_eq_kept
    L.needsFin_subset_of_sufficient S hS

/-- The score of two families is the total cost of the records both need. -/
theorem ledger_score_eq_shared_needs [DecidableEq D] (L : RecordLedger D P Record) (S T : Finset D)
    (hS : ExactlyServed L.maintained L.sufficient L.usesToRealize L.kept L.needsFin S)
    (hT : ExactlyServed L.maintained L.sufficient L.usesToRealize L.kept L.needsFin T)
    (hST : ExactlyServed L.maintained L.sufficient L.usesToRealize L.kept L.needsFin (S ∪ T)) :
    ledgerScore L S T = ∑ a ∈ S.biUnion L.needsFin ∩ T.biUnion L.needsFin, (L.cost a : ℝ) :=
  interface_sharedCost_families L.wholeResource L.calibration L.maintained L.sufficient
    L.usesToRealize L.kept L.needsFin L.cost L.bill_eq_sum L.maintained_eq_kept
    L.needsFin_subset_of_sufficient S T hS hT hST

/-- K1's typed conditions for the scores of a counted family of a record ledger, from the declared B05
and the availability sentence. -/
theorem ledger_counted_family_satisfies_K1 {ι : Type*} [Fintype ι] [DecidableEq ι] [DecidableEq D]
    [Fintype Record] (L : RecordLedger D P Record) (tested : D → Prop) (C eps : ℝ)
    (hB05 : APFB05.MarginalFloor (Context := Unit) (D := fun _ => D) (P := fun _ => P)
      (R := fun _ => Finset Record) (Record := fun _ => Record) (fun _ => L.wholeResource)
      (fun _ => L.calibration) (fun _ => L.maintained) (fun _ => L.sufficient)
      (fun _ => L.usesToRealize) (fun _ => tested) (fun _ => C) (fun _ => eps))
    (havail : LedgerAvailable L C) (dist : ι → D) (hcounted : LedgerCounted L tested C dist) :
    IsBilinear (VP := ι → ℝ) (VE := ι → ℝ)
        (tableForm (fun i j : ι => ledgerScore L {dist i} {dist j})) ∧
      FaithfulNonnegDiagonal (tableForm (fun i j : ι => ledgerScore L {dist i} {dist j}))
        (LinearEquiv.refl ℝ (ι → ℝ)) := by
  have key := interface_region_satisfies_K1_of_floor L.wholeResource L.calibration L.maintained
    L.sufficient L.usesToRealize L.kept L.needsFin L.cost L.bill_eq_sum L.maintained_eq_kept
    L.needsFin_subset_of_sufficient tested C eps hB05 havail dist hcounted.1 hcounted.2.1
    hcounted.2.2
  exact key

end

/-! ### A ledger on which the premises hold together -/

namespace Book

open BridgeWitness

variable {ι : Type} [DecidableEq ι]



theorem book_needs (d : ι) : (book (ι := ι)).needs d = (↑(fam d) : Set (Option ι)) := by
  ext a
  constructor
  · intro h
    exact h ∅ (↑(fam d)) subset_rfl
  · intro ha _ sigma hsub
    exact hsub ha

theorem book_needsFin (d : ι) : (book (ι := ι)).needsFin d = fam d := by
  have hfin : ((book (ι := ι)).needs d).Finite := by
    rw [book_needs]
    exact Finset.finite_toSet _
  unfold RecordLedger.needsFin
  rw [dif_pos hfin]
  apply Finset.coe_injective
  rw [hfin.coe_toFinset, book_needs]

/-- B05 as declared, the availability sentence and "counted" hold together on the book. -/
theorem book_meets_hypotheses [Fintype ι] : ∃ C : ℝ,
    APFB05.MarginalFloor (Context := Unit) (D := fun _ => ι) (P := fun _ => Finset (Option ι))
      (R := fun _ => Finset (Option ι)) (Record := fun _ => Option ι)
      (fun _ => (book (ι := ι)).wholeResource) (fun _ => (book (ι := ι)).calibration)
      (fun _ => (book (ι := ι)).maintained) (fun _ => (book (ι := ι)).sufficient)
      (fun _ => (book (ι := ι)).usesToRealize) (fun _ => fun _ => True) (fun _ => C) (fun _ => 1) ∧
    LedgerAvailable (book (ι := ι)) C ∧
    LedgerCounted (book (ι := ι)) (fun _ => True) C (fun i : ι => i) := by
  have hfun : (book (ι := ι)).needsFin = fam := funext book_needsFin
  obtain ⟨C, hC⟩ : ∃ C : ℝ,
      familyCost (book (ι := ι)).wholeResource (book (ι := ι)).calibration
        (book (ι := ι)).maintained (book (ι := ι)).sufficient (book (ι := ι)).usesToRealize
        (Finset.univ.image (fun i : ι => i)) ≤ C := ⟨_, le_refl _⟩
  have hserve : ∀ S : Finset ι, ∃ p : Finset (Option ι),
      (book (ι := ι)).kept p = S.biUnion (book (ι := ι)).needsFin ∧ ∀ d ∈ S, ∃ sigma : Set (Option ι),
        sigma ⊆ (book (ι := ι)).maintained p ∧ (book (ι := ι)).sufficient p sigma d ∧
        (book (ι := ι)).usesToRealize p d sigma := by
    intro S
    rw [hfun]
    exact exactly_served S
  have hneeds : ∀ i : ι,
      ¬ fam i ⊆ ((Finset.univ.erase i).image (fun i : ι => i)).biUnion fam := by
    intro i h
    have hi : some i ∈ fam i := by simp [fam]
    have h2 := h hi
    rw [Finset.mem_biUnion] at h2
    obtain ⟨k, hk, hmem⟩ := h2
    rw [Finset.mem_image] at hk
    obtain ⟨k', hk', rfl⟩ := hk
    have hne : k' ≠ i := (Finset.mem_erase.mp hk').1
    simp [fam] at hmem
    exact hne hmem.symm
  refine ⟨C, ?_, fun S _ => hserve S, ?_, fun _ => trivial, ?_⟩
  · exact APFB05.weighted_record_model_satisfies_floor (Context := Unit) w fam 1 one_pos
      (fun a => by simp [w]) (fun _ => C)
  · refine And.intro ?_ hC
    obtain ⟨p, _, hp⟩ := hserve (Finset.univ.image (fun i : ι => i))
    exact ⟨p, hp⟩
  · intro i
    exact recordModel_supportNovel_of_needs_own_record w fam 1 one_pos (fun a => by simp [w]) _ i
      (hneeds i)

end Book

end APFPaper5.K1


theorem solution :
∀ {ι : Type} [inst : DecidableEq.{1} ι] [inst_1 : Fintype.{0} ι],
  @Exists.{1} Real fun (C : Real) =>
    And
      (@APFB05.MarginalFloor.{0, 0, 0, 0, 0} Unit (fun (x : Unit) => ι) (fun (x : Unit) => Finset.{0} (Option.{0} ι))
        (fun (x : Unit) => Finset.{0} (Option.{0} ι)) (fun (x : Unit) => Option.{0} ι) (fun (g : Unit) => inst)
        (fun (x : Unit) =>
          @APFPaper1.RecordLedger.wholeResource.{0, 0, 0} ι (Finset.{0} (Option.{0} ι)) (Option.{0} ι)
            (@APFPaper5.K1.Book.book ι inst))
        (fun (x : Unit) =>
          @APFPaper1.RecordLedger.calibration.{0, 0, 0} ι (Finset.{0} (Option.{0} ι)) (Option.{0} ι)
            (@APFPaper5.K1.Book.book ι inst))
        (fun (x : Unit) =>
          @APFPaper1.RecordLedger.maintained.{0, 0, 0} ι (Finset.{0} (Option.{0} ι)) (Option.{0} ι)
            (@APFPaper5.K1.Book.book ι inst))
        (fun (x : Unit) =>
          @APFPaper1.RecordLedger.sufficient.{0, 0, 0} ι (Finset.{0} (Option.{0} ι)) (Option.{0} ι)
            (@APFPaper5.K1.Book.book ι inst))
        (fun (x : Unit) =>
          @APFPaper1.RecordLedger.usesToRealize.{0, 0, 0} ι (Finset.{0} (Option.{0} ι)) (Option.{0} ι)
            (@APFPaper5.K1.Book.book ι inst))
        (fun (x : Unit) (x_1 : ι) => True) (fun (x : Unit) => C) fun (x : Unit) =>
        @OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
      (And
        (@APFPaper5.K1.LedgerAvailable.{0, 0, 0} ι (Finset.{0} (Option.{0} ι)) (Option.{0} ι)
          (fun (a b : Option.{0} ι) => @Option.instDecidableEq.{0} ι inst a b) (@APFPaper5.K1.Book.book ι inst) C)
        (@APFPaper5.K1.LedgerCounted.{0, 0, 0, 0} ι (Finset.{0} (Option.{0} ι)) (Option.{0} ι) ι inst_1 inst inst
          (@APFPaper5.K1.Book.book ι inst) (fun (x : ι) => True) C fun (i : ι) => i)) := by
  exact @APFPaper5.K1.Book.book_meets_hypotheses
