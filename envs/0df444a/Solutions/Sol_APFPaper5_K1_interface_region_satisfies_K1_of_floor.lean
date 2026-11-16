-- Prove2me | solution 1 for APFPaper5.K1.interface_region_satisfies_K1_of_floor
-- status  : ACCEPTED   (prove)
-- author  : @FiniteUniverse
-- created : 2026-11-15T23:37:42.527+00:00
-- url     : https://prove2.me/submissions/5be17ee4-d5ff-4b67-ab9a-c8dddd29d463

import Definitions.Def_APFPaper1_FamilyCost
import Definitions.Def_APF_B05_DeclaredInput_r2
import Theorems.Thm_APFB05_support_novel_chain_capacity_bound
import Mathlib.Data.NNReal.Basic
import Mathlib.Tactic.Linarith
import Definitions.Def_APFPaper5_K1_RecordModel
import Definitions.Def_APFPaper5_K1_SharedCost
import Theorems.Thm_APFPaper5_K1_atomTable_symm
import Theorems.Thm_APFPaper5_K1_atomTable_form
import Theorems.Thm_APFPaper5_K1_atomTable_nonneg
import Theorems.Thm_APFPaper5_K1_record_book_table_satisfies_K1
import Mathlib.Data.Finset.Union
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Definitions.Def_APFPaper5_K1_interface_bridge_Vocabulary
import Theorems.Thm_APFPaper1_Source_sum_needed_le_bill
import Theorems.Thm_APFPaper1_Source_familyCost_eq_sum_of_available
import Theorems.Thm_APFPaper1_Source_supportNovel_of_private_record
import Theorems.Thm_APFPaper1_Source_supportNovel_of_private_record_count
import Theorems.Thm_APFPaper1_Source_marginal_ge_of_private_record
import Theorems.Thm_APFPaper1_Source_each_private_excludes_riding
import Theorems.Thm_APFPaper1_Source_supportNovel_of_each_private
import Theorems.Thm_APFPaper1_Source_marginal_zero_of_no_own_record
import Theorems.Thm_APFPaper1_Source_needs_own_record_of_supportNovel
import Theorems.Thm_APFPaper5_K1_familyCost_weighted
import Theorems.Thm_APFPaper5_K1_recordModelCost_eq
import Theorems.Thm_APFPaper5_K1_recordModel_sharedCost
import Theorems.Thm_APFPaper5_K1_recordModel_satisfies_K1
import Theorems.Thm_APFB05_overfull_chain_not_admissible
import Theorems.Thm_APFB05_no_admissible_family_contains_overfull_chain
import Theorems.Thm_APFB05_no_room_for_new_record
/-
APF Foundation Ledger — theorem node. DRAFT for author and cold review. Not gated, not released, not uploaded.
name: APFB05.overfull_chain_not_admissible
title: A family built by more genuinely new tested distinctions than the capacity can pay for is not admissible, and a context with less than one floor of spare capacity cannot take one more
inputs_revision: 2026-10-04.1
mathlib_rev: 0df444a360eaa60ab8c11dca51a86af692955474
source: Paper 1 Supplement v9.28:1781 (ledger admissibility), 1820-1824 (marginal floor and support novelty),
  2625 (support novelty, formal). The consumed nodes cite the same passages by their v9.27 line numbers
  (1763-1782, 1807-1818, 2615-2617). For the reading as a statement about classical record models: v9.28:3724,
  3737 (the defender's admissible record space and charging clause), 6952.
consumes: B05 (encoding MarginalFloor, r2, with its tested guard). B04 enters only as the capacity C in
  familyAdmissible. Uses the uploaded node APFB05.support_novel_chain_capacity_bound.
statement:
  (1) familyAdmissible is inherited by subfamilies.
  (2) If S n is built from S 0 by n tested support-novel insertions and C < n * epsilon, then S n is not admissible.
  (3) Then no admissible family contains S n.
  (4) If S is admissible, d is tested and support-novel over S, and C - familyCost S < epsilon, then insert d S is
      not admissible.
no new definition: every statement is in the existing FamilyCost and B05 vocabulary.
what it does not say: nothing about defenders, Sep, IJC or nonclassicality. Reading (3) or (4) as "no classical
  record model exists" needs a definition tying a defender's record family to familyAdmissible. That definition is
  not on the ledger and is not supplied here.
-/






set_option autoImplicit false
open Classical
open APFPaper1.Source

namespace APFB05

/-- (1) Admissibility passes to subfamilies: the same protocol serves the subfamily, and the infimal bill of a
subfamily is at most that of the family. Ordinary mathematics on source data. -/
theorem familyAdmissible_of_subset {D P R Record : Type*}
    (wholeResource : P → R) (calibration : R → NNReal)
    (maintained : P → Set Record) (sufficient : P → Set Record → D → Prop)
    (usesToRealize : P → D → Set Record → Prop) {C : ℝ} {S T : Finset D} (hST : S ⊆ T)
    (hT : familyAdmissible wholeResource calibration maintained sufficient usesToRealize C T) :
    familyAdmissible wholeResource calibration maintained sufficient usesToRealize C S := by
  obtain ⟨⟨p, hp⟩, hcost⟩ := hT
  refine ⟨⟨p, fun d hd => hp d (hST hd)⟩, le_trans ?_ hcost⟩
  unfold familyCost
  apply csInf_le_csInf
  · refine ⟨0, fun c hc => ?_⟩
    obtain ⟨q, _, rfl⟩ := hc
    exact NNReal.coe_nonneg _
  · exact ⟨_, p, hp, rfl⟩
  · rintro c ⟨q, hq, rfl⟩
    exact ⟨q, fun d hd => hq d (hST hd), rfl⟩







end APFB05

/-
APF Foundation Ledger — theorem node DRAFT (session EthanBrooke-01WrrBvu, 2026-11-12; not gated, not reviewed)
name: APFPaper5_K1_weighted_record_model
title: In the weighted record model the family cost is the weight of the records needed, the shared cost is the weight of the shared records, and K1's record-book conditions hold
inputs_revision: 2026-10-04.1
mathlib_rev: 0df444a360eaa60ab8c11dca51a86af692955474
source: as Def_APFPaper5_K1_RecordModel and Def_APFPaper5_K1_SharedCost.
consumes_inputs: none. Theorems about a MODEL of the source vocabulary.
statement: (familyCost_weighted, recordModelCost_eq) the family cost of S is the total cost of the records its
 members need. (atomTable_eq_sum_inter) the atom table of membership marks is the weight of shared records.
 (sharedCost_weighted_eq_atomTable, recordModel_sharedCost) the shared cost of two single families is that
 atom table. (recordModel_satisfies_K1) if every family has a record of positive cost that no other family
 needs, the table of shared costs is bilinear with a faithful nonnegative diagonal.
 Record costs need not be equal: no clause says cost depends only on the number of records.
not_claimed: that any interface is a record model; the boundary-role isomorphism beyond the identity map; K1.
-/











set_option autoImplicit false
open APFPaper1.Source
namespace APFPaper5.K1

universe u v
variable {ι : Type u} {Rec : Type v} [DecidableEq Rec]





theorem atomTable_eq_sum_inter [Fintype Rec] (w : Rec → ℝ) (fam : ι → Finset Rec) (i j : ι) :
    atomTable w (fun k a => decide (a ∈ fam k)) i j = ∑ a ∈ fam i ∩ fam j, w a := by
  have hterm : ∀ a : Rec, w a * (ind (decide (a ∈ fam i)) * ind (decide (a ∈ fam j))) =
      if a ∈ fam i ∩ fam j then w a else 0 := by
    intro a
    by_cases h1 : a ∈ fam i <;> by_cases h2 : a ∈ fam j <;> simp [ind, Finset.mem_inter, h1, h2]
  unfold atomTable
  simp only [hterm]
  rw [Finset.sum_ite_mem, Finset.univ_inter]







end APFPaper5.K1


/-
APF Foundation Ledger — theorem node DRAFT (Claude seat, session EthanBrooke-01WrrBvv, 2026-11-14; not
 gated, not reviewed, not released, not built in the ledger repo)
name: APFPaper5_K1_interface_bridge
title: On source data of the declared forms, read as adopted on 2026-11-14, the ledger's own family cost is the record model's cost, the shared cost of two distinctions is the weight of the records they share, and the table of shared costs of a region's counted distinctions meets K1's typed conditions
inputs_revision: 2026-11-14.1
mathlib_rev: 0df444a360eaa60ab8c11dca51a86af692955474
source: the author, 2026-11-14 HST 19:31: "Do the k1 bridge". HYPOTHESIS_LEDGER_2026-11-13 line 46 (the K-layer
 model theorems lack "a binding to an original interface, which is one bridge"). Paper 5 Supplement
 v7.33:3037-3040 (K1). Builder seat: Def_APFPaper5_K1_RecordModel (recordModelCost is the ledger's familyCost
 on one supplied set of data), Thm_APFPaper5_K1_weighted_record_model (recordModel_satisfies_K1). This seat:
 Thm_APFPaper1_supportNovel_of_private_record (familyCost_eq_sum_of_available). Declared input B05 in its
 declared form APFB05.MarginalFloor (Def_APF_B05_DeclaredInput_r2). APFB05.familyAdmissible_of_subset.
standing: CONDITIONAL THEOREMS. They bind the K1 record model to any source data of the declared forms. The
 hypotheses, and where each stands:
 - hbill, "the bill is the sum of the costs of the records kept": ADOPTED READING (this seat's reading of the
   author's 13:00 HST reply, confirmed 16:45 HST; RULING_named_calls_2026-11-14).
 - hkept, "what a protocol maintains is a finite set of records": a TYPING CLAUSE of this seat. Not ruled.
 - hneed, "serving a distinction needs that distinction's own records": ADOPTED READING (16:45 HST).
 - hscoped, "every family within capacity has a protocol keeping exactly what it needs": ADOPTED READING in
   the scoped wording (17:29 HST; RULING_calls_after_pass18_2026-11-14).
 - hB05: the DECLARED INPUT B05, consumed in its declared form.
 - hregion, htested: the region's counted distinctions are tested and admissible within capacity. A
   hypothesis on the region in hand.
 - hnov, "each counted distinction is support-novel over the others": NAMED, NOT ADOPTED
   (RULING_fineness_across_regions_2026-11-14).
 - hprivate (the first form only), "each counted distinction has a record of positive cost that no other of
   them needs": the private record is the ADOPTED READING in wording (ii) (17:29 HST); that its cost is
   positive is NOT ADOPTED. private_positive_record_of_floor derives both from hB05 and hnov.
 None of the readings is installed in FOUNDATION_INPUTS. Only the author edits it.
what this file says:
 1. familyCost_eq_recordModelCost. For any family that some protocol serves by keeping exactly what it
    needs, the ledger's family cost equals the record model's cost of that family. The record model is then
    not a supplied model: it is the interface's own cost.
 2. interface_sharedCost_eq_shared_records. The shared cost of two distinctions, built from the ledger's
    family cost alone, is the total cost of the records both need.
 3. interface_region_satisfies_K1. For a region's counted distinctions the table of those shared costs is
    bilinear and has a faithful nonnegative diagonal under the identity role exchange (K1's typed
    conditions as the builder seat typed them), given a private record of positive cost for each.
 4. private_positive_record_of_floor. B05's floor on a support-novel distinction gives it a record of
    positive cost that the family does not need.
 5. interface_region_satisfies_K1_of_floor. The same K1 conditions from the declared B05, the adopted
    readings, and the named sentence hnov, with no separate premise on private records.
what this file does NOT say:
 - That the shared cost is Paper 5's ordered score. The author deferred the identification of a score off
   the record-book side (ruling 4 of the eight decisions, 2026-11-12). On the record-book side the adopted
   score is the shared count (Def_APFPaper5_K1_SharedCount). No score is supplied here, so K1.a
   (Linearizes) is not stated.
 - That the role exchange is anything but the identity. The table is symmetric, so tests and preparations
   are the same space here. Paper 5's typed boundary-role isomorphism in general is not constructed.
 - Anything about K3. The binding of the K3 models' profiles to original profiles (ledger row C12) is a
   different bridge and is not touched.
 - Any bound on the number of directions. Capacity over the floor bounds the count of counted distinctions
   only with a private record for each (Thm_APFPaper5_K1_table_kernel_and_support).
 - No lane. No claim that the transfer is forced, that the carrier gap is closed or narrowed, or that Born
   is derived.
axioms: within propext, Classical.choice, Quot.sound. No sorry.
-/


















set_option autoImplicit false

open APFPaper1.Source

namespace APFPaper5.K1

section
variable {D P R Record : Type*} [DecidableEq Record]
  (wholeResource : P → R) (calibration : R → NNReal)
  (maintained : P → Set Record)
  (sufficient : P → Set Record → D → Prop)
  (usesToRealize : P → D → Set Record → Prop)
  (kept : P → Finset Record) (fam : D → Finset Record) (cost : Record → NNReal)



/-- The ledger's family cost is the record model's cost, on every family that is exactly served. -/
theorem familyCost_eq_recordModelCost
    (hbill : ∀ p : P, (calibration (wholeResource p) : ℝ) = ∑ r ∈ kept p, (cost r : ℝ))
    (hkept : ∀ p : P, maintained p = (↑(kept p) : Set Record))
    (hneed : ∀ (p : P) (sigma : Set Record) (d : D),
      sufficient p sigma d → (↑(fam d) : Set Record) ⊆ sigma)
    (S : Finset D) (havail : ExactlyServed maintained sufficient usesToRealize kept fam S) :
    familyCost wholeResource calibration maintained sufficient usesToRealize S =
      recordModelCost cost fam S := by
  rw [recordModelCost_eq]
  exact familyCost_eq_sum_of_available wholeResource calibration maintained sufficient usesToRealize
    kept fam cost hbill hkept hneed S havail

/-- The shared cost of two distinctions is the total cost of the records both need. -/
theorem interface_sharedCost_eq_shared_records [DecidableEq D]
    (hbill : ∀ p : P, (calibration (wholeResource p) : ℝ) = ∑ r ∈ kept p, (cost r : ℝ))
    (hkept : ∀ p : P, maintained p = (↑(kept p) : Set Record))
    (hneed : ∀ (p : P) (sigma : Set Record) (d : D),
      sufficient p sigma d → (↑(fam d) : Set Record) ⊆ sigma)
    (i j : D)
    (hi : ExactlyServed maintained sufficient usesToRealize kept fam {i})
    (hj : ExactlyServed maintained sufficient usesToRealize kept fam {j})
    (hij : ExactlyServed maintained sufficient usesToRealize kept fam ({i} ∪ {j})) :
    sharedCost (familyCost wholeResource calibration maintained sufficient usesToRealize) {i} {j} =
      ∑ a ∈ fam i ∩ fam j, (cost a : ℝ) := by
  have e1 := familyCost_eq_sum_of_available wholeResource calibration maintained sufficient
    usesToRealize kept fam cost hbill hkept hneed {i} hi
  have e2 := familyCost_eq_sum_of_available wholeResource calibration maintained sufficient
    usesToRealize kept fam cost hbill hkept hneed {j} hj
  have e3 := familyCost_eq_sum_of_available wholeResource calibration maintained sufficient
    usesToRealize kept fam cost hbill hkept hneed ({i} ∪ {j}) hij
  have h1 : ({i} : Finset D).biUnion fam = fam i := Finset.singleton_biUnion
  have h2 : ({j} : Finset D).biUnion fam = fam j := Finset.singleton_biUnion
  have h3 : (({i} : Finset D) ∪ {j}).biUnion fam = fam i ∪ fam j := by
    rw [Finset.union_biUnion, h1, h2]
  rw [h1] at e1
  rw [h2] at e2
  rw [h3] at e3
  have hsum : ∑ a ∈ fam i ∪ fam j, (cost a : ℝ) + ∑ a ∈ fam i ∩ fam j, (cost a : ℝ) =
      ∑ a ∈ fam i, (cost a : ℝ) + ∑ a ∈ fam j, (cost a : ℝ) := Finset.sum_union_inter
  unfold sharedCost
  rw [e1, e2, e3]
  linarith

/-- The table of shared costs of indexed distinctions is the record model's table. -/
theorem interface_table_eq_recordModel_table {ι : Type*} [DecidableEq ι] [DecidableEq D]
    [Fintype Record]
    (hbill : ∀ p : P, (calibration (wholeResource p) : ℝ) = ∑ r ∈ kept p, (cost r : ℝ))
    (hkept : ∀ p : P, maintained p = (↑(kept p) : Set Record))
    (hneed : ∀ (p : P) (sigma : Set Record) (d : D),
      sufficient p sigma d → (↑(fam d) : Set Record) ⊆ sigma)
    (dist : ι → D)
    (havail : ∀ i j : ι,
      ExactlyServed maintained sufficient usesToRealize kept fam ({dist i} ∪ {dist j})) :
    (fun i j : ι => sharedCost
        (familyCost wholeResource calibration maintained sufficient usesToRealize) {dist i} {dist j}) =
      (fun i j : ι => sharedCost (recordModelCost cost (fun k => fam (dist k))) {i} {j}) := by
  funext i j
  have hi : ExactlyServed maintained sufficient usesToRealize kept fam {dist i} := by
    have h := havail i i
    rwa [Finset.union_self] at h
  have hj : ExactlyServed maintained sufficient usesToRealize kept fam {dist j} := by
    have h := havail j j
    rwa [Finset.union_self] at h
  rw [interface_sharedCost_eq_shared_records wholeResource calibration maintained sufficient
      usesToRealize kept fam cost hbill hkept hneed (dist i) (dist j) hi hj (havail i j),
    recordModel_sharedCost, atomTable_eq_sum_inter]

/-- K1's typed conditions for the shared costs of a region's counted distinctions, given a private record
of positive cost for each. -/
theorem interface_region_satisfies_K1 {ι : Type*} [Fintype ι] [DecidableEq ι] [DecidableEq D]
    [Fintype Record]
    (hbill : ∀ p : P, (calibration (wholeResource p) : ℝ) = ∑ r ∈ kept p, (cost r : ℝ))
    (hkept : ∀ p : P, maintained p = (↑(kept p) : Set Record))
    (hneed : ∀ (p : P) (sigma : Set Record) (d : D),
      sufficient p sigma d → (↑(fam d) : Set Record) ⊆ sigma)
    (dist : ι → D)
    (havail : ∀ i j : ι,
      ExactlyServed maintained sufficient usesToRealize kept fam ({dist i} ∪ {dist j}))
    (hprivate : ∀ i, ∃ a, 0 < cost a ∧ ∀ j, (a ∈ fam (dist j) ↔ j = i)) :
    IsBilinear (VP := ι → ℝ) (VE := ι → ℝ)
        (tableForm (fun i j : ι => sharedCost
          (familyCost wholeResource calibration maintained sufficient usesToRealize)
          {dist i} {dist j})) ∧
      FaithfulNonnegDiagonal
        (tableForm (fun i j : ι => sharedCost
          (familyCost wholeResource calibration maintained sufficient usesToRealize)
          {dist i} {dist j}))
        (LinearEquiv.refl ℝ (ι → ℝ)) := by
  rw [interface_table_eq_recordModel_table wholeResource calibration maintained sufficient
    usesToRealize kept fam cost hbill hkept hneed dist havail]
  exact recordModel_satisfies_K1 cost (fun k => fam (dist k)) hprivate

/-- B05's floor on a support-novel distinction gives it a record of positive cost that the family does not
need. -/
theorem private_positive_record_of_floor [DecidableEq D]
    (hbill : ∀ p : P, (calibration (wholeResource p) : ℝ) = ∑ r ∈ kept p, (cost r : ℝ))
    (hkept : ∀ p : P, maintained p = (↑(kept p) : Set Record))
    (hneed : ∀ (p : P) (sigma : Set Record) (d : D),
      sufficient p sigma d → (↑(fam d) : Set Record) ⊆ sigma)
    (tested : D → Prop) (C eps : ℝ)
    (hB05 : APFB05.MarginalFloor (Context := Unit) (D := fun _ => D) (P := fun _ => P)
      (R := fun _ => R) (Record := fun _ => Record) (fun _ => wholeResource) (fun _ => calibration)
      (fun _ => maintained) (fun _ => sufficient) (fun _ => usesToRealize) (fun _ => tested)
      (fun _ => C) (fun _ => eps))
    (S : Finset D) (d : D) (ht : tested d)
    (hS : familyAdmissible wholeResource calibration maintained sufficient usesToRealize C S)
    (hdS : familyAdmissible wholeResource calibration maintained sufficient usesToRealize C
      (insert d S))
    (hnov : supportNovel wholeResource calibration maintained sufficient usesToRealize S d)
    (havail : ExactlyServed maintained sufficient usesToRealize kept fam S)
    (havail' : ExactlyServed maintained sufficient usesToRealize kept fam (insert d S)) :
    ∃ a ∈ fam d, a ∉ S.biUnion fam ∧ 0 < cost a := by
  obtain ⟨heps, hfl⟩ := hB05 ()
  have hgap := hfl S d ht hS hdS hnov
  have e1 := familyCost_eq_sum_of_available wholeResource calibration maintained sufficient
    usesToRealize kept fam cost hbill hkept hneed S havail
  have e2 := familyCost_eq_sum_of_available wholeResource calibration maintained sufficient
    usesToRealize kept fam cost hbill hkept hneed (insert d S) havail'
  have hsplit : ∑ a ∈ (insert d S).biUnion fam, (cost a : ℝ) =
      ∑ a ∈ fam d \ S.biUnion fam, (cost a : ℝ) + ∑ a ∈ S.biUnion fam, (cost a : ℝ) := by
    rw [Finset.biUnion_insert, ← Finset.sdiff_union_self_eq_union,
      Finset.sum_union Finset.sdiff_disjoint]
  by_contra hcon
  have hz : ∑ a ∈ fam d \ S.biUnion fam, (cost a : ℝ) = 0 := by
    apply Finset.sum_eq_zero
    intro a ha
    rw [Finset.mem_sdiff] at ha
    have h0 : ¬ 0 < cost a := fun hpos => hcon ⟨a, ha.1, ha.2, hpos⟩
    have h1 : cost a = 0 := le_antisymm (not_lt.mp h0) zero_le
    simp [h1]
  have hgap' : eps ≤ familyCost wholeResource calibration maintained sufficient usesToRealize
      (insert d S) - familyCost wholeResource calibration maintained sufficient usesToRealize S :=
    hgap
  have heps' : (0 : ℝ) < eps := heps
  rw [e1, e2, hsplit, hz] at hgap'
  linarith

/-- K1's typed conditions for the shared costs of a region's counted distinctions, from the declared B05,
the adopted readings, and the named sentence that each counted distinction is support-novel over the
others. -/
theorem interface_region_satisfies_K1_of_floor {ι : Type*} [Fintype ι] [DecidableEq ι]
    [DecidableEq D] [Fintype Record]
    (hbill : ∀ p : P, (calibration (wholeResource p) : ℝ) = ∑ r ∈ kept p, (cost r : ℝ))
    (hkept : ∀ p : P, maintained p = (↑(kept p) : Set Record))
    (hneed : ∀ (p : P) (sigma : Set Record) (d : D),
      sufficient p sigma d → (↑(fam d) : Set Record) ⊆ sigma)
    (tested : D → Prop) (C eps : ℝ)
    (hB05 : APFB05.MarginalFloor (Context := Unit) (D := fun _ => D) (P := fun _ => P)
      (R := fun _ => R) (Record := fun _ => Record) (fun _ => wholeResource) (fun _ => calibration)
      (fun _ => maintained) (fun _ => sufficient) (fun _ => usesToRealize) (fun _ => tested)
      (fun _ => C) (fun _ => eps))
    (hscoped : ∀ S : Finset D,
      familyAdmissible wholeResource calibration maintained sufficient usesToRealize C S →
      ExactlyServed maintained sufficient usesToRealize kept fam S)
    (dist : ι → D)
    (hregion : familyAdmissible wholeResource calibration maintained sufficient usesToRealize C
      (Finset.univ.image dist))
    (htested : ∀ i, tested (dist i))
    (hnov : ∀ i, supportNovel wholeResource calibration maintained sufficient usesToRealize
      ((Finset.univ.erase i).image dist) (dist i)) :
    IsBilinear (VP := ι → ℝ) (VE := ι → ℝ)
        (tableForm (fun i j : ι => sharedCost
          (familyCost wholeResource calibration maintained sufficient usesToRealize)
          {dist i} {dist j})) ∧
      FaithfulNonnegDiagonal
        (tableForm (fun i j : ι => sharedCost
          (familyCost wholeResource calibration maintained sufficient usesToRealize)
          {dist i} {dist j}))
        (LinearEquiv.refl ℝ (ι → ℝ)) := by
  have hadm : ∀ S : Finset D, S ⊆ Finset.univ.image dist →
      familyAdmissible wholeResource calibration maintained sufficient usesToRealize C S :=
    fun S hS => APFB05.familyAdmissible_of_subset wholeResource calibration maintained sufficient
      usesToRealize hS hregion
  have hmem : ∀ i, dist i ∈ Finset.univ.image dist :=
    fun i => Finset.mem_image_of_mem dist (Finset.mem_univ i)
  have hoth : ∀ i, (Finset.univ.erase i).image dist ⊆ Finset.univ.image dist :=
    fun i => Finset.image_subset_image (Finset.erase_subset i _)
  have hins : ∀ i, insert (dist i) ((Finset.univ.erase i).image dist) ⊆ Finset.univ.image dist :=
    fun i => Finset.insert_subset (hmem i) (hoth i)
  have hpair : ∀ i j, (({dist i} : Finset D) ∪ {dist j}) ⊆ Finset.univ.image dist := by
    intro i j x hx
    rw [Finset.mem_union, Finset.mem_singleton, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · exact hmem i
    · exact hmem j
  refine interface_region_satisfies_K1 wholeResource calibration maintained sufficient usesToRealize
    kept fam cost hbill hkept hneed dist (fun i j => hscoped _ (hadm _ (hpair i j))) ?_
  intro i
  obtain ⟨a, had, haS, hpos⟩ := private_positive_record_of_floor wholeResource calibration
    maintained sufficient usesToRealize kept fam cost hbill hkept hneed tested C eps hB05
    ((Finset.univ.erase i).image dist) (dist i) (htested i) (hadm _ (hoth i)) (hadm _ (hins i))
    (hnov i) (hscoped _ (hadm _ (hoth i))) (hscoped _ (hadm _ (hins i)))
  refine ⟨a, hpos, fun j => ⟨fun haj => ?_, fun hji => ?_⟩⟩
  · by_contra hne
    apply haS
    rw [Finset.mem_biUnion]
    exact ⟨dist j, Finset.mem_image_of_mem dist (Finset.mem_erase.mpr ⟨hne, Finset.mem_univ j⟩), haj⟩
  · subst hji
    exact had

end

end APFPaper5.K1


universe apfNative_u_1 apfNative_u_2 apfNative_u_3 apfNative_u_4 apfNative_u_5
theorem solution :
∀ {D : Type apfNative_u_1} {P : Type apfNative_u_2} {R : Type apfNative_u_3} {Record : Type apfNative_u_4}
  [inst : DecidableEq.{apfNative_u_4 + 1} Record] (wholeResource : P → R) (calibration : R → NNReal)
  (maintained : P → Set.{apfNative_u_4} Record) (sufficient : P → Set.{apfNative_u_4} Record → D → Prop)
  (usesToRealize : P → D → Set.{apfNative_u_4} Record → Prop) (kept : P → Finset.{apfNative_u_4} Record)
  (fam : D → Finset.{apfNative_u_4} Record) (cost : Record → NNReal) {ι : Type apfNative_u_5}
  [inst_1 : Fintype.{apfNative_u_5} ι] [inst_2 : DecidableEq.{apfNative_u_5 + 1} ι]
  [inst_3 : DecidableEq.{apfNative_u_1 + 1} D] [Fintype.{apfNative_u_4} Record]
  (hbill :
    ∀ (p : P),
      @Eq.{1} Real (NNReal.toReal (calibration (wholeResource p)))
        (@Finset.sum.{apfNative_u_4, 0} Record Real Real.instAddCommMonoid (kept p) fun (r : Record) =>
          NNReal.toReal (cost r)))
  (hkept :
    ∀ (p : P),
      @Eq.{apfNative_u_4 + 1} (Set.{apfNative_u_4} Record) (maintained p)
        (@SetLike.coe.{apfNative_u_4, apfNative_u_4} (Finset.{apfNative_u_4} Record) Record
          (@Finset.instSetLike.{apfNative_u_4} Record) (kept p)))
  (hneed :
    ∀ (p : P) (sigma : Set.{apfNative_u_4} Record) (d : D),
      sufficient p sigma d →
        @LE.le.{apfNative_u_4} (Set.{apfNative_u_4} Record) (@Set.instLE.{apfNative_u_4} Record)
          (@SetLike.coe.{apfNative_u_4, apfNative_u_4} (Finset.{apfNative_u_4} Record) Record
            (@Finset.instSetLike.{apfNative_u_4} Record) (fam d))
          sigma)
  (tested : D → Prop) (C eps : Real)
  (hB05 :
    @APFB05.MarginalFloor.{0, apfNative_u_1, apfNative_u_2, apfNative_u_3, apfNative_u_4} Unit (fun (x : Unit) => D)
      (fun (x : Unit) => P) (fun (x : Unit) => R) (fun (x : Unit) => Record) (fun (g : Unit) => inst_3)
      (fun (x : Unit) => wholeResource) (fun (x : Unit) => calibration) (fun (x : Unit) => maintained)
      (fun (x : Unit) => sufficient) (fun (x : Unit) => usesToRealize) (fun (x : Unit) => tested) (fun (x : Unit) => C)
      fun (x : Unit) => eps)
  (hscoped :
    ∀ (S : Finset.{apfNative_u_1} D),
      @APFPaper1.Source.familyAdmissible.{apfNative_u_1, apfNative_u_2, apfNative_u_3, apfNative_u_4} D P R Record
          wholeResource calibration maintained sufficient usesToRealize C S →
        @APFPaper5.K1.ExactlyServed.{apfNative_u_1, apfNative_u_2, apfNative_u_4} D P Record inst maintained sufficient
          usesToRealize kept fam S)
  (dist : ι → D)
  (hregion :
    @APFPaper1.Source.familyAdmissible.{apfNative_u_1, apfNative_u_2, apfNative_u_3, apfNative_u_4} D P R Record
      wholeResource calibration maintained sufficient usesToRealize C
      (@Finset.image.{apfNative_u_5, apfNative_u_1} ι D inst_3 dist (@Finset.univ.{apfNative_u_5} ι inst_1)))
  (htested : ∀ (i : ι), tested (dist i))
  (hnov :
    ∀ (i : ι),
      @APFPaper1.Source.supportNovel.{apfNative_u_1, apfNative_u_2, apfNative_u_3, apfNative_u_4} D P R Record
        wholeResource calibration maintained sufficient usesToRealize
        (@Finset.image.{apfNative_u_5, apfNative_u_1} ι D inst_3 dist
          (@Finset.erase.{apfNative_u_5} ι inst_2 (@Finset.univ.{apfNative_u_5} ι inst_1) i))
        (dist i)),
  And
    (@APFPaper5.K1.IsBilinear.{apfNative_u_5, apfNative_u_5} (ι → Real) (ι → Real)
      (@Pi.addCommGroup.{apfNative_u_5, 0} ι (fun (a : ι) => Real) fun (i : ι) => Real.instAddCommGroup)
      (@Pi.Function.module.{apfNative_u_5, 0, 0} ι Real Real Real.semiring
        (@Semiring.toAddCommMonoid.{0} Real (@Ring.toSemiring.{0} Real Real.instRing))
        (@Semiring.toModule.{0} Real Real.semiring))
      (@Pi.addCommGroup.{apfNative_u_5, 0} ι (fun (a : ι) => Real) fun (i : ι) => Real.instAddCommGroup)
      (@Pi.Function.module.{apfNative_u_5, 0, 0} ι Real Real Real.semiring
        (@Semiring.toAddCommMonoid.{0} Real (@Ring.toSemiring.{0} Real Real.instRing))
        (@Semiring.toModule.{0} Real Real.semiring))
      (@APFPaper5.K1.tableForm.{apfNative_u_5} ι inst_1 fun (i j : ι) =>
        @APFPaper5.K1.sharedCost.{apfNative_u_1} D inst_3
          (@APFPaper1.Source.familyCost.{apfNative_u_1, apfNative_u_2, apfNative_u_3, apfNative_u_4} D P R Record
            wholeResource calibration maintained sufficient usesToRealize)
          (@Singleton.singleton.{apfNative_u_1, apfNative_u_1} D (Finset.{apfNative_u_1} D)
            (@Finset.instSingleton.{apfNative_u_1} D) (dist i))
          (@Singleton.singleton.{apfNative_u_1, apfNative_u_1} D (Finset.{apfNative_u_1} D)
            (@Finset.instSingleton.{apfNative_u_1} D) (dist j))))
    (@APFPaper5.K1.FaithfulNonnegDiagonal.{apfNative_u_5, apfNative_u_5} (ι → Real) (ι → Real)
      (@Pi.addCommGroup.{apfNative_u_5, 0} ι (fun (a : ι) => Real) fun (i : ι) => Real.instAddCommGroup)
      (@Pi.Function.module.{apfNative_u_5, 0, 0} ι Real Real Real.semiring Real.instAddCommMonoid
        (@Semiring.toModule.{0} Real Real.semiring))
      (@Pi.addCommGroup.{apfNative_u_5, 0} ι (fun (a : ι) => Real) fun (i : ι) => Real.instAddCommGroup)
      (@Pi.Function.module.{apfNative_u_5, 0, 0} ι Real Real Real.semiring Real.instAddCommMonoid
        (@Semiring.toModule.{0} Real Real.semiring))
      (@APFPaper5.K1.tableForm.{apfNative_u_5} ι inst_1 fun (i j : ι) =>
        @APFPaper5.K1.sharedCost.{apfNative_u_1} D inst_3
          (@APFPaper1.Source.familyCost.{apfNative_u_1, apfNative_u_2, apfNative_u_3, apfNative_u_4} D P R Record
            wholeResource calibration maintained sufficient usesToRealize)
          (@Singleton.singleton.{apfNative_u_1, apfNative_u_1} D (Finset.{apfNative_u_1} D)
            (@Finset.instSingleton.{apfNative_u_1} D) (dist i))
          (@Singleton.singleton.{apfNative_u_1, apfNative_u_1} D (Finset.{apfNative_u_1} D)
            (@Finset.instSingleton.{apfNative_u_1} D) (dist j)))
      (@LinearEquiv.refl.{0, apfNative_u_5} Real (ι → Real) Real.semiring
        (@Pi.addCommMonoid.{apfNative_u_5, 0} ι (fun (a : ι) => Real) fun (i : ι) => Real.instAddCommMonoid)
        (@Pi.Function.module.{apfNative_u_5, 0, 0} ι Real Real Real.semiring Real.instAddCommMonoid
          (@Semiring.toModule.{0} Real Real.semiring)))) := by
  exact @APFPaper5.K1.interface_region_satisfies_K1_of_floor
