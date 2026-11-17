-- Prove2me | solution 1 for APFPaper5.K1.hasOwnPaidRecord_of_available
-- status  : ACCEPTED   (prove)
-- author  : @FiniteUniverse
-- created : 2026-11-16T17:25:52.483271+00:00
-- url     : https://prove2.me/submissions/fa601fd7-d46e-4d78-8ebc-11ef58abb050

import Definitions.Def_APFPaper1_FamilyCost
import Definitions.Def_APF_B05_DeclaredInput_r2
import Theorems.Thm_APFB05_support_novel_chain_capacity_bound
import Mathlib.Data.NNReal.Basic
import Mathlib.Tactic.Linarith
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
import Definitions.Def_APFPaper5_K1_Counted
import Theorems.Thm_APFPaper5_K1_partyScore_meets_K1_of_own_record
import Theorems.Thm_APFPaper5_K1_memberNeeds_subset_familyNeeds_explicit
import Theorems.Thm_APFPaper5_K1_familyNeeds_eq_of_exactly_served_explicit
import Theorems.Thm_APFPaper5_K1_ledger_party_score_meets_K1_explicit
import Theorems.Thm_APFPaper5_K1_ledger_counted_family_party_score_satisfies_K1_explicit
import Definitions.Def_APFPaper5_K1_free_pair_paid_relation_Vocabulary
import Theorems.Thm_APFPaper5_K1_FreePair_b05_holds
import Theorems.Thm_APFPaper5_K1_FreePair_pair_is_counted
import Theorems.Thm_APFPaper5_K1_FreePair_party_score_not_faithful
import Theorems.Thm_APFPaper5_K1_FreePair_no_own_paid_record
import Definitions.Def_APFPaper5_K1_twins_same_records_Vocabulary
import Theorems.Thm_APFPaper5_K1_Twins_fc_single
import Theorems.Thm_APFPaper5_K1_Twins_b05_holds
import Theorems.Thm_APFPaper5_K1_Twins_single_novel_over_empty
import Theorems.Thm_APFPaper5_K1_Twins_pair_is_counted
import Theorems.Thm_APFPaper5_K1_Twins_party_all
import Theorems.Thm_APFPaper5_K1_Twins_party_score_not_faithful
import Definitions.Def_APFPaper5_K1_counted_pair_with_relation_Vocabulary
import Theorems.Thm_APFPaper5_K1_PaidPair_b05_holds
import Theorems.Thm_APFPaper5_K1_PaidPair_pair_is_counted
import Theorems.Thm_APFPaper5_K1_PaidPair_relation_is_joint
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



end

end APFPaper5.K1

/-
APF Foundation Ledger — theorem node DRAFT (Claude seat, session EthanBrooke-01WrrBvv, 2026-11-15; not
 gated, not reviewed, not released, not built in the ledger repo)
name: APFPaper5_K1_counted_family
title: On a record ledger the table of scores of a counted family is bilinear with a faithful nonnegative diagonal, shared or joint; where the availability sentence holds, the declared B05 makes every family counted as first typed counted as ruled; the free pair and the twins are not counted; a counted pair with a joint record exists
inputs_revision: 2026-11-14.1
mathlib_rev: 0df444a360eaa60ab8c11dca51a86af692955474
source: the author, 2026-11-15 06:17 HST: "A" (RULING_counted_includes_own_record_2026-11-15).
 Def_APFPaper5_K1_Counted, Def_APFPaper5_K1_LedgerPartyScore. This seat: ledger_party_score_meets_K1
 (pass 40), private_positive_record_of_floor (pass 26), the three ledgers of passes 40 to 42.
standing: THEOREMS ON DEFINITIONS, on a record ledger (not installed).
 - counted_family_meets_K1 consumes NO declared input. It follows from what "counted" means as ruled. The
   eight do their work in showing that a family is counted.
 - counted_of_available consumes the declared form of B05 as a hypothesis and the availability sentence
   (the author's call 4 of 2026-11-14 19:57 HST; not installed).
what this file says:
 - counted_family_meets_K1: K1's typed conditions for the ruled score of any counted family.
 - hasOwnPaidRecord_of_available, counted_of_available: where availability holds (so no joint record),
   the declared B05 gives each member of a family counted as first typed a record of its own that costs
   something. So nothing counted before is lost there.
 - FreePair.not_counted, Twins.not_counted: what the ruling rules out.
 - PaidPair.counted_pair_meets_K1: a record ledger with a joint record on which the declared B05 holds,
   the pair is counted, and so K1's typed conditions hold for the ruled score.
what this file does NOT say:
 - That a region's distinctions are counted where a joint record is present. The witness is one ledger.
 - That any of this holds in a world meeting the eight. None is built.
 - Anything about orientation or the role exchange, which is the identity throughout. K3's.
 - No lane. No claim that the transfer is forced, that the carrier gap is closed or narrowed, or that Born
   is derived.
axioms: within propext, Classical.choice, Quot.sound. No sorry.
-/























set_option autoImplicit false

open APFPaper1 APFPaper1.Source

namespace APFPaper5.K1

section
variable {D P Record : Type*} {ι : Type*} [Fintype ι] [DecidableEq ι] [DecidableEq D]

/-- K1's typed conditions for the ruled score of a counted family, shared or joint. -/
theorem counted_family_meets_K1_p2mProof [Fintype Record] (L : RecordLedger D P Record) (tested : D → Prop)
    (C : ℝ) (dist : ι → D) (h : Counted L tested C dist) :
    IsBilinear (VP := ι → ℝ) (VE := ι → ℝ) (tableForm (ledgerPartyScore L dist)) ∧
      FaithfulNonnegDiagonal (tableForm (ledgerPartyScore L dist)) (LinearEquiv.refl ℝ (ι → ℝ)) :=
  APFPaper5.K1.ledger_party_score_meets_K1_explicit L dist h.2

/-- Where the availability sentence holds, the declared B05 gives each member of a family counted as
first typed a record of its own that costs something. -/
theorem hasOwnPaidRecord_of_available_p2mProof [DecidableEq Record] (L : RecordLedger D P Record)
    (tested : D → Prop) (C eps : ℝ)
    (hB05 : APFB05.MarginalFloor (Context := Unit) (D := fun _ => D) (P := fun _ => P)
      (R := fun _ => Finset Record) (Record := fun _ => Record) (fun _ => L.wholeResource)
      (fun _ => L.calibration) (fun _ => L.maintained) (fun _ => L.sufficient)
      (fun _ => L.usesToRealize) (fun _ => tested) (fun _ => C) (fun _ => eps))
    (havail : LedgerAvailable L C) (dist : ι → D) (hcounted : LedgerCounted L tested C dist) :
    HasOwnPaidRecord L dist := by
  intro i
  obtain ⟨hadm, htest, hnov⟩ := hcounted
  have hins : insert (dist i) ((Finset.univ.erase i).image dist) = Finset.univ.image dist := by
    rw [← Finset.image_insert, Finset.insert_erase (Finset.mem_univ i)]
  have hrest : familyAdmissible L.wholeResource L.calibration L.maintained L.sufficient
      L.usesToRealize C ((Finset.univ.erase i).image dist) :=
    APFB05.familyAdmissible_of_subset L.wholeResource L.calibration L.maintained L.sufficient
      L.usesToRealize (Finset.image_subset_image (Finset.erase_subset _ _)) hadm
  have hfull : familyAdmissible L.wholeResource L.calibration L.maintained L.sufficient
      L.usesToRealize C (insert (dist i) ((Finset.univ.erase i).image dist)) := by
    rw [hins]
    exact hadm
  obtain ⟨a, ha, hnot, hpos⟩ := private_positive_record_of_floor L.wholeResource L.calibration
    L.maintained L.sufficient L.usesToRealize L.kept L.needsFin L.cost L.bill_eq_sum
    L.maintained_eq_kept L.needsFin_subset_of_sufficient tested C eps hB05
    ((Finset.univ.erase i).image dist) (dist i) (htest i) hrest hfull (hnov i) (havail _ hrest)
    (havail _ hfull)
  refine ⟨a, hpos, APFPaper5.K1.memberNeeds_subset_familyNeeds_explicit L (Finset.mem_singleton_self _) ha, ?_⟩
  rw [APFPaper5.K1.familyNeeds_eq_of_exactly_served_explicit L _ (havail _ hrest)]
  exact fun h => hnot (Finset.mem_coe.mp h)

/-- Where the availability sentence holds, a family counted as first typed is counted as ruled. -/
theorem counted_of_available_p2mProof [DecidableEq Record] (L : RecordLedger D P Record)
    (tested : D → Prop) (C eps : ℝ)
    (hB05 : APFB05.MarginalFloor (Context := Unit) (D := fun _ => D) (P := fun _ => P)
      (R := fun _ => Finset Record) (Record := fun _ => Record) (fun _ => L.wholeResource)
      (fun _ => L.calibration) (fun _ => L.maintained) (fun _ => L.sufficient)
      (fun _ => L.usesToRealize) (fun _ => tested) (fun _ => C) (fun _ => eps))
    (havail : LedgerAvailable L C) (dist : ι → D) (hcounted : LedgerCounted L tested C dist) :
    Counted L tested C dist :=
  ⟨hcounted, hasOwnPaidRecord_of_available_p2mProof L tested C eps hB05 havail dist hcounted⟩

end

/-- The free pair is not a counted family. -/
theorem FreePair.not_counted_p2mProof :
    ¬ Counted FreePair.ledger (fun _ => True) 1 (fun i : Fin 2 => i) := fun h =>
  FreePair.party_score_not_faithful
    (counted_family_meets_K1_p2mProof FreePair.ledger (fun _ => True) 1 (fun i : Fin 2 => i) h).2

/-- The twins are not a counted family. -/
theorem Twins.not_counted_p2mProof :
    ¬ Counted Twins.ledger (fun _ => True) 2 (fun i : Fin 2 => i) := fun h =>
  Twins.party_score_not_faithful
    (counted_family_meets_K1_p2mProof Twins.ledger (fun _ => True) 2 (fun i : Fin 2 => i) h).2

/-- A counted pair with a joint record: K1's typed conditions hold for its ruled score. -/
theorem PaidPair.counted_pair_meets_K1_p2mProof :
    IsBilinear (VP := Fin 2 → ℝ) (VE := Fin 2 → ℝ)
        (tableForm (ledgerPartyScore PaidPair.ledger (fun i : Fin 2 => i))) ∧
      FaithfulNonnegDiagonal (tableForm (ledgerPartyScore PaidPair.ledger (fun i : Fin 2 => i)))
        (LinearEquiv.refl ℝ (Fin 2 → ℝ)) :=
  counted_family_meets_K1_p2mProof PaidPair.ledger (fun _ => True) 3 (fun i : Fin 2 => i)
    PaidPair.pair_is_counted

end APFPaper5.K1


universe apfNative_u_1 apfNative_u_2 apfNative_u_3 apfNative_u_4
theorem solution :
∀ {D : Type apfNative_u_1} {P : Type apfNative_u_2} {Record : Type apfNative_u_3} {ι : Type apfNative_u_4}
  [inst : Fintype.{apfNative_u_4} ι] [inst_1 : DecidableEq.{apfNative_u_4 + 1} ι]
  [inst_2 : DecidableEq.{apfNative_u_1 + 1} D] [inst_3 : DecidableEq.{apfNative_u_3 + 1} Record]
  (L : APFPaper1.RecordLedger.{apfNative_u_1, apfNative_u_2, apfNative_u_3} D P Record) (tested : D → Prop)
  (C eps : Real)
  (hB05 :
    @APFB05.MarginalFloor.{0, apfNative_u_1, apfNative_u_2, apfNative_u_3, apfNative_u_3} Unit (fun (x : Unit) => D)
      (fun (x : Unit) => P) (fun (x : Unit) => Finset.{apfNative_u_3} Record) (fun (x : Unit) => Record)
      (fun (g : Unit) => inst_2)
      (fun (x : Unit) =>
        @APFPaper1.RecordLedger.wholeResource.{apfNative_u_1, apfNative_u_2, apfNative_u_3} D P Record L)
      (fun (x : Unit) => @APFPaper1.RecordLedger.calibration.{apfNative_u_1, apfNative_u_2, apfNative_u_3} D P Record L)
      (fun (x : Unit) => @APFPaper1.RecordLedger.maintained.{apfNative_u_1, apfNative_u_2, apfNative_u_3} D P Record L)
      (fun (x : Unit) => @APFPaper1.RecordLedger.sufficient.{apfNative_u_1, apfNative_u_2, apfNative_u_3} D P Record L)
      (fun (x : Unit) =>
        @APFPaper1.RecordLedger.usesToRealize.{apfNative_u_1, apfNative_u_2, apfNative_u_3} D P Record L)
      (fun (x : Unit) => tested) (fun (x : Unit) => C) fun (x : Unit) => eps)
  (havail : @APFPaper5.K1.LedgerAvailable.{apfNative_u_1, apfNative_u_2, apfNative_u_3} D P Record inst_3 L C)
  (dist : ι → D)
  (hcounted :
    @APFPaper5.K1.LedgerCounted.{apfNative_u_1, apfNative_u_2, apfNative_u_3, apfNative_u_4} D P Record ι inst inst_1
      inst_2 L tested C dist),
  @APFPaper5.K1.HasOwnPaidRecord.{apfNative_u_1, apfNative_u_2, apfNative_u_3, apfNative_u_4} D P Record ι inst inst_1
    inst_2 L dist := by
  exact @APFPaper5.K1.hasOwnPaidRecord_of_available_p2mProof
