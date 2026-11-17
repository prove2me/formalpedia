-- Prove2me | solution 1 for APFPaper5.K1.memberNeeds_subset_familyNeeds_explicit
-- status  : ACCEPTED   (prove)
-- author  : @FiniteUniverse
-- created : 2026-11-16T15:44:31.839395+00:00
-- url     : https://prove2.me/submissions/aa370e18-8d95-4371-b9eb-a360fb071249

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
import Definitions.Def_APFPaper5_K1_LedgerPartyScore
import Definitions.Def_APFPaper5_K1_LedgerScore
import Theorems.Thm_APFPaper5_K1_partyTo_book_iff
import Theorems.Thm_APFPaper5_K1_partyScore_book
import Theorems.Thm_APFPaper5_K1_partyScore_book_meets_K1
import Theorems.Thm_APFPaper5_K1_partyScore_book_faithful_iff
import Theorems.Thm_APFPaper5_K1_sharedCost_eq_partyScore_of_no_joint
import Definitions.Def_APFPaper5_K1_interface_bridge_Vocabulary
import Theorems.Thm_APFPaper5_K1_interface_region_satisfies_K1_of_floor
import Theorems.Thm_APFPaper1_RecordLedger_bill_eq_sum
import Theorems.Thm_APFPaper1_RecordLedger_maintained_eq_kept
import Theorems.Thm_APFPaper1_RecordLedger_needsFin_subset_of_sufficient
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
name: APFPaper5_K1_ledger_party_score
title: K1's typed conditions for the party score of any keeping rule, from one premise; on a record ledger that premise reads "each distinction, held alone, needs a record of positive cost that the others together do not need"; where the availability sentence holds it follows from the declared B05 for a counted family
inputs_revision: 2026-11-14.1
mathlib_rev: 0df444a360eaa60ab8c11dca51a86af692955474
source: the author, 2026-11-15 05:07 HST: "1 Confirmed, please proceed" (items 4 and 5 of this seat's list
 of 05:00 HST). Def_APFPaper5_K1_LedgerPartyScore, Def_APFPaper5_K1_PartyScore, Def_APFPaper5_K1_LedgerScore
 (LedgerAvailable, LedgerCounted). Builder seat: record_book_table_satisfies_K1. This seat:
 atomTable_faithful_iff (pass 18), private_positive_record_of_floor (pass 26).
standing: THEOREMS ON DEFINITIONS, on a record ledger (not installed).
 - partyScore_meets_K1_of_own_record and ledger_party_score_meets_K1 carry ONE premise. On a record ledger
   "no record of negative cost" is no premise: a record's cost is typed nonnegative, as the declared
   calibration is.
 - ledger_counted_family_party_score_satisfies_K1 consumes the declared form of B05 as a hypothesis and
   the availability sentence. Availability is the author's call 4 of 2026-11-14 19:57 HST (to be an input
   line, his to install); it is NOT installed. Where it holds a family needs exactly what its members
   need, so there is no joint record.
what this file does NOT say:
 - That the one premise follows from the declared B05 and "counted" where joint records are present. It
   does not: Thm_APFPaper5_K1_free_pair_paid_relation is a record ledger on which B05 holds as declared,
   the pair is counted, and the party score is not faithful.
 - Anything about source data that has no record costs. The pass-29 theorem covers that case in the words
   of the shared cost and cannot be restated with this score.
 - No lane. No claim that the transfer is forced, that the carrier gap is closed or narrowed, or that Born
   is derived.
axioms: within propext, Classical.choice, Quot.sound. No sorry.
-/
















set_option autoImplicit false

open APFPaper1 APFPaper1.Source

namespace APFPaper5.K1

/-! ### Any keeping rule -/

section AnyRule
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {W : Type*} [Fintype W]

/-- K1's typed conditions for the party score of any keeping rule: no record of negative cost, and each
mark has a record of positive cost to which it alone is party. -/
theorem partyScore_meets_K1_of_own_record (w : W → ℝ) (hw : ∀ a, 0 ≤ w a)
    (keeps : Finset ι → W → Bool)
    (hown : ∀ i, ∃ a, 0 < w a ∧ PartyTo keeps i a ∧ ∀ j, PartyTo keeps j a → j = i) :
    IsBilinear (VP := ι → ℝ) (VE := ι → ℝ) (tableForm (partyScore w keeps)) ∧
      FaithfulNonnegDiagonal (tableForm (partyScore w keeps)) (LinearEquiv.refl ℝ (ι → ℝ)) := by
  have hsingle : ∀ i, ∃ a, 0 < w a ∧ ∀ j, partyMark keeps j a = decide (j = i) := by
    intro i
    obtain ⟨a, hpos, hi, honly⟩ := hown i
    refine ⟨a, hpos, fun j => ?_⟩
    unfold partyMark
    by_cases hji : j = i
    · rw [hji, @decide_eq_true _ (Classical.propDecidable _) hi]
      exact (decide_eq_true rfl).symm
    · rw [@decide_eq_false _ (Classical.propDecidable _) (fun h => hji (honly j h))]
      exact (decide_eq_false hji).symm
  have h : partyScore w keeps = atomTable w (partyMark keeps) := rfl
  rw [h]
  exact record_book_table_satisfies_K1 w hw (partyMark keeps) hsingle

/-- The exact condition, for any keeping rule: the diagonal is nonnegative and faithful exactly when no
nonzero combination of the marks is cancelled by every record of positive cost. -/
theorem partyScore_faithful_iff (w : W → ℝ) (hw : ∀ a, 0 ≤ w a) (keeps : Finset ι → W → Bool) :
    FaithfulNonnegDiagonal (tableForm (partyScore w keeps)) (LinearEquiv.refl ℝ (ι → ℝ)) ↔
      ∀ x : ι → ℝ, (∀ a, 0 < w a → ∑ i, x i * ind (partyMark keeps i a) = 0) → x = 0 := by
  have h : partyScore w keeps = atomTable w (partyMark keeps) := rfl
  rw [h]
  exact atomTable_faithful_iff w hw (partyMark keeps)

end AnyRule

/-! ### On a record ledger -/

section Ledger
variable {D P Record : Type*}

/-- A larger family needs at least what a smaller one needs. -/
theorem familyNeeds_mono (L : RecordLedger D P Record) {S T : Finset D} (h : S ⊆ T) :
    familyNeeds L S ⊆ familyNeeds L T := by
  intro a ha p hp
  exact ha p (fun d hd => hp d (h hd))

/-- What a member needs, its family needs. -/
theorem memberNeeds_subset_familyNeeds (L : RecordLedger D P Record) {S : Finset D} {d : D}
    (hd : d ∈ S) {a : Record} (ha : a ∈ L.needsFin d) : a ∈ familyNeeds L S := by
  intro p hp
  obtain ⟨sigma, hsub, hsuff, _⟩ := hp d hd
  have h1 : a ∈ sigma := L.needsFin_subset_of_sufficient p sigma d hsuff (Finset.mem_coe.mpr ha)
  exact hsub h1

/-- Where some protocol keeps exactly what the members need and serves the family, the family needs
exactly what its members need. -/
theorem familyNeeds_eq_of_exactly_served [DecidableEq Record] (L : RecordLedger D P Record)
    (S : Finset D)
    (hS : ∃ p : P, L.kept p = S.biUnion L.needsFin ∧ ∀ d ∈ S, ∃ sigma : Set Record,
      sigma ⊆ L.maintained p ∧ L.sufficient p sigma d ∧ L.usesToRealize p d sigma) :
    familyNeeds L S = (↑(S.biUnion L.needsFin) : Set Record) := by
  obtain ⟨p, hk, hserve⟩ := hS
  ext a
  constructor
  · intro ha
    have h := ha p hserve
    rw [hk] at h
    exact Finset.mem_coe.mpr h
  · intro ha
    obtain ⟨d, hd, had⟩ := Finset.mem_biUnion.mp (Finset.mem_coe.mp ha)
    exact memberNeeds_subset_familyNeeds L hd had

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [DecidableEq D]

/-- A record that a distinction needs when held alone and that the others together do not need: that
distinction is party to it and no other is. -/
theorem own_record_of_alone_not_rest (L : RecordLedger D P Record) (dist : ι → D) (i : ι) (a : Record)
    (halone : a ∈ familyNeeds L {dist i})
    (hrest : a ∉ familyNeeds L ((Finset.univ.erase i).image dist)) :
    PartyTo (ledgerKeeps L dist) i a ∧ ∀ j, PartyTo (ledgerKeeps L dist) j a → j = i := by
  constructor
  · refine ⟨∅, ?_, ?_⟩
    · unfold ledgerKeeps
      apply @decide_eq_true _ (Classical.propDecidable _)
      have h : (insert i (∅ : Finset ι)).image dist = {dist i} := by simp
      rw [h]
      exact halone
    · unfold ledgerKeeps
      apply @decide_eq_false _ (Classical.propDecidable _)
      intro h
      exact hrest (familyNeeds_mono L (Finset.image_subset_image (Finset.empty_subset _)) h)
  · rintro j ⟨S, h1, h2⟩
    unfold ledgerKeeps at h1 h2
    have h1' : a ∈ familyNeeds L ((insert j S).image dist) :=
      @of_decide_eq_true _ (Classical.propDecidable _) h1
    have h2' : a ∉ familyNeeds L (S.image dist) :=
      @of_decide_eq_false _ (Classical.propDecidable _) h2
    by_contra hji
    by_cases hiS : i ∈ S
    · exact h2' (familyNeeds_mono L
        (Finset.singleton_subset_iff.mpr (Finset.mem_image_of_mem dist hiS)) halone)
    · have hsub : insert j S ⊆ Finset.univ.erase i := by
        intro k hk
        rcases Finset.mem_insert.mp hk with h | h
        · exact Finset.mem_erase.mpr ⟨by rw [h]; exact hji, Finset.mem_univ _⟩
        · exact Finset.mem_erase.mpr ⟨fun e => hiS (e ▸ h), Finset.mem_univ _⟩
      exact hrest (familyNeeds_mono L (Finset.image_subset_image hsub) h1')

variable [Fintype Record]

/-- K1's typed conditions for the ledger form of the score, from one premise: each distinction, held
alone, needs a record of positive cost that the others together do not need. -/
theorem ledger_party_score_meets_K1 (L : RecordLedger D P Record) (dist : ι → D)
    (hown : ∀ i, ∃ a, 0 < L.cost a ∧ a ∈ familyNeeds L {dist i} ∧
      a ∉ familyNeeds L ((Finset.univ.erase i).image dist)) :
    IsBilinear (VP := ι → ℝ) (VE := ι → ℝ) (tableForm (ledgerPartyScore L dist)) ∧
      FaithfulNonnegDiagonal (tableForm (ledgerPartyScore L dist)) (LinearEquiv.refl ℝ (ι → ℝ)) := by
  have h : ledgerPartyScore L dist =
      partyScore (fun a => ((L.cost a : NNReal) : ℝ)) (ledgerKeeps L dist) := rfl
  rw [h]
  apply partyScore_meets_K1_of_own_record
  · intro a
    exact NNReal.coe_nonneg _
  · intro i
    obtain ⟨a, hpos, h1, h2⟩ := hown i
    have hp := own_record_of_alone_not_rest L dist i a h1 h2
    exact ⟨a, NNReal.coe_pos.mpr hpos, hp.1, hp.2⟩

/-- Where the availability sentence holds, the one premise follows from the declared B05 for a counted
family, so the ledger form of the score meets K1's typed conditions. -/
theorem ledger_counted_family_party_score_satisfies_K1 [DecidableEq Record]
    (L : RecordLedger D P Record) (tested : D → Prop) (C eps : ℝ)
    (hB05 : APFB05.MarginalFloor (Context := Unit) (D := fun _ => D) (P := fun _ => P)
      (R := fun _ => Finset Record) (Record := fun _ => Record) (fun _ => L.wholeResource)
      (fun _ => L.calibration) (fun _ => L.maintained) (fun _ => L.sufficient)
      (fun _ => L.usesToRealize) (fun _ => tested) (fun _ => C) (fun _ => eps))
    (havail : LedgerAvailable L C) (dist : ι → D) (hcounted : LedgerCounted L tested C dist) :
    IsBilinear (VP := ι → ℝ) (VE := ι → ℝ) (tableForm (ledgerPartyScore L dist)) ∧
      FaithfulNonnegDiagonal (tableForm (ledgerPartyScore L dist)) (LinearEquiv.refl ℝ (ι → ℝ)) := by
  apply ledger_party_score_meets_K1
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
  refine ⟨a, hpos, memberNeeds_subset_familyNeeds L (Finset.mem_singleton_self _) ha, ?_⟩
  rw [familyNeeds_eq_of_exactly_served L _ (havail _ hrest)]
  exact fun h => hnot (Finset.mem_coe.mp h)

end Ledger

end APFPaper5.K1


universe apfNative_u_1 apfNative_u_2 apfNative_u_3
theorem solution :
∀ {D : Type apfNative_u_1} {P : Type apfNative_u_2} {Record : Type apfNative_u_3}
  (L : APFPaper1.RecordLedger.{apfNative_u_1, apfNative_u_2, apfNative_u_3} D P Record) {S : Finset.{apfNative_u_1} D}
  {d : D}
  (hd :
    @Membership.mem.{apfNative_u_1, apfNative_u_1} D (Finset.{apfNative_u_1} D)
      (@SetLike.instMembership.{apfNative_u_1, apfNative_u_1} (Finset.{apfNative_u_1} D) D
        (@Finset.instSetLike.{apfNative_u_1} D))
      S d)
  {a : Record}
  (ha :
    @Membership.mem.{apfNative_u_3, apfNative_u_3} Record (Finset.{apfNative_u_3} Record)
      (@SetLike.instMembership.{apfNative_u_3, apfNative_u_3} (Finset.{apfNative_u_3} Record) Record
        (@Finset.instSetLike.{apfNative_u_3} Record))
      (@APFPaper1.RecordLedger.needsFin.{apfNative_u_1, apfNative_u_2, apfNative_u_3} D P Record L d) a),
  @Membership.mem.{apfNative_u_3, apfNative_u_3} Record (Set.{apfNative_u_3} Record)
    (@Set.instMembership.{apfNative_u_3} Record)
    (@APFPaper5.K1.familyNeeds.{apfNative_u_1, apfNative_u_2, apfNative_u_3} D P Record L S) a := by
  exact @APFPaper5.K1.memberNeeds_subset_familyNeeds
