-- Prove2me | solution 1 for APFPaper5.K1.leastBill_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @FiniteUniverse
-- created : 2026-11-16T16:48:55.039192+00:00
-- url     : https://prove2.me/submissions/d50acec5-2721-4200-8c14-3bbc62037a6f

/-
APF Foundation Ledger — theorem node DRAFT (Claude seat, session EthanBrooke-01WrrBvv, 2026-11-15; not
 gated, not reviewed, not released, not built in the ledger repo)
name: APFPaper5_K1_on_source_data
title: On any source data of the declared forms and for any cost of records that is never negative, the table of scores of a counted family is bilinear with a faithful nonnegative diagonal; the record ledger is one case
inputs_revision: 2026-11-14.1
mathlib_rev: 0df444a360eaa60ab8c11dca51a86af692955474
source: the author, 2026-11-15 06:55 HST: "1", in answer to this seat's "1. Derive the record ledger item by
 item from the eight." And 07:00 HST: "Would like the goal here to be adding the work to our p2m
 foundation… thinking it would be ideal to bolt on the Ks to that model? The goal is a P2m that takes us
 from first principals to quantum and gauge form". Read as: state the K layer on the foundation's own
 data. RULING_ledger_item_by_item_and_the_goal_2026-11-15.
 The score and "counted" are the author's rulings B and A, typed in Def_APFPaper5_K1_SourcePartyScore.
consumes_inputs: none. No declared input is used as a hypothesis and none is proved. The statements hold by
 what the score and "counted" mean, together with the builder seat's theorem about record books
 (record_book_table_satisfies_K1).
what changed against pass 42 (counted_family_meets_K1): the record ledger is gone from the statement. The
 data are the declared forms' own: what a protocol maintains, which sets of records are sufficient, which
 it uses. No law on a bill is used anywhere: the bill enters only through "within capacity" and
 "support-novel", as in the declared B05.
theorems:
 - (sourceNeeds_mono) a larger family needs at least what a smaller one needs.
 - (source_own_record_of_alone_not_rest) a record a distinction needs alone and the others together do not
   need: that distinction is party to it and no other is.
 - (source_party_score_meets_K1) K1's typed conditions from the own-record clause, for any cost of records
   that is never negative.
 - (source_counted_family_meets_K1) the same for a counted family.
 - (leastBill_nonneg, leastBill_le_bill, le_leastBill, leastBill_pos_iff) the least bill is never negative;
   a protocol maintaining a record bills at least it; a record costs something in this sense exactly when
   some protocol maintains it and all that do bill at least one fixed positive amount.
 - (source_counted_family_meets_K1_leastBill) K1's typed conditions with each record costing its least
   bill. RESTS ON leastBill, WHICH IS NOT RULED.
 - (familyNeeds_eq_sourceNeeds, ledgerPartyScore_eq_source, counted_iff_sourceCounted) on a record ledger
   the needs, the score and "counted" are the source-data ones at the ledger's costs. The first two hold by
   definition.
 - (cost_le_leastBill, leastBill_eq_cost_of_kept_alone) the ledger's cost of a record against its least
   bill.
 - (sourceCounted_leastBill_of_counted) a family counted on a record ledger is counted on the ledger's
   source data with least bills.
 - (PaidPair.source_counted_pair_meets_K1) not empty with a joint record present: the paid pair of pass 42.
not claimed:
 - K1 as Paper 5 states it. The role exchange is the identity and orientation is not ruled (K3). No
   completed ordered score is constructed.
 - That the declared B05 makes a family counted on source data. On a record ledger with the availability
   sentence it does (counted_of_available); the twins show it can fail without it.
 - That a context has finitely many records. It is a typing hypothesis here ([Fintype Record]).
 - No lane. No claim that the transfer is forced, that the carrier gap is closed or narrowed, or that Born
   is derived.
axioms: within propext, Classical.choice, Quot.sound. No sorry.
-/
import Definitions.Def_APFPaper5_K1_SourcePartyScore
import Definitions.Def_APFPaper5_K1_Counted
import Theorems.Thm_APFPaper5_K1_partyScore_meets_K1_of_own_record
import Theorems.Thm_APFPaper5_K1_memberNeeds_subset_familyNeeds_explicit
import Theorems.Thm_APFPaper5_K1_familyNeeds_eq_of_exactly_served_explicit
import Theorems.Thm_APFPaper5_K1_ledger_party_score_meets_K1_explicit
import Theorems.Thm_APFPaper5_K1_ledger_counted_family_party_score_satisfies_K1_explicit
import Definitions.Def_APFPaper5_K1_counted_pair_with_relation_Vocabulary
import Theorems.Thm_APFPaper5_K1_PaidPair_b05_holds
import Theorems.Thm_APFPaper5_K1_PaidPair_pair_is_counted
import Theorems.Thm_APFPaper5_K1_PaidPair_relation_is_joint

set_option autoImplicit false

open APFPaper1 APFPaper1.Source

namespace APFPaper5.K1

/-! ### On any source data of the declared forms -/

section Source

variable {D P R Record : Type*}

/-- A larger family needs at least what a smaller one needs. -/
theorem sourceNeeds_mono (maintained : P → Set Record) (sufficient : P → Set Record → D → Prop)
    (usesToRealize : P → D → Set Record → Prop) {S T : Finset D} (h : S ⊆ T) :
    sourceNeeds maintained sufficient usesToRealize S ⊆
      sourceNeeds maintained sufficient usesToRealize T := by
  intro a ha p hp
  exact ha p (fun d hd => hp d (h hd))

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [DecidableEq D]

/-- A record that a distinction needs when held alone and that the others together do not need: that
distinction is party to it and no other is. -/
theorem source_own_record_of_alone_not_rest (maintained : P → Set Record)
    (sufficient : P → Set Record → D → Prop) (usesToRealize : P → D → Set Record → Prop)
    (dist : ι → D) (i : ι) (a : Record)
    (halone : a ∈ sourceNeeds maintained sufficient usesToRealize {dist i})
    (hrest : a ∉ sourceNeeds maintained sufficient usesToRealize ((Finset.univ.erase i).image dist)) :
    PartyTo (sourceKeeps maintained sufficient usesToRealize dist) i a ∧
      ∀ j, PartyTo (sourceKeeps maintained sufficient usesToRealize dist) j a → j = i := by
  constructor
  · refine ⟨∅, ?_, ?_⟩
    · unfold sourceKeeps
      apply @decide_eq_true _ (Classical.propDecidable _)
      have h : (insert i (∅ : Finset ι)).image dist = {dist i} := by simp
      rw [h]
      exact halone
    · unfold sourceKeeps
      apply @decide_eq_false _ (Classical.propDecidable _)
      intro h
      exact hrest (sourceNeeds_mono maintained sufficient usesToRealize
        (Finset.image_subset_image (Finset.empty_subset _)) h)
  · rintro j ⟨S, h1, h2⟩
    unfold sourceKeeps at h1 h2
    have h1' : a ∈ sourceNeeds maintained sufficient usesToRealize ((insert j S).image dist) :=
      @of_decide_eq_true _ (Classical.propDecidable _) h1
    have h2' : a ∉ sourceNeeds maintained sufficient usesToRealize (S.image dist) :=
      @of_decide_eq_false _ (Classical.propDecidable _) h2
    by_contra hji
    by_cases hiS : i ∈ S
    · exact h2' (sourceNeeds_mono maintained sufficient usesToRealize
        (Finset.singleton_subset_iff.mpr (Finset.mem_image_of_mem dist hiS)) halone)
    · have hsub : insert j S ⊆ Finset.univ.erase i := by
        intro k hk
        rcases Finset.mem_insert.mp hk with h | h
        · exact Finset.mem_erase.mpr ⟨by rw [h]; exact hji, Finset.mem_univ _⟩
        · exact Finset.mem_erase.mpr ⟨fun e => hiS (e ▸ h), Finset.mem_univ _⟩
      exact hrest (sourceNeeds_mono maintained sufficient usesToRealize
        (Finset.image_subset_image hsub) h1')

variable [Fintype Record]

/-- K1's typed conditions on source data, for any cost of records that is never negative, from the
own-record clause. No law on a bill is used. -/
theorem source_party_score_meets_K1 (w : Record → ℝ) (hw : ∀ a, 0 ≤ w a)
    (maintained : P → Set Record) (sufficient : P → Set Record → D → Prop)
    (usesToRealize : P → D → Set Record → Prop) (dist : ι → D)
    (hown : SourceHasOwnPaidRecord w maintained sufficient usesToRealize dist) :
    IsBilinear (VP := ι → ℝ) (VE := ι → ℝ)
        (tableForm (sourcePartyScore w maintained sufficient usesToRealize dist)) ∧
      FaithfulNonnegDiagonal
        (tableForm (sourcePartyScore w maintained sufficient usesToRealize dist))
        (LinearEquiv.refl ℝ (ι → ℝ)) := by
  have h : sourcePartyScore w maintained sufficient usesToRealize dist =
      partyScore w (sourceKeeps maintained sufficient usesToRealize dist) := rfl
  rw [h]
  apply partyScore_meets_K1_of_own_record w hw
  intro i
  obtain ⟨a, hpos, h1, h2⟩ := hown i
  have hp := source_own_record_of_alone_not_rest maintained sufficient usesToRealize dist i a h1 h2
  exact ⟨a, hpos, hp.1, hp.2⟩

/-- K1's typed conditions for the ruled score of a counted family, on any source data of the declared
forms and for any cost of records that is never negative. -/
theorem source_counted_family_meets_K1 (w : Record → ℝ) (hw : ∀ a, 0 ≤ w a)
    (wholeResource : P → R) (calibration : R → NNReal) (maintained : P → Set Record)
    (sufficient : P → Set Record → D → Prop) (usesToRealize : P → D → Set Record → Prop)
    (tested : D → Prop) (C : ℝ) (dist : ι → D)
    (h : SourceCounted w wholeResource calibration maintained sufficient usesToRealize tested C
      dist) :
    IsBilinear (VP := ι → ℝ) (VE := ι → ℝ)
        (tableForm (sourcePartyScore w maintained sufficient usesToRealize dist)) ∧
      FaithfulNonnegDiagonal
        (tableForm (sourcePartyScore w maintained sufficient usesToRealize dist))
        (LinearEquiv.refl ℝ (ι → ℝ)) :=
  source_party_score_meets_K1 w hw maintained sufficient usesToRealize dist h.2

end Source

/-! ### The least bill: a cost every record carries on any source data -/

section LeastBill

variable {P R Record : Type*}

/-- The least bill of a record is never negative. -/
theorem leastBill_nonneg_p2mProof (wholeResource : P → R) (calibration : R → NNReal)
    (maintained : P → Set Record) (a : Record) :
    0 ≤ leastBill wholeResource calibration maintained a := by
  apply Real.sInf_nonneg
  rintro c ⟨p, _, rfl⟩
  exact NNReal.coe_nonneg _

/-- A protocol that maintains a record bills at least the record's least bill. -/
theorem leastBill_le_bill (wholeResource : P → R) (calibration : R → NNReal)
    (maintained : P → Set Record) (a : Record) (p : P) (hp : a ∈ maintained p) :
    leastBill wholeResource calibration maintained a ≤ (calibration (wholeResource p) : ℝ) := by
  apply csInf_le
  · refine ⟨0, ?_⟩
    rintro c ⟨q, _, rfl⟩
    exact NNReal.coe_nonneg _
  · exact ⟨p, hp, rfl⟩

/-- If some protocol maintains the record and every protocol that maintains it bills at least `e`, the
record's least bill is at least `e`. -/
theorem le_leastBill (wholeResource : P → R) (calibration : R → NNReal)
    (maintained : P → Set Record) (a : Record) (e : ℝ) (hne : ∃ p : P, a ∈ maintained p)
    (hbd : ∀ p : P, a ∈ maintained p → e ≤ (calibration (wholeResource p) : ℝ)) :
    e ≤ leastBill wholeResource calibration maintained a := by
  apply le_csInf
  · obtain ⟨p, hp⟩ := hne
    exact ⟨_, p, hp, rfl⟩
  · rintro c ⟨p, hp, rfl⟩
    exact hbd p hp

/-- A record costs something, in the least-bill sense, exactly when some protocol maintains it and the
protocols that maintain it all bill at least one fixed positive amount. -/
theorem leastBill_pos_iff (wholeResource : P → R) (calibration : R → NNReal)
    (maintained : P → Set Record) (a : Record) :
    0 < leastBill wholeResource calibration maintained a ↔
      (∃ p : P, a ∈ maintained p) ∧
        ∃ e : ℝ, 0 < e ∧ ∀ p : P, a ∈ maintained p → e ≤ (calibration (wholeResource p) : ℝ) := by
  constructor
  · intro hpos
    refine ⟨?_, leastBill wholeResource calibration maintained a, hpos,
      fun p hp => leastBill_le_bill wholeResource calibration maintained a p hp⟩
    by_contra hnone
    have hempty : {c : ℝ | ∃ p : P, a ∈ maintained p ∧ (calibration (wholeResource p) : ℝ) = c} = ∅ := by
      ext c
      constructor
      · rintro ⟨p, hp, _⟩
        exact hnone ⟨p, hp⟩
      · intro h
        exact absurd h (Set.notMem_empty c)
    have hzero : leastBill wholeResource calibration maintained a = 0 := by
      unfold leastBill
      rw [hempty]
      exact Real.sInf_empty
    rw [hzero] at hpos
    exact lt_irrefl _ hpos
  · rintro ⟨hne, e, he, hbd⟩
    exact lt_of_lt_of_le he (le_leastBill wholeResource calibration maintained a e hne hbd)

variable {D : Type*} {ι : Type*} [Fintype ι] [DecidableEq ι] [DecidableEq D] [Fintype Record]

/-- K1's typed conditions for the ruled score of a counted family on any source data of the declared
forms, with each record costing its least bill. Nothing beyond the source data enters. -/
theorem source_counted_family_meets_K1_leastBill (wholeResource : P → R) (calibration : R → NNReal)
    (maintained : P → Set Record) (sufficient : P → Set Record → D → Prop)
    (usesToRealize : P → D → Set Record → Prop) (tested : D → Prop) (C : ℝ) (dist : ι → D)
    (h : SourceCounted (leastBill wholeResource calibration maintained) wholeResource calibration
      maintained sufficient usesToRealize tested C dist) :
    IsBilinear (VP := ι → ℝ) (VE := ι → ℝ)
        (tableForm (sourcePartyScore (leastBill wholeResource calibration maintained) maintained
          sufficient usesToRealize dist)) ∧
      FaithfulNonnegDiagonal
        (tableForm (sourcePartyScore (leastBill wholeResource calibration maintained) maintained
          sufficient usesToRealize dist))
        (LinearEquiv.refl ℝ (ι → ℝ)) :=
  source_counted_family_meets_K1 _ (APFPaper5.K1.leastBill_nonneg_p2mProof wholeResource calibration maintained)
    wholeResource calibration maintained sufficient usesToRealize tested C dist h

end LeastBill

/-! ### The record ledger is one case -/

section LedgerCase

variable {D P Record : Type*}

/-- On a record ledger, what a family needs is what it needs on the ledger's source data. -/
theorem familyNeeds_eq_sourceNeeds (L : RecordLedger D P Record) (S : Finset D) :
    familyNeeds L S = sourceNeeds L.maintained L.sufficient L.usesToRealize S := rfl

/-- On a record ledger, a record that some protocol keeps has a least bill of at least its cost. -/
theorem cost_le_leastBill (L : RecordLedger D P Record) (a : Record) (hne : ∃ p : P, a ∈ L.kept p) :
    ((L.cost a : NNReal) : ℝ) ≤ leastBill L.wholeResource L.calibration L.maintained a := by
  apply le_leastBill
  · obtain ⟨p, hp⟩ := hne
    exact ⟨p, Finset.mem_coe.mpr hp⟩
  · intro p hp
    rw [L.bill_eq_sum p]
    exact Finset.single_le_sum (f := fun r => ((L.cost r : NNReal) : ℝ))
      (fun r _ => NNReal.coe_nonneg _) (Finset.mem_coe.mp hp)

/-- On a record ledger, a record that some protocol keeps alone has a least bill equal to its cost. -/
theorem leastBill_eq_cost_of_kept_alone (L : RecordLedger D P Record) (a : Record)
    (halone : ∃ p : P, L.kept p = {a}) :
    leastBill L.wholeResource L.calibration L.maintained a = ((L.cost a : NNReal) : ℝ) := by
  obtain ⟨p, hp⟩ := halone
  have hmem : a ∈ L.kept p := by rw [hp]; exact Finset.mem_singleton_self a
  apply le_antisymm
  · have h := leastBill_le_bill L.wholeResource L.calibration L.maintained a p
      (Finset.mem_coe.mpr hmem)
    rw [L.bill_eq_sum p, hp, Finset.sum_singleton] at h
    exact h
  · exact cost_le_leastBill L a ⟨p, hmem⟩

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [DecidableEq D]

/-- The ledger form of the score is the score on the ledger's source data, at the ledger's costs. -/
theorem ledgerPartyScore_eq_source [Fintype Record] (L : RecordLedger D P Record) (dist : ι → D) :
    ledgerPartyScore L dist =
      sourcePartyScore (fun a => ((L.cost a : NNReal) : ℝ)) L.maintained L.sufficient
        L.usesToRealize dist := rfl

/-- Counted on a record ledger is counted on the ledger's source data, at the ledger's costs. -/
theorem counted_iff_sourceCounted (L : RecordLedger D P Record) (tested : D → Prop) (C : ℝ)
    (dist : ι → D) :
    Counted L tested C dist ↔
      SourceCounted (fun a => ((L.cost a : NNReal) : ℝ)) L.wholeResource L.calibration L.maintained
        L.sufficient L.usesToRealize tested C dist := by
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨h1, fun i => ?_⟩
    obtain ⟨a, hpos, ha, hb⟩ := h2 i
    exact ⟨a, NNReal.coe_pos.mpr hpos, ha, hb⟩
  · rintro ⟨h1, h2⟩
    refine ⟨h1, fun i => ?_⟩
    obtain ⟨a, hpos, ha, hb⟩ := h2 i
    exact ⟨a, NNReal.coe_pos.mp hpos, ha, hb⟩

/-- A family counted on a record ledger is counted on the ledger's source data with each record costing
its least bill: the ledger's costs are not needed to say it. -/
theorem sourceCounted_leastBill_of_counted (L : RecordLedger D P Record) (tested : D → Prop) (C : ℝ)
    (dist : ι → D) (h : Counted L tested C dist) :
    SourceCounted (leastBill L.wholeResource L.calibration L.maintained) L.wholeResource
      L.calibration L.maintained L.sufficient L.usesToRealize tested C dist := by
  obtain ⟨h1, h2⟩ := h
  refine ⟨h1, fun i => ?_⟩
  obtain ⟨a, hpos, ha, hb⟩ := h2 i
  refine ⟨a, ?_, ha, hb⟩
  obtain ⟨⟨p, hp⟩, _⟩ := h1.1
  have hserve : Serves L p {dist i} := by
    intro d hd
    rw [Finset.mem_singleton] at hd
    rw [hd]
    exact hp (dist i) (Finset.mem_image_of_mem dist (Finset.mem_univ i))
  have hkept : a ∈ L.kept p := ha p hserve
  exact lt_of_lt_of_le (NNReal.coe_pos.mpr hpos) (cost_le_leastBill L a ⟨p, hkept⟩)

end LedgerCase

/-- Not empty, with a joint record present: the paid pair is a counted family on its source data with
each record costing its least bill, and K1's typed conditions hold for its score there. -/
theorem PaidPair.source_counted_pair_meets_K1 :
    SourceCounted
        (leastBill PaidPair.ledger.wholeResource PaidPair.ledger.calibration
          PaidPair.ledger.maintained)
        PaidPair.ledger.wholeResource PaidPair.ledger.calibration PaidPair.ledger.maintained
        PaidPair.ledger.sufficient PaidPair.ledger.usesToRealize (fun _ => True) 3
        (fun i : Fin 2 => i) ∧
      (IsBilinear (VP := Fin 2 → ℝ) (VE := Fin 2 → ℝ)
          (tableForm (sourcePartyScore
            (leastBill PaidPair.ledger.wholeResource PaidPair.ledger.calibration
              PaidPair.ledger.maintained)
            PaidPair.ledger.maintained PaidPair.ledger.sufficient PaidPair.ledger.usesToRealize
            (fun i : Fin 2 => i))) ∧
        FaithfulNonnegDiagonal
          (tableForm (sourcePartyScore
            (leastBill PaidPair.ledger.wholeResource PaidPair.ledger.calibration
              PaidPair.ledger.maintained)
            PaidPair.ledger.maintained PaidPair.ledger.sufficient PaidPair.ledger.usesToRealize
            (fun i : Fin 2 => i)))
          (LinearEquiv.refl ℝ (Fin 2 → ℝ))) := by
  have hc := sourceCounted_leastBill_of_counted PaidPair.ledger (fun _ => True) 3
    (fun i : Fin 2 => i) PaidPair.pair_is_counted
  exact ⟨hc, source_counted_family_meets_K1_leastBill _ _ _ _ _ _ _ _ hc⟩

end APFPaper5.K1


universe apfNative_u_1 apfNative_u_2 apfNative_u_3
theorem solution :
∀ {P : Type apfNative_u_1} {R : Type apfNative_u_2} {Record : Type apfNative_u_3} (wholeResource : P → R)
  (calibration : R → NNReal) (maintained : P → Set.{apfNative_u_3} Record) (a : Record),
  @LE.le.{0} Real Real.instLE (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
    (@APFPaper5.K1.leastBill.{apfNative_u_1, apfNative_u_2, apfNative_u_3} P R Record wholeResource calibration
      maintained a) := by
  exact @APFPaper5.K1.leastBill_nonneg_p2mProof
