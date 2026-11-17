-- Prove2me | solution 1 for APFPaper5.K1.Twins.b05_holds
-- status  : ACCEPTED   (prove)
-- author  : @FiniteUniverse
-- created : 2026-11-16T16:24:11.717839+00:00
-- url     : https://prove2.me/submissions/2e28b41f-bda1-4652-b15b-477efce913f5

import Definitions.Def_APFPaper5_K1_twins_same_records_Vocabulary
/-
APF Foundation Ledger — theorem node DRAFT (Claude seat, session EthanBrooke-01WrrBvv, 2026-11-15; not
 gated, not reviewed, not released, not built in the ledger repo)
name: APFPaper5_K1_twins_same_records
title: A record ledger on which the declared B05 holds, a pair is counted and each distinction costs the floor when held alone, yet the party score is not faithful: the two distinctions are party to exactly the same records
inputs_revision: 2026-11-14.1
mathlib_rev: 0df444a360eaa60ab8c11dca51a86af692955474
source: the author, 2026-11-15 05:56 HST: "Let's finish working on this can you tee it up", on the question
 whether "a counted distinction has a record of its own that costs something" is part of what counted
 means. This file tests the weaker clause "each counted distinction costs at least the floor when held
 alone" (the singleton floor of Paper 1 Supplement v9.28, thm:minimum-distinction-floor and def:MD).
standing: A COUNTERMODEL, on a record ledger. It shows that the declared B05, "counted" and a floor on each
 distinction held alone do NOT together give K1's faithful diagonal for the party score. With
 Thm_APFPaper5_K1_free_pair_paid_relation it leaves the own-record clause, or the exact condition, as what
 K1 needs where a joint record is present.
 LIMIT: a record ledger with B05, countedness and the singleton floor checked. It has no states, sides or
 continuations; B01 to B04, B06, B07a and B07b are NOT checked on it. It is not a world meeting the eight.
the ledger: two records, each costing 1. Four protocols: one keeps nothing; one serves distinction 0 and
 keeps record 0; one serves distinction 1 and keeps record 0; one serves both and keeps records 0 and 1.
 The two single protocols keep the same record and differ only in which distinction they serve.
what this file says:
 - Costs: nothing 0, each distinction alone 1, the two together 2.
 - b05_holds: the declared B05 holds with floor 1 and capacity 2, every distinction tested.
 - single_novel_over_empty, fc_single: each distinction is support-novel over the empty family and costs
   exactly the floor when held alone.
 - pair_is_counted: the pair is a counted family.
 - party_all: each distinction is party to both records. party_score_not_faithful: so the party score
   cannot tell them apart.
what this file does NOT say: that such a ledger is physical, or that the eight admit it. No lane. No claim
 that the transfer is forced, that the carrier gap is closed or narrowed, or that Born is derived.
axioms: within propext, Classical.choice, Quot.sound. No sorry.
-/
import Theorems.Thm_APFPaper5_K1_partyScore_meets_K1_of_own_record
import Theorems.Thm_APFPaper5_K1_memberNeeds_subset_familyNeeds_explicit
import Theorems.Thm_APFPaper5_K1_familyNeeds_eq_of_exactly_served_explicit
import Theorems.Thm_APFPaper5_K1_ledger_party_score_meets_K1_explicit
import Theorems.Thm_APFPaper5_K1_ledger_counted_family_party_score_satisfies_K1_explicit
import Definitions.Def_APFPaper5_K1_table_kernel_and_support_Vocabulary
import Theorems.Thm_APFPaper5_K1_atomTable_form_eq_zero_iff
import Theorems.Thm_APFPaper5_K1_atomTable_faithful_iff
import Theorems.Thm_APFPaper5_K1_atomTable_row_eq_of_same_marks
import Theorems.Thm_APFPaper5_K1_atomTable_merge_of_same_marks
import Theorems.Thm_APFPaper5_K1_atomTable_eq_zero_of_disjoint
import Theorems.Thm_APFPaper5_K1_card_mul_le_sum_of_private
import Theorems.Thm_APFPaper1_Source_familyCost_nonneg
import Theorems.Thm_APFPaper1_Source_familyCost_mono
import Definitions.Def_APF_B05_DeclaredInput_r2
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith

set_option autoImplicit false

open APFPaper1 APFPaper1.Source

namespace APFPaper5.K1.Twins







theorem ne_other : ∀ i : Fin 2, i ≠ other i := by decide



theorem serve_iff (p : Prot) (d : Fin 2) :
    (∃ sigma : Set (Fin 2), sigma ⊆ ledger.maintained p ∧ ledger.sufficient p sigma d ∧
        ledger.usesToRealize p d sigma) ↔ (p = Prot.one d ∨ p = Prot.both) := by
  constructor
  · rintro ⟨sigma, _, ⟨h, _⟩, _⟩
    exact h
  · intro h
    exact ⟨(↑(keptOf p) : Set (Fin 2)), subset_rfl, ⟨h, rfl⟩, trivial⟩

/-- The bill of a protocol is the number of records it keeps. -/
theorem bill_eq (p : Prot) :
    ((ledger.calibration (ledger.wholeResource p) : NNReal) : ℝ) = ((keptOf p).card : ℝ) := by
  rw [ledger.bill_eq_sum]
  show ∑ _r ∈ keptOf p, (((1 : NNReal)) : ℝ) = _
  simp

theorem card_idle : ((keptOf Prot.idle).card : ℝ) = 0 := by simp [keptOf]
theorem card_one (d : Fin 2) : ((keptOf (Prot.one d)).card : ℝ) = 1 := by simp [keptOf]
theorem card_both : ((keptOf Prot.both).card : ℝ) = 2 := by simp [keptOf]



theorem fc_mem (S : Finset (Fin 2)) (p : Prot) (hp : ∀ d ∈ S, p = Prot.one d ∨ p = Prot.both) :
    ((keptOf p).card : ℝ) ∈ {c : ℝ | ∃ q : Prot,
      (∀ d ∈ S, ∃ sigma : Set (Fin 2), sigma ⊆ ledger.maintained q ∧ ledger.sufficient q sigma d ∧
        ledger.usesToRealize q d sigma) ∧
      ((ledger.calibration (ledger.wholeResource q) : NNReal) : ℝ) = c} :=
  ⟨p, fun d hd => (serve_iff p d).mpr (hp d hd), bill_eq p⟩

theorem fc_le (S : Finset (Fin 2)) (p : Prot) (hp : ∀ d ∈ S, p = Prot.one d ∨ p = Prot.both) :
    fc S ≤ ((keptOf p).card : ℝ) := by
  unfold fc RecordLedger.familyCost APFPaper1.Source.familyCost
  refine csInf_le ⟨0, ?_⟩ (fc_mem S p hp)
  rintro c ⟨q, _, rfl⟩
  exact NNReal.coe_nonneg _

theorem fc_ge (S : Finset (Fin 2)) (c : ℝ) (p0 : Prot)
    (hp0 : ∀ d ∈ S, p0 = Prot.one d ∨ p0 = Prot.both)
    (h : ∀ q : Prot, (∀ d ∈ S, q = Prot.one d ∨ q = Prot.both) → c ≤ ((keptOf q).card : ℝ)) :
    c ≤ fc S := by
  unfold fc RecordLedger.familyCost APFPaper1.Source.familyCost
  apply le_csInf ⟨_, fc_mem S p0 hp0⟩
  rintro x ⟨q, hq, rfl⟩
  rw [bill_eq]
  exact h q (fun d hd => (serve_iff q d).mp (hq d hd))

theorem fc_nonneg (S : Finset (Fin 2)) : 0 ≤ fc S :=
  familyCost_nonneg ledger.wholeResource ledger.calibration ledger.maintained ledger.sufficient
    ledger.usesToRealize S

theorem fc_empty : fc ∅ = 0 := by
  have h := fc_le ∅ Prot.idle (fun d hd => absurd hd (Finset.notMem_empty d))
  rw [card_idle] at h
  exact le_antisymm h (fc_nonneg ∅)

/-- Each distinction, held alone, costs 1. -/
theorem fc_single (d : Fin 2) : fc {d} = 1 := by
  apply le_antisymm
  · have h := fc_le {d} (Prot.one d) (fun e he => Or.inl (by rw [Finset.mem_singleton.mp he]))
    rwa [card_one] at h
  · apply fc_ge {d} 1 (Prot.one d) (fun e he => Or.inl (by rw [Finset.mem_singleton.mp he]))
    intro q hq
    rcases hq d (Finset.mem_singleton_self d) with h | h
    · rw [h, card_one]
    · rw [h, card_both]
      norm_num

/-- A protocol serving both distinctions is the one that keeps both records. -/
theorem both_of_serves_univ (q : Prot)
    (hq : ∀ d ∈ (Finset.univ : Finset (Fin 2)), q = Prot.one d ∨ q = Prot.both) : q = Prot.both := by
  rcases hq 0 (Finset.mem_univ _) with h0 | h0
  · rcases hq 1 (Finset.mem_univ _) with h1 | h1
    · rw [h0] at h1
      exact absurd (Prot.one.inj h1) (by decide)
    · exact h1
  · exact h0

/-- The two together cost 2. -/
theorem fc_univ : fc Finset.univ = 2 := by
  apply le_antisymm
  · have h := fc_le Finset.univ Prot.both (fun _ _ => Or.inr rfl)
    rwa [card_both] at h
  · apply fc_ge Finset.univ 2 Prot.both (fun _ _ => Or.inr rfl)
    intro q hq
    rw [both_of_serves_univ q hq, card_both]

theorem finset_fin2_cases :
    ∀ S : Finset (Fin 2), S = ∅ ∨ S = {0} ∨ S = {1} ∨ S = Finset.univ := by decide

theorem not_novel (S : Finset (Fin 2)) (d : Fin 2) (q : Prot)
    (hq : ∀ e ∈ S, q = Prot.one e ∨ q = Prot.both)
    (hbill : ((keptOf q).card : ℝ) ≤ fc S) (hd : q = Prot.one d ∨ q = Prot.both) :
    ¬ supportNovel ledger.wholeResource ledger.calibration ledger.maintained ledger.sufficient
        ledger.usesToRealize S d := by
  rintro ⟨eta, heta, h⟩
  have hb : ((ledger.calibration (ledger.wholeResource q) : NNReal) : ℝ) ≤ fc S + eta := by
    rw [bill_eq]
    linarith
  apply h q (fun e he => (serve_iff q e).mpr (hq e he)) hb
  obtain ⟨sigma, hs, hsuff, _⟩ := (serve_iff q d).mpr hd
  exact ⟨sigma, hs, hsuff⟩

/-- The declared B05 holds on the ledger, with floor 1 and capacity 2, every distinction tested. -/
theorem b05_holds :
    APFB05.MarginalFloor (Context := Unit) (D := fun _ => Fin 2) (P := fun _ => Prot)
      (R := fun _ => Finset (Fin 2)) (Record := fun _ => Fin 2) (fun _ => ledger.wholeResource)
      (fun _ => ledger.calibration) (fun _ => ledger.maintained) (fun _ => ledger.sufficient)
      (fun _ => ledger.usesToRealize) (fun _ _ => True) (fun _ => 2) (fun _ => 1) := by
  intro g
  refine ⟨one_pos, ?_⟩
  intro S d _ _ _ hnov
  have e0 : insert (0 : Fin 2) (∅ : Finset (Fin 2)) = {0} := by decide
  have e1 : insert (1 : Fin 2) (∅ : Finset (Fin 2)) = {1} := by decide
  have u0 : insert (0 : Fin 2) ({1} : Finset (Fin 2)) = Finset.univ := by decide
  have u1 : insert (1 : Fin 2) ({0} : Finset (Fin 2)) = Finset.univ := by decide
  rcases finset_fin2_cases S with rfl | rfl | rfl | rfl <;> fin_cases d
  · show (1 : ℝ) ≤ fc (insert 0 ∅) - fc ∅
    rw [e0, fc_single, fc_empty]
    norm_num
  · show (1 : ℝ) ≤ fc (insert 1 ∅) - fc ∅
    rw [e1, fc_single, fc_empty]
    norm_num
  · exact absurd hnov (not_novel {0} 0 (Prot.one 0)
      (fun e he => Or.inl (by rw [Finset.mem_singleton.mp he]))
      (by rw [card_one, fc_single]) (Or.inl rfl))
  · show (1 : ℝ) ≤ fc (insert 1 {0}) - fc {0}
    rw [u1, fc_univ, fc_single]
    norm_num
  · show (1 : ℝ) ≤ fc (insert 0 {1}) - fc {1}
    rw [u0, fc_univ, fc_single]
    norm_num
  · exact absurd hnov (not_novel {1} 1 (Prot.one 1)
      (fun e he => Or.inl (by rw [Finset.mem_singleton.mp he]))
      (by rw [card_one, fc_single]) (Or.inl rfl))
  · exact absurd hnov (not_novel Finset.univ 0 Prot.both (fun _ _ => Or.inr rfl)
      (by rw [card_both, fc_univ]) (Or.inr rfl))
  · exact absurd hnov (not_novel Finset.univ 1 Prot.both (fun _ _ => Or.inr rfl)
      (by rw [card_both, fc_univ]) (Or.inr rfl))

/-- Each distinction is support-novel over the empty family: no protocol within 1/2 of costing nothing
serves it. So the marginal floor reaches the single distinction. -/
theorem single_novel_over_empty (d : Fin 2) :
    supportNovel ledger.wholeResource ledger.calibration ledger.maintained ledger.sufficient
      ledger.usesToRealize ∅ d := by
  refine ⟨1 / 2, by norm_num, ?_⟩
  intro p _ hbill
  rintro ⟨sigma, _, hsuff⟩
  rw [bill_eq] at hbill
  have hb : ((keptOf p).card : ℝ) ≤ fc ∅ + 1 / 2 := hbill
  rw [fc_empty] at hb
  rcases hsuff.1 with h | h
  · rw [h, card_one] at hb
    norm_num at hb
  · rw [h, card_both] at hb
    norm_num at hb

/-- The pair is a counted family: within capacity, tested, each support-novel over the other. -/
theorem pair_is_counted : LedgerCounted ledger (fun _ => True) 2 (fun i : Fin 2 => i) := by
  refine ⟨?_, fun _ => trivial, ?_⟩
  · have himg : (Finset.univ : Finset (Fin 2)).image (fun i => i) = Finset.univ := by decide
    rw [himg]
    refine ⟨⟨Prot.both, fun d _ => (serve_iff _ d).mpr (Or.inr rfl)⟩, ?_⟩
    show fc Finset.univ ≤ 2
    rw [fc_univ]
  · intro i
    have himg : ∀ j : Fin 2,
        ((Finset.univ : Finset (Fin 2)).erase j).image (fun i => i) = {other j} := by decide
    rw [himg i]
    refine ⟨1 / 2, by norm_num, ?_⟩
    intro p hserve hbill
    rintro ⟨sigma, _, hsuff⟩
    have h1 : p = Prot.one (other i) ∨ p = Prot.both :=
      (serve_iff p (other i)).mp (hserve (other i) (Finset.mem_singleton_self _))
    have h2 : p = Prot.one i ∨ p = Prot.both := hsuff.1
    rw [bill_eq] at hbill
    have hb : ((keptOf p).card : ℝ) ≤ fc {other i} + 1 / 2 := hbill
    rw [fc_single] at hb
    rcases h2 with h2 | h2
    · rcases h1 with h1 | h1
      · rw [h2] at h1
        exact ne_other i (Prot.one.inj h1)
      · rw [h2] at h1
        exact Prot.noConfusion h1
    · rw [h2, card_both] at hb
      norm_num at hb

theorem image_single : ∀ d : Fin 2, (insert d (∅ : Finset (Fin 2))).image (fun i => i) = {d} := by
  decide

theorem image_pair :
    ∀ d : Fin 2, (insert d ({other d} : Finset (Fin 2))).image (fun i => i) = Finset.univ := by
  decide

theorem image_other : ∀ d : Fin 2, ({other d} : Finset (Fin 2)).image (fun i => i) = {other d} := by
  decide

/-- Each distinction is party to both records. -/
theorem party_all (d : Fin 2) (a : Fin 2) :
    partyMark (ledgerKeeps ledger (fun i : Fin 2 => i)) d a = true := by
  unfold partyMark
  apply @decide_eq_true _ (Classical.propDecidable _)
  fin_cases a
  · refine ⟨∅, ?_, ?_⟩
    · unfold ledgerKeeps
      apply @decide_eq_true _ (Classical.propDecidable _)
      rw [image_single d]
      intro p hp
      rcases (serve_iff p d).mp (hp d (Finset.mem_singleton_self d)) with h | h
      · rw [h]
        show (0 : Fin 2) ∈ ({0} : Finset (Fin 2))
        exact Finset.mem_singleton_self 0
      · rw [h]
        exact Finset.mem_univ _
    · unfold ledgerKeeps
      apply @decide_eq_false _ (Classical.propDecidable _)
      rw [Finset.image_empty]
      intro h
      have h0 : (0 : Fin 2) ∈ (∅ : Finset (Fin 2)) :=
        h Prot.idle (fun e he => absurd he (Finset.notMem_empty e))
      exact absurd h0 (Finset.notMem_empty _)
  · refine ⟨{other d}, ?_, ?_⟩
    · unfold ledgerKeeps
      apply @decide_eq_true _ (Classical.propDecidable _)
      rw [image_pair d]
      intro p hp
      have hb : p = Prot.both :=
        both_of_serves_univ p (fun e he => (serve_iff p e).mp (hp e he))
      rw [hb]
      exact Finset.mem_univ _
    · unfold ledgerKeeps
      apply @decide_eq_false _ (Classical.propDecidable _)
      rw [image_other d]
      intro h
      have h1 : (1 : Fin 2) ∈ ({0} : Finset (Fin 2)) :=
        h (Prot.one (other d)) (fun e he => (serve_iff _ e).mpr
          (Or.inl (by rw [Finset.mem_singleton.mp he])))
      exact absurd h1 (by decide)

/-- The party score is not faithful: the two distinctions are party to the same records. -/
theorem party_score_not_faithful :
    ¬ FaithfulNonnegDiagonal (tableForm (ledgerPartyScore ledger (fun i : Fin 2 => i)))
        (LinearEquiv.refl ℝ (Fin 2 → ℝ)) :=
  (atomTable_merge_of_same_marks (fun a => ((ledger.cost a : NNReal) : ℝ))
    (fun a => NNReal.coe_nonneg _) (partyMark (ledgerKeeps ledger (fun i : Fin 2 => i))) 0 1
    (by decide) (fun a _ => by rw [party_all 0 a, party_all 1 a])).2

end APFPaper5.K1.Twins


theorem solution :
@APFB05.MarginalFloor.{0, 0, 0, 0, 0} Unit
  (fun (x : Unit) => Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
  (fun (x : Unit) => APFPaper5.K1.Twins.Prot)
  (fun (x : Unit) => Finset.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
  (fun (x : Unit) => Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
  (fun (g : Unit) => instDecidableEqFin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
  (fun (x : Unit) =>
    @APFPaper1.RecordLedger.wholeResource.{0, 0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      APFPaper5.K1.Twins.Prot (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      APFPaper5.K1.Twins.ledger)
  (fun (x : Unit) =>
    @APFPaper1.RecordLedger.calibration.{0, 0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      APFPaper5.K1.Twins.Prot (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      APFPaper5.K1.Twins.ledger)
  (fun (x : Unit) =>
    @APFPaper1.RecordLedger.maintained.{0, 0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      APFPaper5.K1.Twins.Prot (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      APFPaper5.K1.Twins.ledger)
  (fun (x : Unit) =>
    @APFPaper1.RecordLedger.sufficient.{0, 0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      APFPaper5.K1.Twins.Prot (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      APFPaper5.K1.Twins.ledger)
  (fun (x : Unit) =>
    @APFPaper1.RecordLedger.usesToRealize.{0, 0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      APFPaper5.K1.Twins.Prot (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      APFPaper5.K1.Twins.ledger)
  (fun (x : Unit) (x_1 : Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) => True)
  (fun (x : Unit) =>
    @OfNat.ofNat.{0} Real (nat_lit 2)
      (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
        (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
          (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
  fun (x : Unit) => @OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne) := by
  exact @APFPaper5.K1.Twins.b05_holds
