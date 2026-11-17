-- Prove2me | solution 1 for APFPaper5.K1.FreePair.pair_is_counted
-- status  : ACCEPTED   (prove)
-- author  : @FiniteUniverse
-- created : 2026-11-16T16:23:01.604583+00:00
-- url     : https://prove2.me/submissions/0a517c29-67e1-4e2c-a93c-8a45fd2b1316

import Definitions.Def_APFPaper5_K1_free_pair_paid_relation_Vocabulary
/-
APF Foundation Ledger — theorem node DRAFT (Claude seat, session EthanBrooke-01WrrBvv, 2026-11-15; not
 gated, not reviewed, not released, not built in the ledger repo)
name: APFPaper5_K1_free_pair_paid_relation
title: A record ledger on which the declared B05 holds and a pair is counted, yet the party score is not faithful: two distinctions that each cost nothing alone and whose relation costs 1
inputs_revision: 2026-11-14.1
mathlib_rev: 0df444a360eaa60ab8c11dca51a86af692955474
source: the author, 2026-11-15 05:07 HST: "1 Confirmed, please proceed" (item 5 of this seat's list of
 05:00 HST: derive the premises or build a countermodel). Def_APFPaper5_K1_LedgerPartyScore,
 Def_APFPaper5_K1_LedgerScore (LedgerCounted), Def_APF_B05_DeclaredInput_r2.
standing: A COUNTERMODEL, on a record ledger. It shows that the declared B05 together with "counted" does
 NOT give "each distinction, held alone, needs a record of positive cost that the others together do not
 need", and does not give K1's faithful diagonal for the party score, where a joint record is present.
 LIMIT: it is a record ledger with B05 and countedness checked. It has no states, sides or continuations,
 and B01 to B04, B06, B07a and B07b are NOT checked on it. It is not a world meeting the eight.
the ledger: three records. Records 0 and 1 are the two distinctions' own and cost nothing. Record 2 costs
 1. A protocol is the set of records it keeps. A set of records is sufficient for a distinction, in a
 protocol, when it holds the distinction's own record and, if the protocol also keeps the other's own
 record, record 2 as well. So each distinction can be served alone for nothing, and serving both takes
 record 2.
what this file says:
 - Costs: each distinction alone 0, the two together 1.
 - b05_holds: the declared B05 holds with floor 1 and capacity 1, every distinction tested. The floor is
   met at the one step where it applies: adding either distinction to the other adds 1.
 - pair_is_counted: the pair is a counted family.
 - party_score_not_faithful: both distinctions are party to the only record of positive cost, so the party
   score cannot tell them apart.
 - no_own_paid_record: neither distinction, held alone, needs a record of positive cost.
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

namespace APFPaper5.K1.FreePair







/-- A protocol serves a distinction exactly when it keeps its own record and, if it also keeps the
other's, record 2. -/
theorem serve_iff (p : Finset (Fin 3)) (d : Fin 2) :
    (∃ sigma : Set (Fin 3), sigma ⊆ ledger.maintained p ∧ ledger.sufficient p sigma d ∧
        ledger.usesToRealize p d sigma) ↔
      own d ∈ p ∧ (own (other d) ∈ p → (2 : Fin 3) ∈ p) := by
  constructor
  · rintro ⟨sigma, hsub, ⟨h1, h2⟩, _⟩
    exact ⟨hsub h1, fun h => hsub (h2 h)⟩
  · rintro ⟨h1, h2⟩
    exact ⟨(↑p : Set (Fin 3)), subset_rfl, ⟨h1, h2⟩, trivial⟩

/-- The bill of a protocol: 1 if it keeps record 2, nothing otherwise. -/
theorem bill_eq (p : Finset (Fin 3)) :
    ((ledger.calibration (ledger.wholeResource p) : NNReal) : ℝ) = if (2 : Fin 3) ∈ p then 1 else 0 := by
  rw [ledger.bill_eq_sum]
  have hc : ∀ r : Fin 3, ((ledger.cost r : NNReal) : ℝ) = if r = 2 then (1 : ℝ) else 0 := by
    intro r
    show (((if r = 2 then 1 else 0 : NNReal)) : ℝ) = _
    split_ifs <;> simp
  show ∑ r ∈ p, ((ledger.cost r : NNReal) : ℝ) = _
  rw [Finset.sum_congr rfl (fun r _ => hc r), Finset.sum_ite_eq']



theorem fc_mem (S : Finset (Fin 2)) (p : Finset (Fin 3))
    (hp : ∀ d ∈ S, own d ∈ p ∧ (own (other d) ∈ p → (2 : Fin 3) ∈ p)) :
    (if (2 : Fin 3) ∈ p then (1 : ℝ) else 0) ∈ {c : ℝ | ∃ q : Finset (Fin 3),
      (∀ d ∈ S, ∃ sigma : Set (Fin 3), sigma ⊆ ledger.maintained q ∧ ledger.sufficient q sigma d ∧
        ledger.usesToRealize q d sigma) ∧
      ((ledger.calibration (ledger.wholeResource q) : NNReal) : ℝ) = c} :=
  ⟨p, fun d hd => (serve_iff p d).mpr (hp d hd), bill_eq p⟩

theorem fc_le (S : Finset (Fin 2)) (p : Finset (Fin 3))
    (hp : ∀ d ∈ S, own d ∈ p ∧ (own (other d) ∈ p → (2 : Fin 3) ∈ p)) :
    fc S ≤ if (2 : Fin 3) ∈ p then (1 : ℝ) else 0 := by
  unfold fc RecordLedger.familyCost APFPaper1.Source.familyCost
  refine csInf_le ⟨0, ?_⟩ (fc_mem S p hp)
  rintro c ⟨q, _, rfl⟩
  exact NNReal.coe_nonneg _

theorem fc_nonneg (S : Finset (Fin 2)) : 0 ≤ fc S :=
  familyCost_nonneg ledger.wholeResource ledger.calibration ledger.maintained ledger.sufficient
    ledger.usesToRealize S

/-- A family served by a protocol that does not keep record 2 costs nothing. -/
theorem fc_free (S : Finset (Fin 2)) (p : Finset (Fin 3))
    (hp : ∀ d ∈ S, own d ∈ p ∧ (own (other d) ∈ p → (2 : Fin 3) ∈ p)) (h2 : (2 : Fin 3) ∉ p) :
    fc S = 0 := by
  have h := fc_le S p hp
  rw [if_neg h2] at h
  exact le_antisymm h (fc_nonneg S)

/-- Every protocol serving both distinctions keeps record 2. -/
theorem two_mem_of_serves_both (p : Finset (Fin 3))
    (h : ∀ d ∈ (Finset.univ : Finset (Fin 2)), ∃ sigma : Set (Fin 3),
      sigma ⊆ ledger.maintained p ∧ ledger.sufficient p sigma d ∧ ledger.usesToRealize p d sigma) :
    (2 : Fin 3) ∈ p := by
  have h0 := (serve_iff p 0).mp (h 0 (Finset.mem_univ _))
  have h1 := (serve_iff p 1).mp (h 1 (Finset.mem_univ _))
  exact h0.2 h1.1

/-- The two together cost 1. -/
theorem fc_univ : fc Finset.univ = 1 := by
  apply le_antisymm
  · have h := fc_le Finset.univ Finset.univ (by decide)
    rwa [if_pos (Finset.mem_univ _)] at h
  · unfold fc RecordLedger.familyCost APFPaper1.Source.familyCost
    apply le_csInf ⟨_, fc_mem Finset.univ Finset.univ (by decide)⟩
    rintro c ⟨q, hq, rfl⟩
    rw [bill_eq, if_pos (two_mem_of_serves_both q hq)]

/-- The protocol keeping only a distinction's own record serves it. -/
theorem own_serves_single : ∀ d : Fin 2, ∀ e ∈ ({d} : Finset (Fin 2)),
    own e ∈ ({own d} : Finset (Fin 3)) ∧
      (own (other e) ∈ ({own d} : Finset (Fin 3)) → (2 : Fin 3) ∈ ({own d} : Finset (Fin 3))) := by
  decide

theorem two_not_own : ∀ d : Fin 2, (2 : Fin 3) ∉ ({own d} : Finset (Fin 3)) := by decide

theorem fc_single (d : Fin 2) : fc {d} = 0 :=
  fc_free {d} {own d} (own_serves_single d) (two_not_own d)

theorem finset_fin2_cases :
    ∀ S : Finset (Fin 2), S = ∅ ∨ S = {0} ∨ S = {1} ∨ S = Finset.univ := by decide

/-- A distinction is not support-novel over a family that some protocol serves at the family's cost
while also serving the distinction. -/
theorem not_novel (S : Finset (Fin 2)) (d : Fin 2) (q : Finset (Fin 3))
    (hq : ∀ e ∈ S, own e ∈ q ∧ (own (other e) ∈ q → (2 : Fin 3) ∈ q))
    (hbill : (if (2 : Fin 3) ∈ q then (1 : ℝ) else 0) ≤ fc S)
    (hd : own d ∈ q ∧ (own (other d) ∈ q → (2 : Fin 3) ∈ q)) :
    ¬ supportNovel ledger.wholeResource ledger.calibration ledger.maintained ledger.sufficient
        ledger.usesToRealize S d := by
  rintro ⟨eta, heta, h⟩
  have hb : ((ledger.calibration (ledger.wholeResource q) : NNReal) : ℝ) ≤ fc S + eta := by
    rw [bill_eq]
    linarith
  apply h q (fun e he => (serve_iff q e).mpr (hq e he)) hb
  obtain ⟨sigma, hs, hsuff, _⟩ := (serve_iff q d).mpr hd
  exact ⟨sigma, hs, hsuff⟩

/-- The declared B05 holds on the ledger, with floor 1 and capacity 1, every distinction tested. -/
theorem b05_holds :
    APFB05.MarginalFloor (Context := Unit) (D := fun _ => Fin 2) (P := fun _ => Finset (Fin 3))
      (R := fun _ => Finset (Fin 3)) (Record := fun _ => Fin 3) (fun _ => ledger.wholeResource)
      (fun _ => ledger.calibration) (fun _ => ledger.maintained) (fun _ => ledger.sufficient)
      (fun _ => ledger.usesToRealize) (fun _ _ => True) (fun _ => 1) (fun _ => 1) := by
  intro g
  refine ⟨one_pos, ?_⟩
  intro S d _ _ _ hnov
  have hz0 : (if (2 : Fin 3) ∈ ({0} : Finset (Fin 3)) then (1 : ℝ) else 0) = 0 := if_neg (by decide)
  have hz1 : (if (2 : Fin 3) ∈ ({1} : Finset (Fin 3)) then (1 : ℝ) else 0) = 0 := if_neg (by decide)
  have hu : (if (2 : Fin 3) ∈ (Finset.univ : Finset (Fin 3)) then (1 : ℝ) else 0) = 1 :=
    if_pos (Finset.mem_univ _)
  rcases finset_fin2_cases S with rfl | rfl | rfl | rfl <;> fin_cases d
  · exact absurd hnov (not_novel ∅ 0 {0} (by decide) (by rw [hz0]; exact fc_nonneg _) (by decide))
  · exact absurd hnov (not_novel ∅ 1 {1} (by decide) (by rw [hz1]; exact fc_nonneg _) (by decide))
  · exact absurd hnov (not_novel {0} 0 {0} (by decide) (by rw [hz0]; exact fc_nonneg _) (by decide))
  · show (1 : ℝ) ≤ fc (insert 1 {0}) - fc {0}
    have h : insert (1 : Fin 2) ({0} : Finset (Fin 2)) = Finset.univ := by decide
    rw [h, fc_univ, fc_single]
    norm_num
  · show (1 : ℝ) ≤ fc (insert 0 {1}) - fc {1}
    have h : insert (0 : Fin 2) ({1} : Finset (Fin 2)) = Finset.univ := by decide
    rw [h, fc_univ, fc_single]
    norm_num
  · exact absurd hnov (not_novel {1} 1 {1} (by decide) (by rw [hz1]; exact fc_nonneg _) (by decide))
  · exact absurd hnov
      (not_novel Finset.univ 0 Finset.univ (by decide) (by rw [hu, fc_univ]) (by decide))
  · exact absurd hnov
      (not_novel Finset.univ 1 Finset.univ (by decide) (by rw [hu, fc_univ]) (by decide))

/-- The pair is a counted family: within capacity, tested, each support-novel over the other. -/
theorem pair_is_counted : LedgerCounted ledger (fun _ => True) 1 (fun i : Fin 2 => i) := by
  refine ⟨?_, fun _ => trivial, ?_⟩
  · have himg : (Finset.univ : Finset (Fin 2)).image (fun i => i) = Finset.univ := by decide
    rw [himg]
    refine ⟨⟨Finset.univ, fun d _ => (serve_iff _ d).mpr (by revert d; decide)⟩, ?_⟩
    show fc Finset.univ ≤ 1
    rw [fc_univ]
  · intro i
    have himg : ((Finset.univ : Finset (Fin 2)).erase i).image (fun i => i) = {other i} := by
      revert i
      decide
    rw [himg]
    refine ⟨1 / 2, by norm_num, ?_⟩
    intro p hserve hbill
    rintro ⟨sigma, hsub, hsuff⟩
    have ho : own (other i) ∈ p :=
      ((serve_iff p (other i)).mp (hserve (other i) (Finset.mem_singleton_self _))).1
    have h2 : (2 : Fin 3) ∈ p := hsub (hsuff.2 ho)
    rw [bill_eq, if_pos h2] at hbill
    have hb : (1 : ℝ) ≤ fc {other i} + 1 / 2 := hbill
    rw [fc_single] at hb
    norm_num at hb

/-- Both distinctions are party to record 2. -/
theorem party_two (d : Fin 2) :
    partyMark (ledgerKeeps ledger (fun i : Fin 2 => i)) d 2 = true := by
  unfold partyMark
  apply @decide_eq_true _ (Classical.propDecidable _)
  refine ⟨{other d}, ?_, ?_⟩
  · unfold ledgerKeeps
    apply @decide_eq_true _ (Classical.propDecidable _)
    have himg : (insert d ({other d} : Finset (Fin 2))).image (fun i => i) = Finset.univ := by
      revert d
      decide
    rw [himg]
    intro p hp
    exact two_mem_of_serves_both p hp
  · unfold ledgerKeeps
    apply @decide_eq_false _ (Classical.propDecidable _)
    have himg : ({other d} : Finset (Fin 2)).image (fun i => i) = {other d} := by
      revert d
      decide
    rw [himg]
    intro h
    have h2 : (2 : Fin 3) ∈ ({own (other d)} : Finset (Fin 3)) :=
      h {own (other d)} (fun e he => (serve_iff _ e).mpr (own_serves_single (other d) e he))
    exact two_not_own (other d) h2

/-- The party score is not faithful: the only record of positive cost has both distinctions party to it. -/
theorem party_score_not_faithful :
    ¬ FaithfulNonnegDiagonal (tableForm (ledgerPartyScore ledger (fun i : Fin 2 => i)))
        (LinearEquiv.refl ℝ (Fin 2 → ℝ)) := by
  have hsame : ∀ a : Fin 3, 0 < ((ledger.cost a : NNReal) : ℝ) →
      partyMark (ledgerKeeps ledger (fun i : Fin 2 => i)) 0 a =
        partyMark (ledgerKeeps ledger (fun i : Fin 2 => i)) 1 a := by
    intro a ha
    have ha2 : a = 2 := by
      by_contra hne
      have hz : ((ledger.cost a : NNReal) : ℝ) = 0 := by
        show (((if a = 2 then 1 else 0 : NNReal)) : ℝ) = 0
        rw [if_neg hne]
        simp
      linarith
    rw [ha2, party_two 0, party_two 1]
  exact (atomTable_merge_of_same_marks (fun a => ((ledger.cost a : NNReal) : ℝ))
    (fun a => NNReal.coe_nonneg _) (partyMark (ledgerKeeps ledger (fun i : Fin 2 => i))) 0 1
    (by decide) hsame).2

/-- Neither distinction, held alone, needs a record of positive cost. -/
theorem no_own_paid_record (d : Fin 2) (a : Fin 3) (ha : a ∈ familyNeeds ledger {d}) :
    ledger.cost a = 0 := by
  have h : a ∈ ({own d} : Finset (Fin 3)) :=
    ha {own d} (fun e he => (serve_iff _ e).mpr (own_serves_single d e he))
  have hne : a ≠ 2 := by
    intro h2
    rw [h2] at h
    exact two_not_own d h
  show (if a = 2 then 1 else 0 : NNReal) = 0
  rw [if_neg hne]

end APFPaper5.K1.FreePair


theorem solution :
@APFPaper5.K1.LedgerCounted.{0, 0, 0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
  (Finset.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
  (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
  (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
  (Fin.fintype (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
  (instDecidableEqFin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
  (instDecidableEqFin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) APFPaper5.K1.FreePair.ledger
  (fun (x : Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) => True)
  (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
  fun (i : Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) => i := by
  exact @APFPaper5.K1.FreePair.pair_is_counted
