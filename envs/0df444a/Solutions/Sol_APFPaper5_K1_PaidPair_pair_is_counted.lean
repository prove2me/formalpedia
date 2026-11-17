-- Prove2me | solution 1 for APFPaper5.K1.PaidPair.pair_is_counted
-- status  : ACCEPTED   (prove)
-- author  : @FiniteUniverse
-- created : 2026-11-16T16:23:00.646834+00:00
-- url     : https://prove2.me/submissions/e68baf67-9a2e-4122-b981-5c1c047f6fb2

import Definitions.Def_APFPaper5_K1_counted_pair_with_relation_Vocabulary
/-
APF Foundation Ledger — theorem node DRAFT (Claude seat, session EthanBrooke-01WrrBvv, 2026-11-15; not
 gated, not reviewed, not released, not built in the ledger repo)
name: APFPaper5_K1_counted_pair_with_relation
title: A record ledger with a joint record on which the declared B05 holds and the pair is counted: two distinctions each with a record of its own costing 1 and a relation record costing 1 that only serving both takes; costs 1, 1 and 3 together
inputs_revision: 2026-11-14.1
mathlib_rev: 0df444a360eaa60ab8c11dca51a86af692955474
source: the author, 2026-11-15 06:17 HST: "A" (RULING_counted_includes_own_record_2026-11-15).
 Def_APFPaper5_K1_Counted. The costs 1, 1 and 3 are those of this seat's residue world and of the
 codebank's parity pair (apf/delta_calculus.py line 1180).
standing: A WITNESS, on a record ledger. It shows that "counted" as ruled is met by a family with a joint
 record present, and that the declared B05 holds there. So the K1 statement for counted families is not
 empty where joint records are present.
 LIMIT: a record ledger with B05 and countedness checked. It has no states, sides or continuations; B01 to
 B04, B06, B07a and B07b are NOT checked on it. It is not a world meeting the eight, and it is not shown
 to be the residue world's ledger.
the ledger: three records, each costing 1. Records 0 and 1 are the two distinctions' own; record 2 is the
 relation's. A protocol is the set of records it keeps. A set of records is sufficient for a distinction,
 in a protocol, when it holds the distinction's own record and, if the protocol also keeps the other's own
 record, record 2 as well.
what this file says:
 - Costs: nothing 0, each distinction alone 1, the two together 3.
 - b05_holds: the declared B05 holds with floor 1 and capacity 3, every distinction tested.
 - relation_is_joint: the pair needs record 2 and neither distinction needs it alone.
 - pair_is_counted: the pair is counted, own-record clause included.
what this file does NOT say: that such a ledger is physical, or that the eight admit it. No lane. No claim
 that the transfer is forced, that the carrier gap is closed or narrowed, or that Born is derived.
axioms: within propext, Classical.choice, Quot.sound. No sorry.
-/
import Definitions.Def_APFPaper5_K1_Counted
import Theorems.Thm_APFPaper5_K1_partyScore_meets_K1_of_own_record
import Theorems.Thm_APFPaper5_K1_memberNeeds_subset_familyNeeds_explicit
import Theorems.Thm_APFPaper5_K1_familyNeeds_eq_of_exactly_served_explicit
import Theorems.Thm_APFPaper5_K1_ledger_party_score_meets_K1_explicit
import Theorems.Thm_APFPaper5_K1_ledger_counted_family_party_score_satisfies_K1_explicit
import Theorems.Thm_APFPaper1_Source_familyCost_nonneg
import Theorems.Thm_APFPaper1_Source_familyCost_mono
import Definitions.Def_APF_B05_DeclaredInput_r2
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith

set_option autoImplicit false

open APFPaper1 APFPaper1.Source

namespace APFPaper5.K1.PaidPair







theorem serve_iff (p : Finset (Fin 3)) (d : Fin 2) :
    (∃ sigma : Set (Fin 3), sigma ⊆ ledger.maintained p ∧ ledger.sufficient p sigma d ∧
        ledger.usesToRealize p d sigma) ↔
      own d ∈ p ∧ (own (other d) ∈ p → (2 : Fin 3) ∈ p) := by
  constructor
  · rintro ⟨sigma, hsub, ⟨h1, h2⟩, _⟩
    exact ⟨hsub h1, fun h => hsub (h2 h)⟩
  · rintro ⟨h1, h2⟩
    exact ⟨(↑p : Set (Fin 3)), subset_rfl, ⟨h1, h2⟩, trivial⟩

/-- The bill of a protocol is the number of records it keeps. -/
theorem bill_eq (p : Finset (Fin 3)) :
    ((ledger.calibration (ledger.wholeResource p) : NNReal) : ℝ) = (p.card : ℝ) := by
  rw [ledger.bill_eq_sum]
  show ∑ _r ∈ p, (((1 : NNReal)) : ℝ) = _
  simp



theorem fc_mem (S : Finset (Fin 2)) (p : Finset (Fin 3))
    (hp : ∀ d ∈ S, own d ∈ p ∧ (own (other d) ∈ p → (2 : Fin 3) ∈ p)) :
    (p.card : ℝ) ∈ {c : ℝ | ∃ q : Finset (Fin 3),
      (∀ d ∈ S, ∃ sigma : Set (Fin 3), sigma ⊆ ledger.maintained q ∧ ledger.sufficient q sigma d ∧
        ledger.usesToRealize q d sigma) ∧
      ((ledger.calibration (ledger.wholeResource q) : NNReal) : ℝ) = c} :=
  ⟨p, fun d hd => (serve_iff p d).mpr (hp d hd), bill_eq p⟩

theorem fc_le (S : Finset (Fin 2)) (p : Finset (Fin 3))
    (hp : ∀ d ∈ S, own d ∈ p ∧ (own (other d) ∈ p → (2 : Fin 3) ∈ p)) : fc S ≤ (p.card : ℝ) := by
  unfold fc RecordLedger.familyCost APFPaper1.Source.familyCost
  refine csInf_le ⟨0, ?_⟩ (fc_mem S p hp)
  rintro c ⟨q, _, rfl⟩
  exact NNReal.coe_nonneg _

theorem fc_ge (S : Finset (Fin 2)) (c : ℝ) (p0 : Finset (Fin 3))
    (hp0 : ∀ d ∈ S, own d ∈ p0 ∧ (own (other d) ∈ p0 → (2 : Fin 3) ∈ p0))
    (h : ∀ q : Finset (Fin 3),
      (∀ d ∈ S, own d ∈ q ∧ (own (other d) ∈ q → (2 : Fin 3) ∈ q)) → c ≤ (q.card : ℝ)) :
    c ≤ fc S := by
  unfold fc RecordLedger.familyCost APFPaper1.Source.familyCost
  apply le_csInf ⟨_, fc_mem S p0 hp0⟩
  rintro x ⟨q, hq, rfl⟩
  rw [bill_eq]
  exact h q (fun d hd => (serve_iff q d).mp (hq d hd))

theorem fc_nonneg (S : Finset (Fin 2)) : 0 ≤ fc S :=
  familyCost_nonneg ledger.wholeResource ledger.calibration ledger.maintained ledger.sufficient
    ledger.usesToRealize S

theorem own_serves_single : ∀ d : Fin 2, ∀ e ∈ ({d} : Finset (Fin 2)),
    own e ∈ ({own d} : Finset (Fin 3)) ∧
      (own (other e) ∈ ({own d} : Finset (Fin 3)) → (2 : Fin 3) ∈ ({own d} : Finset (Fin 3))) := by
  decide

theorem all_serves_all : ∀ d ∈ (Finset.univ : Finset (Fin 2)),
    own d ∈ (Finset.univ : Finset (Fin 3)) ∧
      (own (other d) ∈ (Finset.univ : Finset (Fin 3)) → (2 : Fin 3) ∈ (Finset.univ : Finset (Fin 3))) := by
  decide

theorem own_not_others : ∀ i : Fin 2, own i ∉ ({own (other i)} : Finset (Fin 3)) := by decide

theorem two_not_own : ∀ d : Fin 2, (2 : Fin 3) ∉ ({own d} : Finset (Fin 3)) := by decide

theorem fc_empty : fc ∅ = 0 := by
  have h := fc_le ∅ ∅ (fun d hd => absurd hd (Finset.notMem_empty d))
  rw [Finset.card_empty, Nat.cast_zero] at h
  exact le_antisymm h (fc_nonneg ∅)

/-- Each distinction, held alone, costs 1. -/
theorem fc_single (d : Fin 2) : fc {d} = 1 := by
  apply le_antisymm
  · have h := fc_le {d} {own d} (own_serves_single d)
    rwa [Finset.card_singleton, Nat.cast_one] at h
  · apply fc_ge {d} 1 {own d} (own_serves_single d)
    intro q hq
    have hmem : own d ∈ q := (hq d (Finset.mem_singleton_self d)).1
    exact Nat.one_le_cast.mpr (Finset.card_pos.mpr ⟨own d, hmem⟩)

/-- A protocol serving both distinctions keeps all three records. -/
theorem univ_of_serves_both (q : Finset (Fin 3))
    (hq : ∀ d ∈ (Finset.univ : Finset (Fin 2)), own d ∈ q ∧ (own (other d) ∈ q → (2 : Fin 3) ∈ q)) :
    q = Finset.univ := by
  have h0 : (0 : Fin 3) ∈ q := (hq 0 (Finset.mem_univ _)).1
  have h1 : (1 : Fin 3) ∈ q := (hq 1 (Finset.mem_univ _)).1
  have h2 : (2 : Fin 3) ∈ q := (hq 0 (Finset.mem_univ _)).2 h1
  apply Finset.eq_univ_iff_forall.mpr
  intro x
  fin_cases x
  · exact h0
  · exact h1
  · exact h2

/-- The two together cost 3. -/
theorem fc_univ : fc Finset.univ = 3 := by
  have hc : (((Finset.univ : Finset (Fin 3)).card : ℕ) : ℝ) = 3 := by simp
  apply le_antisymm
  · have h := fc_le Finset.univ Finset.univ all_serves_all
    rwa [hc] at h
  · apply fc_ge Finset.univ 3 Finset.univ all_serves_all
    intro q hq
    rw [univ_of_serves_both q hq, hc]

theorem finset_fin2_cases :
    ∀ S : Finset (Fin 2), S = ∅ ∨ S = {0} ∨ S = {1} ∨ S = Finset.univ := by decide

theorem not_novel (S : Finset (Fin 2)) (d : Fin 2) (q : Finset (Fin 3))
    (hq : ∀ e ∈ S, own e ∈ q ∧ (own (other e) ∈ q → (2 : Fin 3) ∈ q))
    (hbill : (q.card : ℝ) ≤ fc S) (hd : own d ∈ q ∧ (own (other d) ∈ q → (2 : Fin 3) ∈ q)) :
    ¬ supportNovel ledger.wholeResource ledger.calibration ledger.maintained ledger.sufficient
        ledger.usesToRealize S d := by
  rintro ⟨eta, heta, h⟩
  have hb : ((ledger.calibration (ledger.wholeResource q) : NNReal) : ℝ) ≤ fc S + eta := by
    rw [bill_eq]
    linarith
  apply h q (fun e he => (serve_iff q e).mpr (hq e he)) hb
  obtain ⟨sigma, hs, hsuff, _⟩ := (serve_iff q d).mpr hd
  exact ⟨sigma, hs, hsuff⟩

/-- The declared B05 holds on the ledger, with floor 1 and capacity 3, every distinction tested. -/
theorem b05_holds :
    APFB05.MarginalFloor (Context := Unit) (D := fun _ => Fin 2) (P := fun _ => Finset (Fin 3))
      (R := fun _ => Finset (Fin 3)) (Record := fun _ => Fin 3) (fun _ => ledger.wholeResource)
      (fun _ => ledger.calibration) (fun _ => ledger.maintained) (fun _ => ledger.sufficient)
      (fun _ => ledger.usesToRealize) (fun _ _ => True) (fun _ => 3) (fun _ => 1) := by
  intro g
  refine ⟨one_pos, ?_⟩
  intro S d _ _ _ hnov
  have e0 : insert (0 : Fin 2) (∅ : Finset (Fin 2)) = {0} := by decide
  have e1 : insert (1 : Fin 2) (∅ : Finset (Fin 2)) = {1} := by decide
  have u0 : insert (0 : Fin 2) ({1} : Finset (Fin 2)) = Finset.univ := by decide
  have u1 : insert (1 : Fin 2) ({0} : Finset (Fin 2)) = Finset.univ := by decide
  have c0 : ((({own 0} : Finset (Fin 3)).card : ℕ) : ℝ) = 1 := by simp
  have c1 : ((({own 1} : Finset (Fin 3)).card : ℕ) : ℝ) = 1 := by simp
  have cu : (((Finset.univ : Finset (Fin 3)).card : ℕ) : ℝ) = 3 := by simp
  rcases finset_fin2_cases S with rfl | rfl | rfl | rfl <;> fin_cases d
  · show (1 : ℝ) ≤ fc (insert 0 ∅) - fc ∅
    rw [e0, fc_single, fc_empty]
    norm_num
  · show (1 : ℝ) ≤ fc (insert 1 ∅) - fc ∅
    rw [e1, fc_single, fc_empty]
    norm_num
  · exact absurd hnov (not_novel {0} 0 {own 0} (own_serves_single 0)
      (by rw [c0, fc_single]) (own_serves_single 0 0 (Finset.mem_singleton_self 0)))
  · show (1 : ℝ) ≤ fc (insert 1 {0}) - fc {0}
    rw [u1, fc_univ, fc_single]
    norm_num
  · show (1 : ℝ) ≤ fc (insert 0 {1}) - fc {1}
    rw [u0, fc_univ, fc_single]
    norm_num
  · exact absurd hnov (not_novel {1} 1 {own 1} (own_serves_single 1)
      (by rw [c1, fc_single]) (own_serves_single 1 1 (Finset.mem_singleton_self 1)))
  · exact absurd hnov (not_novel Finset.univ 0 Finset.univ all_serves_all
      (by rw [cu, fc_univ]) (all_serves_all 0 (Finset.mem_univ _)))
  · exact absurd hnov (not_novel Finset.univ 1 Finset.univ all_serves_all
      (by rw [cu, fc_univ]) (all_serves_all 1 (Finset.mem_univ _)))

theorem image_all : (Finset.univ : Finset (Fin 2)).image (fun i => i) = Finset.univ := by decide

theorem image_rest :
    ∀ j : Fin 2, ((Finset.univ : Finset (Fin 2)).erase j).image (fun i => i) = {other j} := by decide

/-- Counted as first typed for call 2: within capacity, tested, each support-novel over the other. -/
theorem pair_is_ledgerCounted : LedgerCounted ledger (fun _ => True) 3 (fun i : Fin 2 => i) := by
  refine ⟨?_, fun _ => trivial, ?_⟩
  · rw [image_all]
    refine ⟨⟨Finset.univ, fun d hd => (serve_iff _ d).mpr (all_serves_all d hd)⟩, ?_⟩
    show fc Finset.univ ≤ 3
    rw [fc_univ]
  · intro i
    rw [image_rest i]
    refine ⟨1 / 2, by norm_num, ?_⟩
    intro p hserve hbill
    rintro ⟨sigma, hsub, hsuff⟩
    have ho : own (other i) ∈ p :=
      ((serve_iff p (other i)).mp (hserve (other i) (Finset.mem_singleton_self _))).1
    have hi : own i ∈ p := hsub hsuff.1
    have h2 : (2 : Fin 3) ∈ p := hsub (hsuff.2 ho)
    have h3 : (3 : ℝ) ≤ (p.card : ℝ) := by
      have hsubset : ({own i, own (other i), 2} : Finset (Fin 3)) ⊆ p := by
        intro x hx
        rcases Finset.mem_insert.mp hx with h | hx
        · rw [h]
          exact hi
        · rcases Finset.mem_insert.mp hx with h | hx
          · rw [h]
            exact ho
          · rw [Finset.mem_singleton.mp hx]
            exact h2
      have hcard : ∀ j : Fin 2, ({own j, own (other j), 2} : Finset (Fin 3)).card = 3 := by decide
      have := Finset.card_le_card hsubset
      rw [hcard i] at this
      exact_mod_cast this
    rw [bill_eq] at hbill
    have hb : (p.card : ℝ) ≤ fc {other i} + 1 / 2 := hbill
    rw [fc_single] at hb
    linarith

/-- The own-record clause: each distinction's own record costs 1, is needed when it is held alone, and
is not needed by the other. -/
theorem has_own_paid_record : HasOwnPaidRecord ledger (fun i : Fin 2 => i) := by
  intro i
  refine ⟨own i, ?_, ?_, ?_⟩
  · show (0 : NNReal) < 1
    exact one_pos
  · intro p hp
    exact ((serve_iff p i).mp (hp i (Finset.mem_singleton_self _))).1
  · rw [image_rest i]
    intro h
    have h1 : own i ∈ ({own (other i)} : Finset (Fin 3)) :=
      h {own (other i)} (fun e he => (serve_iff _ e).mpr (own_serves_single (other i) e he))
    exact own_not_others i h1

/-- The pair is a counted family, own-record clause included. -/
theorem pair_is_counted : Counted ledger (fun _ => True) 3 (fun i : Fin 2 => i) :=
  ⟨pair_is_ledgerCounted, has_own_paid_record⟩

/-- Record 2 is a joint record: the pair needs it, and neither distinction needs it alone. -/
theorem relation_is_joint (d : Fin 2) :
    (2 : Fin 3) ∈ familyNeeds ledger Finset.univ ∧ (2 : Fin 3) ∉ familyNeeds ledger {d} := by
  constructor
  · intro p hp
    have hu := univ_of_serves_both p (fun e he => (serve_iff p e).mp (hp e he))
    rw [hu]
    exact Finset.mem_univ _
  · intro h
    have h2 : (2 : Fin 3) ∈ ({own d} : Finset (Fin 3)) :=
      h {own d} (fun e he => (serve_iff _ e).mpr (own_serves_single d e he))
    exact two_not_own d h2

end APFPaper5.K1.PaidPair


theorem solution :
@APFPaper5.K1.Counted.{0, 0, 0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
  (Finset.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
  (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
  (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
  (Fin.fintype (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
  (instDecidableEqFin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
  (instDecidableEqFin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) APFPaper5.K1.PaidPair.ledger
  (fun (x : Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) => True)
  (@OfNat.ofNat.{0} Real (nat_lit 3)
    (@instOfNatAtLeastTwo.{0} Real (nat_lit 3) Real.instNatCast
      (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
        (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))))
  fun (i : Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) => i := by
  exact @APFPaper5.K1.PaidPair.pair_is_counted
