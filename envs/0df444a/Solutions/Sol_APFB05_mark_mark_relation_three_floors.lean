-- Prove2me | solution 1 for APFB05.mark_mark_relation_three_floors
-- status  : ACCEPTED   (prove)
-- author  : @FiniteUniverse
-- created : 2026-11-13T16:59:47.983907+00:00
-- url     : https://prove2.me/submissions/d10c12e9-3b34-4de1-9d13-d02b956e7d85

/-
APF Foundation Ledger — theorem node DRAFT (session EthanBrooke-01WrrBvu, 2026-11-12; not gated, not reviewed)
name: APFB05_relation_task
title: A relation held as a task: its floor, the three-floor count, and the budget window
inputs_revision: 2026-10-04.1
mathlib_rev: 0df444a360eaa60ab8c11dca51a86af692955474
source: Paper 1 Supplement v9.28:1816-1827 (marginal floor), 2615-2617 (support novelty); Paper 0 v6.3.2
 sec:chained_boats, "What is paid for" (the relation task d_rel and its comparison domain).
consumes_inputs: B05 (MarginalFloor, r2, with its tested guard) in the last three statements. The first
 statement consumes no input.
statement: (not_supportNovel_of_carried) if S is feasible and every protocol serving S already maintains
 sufficient support for r, then r is not support-novel over S. (relation_task_third_charge) under B05, a
 tested r that is support-novel over S, with S and insert r S both ledger-admissible, satisfies
 familyCost S + epsilon <= familyCost (insert r S). (mark_mark_relation_three_floors) under B05, a novel
 chain d1, d2, r over S with all four families admissible satisfies familyCost S + 3 * epsilon <=
 familyCost of the full family. (relation_excluded_in_window) hence if the capacity is below
 familyCost S + 3 * epsilon, the full family is not ledger-admissible.
not_claimed: that any relation task is tested, admitted or support-novel; that holding two marks requires
 holding their relation; any premium over the sum of the two separate costs (the floor gives a count of
 floors, not a comparison with separately realized singleton bills).
-/
import Definitions.Def_APFPaper1_FamilyCost
import Definitions.Def_APF_B05_DeclaredInput_r2
import Mathlib.Data.NNReal.Basic
import Mathlib.Data.Finset.Insert
import Mathlib.Tactic.Linarith

set_option autoImplicit false
open APFPaper1.Source

/-- Support already carried by every serving protocol is not new support. -/
theorem APFPaper1.Source.not_supportNovel_of_carried
    {D P R Record : Type*}
    (wholeResource : P → R) (calibration : R → NNReal)
    (maintained : P → Set Record)
    (sufficient : P → Set Record → D → Prop)
    (usesToRealize : P → D → Set Record → Prop) (S : Finset D) (r : D)
    (hfeas : familyFeasible maintained sufficient usesToRealize S)
    (hcarried : ∀ p : P,
      (∀ e ∈ S, ∃ sigma : Set Record,
        sigma ⊆ maintained p ∧ sufficient p sigma e ∧ usesToRealize p e sigma) →
      ∃ sigma : Set Record, sigma ⊆ maintained p ∧ sufficient p sigma r) :
    ¬ supportNovel wholeResource calibration maintained sufficient usesToRealize S r := by
  rintro ⟨eta, heta, hwin⟩
  obtain ⟨p0, hp0⟩ := hfeas
  have hne : ({c : ℝ | ∃ p : P,
      (∀ d ∈ S, ∃ sigma : Set Record,
        sigma ⊆ maintained p ∧ sufficient p sigma d ∧ usesToRealize p d sigma) ∧
      (calibration (wholeResource p) : ℝ) = c}).Nonempty := ⟨_, p0, hp0, rfl⟩
  have hlt : familyCost wholeResource calibration maintained sufficient usesToRealize S <
      familyCost wholeResource calibration maintained sufficient usesToRealize S + eta := by
    linarith
  obtain ⟨c, ⟨p, hserve, hbill⟩, hc⟩ := exists_lt_of_csInf_lt hne hlt
  exact hwin p hserve (by rw [hbill]; exact le_of_lt hc) (hcarried p hserve)

section
variable {Context : Type*} {D P R Record : Context → Type*} [∀ g, DecidableEq (D g)]
  (wholeResource : (g : Context) → P g → R g)
  (calibration : (g : Context) → R g → NNReal)
  (maintained : (g : Context) → P g → Set (Record g))
  (sufficient : (g : Context) → P g → Set (Record g) → D g → Prop)
  (usesToRealize : (g : Context) → P g → D g → Set (Record g) → Prop)
  (tested : (g : Context) → D g → Prop)
  (C epsilon : Context → ℝ)

/-- The third charge: a tested, support-novel relation task adds at least one floor. -/
theorem APFB05.relation_task_third_charge
    (hB05 : APFB05.MarginalFloor wholeResource calibration maintained sufficient usesToRealize
      tested C epsilon)
    (g : Context) (S : Finset (D g)) (r : D g)
    (htested : tested g r)
    (hS : familyAdmissible (wholeResource g) (calibration g) (maintained g)
      (sufficient g) (usesToRealize g) (C g) S)
    (hSr : familyAdmissible (wholeResource g) (calibration g) (maintained g)
      (sufficient g) (usesToRealize g) (C g) (insert r S))
    (hnew : supportNovel (wholeResource g) (calibration g) (maintained g)
      (sufficient g) (usesToRealize g) S r) :
    familyCost (wholeResource g) (calibration g) (maintained g)
        (sufficient g) (usesToRealize g) S + epsilon g ≤
      familyCost (wholeResource g) (calibration g) (maintained g)
        (sufficient g) (usesToRealize g) (insert r S) := by
  have h := (hB05 g).2 S r htested hS hSr hnew
  linarith

/-- Mark, mark, relation as a novel chain: three floors above the starting family. -/
theorem APFB05.mark_mark_relation_three_floors
    (hB05 : APFB05.MarginalFloor wholeResource calibration maintained sufficient usesToRealize
      tested C epsilon)
    (g : Context) (S : Finset (D g)) (d1 d2 r : D g)
    (ht1 : tested g d1) (ht2 : tested g d2) (htr : tested g r)
    (h0 : familyAdmissible (wholeResource g) (calibration g) (maintained g)
      (sufficient g) (usesToRealize g) (C g) S)
    (h1 : familyAdmissible (wholeResource g) (calibration g) (maintained g)
      (sufficient g) (usesToRealize g) (C g) (insert d1 S))
    (h2 : familyAdmissible (wholeResource g) (calibration g) (maintained g)
      (sufficient g) (usesToRealize g) (C g) (insert d2 (insert d1 S)))
    (h3 : familyAdmissible (wholeResource g) (calibration g) (maintained g)
      (sufficient g) (usesToRealize g) (C g) (insert r (insert d2 (insert d1 S))))
    (hn1 : supportNovel (wholeResource g) (calibration g) (maintained g)
      (sufficient g) (usesToRealize g) S d1)
    (hn2 : supportNovel (wholeResource g) (calibration g) (maintained g)
      (sufficient g) (usesToRealize g) (insert d1 S) d2)
    (hn3 : supportNovel (wholeResource g) (calibration g) (maintained g)
      (sufficient g) (usesToRealize g) (insert d2 (insert d1 S)) r) :
    familyCost (wholeResource g) (calibration g) (maintained g)
        (sufficient g) (usesToRealize g) S + 3 * epsilon g ≤
      familyCost (wholeResource g) (calibration g) (maintained g)
        (sufficient g) (usesToRealize g) (insert r (insert d2 (insert d1 S))) := by
  have a := (hB05 g).2 S d1 ht1 h0 h1 hn1
  have b := (hB05 g).2 (insert d1 S) d2 ht2 h1 h2 hn2
  have c := (hB05 g).2 (insert d2 (insert d1 S)) r htr h2 h3 hn3
  linarith

/-- The budget window: with less than three floors of room, the relation cannot be held as well. -/
theorem APFB05.relation_excluded_in_window
    (hB05 : APFB05.MarginalFloor wholeResource calibration maintained sufficient usesToRealize
      tested C epsilon)
    (g : Context) (S : Finset (D g)) (d1 d2 r : D g)
    (ht1 : tested g d1) (ht2 : tested g d2) (htr : tested g r)
    (h0 : familyAdmissible (wholeResource g) (calibration g) (maintained g)
      (sufficient g) (usesToRealize g) (C g) S)
    (h1 : familyAdmissible (wholeResource g) (calibration g) (maintained g)
      (sufficient g) (usesToRealize g) (C g) (insert d1 S))
    (h2 : familyAdmissible (wholeResource g) (calibration g) (maintained g)
      (sufficient g) (usesToRealize g) (C g) (insert d2 (insert d1 S)))
    (hn1 : supportNovel (wholeResource g) (calibration g) (maintained g)
      (sufficient g) (usesToRealize g) S d1)
    (hn2 : supportNovel (wholeResource g) (calibration g) (maintained g)
      (sufficient g) (usesToRealize g) (insert d1 S) d2)
    (hn3 : supportNovel (wholeResource g) (calibration g) (maintained g)
      (sufficient g) (usesToRealize g) (insert d2 (insert d1 S)) r)
    (hwindow : C g < familyCost (wholeResource g) (calibration g) (maintained g)
        (sufficient g) (usesToRealize g) S + 3 * epsilon g) :
    ¬ familyAdmissible (wholeResource g) (calibration g) (maintained g)
        (sufficient g) (usesToRealize g) (C g) (insert r (insert d2 (insert d1 S))) := by
  intro h3
  have h := APFB05.mark_mark_relation_three_floors wholeResource calibration maintained sufficient
    usesToRealize tested C epsilon hB05 g S d1 d2 r ht1 ht2 htr h0 h1 h2 h3 hn1 hn2 hn3
  have hcap := h3.2
  linarith

end


universe apfNative_u_1 apfNative_u_2 apfNative_u_3 apfNative_u_4 apfNative_u_5
theorem solution :
∀ {Context : Type apfNative_u_1} {D : Context → Type apfNative_u_2} {P : Context → Type apfNative_u_3}
  {R : Context → Type apfNative_u_4} {Record : Context → Type apfNative_u_5}
  [inst : (g : Context) → DecidableEq.{apfNative_u_2 + 1} (D g)] (wholeResource : (g : Context) → P g → R g)
  (calibration : (g : Context) → R g → NNReal) (maintained : (g : Context) → P g → Set.{apfNative_u_5} (Record g))
  (sufficient : (g : Context) → P g → Set.{apfNative_u_5} (Record g) → D g → Prop)
  (usesToRealize : (g : Context) → P g → D g → Set.{apfNative_u_5} (Record g) → Prop)
  (tested : (g : Context) → D g → Prop) (C epsilon : Context → Real)
  (hB05 :
    @APFB05.MarginalFloor.{apfNative_u_1, apfNative_u_2, apfNative_u_3, apfNative_u_4, apfNative_u_5} Context D P R
      Record inst wholeResource calibration maintained sufficient usesToRealize tested C epsilon)
  (g : Context) (S : Finset.{apfNative_u_2} (D g)) (d1 d2 r : D g) (ht1 : tested g d1) (ht2 : tested g d2)
  (htr : tested g r)
  (h0 :
    @APFPaper1.Source.familyAdmissible.{apfNative_u_2, apfNative_u_3, apfNative_u_4, apfNative_u_5} (D g) (P g) (R g)
      (Record g) (wholeResource g) (calibration g) (maintained g) (sufficient g) (usesToRealize g) (C g) S)
  (h1 :
    @APFPaper1.Source.familyAdmissible.{apfNative_u_2, apfNative_u_3, apfNative_u_4, apfNative_u_5} (D g) (P g) (R g)
      (Record g) (wholeResource g) (calibration g) (maintained g) (sufficient g) (usesToRealize g) (C g)
      (@Insert.insert.{apfNative_u_2, apfNative_u_2} (D g) (Finset.{apfNative_u_2} (D g))
        (@Finset.instInsert.{apfNative_u_2} (D g) (inst g)) d1 S))
  (h2 :
    @APFPaper1.Source.familyAdmissible.{apfNative_u_2, apfNative_u_3, apfNative_u_4, apfNative_u_5} (D g) (P g) (R g)
      (Record g) (wholeResource g) (calibration g) (maintained g) (sufficient g) (usesToRealize g) (C g)
      (@Insert.insert.{apfNative_u_2, apfNative_u_2} (D g) (Finset.{apfNative_u_2} (D g))
        (@Finset.instInsert.{apfNative_u_2} (D g) (inst g)) d2
        (@Insert.insert.{apfNative_u_2, apfNative_u_2} (D g) (Finset.{apfNative_u_2} (D g))
          (@Finset.instInsert.{apfNative_u_2} (D g) (inst g)) d1 S)))
  (h3 :
    @APFPaper1.Source.familyAdmissible.{apfNative_u_2, apfNative_u_3, apfNative_u_4, apfNative_u_5} (D g) (P g) (R g)
      (Record g) (wholeResource g) (calibration g) (maintained g) (sufficient g) (usesToRealize g) (C g)
      (@Insert.insert.{apfNative_u_2, apfNative_u_2} (D g) (Finset.{apfNative_u_2} (D g))
        (@Finset.instInsert.{apfNative_u_2} (D g) (inst g)) r
        (@Insert.insert.{apfNative_u_2, apfNative_u_2} (D g) (Finset.{apfNative_u_2} (D g))
          (@Finset.instInsert.{apfNative_u_2} (D g) (inst g)) d2
          (@Insert.insert.{apfNative_u_2, apfNative_u_2} (D g) (Finset.{apfNative_u_2} (D g))
            (@Finset.instInsert.{apfNative_u_2} (D g) (inst g)) d1 S))))
  (hn1 :
    @APFPaper1.Source.supportNovel.{apfNative_u_2, apfNative_u_3, apfNative_u_4, apfNative_u_5} (D g) (P g) (R g)
      (Record g) (wholeResource g) (calibration g) (maintained g) (sufficient g) (usesToRealize g) S d1)
  (hn2 :
    @APFPaper1.Source.supportNovel.{apfNative_u_2, apfNative_u_3, apfNative_u_4, apfNative_u_5} (D g) (P g) (R g)
      (Record g) (wholeResource g) (calibration g) (maintained g) (sufficient g) (usesToRealize g)
      (@Insert.insert.{apfNative_u_2, apfNative_u_2} (D g) (Finset.{apfNative_u_2} (D g))
        (@Finset.instInsert.{apfNative_u_2} (D g) (inst g)) d1 S)
      d2)
  (hn3 :
    @APFPaper1.Source.supportNovel.{apfNative_u_2, apfNative_u_3, apfNative_u_4, apfNative_u_5} (D g) (P g) (R g)
      (Record g) (wholeResource g) (calibration g) (maintained g) (sufficient g) (usesToRealize g)
      (@Insert.insert.{apfNative_u_2, apfNative_u_2} (D g) (Finset.{apfNative_u_2} (D g))
        (@Finset.instInsert.{apfNative_u_2} (D g) (inst g)) d2
        (@Insert.insert.{apfNative_u_2, apfNative_u_2} (D g) (Finset.{apfNative_u_2} (D g))
          (@Finset.instInsert.{apfNative_u_2} (D g) (inst g)) d1 S))
      r),
  @LE.le.{0} Real Real.instLE
    (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
      (@APFPaper1.Source.familyCost.{apfNative_u_2, apfNative_u_3, apfNative_u_4, apfNative_u_5} (D g) (P g) (R g)
        (Record g) (wholeResource g) (calibration g) (maintained g) (sufficient g) (usesToRealize g) S)
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (@OfNat.ofNat.{0} Real (nat_lit 3)
          (@instOfNatAtLeastTwo.{0} Real (nat_lit 3) Real.instNatCast
            (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
              (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))))
        (epsilon g)))
    (@APFPaper1.Source.familyCost.{apfNative_u_2, apfNative_u_3, apfNative_u_4, apfNative_u_5} (D g) (P g) (R g)
      (Record g) (wholeResource g) (calibration g) (maintained g) (sufficient g) (usesToRealize g)
      (@Insert.insert.{apfNative_u_2, apfNative_u_2} (D g) (Finset.{apfNative_u_2} (D g))
        (@Finset.instInsert.{apfNative_u_2} (D g) (inst g)) r
        (@Insert.insert.{apfNative_u_2, apfNative_u_2} (D g) (Finset.{apfNative_u_2} (D g))
          (@Finset.instInsert.{apfNative_u_2} (D g) (inst g)) d2
          (@Insert.insert.{apfNative_u_2, apfNative_u_2} (D g) (Finset.{apfNative_u_2} (D g))
            (@Finset.instInsert.{apfNative_u_2} (D g) (inst g)) d1 S)))) := by
  exact @APFB05.mark_mark_relation_three_floors
