-- Prove2me | solution 1 for APFPaper5.K1.repeated_draw_bounded
-- status  : ACCEPTED   (prove)
-- author  : @FiniteUniverse
-- created : 2026-11-14T06:13:46.097817+00:00
-- url     : https://prove2.me/submissions/2ad1d739-01db-4152-abf8-a541defe5dcc

/-
APF Foundation Ledger — theorem node DRAFT (session EthanBrooke-01WrrBvu, 2026-11-13; not gated, not reviewed)
name: APFPaper5_K1_bill_is_a_sum
title: When the bill is the sum of the costs of the records kept: the empty protocol bills nothing, a hold that draws nothing and erases nothing bills nothing more, a step that draws new records each time adds their cost each time, and such a step can be taken only so many times
inputs_revision: 2026-10-04.1
mathlib_rev: 0df444a360eaa60ab8c11dca51a86af692955474
source: the author's statement of 2026-11-13 16:38 HST ("You can derive the things you list as still supplied
 at least the first two"). FOUNDATION_INPUTS B07a, whose definition node binds A2's price to "the ORIGINAL
 total admissibility cost (sum of distinction costs in the adopted Paper0 statement)"; B03; B04. The RECORDS
 clause adopted 2026-11-12 (the record model: a protocol is the set of records it keeps, and its bill is the
 sum of their costs). The hold sentence adopted 2026-11-13 ("Under a hold, distinctions aren't drawn or
 erased, just rearranged").
consumes_inputs: none as a declared predicate. The price is taken to be a sum over the records kept, which
 is what A2's node says the price is and what the RECORDS clause types. A2's declared Lean form leaves the
 price a supplied function, so nothing here follows from that form alone.
statement: K is the set of records a protocol keeps, w the cost of each record, and the bill is the sum of w
 over K.
 (bill_empty) the protocol that keeps nothing bills nothing.
 (hold_bills_nothing_more) if after a step no record has been added and none removed, the bill is the same.
 (bill_of_draw) adding records that were not kept adds exactly their cost.
 (bill_of_repeated_draw) a step that adds new records costing b each time it is taken has, after n times,
 the starting bill plus n times b.
 (repeated_draw_bounded) if b > 0, record costs are not negative and the bill after n times is at most the
 capacity, then n is at most the capacity divided by b.
reading: with the price read as the source reads it, "the bill of a repeated step adds up" and "a hold bills
 nothing" are not assumptions. They are what a sum is.
not_claimed: that the calibrated whole-resource bill of the ledger is this sum for every protocol; that link
 is the RECORDS clause (ledger item B3 in the sibling seat's hypothesis ledger), adopted and not derived
 from the declared forms. That a hold keeps the same records is the hold sentence.
-/
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

set_option autoImplicit false
namespace APFPaper5.K1

theorem bill_empty {Rec : Type*} (w : Rec → ℝ) : ∑ r ∈ (∅ : Finset Rec), w r = 0 :=
  Finset.sum_empty

theorem hold_bills_nothing_more {Rec : Type*} (w : Rec → ℝ) (K K' : Finset Rec)
    (hnodraw : K' ⊆ K) (hnoerase : K ⊆ K') : ∑ r ∈ K', w r = ∑ r ∈ K, w r := by
  rw [Finset.Subset.antisymm hnodraw hnoerase]

theorem bill_of_draw {Rec : Type*} [DecidableEq Rec] (w : Rec → ℝ) (K N : Finset Rec)
    (hnew : Disjoint K N) : ∑ r ∈ K ∪ N, w r = ∑ r ∈ K, w r + ∑ r ∈ N, w r :=
  Finset.sum_union hnew

theorem bill_of_repeated_draw {Rec : Type*} [DecidableEq Rec] (w : Rec → ℝ) (b : ℝ)
    (K N : ℕ → Finset Rec) (hstep : ∀ n : ℕ, K (n + 1) = K n ∪ N n)
    (hnew : ∀ n : ℕ, Disjoint (K n) (N n)) (hb : ∀ n : ℕ, ∑ r ∈ N n, w r = b) (n : ℕ) :
    ∑ r ∈ K n, w r = ∑ r ∈ K 0, w r + n * b := by
  induction n with
  | zero => rw [Nat.cast_zero, zero_mul, add_zero]
  | succ k ih =>
    rw [hstep k, bill_of_draw w (K k) (N k) (hnew k), ih, hb k]
    push_cast
    ring

theorem repeated_draw_bounded {Rec : Type*} [DecidableEq Rec] (w : Rec → ℝ) (b C : ℝ)
    (hw : ∀ r : Rec, 0 ≤ w r) (hbpos : 0 < b)
    (K N : ℕ → Finset Rec) (hstep : ∀ n : ℕ, K (n + 1) = K n ∪ N n)
    (hnew : ∀ n : ℕ, Disjoint (K n) (N n)) (hb : ∀ n : ℕ, ∑ r ∈ N n, w r = b) (n : ℕ)
    (hC : ∑ r ∈ K n, w r ≤ C) : (n : ℝ) ≤ C / b := by
  have h0 : 0 ≤ ∑ r ∈ K 0, w r := Finset.sum_nonneg (fun r _ => hw r)
  rw [bill_of_repeated_draw w b K N hstep hnew hb n] at hC
  exact (le_div_iff₀ hbpos).mpr (by linarith)

end APFPaper5.K1


universe apfNative_u_1
theorem solution :
∀ {Rec : Type apfNative_u_1} [inst : DecidableEq.{apfNative_u_1 + 1} Rec] (w : Rec → Real) (b C : Real)
  (hw :
    ∀ (r : Rec),
      @LE.le.{0} Real Real.instLE (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) (w r))
  (hbpos : @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) b)
  (K N : Nat → Finset.{apfNative_u_1} Rec)
  (hstep :
    ∀ (n : Nat),
      @Eq.{apfNative_u_1 + 1} (Finset.{apfNative_u_1} Rec)
        (K
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n
            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
        (@Union.union.{apfNative_u_1} (Finset.{apfNative_u_1} Rec) (@Finset.instUnion.{apfNative_u_1} Rec inst) (K n)
          (N n)))
  (hnew :
    ∀ (n : Nat),
      @Disjoint.{apfNative_u_1} (Finset.{apfNative_u_1} Rec) (@Finset.instPartialOrder.{apfNative_u_1} Rec)
        (@Finset.instOrderBot.{apfNative_u_1} Rec) (K n) (N n))
  (hb :
    ∀ (n : Nat),
      @Eq.{1} Real (@Finset.sum.{apfNative_u_1, 0} Rec Real Real.instAddCommMonoid (N n) fun (r : Rec) => w r) b)
  (n : Nat)
  (hC :
    @LE.le.{0} Real Real.instLE
      (@Finset.sum.{apfNative_u_1, 0} Rec Real Real.instAddCommMonoid (K n) fun (r : Rec) => w r) C),
  @LE.le.{0} Real Real.instLE (@Nat.cast.{0} Real Real.instNatCast n)
    (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid)) C b) := by
  exact @APFPaper5.K1.repeated_draw_bounded
