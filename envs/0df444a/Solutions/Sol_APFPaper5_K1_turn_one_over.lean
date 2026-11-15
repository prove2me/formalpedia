-- Prove2me | solution 1 for APFPaper5.K1.turn_one_over
-- status  : ACCEPTED   (prove)
-- author  : @FiniteUniverse
-- created : 2026-11-14T06:30:11.798584+00:00
-- url     : https://prove2.me/submissions/c419be26-e774-47ed-bb75-da3b4ff08965

/-
APF Foundation Ledger — theorem node DRAFT (session EthanBrooke-01WrrBvu, 2026-11-13; not gated, not reviewed)
name: APFPaper5_K1_oriented_count
title: Counting records that have two sides: the cost is still the count, the overlap becomes agreements less oppositions and can be negative, the recombination and the distance between are counts, and turning one record over moves the overlap by two at fixed costs
inputs_revision: 2026-10-04.1
mathlib_rev: 0df444a360eaa60ab8c11dca51a86af692955474
source: the author's question of 2026-11-13 17:44 HST ("The count - what are we counting? Something physical
 ... it has to have at least two sides? Physicality implies orientation as well as the distance between?").
 FOUNDATION_INPUTS B02 ("A distinction is a finite, enforceable separator of continuation profiles"; its
 declared form asks every distinction to take both values). The record model of K1 (overlap as a count of
 shared records). Thm_APFPaper5_K3_two_components (records_are_cross_data: the recombination record is the
 two costs plus twice the cross term).
consumes_inputs: none as a declared predicate.
standing: a supplied MODEL of what the question proposes. Each record is held on one of two sides or not at
 all: a holding is a function from records to the reals, with values 1, -1 and 0 in the intended reading.
 The theorems are stated for any real values.
statement: a and b are two holdings. The cost of a holding is the sum of the squares of its values (for
 values 1, -1, 0: the number of records held, whichever side). The overlap is the sum of the products (for
 those values: records held on the same side, less records held on opposite sides).
 (recombination_is_a_count) the sum of the squares of a + b is the two costs plus twice the overlap.
 (distance_is_a_count) the sum of the squares of a - b is the two costs less twice the overlap.
 (overlap_between_bounds) so twice the overlap lies between minus and plus the sum of the two costs.
 (turn_all_over) turning every record of b over keeps the cost of b and reverses the overlap.
 (turn_one_over, turn_one_over_keeps_cost) turning one record of b over keeps the cost of b and lowers the
 overlap by twice the product of the two values there: by two if the two agreed there, raises it by two if
 they opposed.
reading: with two-sided records the count model has a relation that can be negative and that moves through
 its range one record at a time while both costs stay fixed and no record is drawn or erased. The identity
 for the recombination is the one the two-component model has.
not_claimed: that the records the ledger counts have two sides (B02 says it of distinctions; that a kept
 record is held on a side is the proposal under test); anything continuous; the quarter turn or the rate,
 which two sides do not give (mirror_has_no_half); that an interface is the two-component model.
-/
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

set_option autoImplicit false
namespace APFPaper5.K1

theorem recombination_is_a_count {Rec : Type*} [Fintype Rec] (a b : Rec → ℝ) :
    ∑ r, (a r + b r) * (a r + b r) = ∑ r, a r * a r + ∑ r, b r * b r + 2 * ∑ r, a r * b r := by
  have h : ∀ r : Rec, (a r + b r) * (a r + b r) =
      a r * a r + b r * b r + (a r * b r + a r * b r) := fun r => by ring
  rw [Finset.sum_congr rfl (fun r _ => h r), Finset.sum_add_distrib, Finset.sum_add_distrib,
    Finset.sum_add_distrib, two_mul]

theorem distance_is_a_count {Rec : Type*} [Fintype Rec] (a b : Rec → ℝ) :
    ∑ r, (a r - b r) * (a r - b r) = ∑ r, a r * a r + ∑ r, b r * b r - 2 * ∑ r, a r * b r := by
  have h : ∀ r : Rec, (a r - b r) * (a r - b r) =
      a r * a r + b r * b r - (a r * b r + a r * b r) := fun r => by ring
  rw [Finset.sum_congr rfl (fun r _ => h r), Finset.sum_sub_distrib, Finset.sum_add_distrib,
    Finset.sum_add_distrib, two_mul]

theorem overlap_between_bounds {Rec : Type*} [Fintype Rec] (a b : Rec → ℝ) :
    -(∑ r, a r * a r + ∑ r, b r * b r) ≤ 2 * ∑ r, a r * b r ∧
      2 * ∑ r, a r * b r ≤ ∑ r, a r * a r + ∑ r, b r * b r := by
  have h1 : 0 ≤ ∑ r, (a r + b r) * (a r + b r) :=
    Finset.sum_nonneg (fun r _ => mul_self_nonneg _)
  have h2 : 0 ≤ ∑ r, (a r - b r) * (a r - b r) :=
    Finset.sum_nonneg (fun r _ => mul_self_nonneg _)
  rw [recombination_is_a_count] at h1
  rw [distance_is_a_count] at h2
  exact ⟨by linarith, by linarith⟩

theorem turn_all_over {Rec : Type*} [Fintype Rec] (a b : Rec → ℝ) :
    ∑ r, (-b r) * (-b r) = ∑ r, b r * b r ∧ ∑ r, a r * (-b r) = -∑ r, a r * b r := by
  refine ⟨Finset.sum_congr rfl (fun r _ => by ring), ?_⟩
  rw [← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl (fun r _ => by ring)

theorem turn_one_over {Rec : Type*} [Fintype Rec] [DecidableEq Rec] (a b : Rec → ℝ) (r0 : Rec) :
    ∑ r, a r * (if r = r0 then -b r else b r) = ∑ r, a r * b r - 2 * (a r0 * b r0) := by
  have h : ∀ r : Rec, a r * (if r = r0 then -b r else b r) =
      a r * b r - (if r = r0 then 2 * (a r0 * b r0) else 0) := by
    intro r
    by_cases hr : r = r0
    · rw [if_pos hr, if_pos hr, hr]
      ring
    · rw [if_neg hr, if_neg hr]
      ring
  rw [Finset.sum_congr rfl (fun r _ => h r), Finset.sum_sub_distrib, Finset.sum_ite_eq',
    if_pos (Finset.mem_univ r0)]

theorem turn_one_over_keeps_cost {Rec : Type*} [Fintype Rec] [DecidableEq Rec] (b : Rec → ℝ)
    (r0 : Rec) :
    ∑ r, (if r = r0 then -b r else b r) * (if r = r0 then -b r else b r) = ∑ r, b r * b r := by
  refine Finset.sum_congr rfl (fun r _ => ?_)
  by_cases hr : r = r0
  · rw [if_pos hr]
    ring
  · rw [if_neg hr]

end APFPaper5.K1


universe apfNative_u_1
theorem solution :
∀ {Rec : Type apfNative_u_1} [inst : Fintype.{apfNative_u_1} Rec] [inst_1 : DecidableEq.{apfNative_u_1 + 1} Rec]
  (a b : Rec → Real) (r0 : Rec),
  @Eq.{1} Real
    (@Finset.sum.{apfNative_u_1, 0} Rec Real Real.instAddCommMonoid (@Finset.univ.{apfNative_u_1} Rec inst)
      fun (r : Rec) =>
      @HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) (a r)
        (@ite.{1} Real (@Eq.{apfNative_u_1 + 1} Rec r r0) (inst_1 r r0) (@Neg.neg.{0} Real Real.instNeg (b r)) (b r)))
    (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
      (@Finset.sum.{apfNative_u_1, 0} Rec Real Real.instAddCommMonoid (@Finset.univ.{apfNative_u_1} Rec inst)
        fun (r : Rec) => @HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) (a r) (b r))
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (@OfNat.ofNat.{0} Real (nat_lit 2)
          (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
            (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
              (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) (a r0) (b r0)))) := by
  exact @APFPaper5.K1.turn_one_over
