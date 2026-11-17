-- Prove2me | solution 1 for APFPaper5.K1.dominant_table_lower_bound
-- status  : ACCEPTED   (prove)
-- author  : @FiniteUniverse
-- created : 2026-11-16T14:52:40.827272+00:00
-- url     : https://prove2.me/submissions/e33b7e3d-b293-4a75-8b77-7b0bba89c693

import Definitions.Def_APFPaper5_K1_dominant_table_Vocabulary
/-
APF Foundation Ledger — theorem node DRAFT (Claude seat, session EthanBrooke-01WrrBvv, 2026-11-14; not
 gated, not reviewed, not released, not built in the ledger repo)
name: APFPaper5_K1_dominant_table
title: For any number of marks, shared or joint: a symmetric table in which each mark's own entry exceeds the total size of its entries with all the others is bilinear with a nonnegative and faithful diagonal
inputs_revision: 2026-11-14.1
mathlib_rev: 0df444a360eaa60ab8c11dca51a86af692955474
source: the author, 2026-11-14 21:44 HST: "Derive all items stil owed for k1". Item owed in
 MEMO_pullbacks_pass36_K1_finish_shared_and_joint_2026-11-14: three or more distinctions with joint
 records. Builder seat: tableForm, IsBilinear, FaithfulNonnegDiagonal, tableForm_isBilinear.
standing: A THEOREM about real tables (the classical statement that a symmetric, strictly diagonally
 dominant table with positive diagonal is positive definite). No input is consumed.
what this file says: read on a table of shared costs, where the diagonal entry is a distinction's own cost
 and an off-diagonal entry is what two distinctions save by sharing (positive) or add by a joint record
 (negative): if each distinction costs more than the sizes of all its savings and additions with the
 others put together, K1's typed conditions hold for the table. The signs do not matter.
what this file does NOT say:
 - That the condition is necessary. It is sufficient only. A table can meet K1's conditions without it;
   for two marks the exact condition is the pair bound of pass 36, which is weaker.
 - That the condition holds in any physical context or follows from the eight.
 - No lane. No claim that the transfer is forced, that the carrier gap is closed or narrowed, or that Born
   is derived.
axioms: within propext, Classical.choice, Quot.sound. No sorry.
-/
import Theorems.Thm_APFPaper5_K1_atomTable_symm
import Theorems.Thm_APFPaper5_K1_atomTable_form
import Theorems.Thm_APFPaper5_K1_atomTable_nonneg
import Theorems.Thm_APFPaper5_K1_record_book_table_satisfies_K1
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

set_option autoImplicit false

namespace APFPaper5.K1

/-- The size of twice a cross term is at most the two squares weighted by the size of the entry. -/
theorem pair_term_bound (g a b : ℝ) : -(|g| * (a * a)) - |g| * (b * b) ≤ 2 * (a * g * b) := by
  have h1 : 0 ≤ (|g| + g) * ((a + b) * (a + b)) :=
    mul_nonneg (by linarith [neg_abs_le g]) (mul_self_nonneg _)
  have h2 : 0 ≤ (|g| - g) * ((a - b) * (a - b)) :=
    mul_nonneg (by linarith [le_abs_self g]) (mul_self_nonneg _)
  nlinarith [h1, h2]

variable {ι : Type*} [Fintype ι] [DecidableEq ι]



/-- Twice the form is at least the sum over marks of twice (own entry less the sizes of its entries with
the others) times the square. -/
theorem dominant_table_lower_bound (G : ι → ι → ℝ) (hsymm : ∀ i j, G i j = G j i) (x : ι → ℝ) :
    ∑ i, 2 * ((G i i - ∑ j, offSize G i j) * (x i * x i)) ≤ 2 * tableForm G x x := by
  have hoff : ∀ i j, offSize G i j = offSize G j i := by
    intro i j
    unfold offSize
    by_cases h : i = j
    · subst h
      rfl
    · have h' : ¬ j = i := fun e => h e.symm
      rw [if_neg h, if_neg h', hsymm i j]
  have hterm : ∀ i j,
      (if i = j then 2 * (G i i * (x i * x i)) else 0) - offSize G i j * (x i * x i) -
          offSize G i j * (x j * x j) ≤ 2 * (x i * G i j * x j) := by
    intro i j
    by_cases h : i = j
    · subst h
      have h0 : offSize G i i = 0 := by
        unfold offSize
        rw [if_pos rfl]
      rw [if_pos rfl, h0]
      apply le_of_eq
      ring
    · have hij : offSize G i j = |G i j| := by
        unfold offSize
        rw [if_neg h]
      rw [if_neg h, hij]
      have := pair_term_bound (G i j) (x i) (x j)
      linarith
  have hsum : ∑ i, ∑ j,
      ((if i = j then 2 * (G i i * (x i * x i)) else 0) - offSize G i j * (x i * x i) -
          offSize G i j * (x j * x j)) ≤ ∑ i, ∑ j, 2 * (x i * G i j * x j) :=
    Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun j _ => hterm i j))
  have hR : ∑ i, ∑ j, 2 * (x i * G i j * x j) = 2 * tableForm G x x := by
    unfold tableForm
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.mul_sum]
  have hswap : ∑ i, ∑ j, offSize G i j * (x j * x j) = ∑ i, ∑ j, offSize G i j * (x i * x i) := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro i _
    rw [hoff i j]
  have hdiag : ∑ i, ∑ j, (if i = j then 2 * (G i i * (x i * x i)) else 0) =
      ∑ i, 2 * (G i i * (x i * x i)) := by
    apply Finset.sum_congr rfl
    intro i _
    simp
  have hL : ∑ i, ∑ j,
      ((if i = j then 2 * (G i i * (x i * x i)) else 0) - offSize G i j * (x i * x i) -
          offSize G i j * (x j * x j)) =
      ∑ i, 2 * (G i i * (x i * x i)) - ∑ i, ∑ j, offSize G i j * (x i * x i) -
        ∑ i, ∑ j, offSize G i j * (x i * x i) := by
    simp only [Finset.sum_sub_distrib]
    rw [hdiag, hswap]
  have hC : ∑ i, 2 * ((G i i - ∑ j, offSize G i j) * (x i * x i)) =
      ∑ i, 2 * (G i i * (x i * x i)) - ∑ i, ∑ j, offSize G i j * (x i * x i) -
        ∑ i, ∑ j, offSize G i j * (x i * x i) := by
    rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    rw [← Finset.sum_mul]
    ring
  rw [hC, ← hL, ← hR]
  exact hsum

/-- K1's typed conditions for a symmetric table in which each mark's own entry exceeds the total size of
its entries with the others. -/
theorem dominant_table_meets_K1 (G : ι → ι → ℝ) (hsymm : ∀ i j, G i j = G j i)
    (hdom : ∀ i, ∑ j, offSize G i j < G i i) :
    IsBilinear (VP := ι → ℝ) (VE := ι → ℝ) (tableForm G) ∧
      FaithfulNonnegDiagonal (tableForm G) (LinearEquiv.refl ℝ (ι → ℝ)) := by
  have hpos : ∀ i, 0 < G i i - ∑ j, offSize G i j := fun i => by linarith [hdom i]
  have hnn : ∀ (x : ι → ℝ) (i : ι), 0 ≤ 2 * ((G i i - ∑ j, offSize G i j) * (x i * x i)) :=
    fun x i => mul_nonneg (by norm_num) (mul_nonneg (hpos i).le (mul_self_nonneg _))
  refine ⟨tableForm_isBilinear _, fun x => ?_, fun x hx => ?_⟩
  · show 0 ≤ tableForm G x x
    have h := dominant_table_lower_bound G hsymm x
    have h2 : 0 ≤ ∑ i, 2 * ((G i i - ∑ j, offSize G i j) * (x i * x i)) :=
      Finset.sum_nonneg (fun i _ => hnn x i)
    linarith
  · have hx' : tableForm G x x = 0 := hx
    have h := dominant_table_lower_bound G hsymm x
    rw [hx', mul_zero] at h
    have hz : ∑ i, 2 * ((G i i - ∑ j, offSize G i j) * (x i * x i)) = 0 :=
      le_antisymm h (Finset.sum_nonneg (fun i _ => hnn x i))
    have hall := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => hnn x i)).mp hz
    funext i
    have hi := hall i (Finset.mem_univ i)
    have hxx : x i * x i = 0 := by
      have h3 : (G i i - ∑ j, offSize G i j) * (x i * x i) = 0 := by linarith
      rcases mul_eq_zero.mp h3 with h4 | h4
      · exact absurd h4 (hpos i).ne'
      · exact h4
    simpa using mul_self_eq_zero.mp hxx

end APFPaper5.K1


universe apfNative_u_1
theorem solution :
∀ {ι : Type apfNative_u_1} [inst : Fintype.{apfNative_u_1} ι] [inst_1 : DecidableEq.{apfNative_u_1 + 1} ι]
  (G : ι → ι → Real) (hsymm : ∀ (i j : ι), @Eq.{1} Real (G i j) (G j i)) (x : ι → Real),
  @LE.le.{0} Real Real.instLE
    (@Finset.sum.{apfNative_u_1, 0} ι Real Real.instAddCommMonoid (@Finset.univ.{apfNative_u_1} ι inst) fun (i : ι) =>
      @HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (@OfNat.ofNat.{0} Real (nat_lit 2)
          (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
            (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
              (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
          (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) (G i i)
            (@Finset.sum.{apfNative_u_1, 0} ι Real Real.instAddCommMonoid (@Finset.univ.{apfNative_u_1} ι inst)
              fun (j : ι) => @APFPaper5.K1.offSize.{apfNative_u_1} ι inst_1 G i j))
          (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) (x i) (x i))))
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (@OfNat.ofNat.{0} Real (nat_lit 2)
        (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
          (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
            (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
      (@APFPaper5.K1.tableForm.{apfNative_u_1} ι inst G x x)) := by
  exact @APFPaper5.K1.dominant_table_lower_bound
