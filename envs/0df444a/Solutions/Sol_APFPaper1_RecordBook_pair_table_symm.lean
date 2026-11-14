-- Prove2me | solution 1 for APFPaper1.RecordBook.pair_table_symm
-- status  : ACCEPTED   (prove)
-- author  : @FiniteUniverse
-- created : 2026-11-13T17:21:33.332207+00:00
-- url     : https://prove2.me/submissions/b4c0b11c-eb0b-4576-be85-acfc9df948c1

/-
APF Foundation Ledger — theorem node DRAFT (session EthanBrooke-01WrrBvu, 2026-11-12; not gated, not reviewed)
name: APFPaper1_pair_number_symm
title: The number between two marks is the same from either side, because the four-letter word is one word
inputs_revision: 2026-10-04.1
mathlib_rev: 0df444a360eaa60ab8c11dca51a86af692955474
source: Author's remark of 2026-11-12, "Symmetry is cheaper because it's the same information when it's
 turned". Consulted: Paper 5 Supplement v7.33:311-350 (the scalar ledger does not determine the ordered
 two-ended score; counterfamily with an alternating part) and 476-512 (Q2C, scalar swap symmetry does not give
 closure under reversal). Codebank and archive: no statement of this result found by keyword search.
consumes_inputs: none. CONDITIONAL algebra in a real algebra: the numbers c and c' are supplied by the two
 pair relations p * q * p = c • p and q * p * q = c' • q.
statement: (word4_two_readings) p * q * p * q read from the front is (p * q * p) * q and read from the back is
 p * (q * p * q). (pair_number_symm) if p and q are not zero and both pair relations hold, then c = c'.
 (pair_table_symm) so the table of pair numbers of a family of nonzero marks is symmetric.
 (pair_number_self) a nonzero repeatable mark scores 1 against itself.
not_claimed: that either pair relation holds at any interface; that the number is nonnegative or at most 1
 (it need not be: see Thm_APFPaper5_K3_two_mark_exchange, slanted marks); a role-exchange map; closure of
 admitted processes under reversal, which the Supplement's Q2C shows is a separate matter.
-/
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Algebra.Defs
import Mathlib.Algebra.NoZeroSMulDivisors.Basic

set_option autoImplicit false
namespace APFPaper1.RecordBook

universe uA uI
variable {A : Type uA} [Ring A] [Algebra ℝ A]

omit [Algebra ℝ A] in
/-- One four-letter word, read from the front and from the back. -/
theorem word4_two_readings (p q : A) : p * q * p * q = p * (q * p * q) := by
  simp only [mul_assoc]

/-- The number between two marks is the same from either side. -/
theorem pair_number_symm (p q : A) (c c' : ℝ) (hp0 : p ≠ 0) (hq0 : q ≠ 0)
    (hrel : p * q * p = c • p) (hrel' : q * p * q = c' • q) : c = c' := by
  by_cases hpq : p * q = 0
  · have h1 : c • p = 0 := by rw [← hrel, hpq, zero_mul]
    have h2 : c' • q = 0 := by rw [← hrel', mul_assoc, hpq, mul_zero]
    have hc : c = 0 := (smul_eq_zero.mp h1).resolve_right hp0
    have hc' : c' = 0 := (smul_eq_zero.mp h2).resolve_right hq0
    rw [hc, hc']
  · have h1 : p * q * p * q = c • (p * q) := by rw [hrel, smul_mul_assoc]
    have h2 : p * q * p * q = c' • (p * q) := by
      rw [word4_two_readings p q, hrel', Algebra.mul_smul_comm]
    have h3 : (c - c') • (p * q) = 0 := by rw [sub_smul, ← h1, ← h2, sub_self]
    rcases smul_eq_zero.mp h3 with h | h
    · exact sub_eq_zero.mp h
    · exact absurd h hpq

/-- The table of pair numbers of a family of nonzero marks is symmetric. -/
theorem pair_table_symm {ι : Type uI} (p : ι → A) (c : ι → ι → ℝ) (hp0 : ∀ i, p i ≠ 0)
    (hrel : ∀ i j, p i * p j * p i = c i j • p i) : ∀ i j, c i j = c j i :=
  fun i j => pair_number_symm (p i) (p j) (c i j) (c j i) (hp0 i) (hp0 j) (hrel i j) (hrel j i)

/-- A nonzero repeatable mark scores 1 against itself. -/
theorem pair_number_self (p : A) (c : ℝ) (hp0 : p ≠ 0) (hp : p * p = p)
    (hrel : p * p * p = c • p) : c = 1 := by
  have h : (c - 1) • p = 0 := by rw [sub_smul, one_smul, ← hrel, hp, hp, sub_self]
  rcases smul_eq_zero.mp h with h | h
  · exact sub_eq_zero.mp h
  · exact absurd h hp0

end APFPaper1.RecordBook


universe apfNative_uA apfNative_uI
theorem solution :
∀ {A : Type apfNative_uA} [inst : Ring.{apfNative_uA} A]
  [inst_1 : @Algebra.{0, apfNative_uA} Real A Real.instCommSemiring (@Ring.toSemiring.{apfNative_uA} A inst)]
  {ι : Type apfNative_uI} (p : ι → A) (c : ι → ι → Real)
  (hp0 :
    ∀ (i : ι),
      @Ne.{apfNative_uA + 1} A (p i)
        (@OfNat.ofNat.{apfNative_uA} A (nat_lit 0)
          (@Zero.toOfNat0.{apfNative_uA} A
            (@MulZeroClass.toZero.{apfNative_uA} A
              (@instMulZeroClassOfSemiring.{apfNative_uA} A (@Ring.toSemiring.{apfNative_uA} A inst))))))
  (hrel :
    ∀ (i j : ι),
      @Eq.{apfNative_uA + 1} A
        (@HMul.hMul.{apfNative_uA, apfNative_uA, apfNative_uA} A A A
          (@instHMul.{apfNative_uA} A
            (@Distrib.toMul.{apfNative_uA} A
              (@instDistribOfSemiring.{apfNative_uA} A (@Ring.toSemiring.{apfNative_uA} A inst))))
          (@HMul.hMul.{apfNative_uA, apfNative_uA, apfNative_uA} A A A
            (@instHMul.{apfNative_uA} A
              (@Distrib.toMul.{apfNative_uA} A
                (@instDistribOfSemiring.{apfNative_uA} A (@Ring.toSemiring.{apfNative_uA} A inst))))
            (p i) (p j))
          (p i))
        (@HSMul.hSMul.{0, apfNative_uA, apfNative_uA} Real A A
          (@instHSMul.{0, apfNative_uA} Real A
            (@Algebra.toSMul.{0, apfNative_uA} Real A Real.instCommSemiring (@Ring.toSemiring.{apfNative_uA} A inst)
              inst_1))
          (c i j) (p i)))
  (i j : ι), @Eq.{1} Real (c i j) (c j i) := by
  exact @APFPaper1.RecordBook.pair_table_symm
