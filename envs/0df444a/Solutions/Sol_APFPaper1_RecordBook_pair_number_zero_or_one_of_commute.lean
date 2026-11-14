-- Prove2me | solution 1 for APFPaper1.RecordBook.pair_number_zero_or_one_of_commute
-- status  : ACCEPTED   (prove)
-- author  : @FiniteUniverse
-- created : 2026-11-13T17:21:21.579195+00:00
-- url     : https://prove2.me/submissions/9bf4c842-9098-4b13-9a0d-d240c3bd0d30

/-
APF Foundation Ledger — theorem node DRAFT (session EthanBrooke-01WrrBvu, 2026-11-12; not gated, not reviewed)
name: APFPaper1_pair_number
title: The number between two repeatable marks: two-valued when they commute, free when they do not
inputs_revision: 2026-10-04.1
mathlib_rev: 0df444a360eaa60ab8c11dca51a86af692955474
source: Author's remark of 2026-11-12, "Continuity is in the relation between distinctions". Paper 1
 Supplement v9.28:6276-6280 (the commuting collapse) and 6254-6355 (the two-query table, where the value
 one half appears between X and Z).
consumes_inputs: none. CONDITIONAL algebra in a real algebra: p and q are idempotent values of two marks,
 and c is supplied by the relation p * q * p = c • p (and q * p * q = c • q where used).
statement: (pair_number_zero_or_one_of_commute) if p and q are idempotent, commute, p is not zero and
 p * q * p = c • p, then c = 0 or c = 1. (pq_mul_pq, pq_mul_qp, qp_mul_pq, qp_mul_qp) with no commuting
 assumption, if p * q * p = c • p and q * p * q = c • q then the four products of p * q and q * p are
 c • (p * q), c • p, c • q and c • (q * p): the span of p, q, p * q, q * p is closed under multiplication
 with structure constants that depend on c alone.
not_claimed: that any interface supplies a real algebra of word values or the number c; that c takes any
 particular value or a continuum of values; that c can be changed by an admissible process; anything
 about time evolution or reversibility.
-/
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Algebra.Defs
import Mathlib.Algebra.NoZeroSMulDivisors.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

set_option autoImplicit false
namespace APFPaper1.RecordBook

universe uA
variable {A : Type uA} [Ring A] [Algebra ℝ A]

/-- Commuting repeatable marks: the number between them is 0 or 1. -/
theorem pair_number_zero_or_one_of_commute (p q : A) (c : ℝ)
    (hp : p * p = p) (hq : q * q = q) (hcomm : p * q = q * p)
    (hrel : p * q * p = c • p) (hp0 : p ≠ 0) : c = 0 ∨ c = 1 := by
  have hpqp : p * q * p = p * q := by rw [mul_assoc, ← hcomm, ← mul_assoc, hp]
  have h1 : p * q = c • p := by rw [← hpqp]; exact hrel
  have hidem : p * q * (p * q) = p * q := by
    calc p * q * (p * q) = p * (q * p) * q := by simp only [mul_assoc]
      _ = p * (p * q) * q := by rw [← hcomm]
      _ = (p * p) * (q * q) := by simp only [mul_assoc]
      _ = p * q := by rw [hp, hq]
  rw [h1, smul_mul_assoc, Algebra.mul_smul_comm, smul_smul, hp] at hidem
  have hz : (c * c - c) • p = 0 := by rw [sub_smul, hidem, sub_self]
  rcases smul_eq_zero.mp hz with h | h
  · have hfac : c * (c - 1) = 0 := by linarith
    rcases mul_eq_zero.mp hfac with h0 | h1'
    · exact Or.inl h0
    · exact Or.inr (by linarith)
  · exact absurd h hp0

/-- Without commuting: the products of `p * q` and `q * p` are fixed by the one number `c`. -/
theorem pq_mul_pq (p q : A) (c : ℝ) (hrel : p * q * p = c • p) :
    p * q * (p * q) = c • (p * q) := by
  rw [← mul_assoc, hrel, smul_mul_assoc]

theorem pq_mul_qp (p q : A) (c : ℝ) (hq : q * q = q) (hrel : p * q * p = c • p) :
    p * q * (q * p) = c • p := by
  rw [← mul_assoc, mul_assoc p q q, hq, hrel]

theorem qp_mul_pq (p q : A) (c : ℝ) (hp : p * p = p) (hrel' : q * p * q = c • q) :
    q * p * (p * q) = c • q := by
  rw [← mul_assoc, mul_assoc q p p, hp, hrel']

theorem qp_mul_qp (p q : A) (c : ℝ) (hrel' : q * p * q = c • q) :
    q * p * (q * p) = c • (q * p) := by
  rw [← mul_assoc, hrel', smul_mul_assoc]

end APFPaper1.RecordBook


universe apfNative_uA
theorem solution :
∀ {A : Type apfNative_uA} [inst : Ring.{apfNative_uA} A]
  [inst_1 : @Algebra.{0, apfNative_uA} Real A Real.instCommSemiring (@Ring.toSemiring.{apfNative_uA} A inst)] (p q : A)
  (c : Real)
  (hp :
    @Eq.{apfNative_uA + 1} A
      (@HMul.hMul.{apfNative_uA, apfNative_uA, apfNative_uA} A A A
        (@instHMul.{apfNative_uA} A
          (@Distrib.toMul.{apfNative_uA} A
            (@instDistribOfSemiring.{apfNative_uA} A (@Ring.toSemiring.{apfNative_uA} A inst))))
        p p)
      p)
  (hq :
    @Eq.{apfNative_uA + 1} A
      (@HMul.hMul.{apfNative_uA, apfNative_uA, apfNative_uA} A A A
        (@instHMul.{apfNative_uA} A
          (@Distrib.toMul.{apfNative_uA} A
            (@instDistribOfSemiring.{apfNative_uA} A (@Ring.toSemiring.{apfNative_uA} A inst))))
        q q)
      q)
  (hcomm :
    @Eq.{apfNative_uA + 1} A
      (@HMul.hMul.{apfNative_uA, apfNative_uA, apfNative_uA} A A A
        (@instHMul.{apfNative_uA} A
          (@Distrib.toMul.{apfNative_uA} A
            (@instDistribOfSemiring.{apfNative_uA} A (@Ring.toSemiring.{apfNative_uA} A inst))))
        p q)
      (@HMul.hMul.{apfNative_uA, apfNative_uA, apfNative_uA} A A A
        (@instHMul.{apfNative_uA} A
          (@Distrib.toMul.{apfNative_uA} A
            (@instDistribOfSemiring.{apfNative_uA} A (@Ring.toSemiring.{apfNative_uA} A inst))))
        q p))
  (hrel :
    @Eq.{apfNative_uA + 1} A
      (@HMul.hMul.{apfNative_uA, apfNative_uA, apfNative_uA} A A A
        (@instHMul.{apfNative_uA} A
          (@Distrib.toMul.{apfNative_uA} A
            (@instDistribOfSemiring.{apfNative_uA} A (@Ring.toSemiring.{apfNative_uA} A inst))))
        (@HMul.hMul.{apfNative_uA, apfNative_uA, apfNative_uA} A A A
          (@instHMul.{apfNative_uA} A
            (@Distrib.toMul.{apfNative_uA} A
              (@instDistribOfSemiring.{apfNative_uA} A (@Ring.toSemiring.{apfNative_uA} A inst))))
          p q)
        p)
      (@HSMul.hSMul.{0, apfNative_uA, apfNative_uA} Real A A
        (@instHSMul.{0, apfNative_uA} Real A
          (@Algebra.toSMul.{0, apfNative_uA} Real A Real.instCommSemiring (@Ring.toSemiring.{apfNative_uA} A inst)
            inst_1))
        c p))
  (hp0 :
    @Ne.{apfNative_uA + 1} A p
      (@OfNat.ofNat.{apfNative_uA} A (nat_lit 0)
        (@Zero.toOfNat0.{apfNative_uA} A
          (@MulZeroClass.toZero.{apfNative_uA} A
            (@instMulZeroClassOfSemiring.{apfNative_uA} A (@Ring.toSemiring.{apfNative_uA} A inst)))))),
  Or (@Eq.{1} Real c (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)))
    (@Eq.{1} Real c (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))) := by
  exact @APFPaper1.RecordBook.pair_number_zero_or_one_of_commute
