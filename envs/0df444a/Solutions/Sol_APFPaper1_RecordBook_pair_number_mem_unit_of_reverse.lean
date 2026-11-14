-- Prove2me | solution 1 for APFPaper1.RecordBook.pair_number_mem_unit_of_reverse
-- status  : ACCEPTED   (prove)
-- author  : @FiniteUniverse
-- created : 2026-11-13T17:19:43.519837+00:00
-- url     : https://prove2.me/submissions/7739767a-9389-418d-95ce-808f629502f8

/-
APF Foundation Ledger — theorem node DRAFT (session EthanBrooke-01WrrBvu, 2026-11-12; not gated, not reviewed)
name: APFPaper1_pair_number_range
title: If words can be read backwards, marks read the same backwards, and a word against its reverse never scores negative, the pair number lies from 0 to 1
inputs_revision: 2026-10-04.1
mathlib_rev: 0df444a360eaa60ab8c11dca51a86af692955474
source: Paper 5 Supplement v7.33:427-470 (closed-ledger internal adjoint; orientation reversal is the whole
 internal-adjoint burden). Thm_APFPaper1_pair_number_symm.
consumes_inputs: none. CONDITIONAL algebra in a real algebra. The reversal rev and its four laws are
 hypotheses, as is the positivity clause hpos.
statement: (pair_number_mem_unit_of_reverse) let p and q be repeatable with p * q * p = c • p. Let rev reverse
 products, respect differences, and fix p and q. If rev x * x = t • p always forces 0 ≤ t, then 0 ≤ c ≤ 1.
not_claimed: that the ledger supplies a reversal; that marks read the same backwards; the positivity clause.
 These are the reversal obligations the Supplement lists and they stay open.
-/
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Algebra.Defs
import Mathlib.Tactic.Linarith

set_option autoImplicit false
namespace APFPaper1.RecordBook

universe uA
variable {A : Type uA} [Ring A] [Algebra ℝ A]

theorem pair_number_mem_unit_of_reverse (p q : A) (c : ℝ) (rev : A → A)
    (hp : p * p = p) (hq : q * q = q) (hrel : p * q * p = c • p)
    (hmul : ∀ x y : A, rev (x * y) = rev y * rev x)
    (hsub : ∀ x y : A, rev (x - y) = rev x - rev y)
    (hrp : rev p = p) (hrq : rev q = q)
    (hpos : ∀ (x : A) (t : ℝ), rev x * x = t • p → 0 ≤ t) : 0 ≤ c ∧ c ≤ 1 := by
  have hqqp : q * (q * p) = q * p := by rw [← mul_assoc, hq]
  have hpqp : p * (q * p) = c • p := by rw [← mul_assoc]; exact hrel
  have hpqqp : p * q * (q * p) = c • p := by rw [mul_assoc p q (q * p), hqqp, hpqp]
  have h1 : rev (q * p) * (q * p) = c • p := by rw [hmul, hrp, hrq]; exact hpqqp
  have h2 : rev (p - q * p) * (p - q * p) = (1 - c) • p := by
    rw [hsub, hmul, hrp, hrq, mul_sub, sub_mul, sub_mul, hp, hrel, hpqp, hpqqp, sub_self,
      sub_zero, sub_smul, one_smul]
  have hc0 := hpos _ _ h1
  have hc1 := hpos _ _ h2
  exact ⟨hc0, by linarith⟩

end APFPaper1.RecordBook


universe apfNative_uA
theorem solution :
∀ {A : Type apfNative_uA} [inst : Ring.{apfNative_uA} A]
  [inst_1 : @Algebra.{0, apfNative_uA} Real A Real.instCommSemiring (@Ring.toSemiring.{apfNative_uA} A inst)] (p q : A)
  (c : Real) (rev : A → A)
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
  (hmul :
    ∀ (x y : A),
      @Eq.{apfNative_uA + 1} A
        (rev
          (@HMul.hMul.{apfNative_uA, apfNative_uA, apfNative_uA} A A A
            (@instHMul.{apfNative_uA} A
              (@Distrib.toMul.{apfNative_uA} A
                (@instDistribOfSemiring.{apfNative_uA} A (@Ring.toSemiring.{apfNative_uA} A inst))))
            x y))
        (@HMul.hMul.{apfNative_uA, apfNative_uA, apfNative_uA} A A A
          (@instHMul.{apfNative_uA} A
            (@Distrib.toMul.{apfNative_uA} A
              (@instDistribOfSemiring.{apfNative_uA} A (@Ring.toSemiring.{apfNative_uA} A inst))))
          (rev y) (rev x)))
  (hsub :
    ∀ (x y : A),
      @Eq.{apfNative_uA + 1} A
        (rev
          (@HSub.hSub.{apfNative_uA, apfNative_uA, apfNative_uA} A A A
            (@instHSub.{apfNative_uA} A
              (@SubNegMonoid.toSub.{apfNative_uA} A
                (@AddGroup.toSubNegMonoid.{apfNative_uA} A
                  (@AddGroupWithOne.toAddGroup.{apfNative_uA} A (@Ring.toAddGroupWithOne.{apfNative_uA} A inst)))))
            x y))
        (@HSub.hSub.{apfNative_uA, apfNative_uA, apfNative_uA} A A A
          (@instHSub.{apfNative_uA} A
            (@SubNegMonoid.toSub.{apfNative_uA} A
              (@AddGroup.toSubNegMonoid.{apfNative_uA} A
                (@AddGroupWithOne.toAddGroup.{apfNative_uA} A (@Ring.toAddGroupWithOne.{apfNative_uA} A inst)))))
          (rev x) (rev y)))
  (hrp : @Eq.{apfNative_uA + 1} A (rev p) p) (hrq : @Eq.{apfNative_uA + 1} A (rev q) q)
  (hpos :
    ∀ (x : A) (t : Real),
      @Eq.{apfNative_uA + 1} A
          (@HMul.hMul.{apfNative_uA, apfNative_uA, apfNative_uA} A A A
            (@instHMul.{apfNative_uA} A
              (@Distrib.toMul.{apfNative_uA} A
                (@instDistribOfSemiring.{apfNative_uA} A (@Ring.toSemiring.{apfNative_uA} A inst))))
            (rev x) x)
          (@HSMul.hSMul.{0, apfNative_uA, apfNative_uA} Real A A
            (@instHSMul.{0, apfNative_uA} Real A
              (@Algebra.toSMul.{0, apfNative_uA} Real A Real.instCommSemiring (@Ring.toSemiring.{apfNative_uA} A inst)
                inst_1))
            t p) →
        @LE.le.{0} Real Real.instLE (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) t),
  And (@LE.le.{0} Real Real.instLE (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) c)
    (@LE.le.{0} Real Real.instLE c (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))) := by
  exact @APFPaper1.RecordBook.pair_number_mem_unit_of_reverse
