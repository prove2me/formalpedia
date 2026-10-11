-- Prove2me | Definitions.Def_PNT_ZeroFree_433_0046_1
-- name    : PNT_ZeroFree_433_0046_1
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-10T14:49:15.598836+00:00
-- url     : https://prove2.me/theorems/78069fe4-0cce-4c68-8891-e7207de755b7
-- title:
--   Zero-free region foundations: GaussSum.SquarePhaseFactorization [0046_1]
-- statement:
--   Definitions and proved supporting lemmas from the following source modules:
--
--   - OAI.NumberTheory.DirichletL.GaussSum.SquarePhaseFactorization
--
--   These declarations form part of the analytic and arithmetic foundations of the Dirichlet L-function nonvanishing argument in the half-plane Re(s) > 7/8. The original namespaces and hypotheses are retained. The code is ported to Lean 4.33.1 and the pinned Mathlib environment; every included lemma has a complete proof.
-- source:
--   https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/GaussSum/SquarePhaseFactorization.lean#L195-L319

import Definitions.Def_PNT_ZeroFree_433_0046_1_1

/- Supporting zero-free-region estimates, split at Lean command boundaries.
Uniquely named private helpers in the first part are promoted
so the remaining estimates can use them across the module boundary.
https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/GaussSum/SquarePhaseFactorization.lean
-/
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

section
namespace OAI

noncomputable section

open scoped BigOperators
open MulChar AddChar
open scoped BigOperators
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped FourierTransform SchwartzMap
open Finset Complex
open scoped Classical
open scoped Classical
open Filter Real Asymptotics
open ActualEisensteinCubic
open Filter
open ActualEisensteinCubic RationalPrimeExtraction ShortDraftLatticeCount
open ActualEisensteinCubic ShortDraftLatticeCount
open Filter
open scoped Topology
open EisensteinEmbedding ConcreteTraceCRT ActualEisensteinCubic
open MulChar AddChar
open Filter Asymptotics
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter
open MulChar AddChar
open MulChar AddChar
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Filter Asymptotics
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics Ideal NumberField
open Filter
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped ContDiff FourierTransform SchwartzMap
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open MeasureTheory Set
open scoped BigOperators

namespace ActualEisensteinCubic


theorem prime_generator_not_mem_of_ne (P Q : Ideal O)
    [P.IsMaximal] [Q.IsMaximal] (hne : P ≠ Q)
    (q : O) (hQ : Q = Ideal.span {q}) : q ∉ P := by
  intro hq
  have hle : Q ≤ P := by
    rw [hQ]
    exact (Ideal.span_singleton_le_iff_mem _).mpr hq
  exact hne (Ideal.IsMaximal.eq_of_le (inferInstance : Q.IsMaximal)
    (Ideal.IsMaximal.ne_top (inferInstance : P.IsMaximal)) hle).symm

theorem cubic_reciprocity_equal_residue_char
    (P Q : Ideal O) [P.IsMaximal] [Q.IsMaximal]
    (hPgood : lambda ∉ P) (hQgood : lambda ∉ Q)
    (hne : P ≠ Q) (hchar : ringChar (O ⧸ Q) = ringChar (O ⧸ P))
    (p q : O) (hP : P = Ideal.span {p}) (hQ : Q = Ideal.span {q})
    (hpprimary : lambda ^ 2 ∣ p - 1) (hqprimary : lambda ^ 2 ∣ q - 1) :
    cubicChar P hPgood (Ideal.Quotient.mk P q) =
      cubicChar Q hQgood (Ideal.Quotient.mk Q p) := by
  classical
  let t : O := -(p + q)
  have hpP : p ∈ P := by rw [hP]; exact Ideal.subset_span (by simp)
  have hqQ : q ∈ Q := by rw [hQ]; exact Ideal.subset_span (by simp)
  have hqP : q ∉ P := prime_generator_not_mem_of_ne P Q hne q hQ
  have hpQ : p ∉ Q := prime_generator_not_mem_of_ne Q P hne.symm p hP
  have htP : t ∉ P := by
    intro ht
    have hs : p + q ∈ P := by simpa only [t, neg_neg] using P.neg_mem ht
    exact hqP (by simpa only [add_sub_cancel_left] using P.sub_mem hs hpP)
  have htQ : t ∉ Q := by
    intro ht
    have hs : p + q ∈ Q := by simpa only [t, neg_neg] using Q.neg_mem ht
    exact hpQ (by simpa only [add_sub_cancel_right] using Q.sub_mem hs hqQ)
  have ht0 : t ≠ 0 := fun h => htP (h ▸ P.zero_mem)
  obtain ⟨s, hst, hs⟩ := exists_primary_prime_factorization t ht0
    (neg_add_primary p q hpprimary hqprimary)
  have hlocal : ∀ r ∈ s,
      cubicChar P hPgood (Ideal.Quotient.mk P r) =
      cubicChar Q hQgood (Ideal.Quotient.mk Q r) := by
    intro r hr
    let R : Ideal O := Ideal.span {r}
    let : R.IsMaximal := PrincipalIdealRing.isMaximal_of_irreducible (hs r hr).1.irreducible
    have hrR : r ∈ R := Ideal.subset_span (by simp)
    have htR : t ∈ R := Ideal.mem_span_singleton.mpr (hst ▸ Multiset.dvd_prod hr)
    have hRgood : lambda ∉ R := primary_maximal_divisor_good t
      (neg_add_primary p q hpprimary hqprimary) R htR
    have hRP := prime_divisor_residue_char_ne P Q R hne hchar t htP htQ htR
    have hRQ : ringChar (O ⧸ R) ≠ ringChar (O ⧸ Q) := by rwa [hchar]
    rw [cubic_reciprocity_distinct_residue_char P R hPgood hRgood hRP
      p r hP rfl hpprimary (hs r hr).2,
      cubic_reciprocity_distinct_residue_char Q R hQgood hRgood hRQ
      q r hQ rfl hqprimary (hs r hr).2]
    have hsum : Ideal.Quotient.mk R p + Ideal.Quotient.mk R q = 0 := by
      have hz := Ideal.Quotient.eq_zero_iff_mem.mpr htR
      simpa only [t, map_neg, map_add, neg_eq_zero] using hz
    have heq : Ideal.Quotient.mk R p = -Ideal.Quotient.mk R q := eq_neg_of_add_eq_zero_left hsum
    rw [heq, ← neg_one_mul (Ideal.Quotient.mk R q), map_mul,
      A3_cubicChar_neg_one, one_mul]
  have hmul : ∀ f : Multiset O,
      (∀ r ∈ f, cubicChar P hPgood (Ideal.Quotient.mk P r) =
        cubicChar Q hQgood (Ideal.Quotient.mk Q r)) →
      cubicChar P hPgood (Ideal.Quotient.mk P f.prod) =
        cubicChar Q hQgood (Ideal.Quotient.mk Q f.prod) := by
    intro f
    induction f using Multiset.induction_on with
    | empty => intro _; simp
    | @cons r f ih =>
      intro hf
      simp only [Multiset.prod_cons, map_mul]
      rw [hf r (Multiset.mem_cons_self _ _), ih
        (fun x hx => hf x (Multiset.mem_cons_of_mem hx))]
  have htval := hmul s hlocal
  rw [hst] at htval
  have hpzero : Ideal.Quotient.mk P p = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr hpP
  have hqzero : Ideal.Quotient.mk Q q = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr hqQ
  simp only [t, map_neg, map_add, hpzero, hqzero, zero_add, add_zero] at htval
  rw [← neg_one_mul (Ideal.Quotient.mk P q), map_mul, A3_cubicChar_neg_one, one_mul,
    ← neg_one_mul (Ideal.Quotient.mk Q p), map_mul, A3_cubicChar_neg_one, one_mul] at htval
  exact htval

theorem cubic_reciprocity_primary
    (P Q : Ideal O) [P.IsMaximal] [Q.IsMaximal]
    (hPgood : lambda ∉ P) (hQgood : lambda ∉ Q)
    (p q : O) (hP : P = Ideal.span {p}) (hQ : Q = Ideal.span {q})
    (hpprimary : lambda ^ 2 ∣ p - 1) (hqprimary : lambda ^ 2 ∣ q - 1) :
    cubicChar P hPgood (Ideal.Quotient.mk P q) =
      cubicChar Q hQgood (Ideal.Quotient.mk Q p) := by
  by_cases hPQ : P = Q
  · have hqP : q ∈ P := by rw [hPQ, hQ]; exact Ideal.subset_span (by simp)
    have hpQ : p ∈ Q := by rw [← hPQ, hP]; exact Ideal.subset_span (by simp)
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr hqP,
      Ideal.Quotient.eq_zero_iff_mem.mpr hpQ, MulChar.map_zero, MulChar.map_zero]
  · by_cases hchar : ringChar (O ⧸ Q) = ringChar (O ⧸ P)
    · exact cubic_reciprocity_equal_residue_char P Q hPgood hQgood hPQ hchar
        p q hP hQ hpprimary hqprimary
    · exact cubic_reciprocity_distinct_residue_char P Q hPgood hQgood hchar
        p q hP hQ hpprimary hqprimary

theorem canonicalSextic_sq_reciprocity_primary
    (P Q : Ideal O) [P.IsMaximal] [Q.IsMaximal]
    (hPgood : lambda ∉ P) (hQgood : lambda ∉ Q)
    (p q : O) (hP : P = Ideal.span {p}) (hQ : Q = Ideal.span {q})
    (hpprimary : lambda ^ 2 ∣ p - 1) (hqprimary : lambda ^ 2 ∣ q - 1) :
    (canonicalSextic P hPgood (Ideal.Quotient.mk P q)) ^ 2 =
      (canonicalSextic Q hQgood (Ideal.Quotient.mk Q p)) ^ 2 := by
  have hP2 : (canonicalSextic P hPgood (Ideal.Quotient.mk P q)) ^ 2 =
      ConcreteTraceCRT.eisEmbedding (cubicChar P hPgood (Ideal.Quotient.mk P q)) := by
    rw [← MulChar.pow_apply' _ (by decide : (2 : ℕ) ≠ 0), canonicalSextic_pow_two]
    rfl
  have hQ2 : (canonicalSextic Q hQgood (Ideal.Quotient.mk Q p)) ^ 2 =
      ConcreteTraceCRT.eisEmbedding (cubicChar Q hQgood (Ideal.Quotient.mk Q p)) := by
    rw [← MulChar.pow_apply' _ (by decide : (2 : ℕ) ≠ 0), canonicalSextic_pow_two]
    rfl
  rw [hP2, hQ2, cubic_reciprocity_primary P Q hPgood hQgood p q hP hQ hpprimary hqprimary]

def cubicTwoIdeal : Ideal O := Ideal.span {(-2 : O)}

instance cubicTwoIdeal_isMaximal : cubicTwoIdeal.IsMaximal := by
  rcases rational_prime_factor_cases 2 Nat.prime_two with hm |
      ⟨a, b, _, _, _, ha, _, _, _⟩
  · simpa only [cubicTwoIdeal, Ideal.span_singleton_neg, Nat.cast_ofNat] using hm
  · have hin : (Ideal.span {a} : Ideal O) ∈ {I : Ideal O | Ideal.absNorm I = 2} := by
      change Ideal.absNorm (Ideal.span {a}) = 2
      rwa [← qNat_eq_absNorm_span]
    rw [ShortDraftHeckeBridge.norm_p_fiber_inert Nat.prime_two (by decide)] at hin
    exact False.elim hin


end ActualEisensteinCubic

open scoped BigOperators Classical

namespace IdealGaussCRT


end IdealGaussCRT

namespace QuadraticGaussRay


open ActualEisensteinCubic ConcreteTraceCRT FiniteGaussPhase ActualEisensteinCoordinates


open ActualEisensteinCubic ConcreteTraceCRT FiniteGaussPhase ActualEisensteinCoordinates


end QuadraticGaussRay

end

end OAI

end


