-- Prove2me | Definitions.Def_PNT_ZeroFree_433_0028
-- name    : PNT_ZeroFree_433_0028
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-10T13:45:12.204292+00:00
-- url     : https://prove2.me/theorems/96839c9e-7673-4464-b55b-8f0af97d3313
-- title:
--   Zero-free region foundations: Hecke.LocalEulerIdentities [0028]
-- statement:
--   Definitions and proved supporting lemmas from the following source modules:
--
--   - OAI.NumberTheory.DirichletL.Hecke.LocalEulerIdentities
--
--   These declarations form part of the analytic and arithmetic foundations of the Dirichlet L-function nonvanishing argument in the half-plane Re(s) > 7/8. The original namespaces and hypotheses are retained. The code is ported to Lean 4.33.1 and the pinned Mathlib environment; every included lemma has a complete proof.
-- source:
--   https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/Hecke/LocalEulerIdentities.lean#L37-L751

import Definitions.Def_PNT_ZeroFree_433_0027

/- Supporting source modules for the zero-free-region proof.
Ported and checked against Lean 4.33.1 / Mathlib 0df444a.
Original source attribution:
https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/Hecke/LocalEulerIdentities.lean#L37-L751
-/

set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

-- Source module: OAI.NumberTheory.DirichletL.Hecke.LocalEulerIdentities
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

namespace ShortDraftHeckeBridge

theorem chiMinusThree_mod_one (n : ℕ) (h : n % 3 = 1) :
    chiMinusThree n = 1 := by
  have hc : (n : ZMod 3) = 1 := by
    calc
      (n : ZMod 3) = ((n % 3 : ℕ) : ZMod 3) := by simp
      _ = 1 := by rw [h]; simp
  change ((quadraticChar (ZMod 3) (n : ZMod 3) : ℤ) : ℂ) = 1
  rw [hc]
  simp

theorem chiMinusThree_mod_two (n : ℕ) (h : n % 3 = 2) :
    chiMinusThree n = -1 := by
  have hc : (n : ZMod 3) = 2 := by
    calc
      (n : ZMod 3) = ((n % 3 : ℕ) : ZMod 3) := by simp
      _ = 2 := by rw [h]; simp
  change ((quadraticChar (ZMod 3) (n : ZMod 3) : ℤ) : ℂ) = -1
  rw [hc]
  change chiMinusThree (2 : ℕ) = -1
  exact chiMinusThree_two

theorem chiMinusThree_mod_zero (n : ℕ) (h : n % 3 = 0) :
    chiMinusThree n = 0 := by
  have hc : (n : ZMod 3) = 0 := by
    calc
      (n : ZMod 3) = ((n % 3 : ℕ) : ZMod 3) := by simp
      _ = 0 := by rw [h]; simp
  change ((quadraticChar (ZMod 3) (n : ZMod 3) : ℤ) : ℂ) = 0
  rw [hc]
  simp

private theorem invCharAF_prime_pow_ge_two {q : ℕ}
    (χ : DirichletCharacter ℂ q) {p j : ℕ} (hp : p.Prime) (hj : 2 ≤ j) :
    invCharAF χ (p ^ j) = 0 := by
  rw [invCharAF_apply χ (pow_ne_zero j hp.ne_zero),
    ArithmeticFunction.moebius_apply_prime_pow hp (by omega)]
  simp [show j ≠ 1 by omega]

theorem pairAF_prime_pow_ge_three {q r : ℕ}
    (χ : DirichletCharacter ℂ q) (ψ : DirichletCharacter ℂ r)
    {p k : ℕ} (hp : p.Prime) (hk : 3 ≤ k) :
    pairAF χ ψ (p ^ k) = 0 := by
  rw [pairAF, ArithmeticFunction.mul_apply]
  conv_lhs => rw [Nat.sum_divisorsAntidiagonal
    (fun a b => invCharAF χ a * invCharAF ψ b)]
  rw [Nat.sum_divisors_prime_pow hp]
  apply Finset.sum_eq_zero
  intro i hi
  have hik : i ≤ k := by
    simpa only [Finset.mem_range, Nat.lt_succ_iff] using hi
  have hdiv : p ^ k / p ^ i = p ^ (k - i) := by
    have heq : k - i + i = k := Nat.sub_add_cancel hik
    calc
      p ^ k / p ^ i = (p ^ (k - i) * p ^ i) / p ^ i := by rw [← pow_add, heq]
      _ = p ^ (k - i) := by simp [hp.ne_zero]
  rw [hdiv]
  by_cases hii : 2 ≤ i
  · rw [invCharAF_prime_pow_ge_two χ hp hii, zero_mul]
  · have hki : 2 ≤ k - i := by omega
    rw [invCharAF_prime_pow_ge_two ψ hp hki, mul_zero]

private instance : IsCyclotomicExtension {3} ℚ ActualEisensteinSieve.K :=
  CyclotomicField.isCyclotomicExtension 3 ℚ

private theorem base_ring_rank_two : Module.finrank ℤ O = 2 := by
  rw [NumberField.RingOfIntegers.rank ActualEisensteinSieve.K,
    IsCyclotomicExtension.Rat.finrank 3 ActualEisensteinSieve.K]
  decide

theorem baseChangeWeight_zero_of_norm_prime_pow_ge_three {q p k : ℕ}
    (χ : DirichletCharacter ℂ q) (hp : p.Prime) (hk : 3 ≤ k)
    (I : Ideal O) (hI : Ideal.absNorm I = p ^ k) :
    baseChangeWeight χ I = 0 := by
  by_cases hμ : UniqueFactorizationMonoid.moebius I = 0
  · simp [baseChangeWeight, hμ]
  have hsq : Squarefree I := by
    by_contra hnsq
    exact hμ (UniqueFactorizationMonoid.moebius_of_not_squarefree hnsq)
  have hmem : ((p ^ k : ℕ) : O) ∈ I := by
    simpa only [hI] using Ideal.absNorm_mem I
  have hspanle : Ideal.span {((p : O) ^ k)} ≤ I :=
    (Ideal.span_singleton_le_iff_mem I).mpr (by simpa using hmem)
  have hpowdiv : I ∣ (Ideal.span {(p : O)}) ^ k := by
    rw [Ideal.span_singleton_pow]
    exact Ideal.dvd_iff_le.mpr hspanle
  have hdiv : I ∣ Ideal.span {(p : O)} :=
    (hsq.dvd_pow_iff_dvd (by omega : k ≠ 0)).mp hpowdiv
  have hnormdiv := map_dvd Ideal.absNorm hdiv
  rw [hI, Ideal.absNorm_span_natCast, base_ring_rank_two] at hnormdiv
  have hk2 : k ≤ 2 := (Nat.pow_dvd_pow_iff_le_right hp.one_lt).mp hnormdiv
  omega

theorem normFiberCoeff_baseChangeWeight_prime_pow_ge_three {q p k : ℕ}
    (χ : DirichletCharacter ℂ q) (hp : p.Prime) (hk : 3 ≤ k) :
    normFiberCoeff (baseChangeWeight χ) (p ^ k) = 0 := by
  classical
  unfold normFiberCoeff
  apply Finset.sum_eq_zero
  intro I hI
  have hnorm : Ideal.absNorm I = p ^ k := by simpa using hI
  exact baseChangeWeight_zero_of_norm_prime_pow_ge_three χ hp hk I hnorm

theorem normFiberCoeff_eq_pairAF_prime_pow_ge_three {q p k : ℕ}
    (χ : DirichletCharacter ℂ q) (hp : p.Prime) (hk : 3 ≤ k) :
    normFiberCoeff (baseChangeWeight χ) (p ^ k) =
      pairAF χ (baseChangeChar χ) (p ^ k) := by
  rw [normFiberCoeff_baseChangeWeight_prime_pow_ge_three χ hp hk,
    pairAF_prime_pow_ge_three χ (baseChangeChar χ) hp hk]

theorem char_prime_zero_of_dvd_level {q p : ℕ}
    (χ : DirichletCharacter ℂ q) (hp : p.Prime) (hd : p ∣ q) :
    χ p = 0 := by
  have hnot : ¬ IsCoprime (p : ℤ) (q : ℕ) := by
    intro hc
    have hn : p.Coprime q := by
      simpa [Int.isCoprime_iff_nat_coprime] using hc
    exact (hp.coprime_iff_not_dvd.mp hn) hd
  simpa using (DirichletCharacter.apply_eq_zero_iff χ (p : ℤ)).mpr hnot

theorem baseChangeChar_prime_zero_of_dvd_q {q p : ℕ}
    (χ : DirichletCharacter ℂ q) (hp : p.Prime) (hd : p ∣ q) :
    baseChangeChar χ p = 0 := by
  have hd' : p ∣ q * 3 := dvd_mul_of_dvd_left hd 3
  exact char_prime_zero_of_dvd_level (baseChangeChar χ) hp hd'

end ShortDraftHeckeBridge

namespace NormSplitArithmetic

theorem eq_parts_of_coprime_square_bounds {a b m n : ℕ}
    (hcop : m.Coprime n) (ha2 : a ∣ m ^ 2) (hb2 : b ∣ n ^ 2)
    (hprod : a * b = m * n) : a = m ∧ b = n := by
  have hm2n : (m ^ 2).Coprime n :=
    (Nat.coprime_pow_left_iff (by decide) m n).mpr hcop
  have hmn2 : m.Coprime (n ^ 2) :=
    (Nat.coprime_pow_right_iff (by decide) m n).mpr hcop
  have han : a.Coprime n := hm2n.coprime_dvd_left ha2
  have hmb : m.Coprime b := hmn2.coprime_dvd_right hb2
  have ha_mn : a ∣ m * n := ⟨b, hprod.symm⟩
  have hm_ab : m ∣ a * b := ⟨n, hprod⟩
  have hn_ab : n ∣ a * b := ⟨m, by rw [hprod, mul_comm]⟩
  have ha_m : a ∣ m := han.dvd_of_dvd_mul_right ha_mn
  have hm_a : m ∣ a := hmb.dvd_of_dvd_mul_right hm_ab
  have hb_n : b ∣ n := by
    have hbn : b.Coprime m := (hmn2.symm).coprime_dvd_left hb2
    have hb_mn : b ∣ n * m := ⟨a, by
      calc
        n * m = m * n := mul_comm n m
        _ = a * b := hprod.symm
        _ = b * a := mul_comm a b⟩
    exact hbn.dvd_of_dvd_mul_right hb_mn
  have hn_b : n ∣ b := han.symm.dvd_of_dvd_mul_left hn_ab
  exact ⟨Nat.dvd_antisymm ha_m hm_a, Nat.dvd_antisymm hb_n hn_b⟩

end NormSplitArithmetic

namespace NormFiberCRT

abbrev O := ActualEisensteinSieve.O
abbrev K := ActualEisensteinSieve.K

private instance : IsCyclotomicExtension {3} ℚ K :=
  CyclotomicField.isCyclotomicExtension 3 ℚ

private theorem ring_rank_two : Module.finrank ℤ O = 2 := by
  rw [NumberField.RingOfIntegers.rank K,
    IsCyclotomicExtension.Rat.finrank 3 K]
  decide

theorem ideal_eq_factors (I : Ideal O) (m n : ℕ)
    (hcop : m.Coprime n) (hI : Ideal.absNorm I = m * n) :
    I = (I ⊔ Ideal.span {(m : O)}) * (I ⊔ Ideal.span {(n : O)}) := by
  let A : Ideal O := Ideal.span {(m : O)}
  let B : Ideal O := Ideal.span {(n : O)}
  have hcast : IsCoprime (m : O) (n : O) := by
    simpa only [map_natCast] using
      (Nat.Coprime.isCoprime hcop).map (Int.castRingHom O)
  have hAB : A ⊔ B = ⊤ := by
    exact Ideal.isCoprime_iff_sup_eq.mp
      ((Ideal.isCoprime_span_singleton_iff (m : O) (n : O)).mpr hcast)
  have hmnmem : ((m * n : ℕ) : O) ∈ I := by
    simpa only [hI] using Ideal.absNorm_mem I
  have hABle : A * B ≤ I := by
    change Ideal.span {(m : O)} * Ideal.span {(n : O)} ≤ I
    rw [Ideal.span_singleton_mul_span_singleton]
    exact (Ideal.span_singleton_le_iff_mem I).mpr (by simpa using hmnmem)
  have hJcop : (I ⊔ A) ⊔ (I ⊔ B) = ⊤ := by
    calc
      (I ⊔ A) ⊔ (I ⊔ B) = I ⊔ (A ⊔ B) := by ac_rfl
      _ = ⊤ := by rw [hAB, sup_top_eq]
  apply le_antisymm
  · rw [Ideal.mul_eq_inf_of_coprime hJcop]
    exact le_inf le_sup_left le_sup_left
  · rw [Ideal.sup_mul, Ideal.mul_sup, Ideal.mul_sup]
    exact sup_le (sup_le Ideal.mul_le_left Ideal.mul_le_left)
      (sup_le Ideal.mul_le_right hABle)

theorem ideal_factor_norms (I : Ideal O) (m n : ℕ)
    (hcop : m.Coprime n) (hI : Ideal.absNorm I = m * n) :
    Ideal.absNorm (I ⊔ Ideal.span {(m : O)}) = m ∧
      Ideal.absNorm (I ⊔ Ideal.span {(n : O)}) = n := by
  have hAm : Ideal.absNorm (Ideal.span {(m : O)}) = m ^ 2 := by
    rw [Ideal.absNorm_span_natCast, ring_rank_two]
  have hBn : Ideal.absNorm (Ideal.span {(n : O)}) = n ^ 2 := by
    rw [Ideal.absNorm_span_natCast, ring_rank_two]
  have hmdiv : Ideal.absNorm (I ⊔ Ideal.span {(m : O)}) ∣ m ^ 2 := by
    rw [← hAm]
    exact Ideal.absNorm_dvd_absNorm_of_le le_sup_right
  have hndiv : Ideal.absNorm (I ⊔ Ideal.span {(n : O)}) ∣ n ^ 2 := by
    rw [← hBn]
    exact Ideal.absNorm_dvd_absNorm_of_le le_sup_right
  have hprod := congrArg Ideal.absNorm (ideal_eq_factors I m n hcop hI)
  rw [map_mul, hI] at hprod
  exact NormSplitArithmetic.eq_parts_of_coprime_square_bounds hcop hmdiv hndiv hprod.symm

end NormFiberCRT

namespace NormFiberMult

abbrev O := ActualEisensteinSieve.O

private theorem ideal_sup_span_norm_left (I J : Ideal O) (m n : ℕ)
    (hcop : m.Coprime n) (hI : Ideal.absNorm I = m)
    (hJ : Ideal.absNorm J = n) :
    I * J ⊔ Ideal.span {(m : O)} = I := by
  let A : Ideal O := Ideal.span {(m : O)}
  have hmI : A ≤ I := by
    apply (Ideal.span_singleton_le_iff_mem _).mpr
    simpa only [hI] using Ideal.absNorm_mem I
  have hnJ : (n : O) ∈ J := by
    simpa only [hJ] using Ideal.absNorm_mem J
  have hnspan : Ideal.span {(n : O)} ≤ J :=
    (Ideal.span_singleton_le_iff_mem _).mpr hnJ
  have hcast : IsCoprime (m : O) (n : O) := by
    simpa only [map_natCast] using
      (Nat.Coprime.isCoprime hcop).map (Int.castRingHom O)
  have hAB : A ⊔ Ideal.span {(n : O)} = ⊤ := by
    exact Ideal.isCoprime_iff_sup_eq.mp
      ((Ideal.isCoprime_span_singleton_iff (m : O) (n : O)).mpr hcast)
  have hJA : J ⊔ A = ⊤ := by
    apply top_unique
    calc
      ⊤ = A ⊔ Ideal.span {(n : O)} := hAB.symm
      _ ≤ J ⊔ A := sup_le le_sup_right (hnspan.trans le_sup_left)
  apply le_antisymm
  · exact sup_le Ideal.mul_le_left hmI
  · calc
      I = I * (J ⊔ A) := by rw [hJA]; simp
      _ = I * J ⊔ I * A := by rw [Ideal.mul_sup]
      _ ≤ I * J ⊔ A := sup_le le_sup_left
        (Ideal.mul_le_right.trans le_sup_right)

private theorem ideal_sup_span_norm_right (I J : Ideal O) (m n : ℕ)
    (hcop : m.Coprime n) (hI : Ideal.absNorm I = m)
    (hJ : Ideal.absNorm J = n) :
    I * J ⊔ Ideal.span {(n : O)} = J := by
  simpa only [mul_comm] using
    ideal_sup_span_norm_left J I n m hcop.symm hJ hI

theorem weighted_norm_fiber_mul (weight : Ideal O → ℂ)
    (hweight : ∀ I J : Ideal O,
      (Ideal.absNorm I).Coprime (Ideal.absNorm J) →
      weight (I * J) = weight I * weight J)
    (m n : ℕ) (hcop : m.Coprime n) :
    (∑ K ∈ (Ideal.finite_setOfPred_absNorm_eq (S := O) (m * n)).toFinset,
       weight K) =
    (∑ I ∈ (Ideal.finite_setOfPred_absNorm_eq (S := O) m).toFinset,
       weight I) *
    (∑ J ∈ (Ideal.finite_setOfPred_absNorm_eq (S := O) n).toFinset,
       weight J) := by
  let F (k : ℕ) : Finset (Ideal O) :=
    (Ideal.finite_setOfPred_absNorm_eq (S := O) k).toFinset
  have hmem (k : ℕ) (I : Ideal O) : I ∈ F k ↔ Ideal.absNorm I = k := by
    simp [F]
  change (∑ K ∈ F (m * n), weight K) =
    (∑ I ∈ F m, weight I) * (∑ J ∈ F n, weight J)
  calc
    (∑ K ∈ F (m * n), weight K) =
        ∑ p ∈ (F m).product (F n), weight (p.1 * p.2) := by
      refine Finset.sum_bij'
        (fun K _ => (K ⊔ Ideal.span {(m : O)},
                     K ⊔ Ideal.span {(n : O)}))
        (fun p _ => p.1 * p.2) ?_ ?_ ?_ ?_ ?_
      · intro K hK
        have hKnorm : Ideal.absNorm K = m * n := (hmem _ _).mp hK
        obtain ⟨hm, hn⟩ := NormFiberCRT.ideal_factor_norms K m n hcop hKnorm
        simp [Finset.mem_product, hmem, hm, hn]
      · intro p hp
        have hm : Ideal.absNorm p.1 = m := (hmem _ _).mp (Finset.mem_product.mp hp).1
        have hn : Ideal.absNorm p.2 = n := (hmem _ _).mp (Finset.mem_product.mp hp).2
        exact (hmem _ _).mpr (by rw [map_mul, hm, hn])
      · intro K hK
        exact (NormFiberCRT.ideal_eq_factors K m n hcop ((hmem _ _).mp hK)).symm
      · intro p hp
        have hm : Ideal.absNorm p.1 = m := (hmem _ _).mp (Finset.mem_product.mp hp).1
        have hn : Ideal.absNorm p.2 = n := (hmem _ _).mp (Finset.mem_product.mp hp).2
        apply Prod.ext
        · exact ideal_sup_span_norm_left p.1 p.2 m n hcop hm hn
        · exact ideal_sup_span_norm_right p.1 p.2 m n hcop hm hn
      · intro K hK
        exact congrArg weight
          (NormFiberCRT.ideal_eq_factors K m n hcop ((hmem _ _).mp hK))
    _ = ∑ p ∈ (F m).product (F n), weight p.1 * weight p.2 := by
      apply Finset.sum_congr rfl
      intro p hp
      have hm : Ideal.absNorm p.1 = m := (hmem _ _).mp (Finset.mem_product.mp hp).1
      have hn : Ideal.absNorm p.2 = n := (hmem _ _).mp (Finset.mem_product.mp hp).2
      exact hweight p.1 p.2 (by simpa [hm, hn] using hcop)
    _ = (∑ I ∈ F m, weight I) * (∑ J ∈ F n, weight J) := by
      calc
        (∑ p ∈ (F m).product (F n), weight p.1 * weight p.2) =
            ∑ I ∈ F m, ∑ J ∈ F n, weight I * weight J := by
          exact Finset.sum_product' (F m) (F n) (fun I J => weight I * weight J)
        _ = (∑ I ∈ F m, weight I) * (∑ J ∈ F n, weight J) := by
          simp only [← Finset.mul_sum, ← Finset.sum_mul]

end NormFiberMult

namespace ShortDraftHeckeBridge

theorem baseChange_normFiber_mul {q : ℕ}
    (χ : DirichletCharacter ℂ q) (m n : ℕ) (hcop : m.Coprime n) :
    normFiberCoeff (baseChangeWeight χ) (m * n) =
      normFiberCoeff (baseChangeWeight χ) m *
        normFiberCoeff (baseChangeWeight χ) n := by
  exact NormFiberMult.weighted_norm_fiber_mul (baseChangeWeight χ)
    (fun I J h => baseChangeWeight_mul_of_coprime_norms χ I J h) m n hcop

theorem normFiberCoeff_baseChangeWeight_one {q : ℕ}
    (χ : DirichletCharacter ℂ q) :
    normFiberCoeff (baseChangeWeight χ) 1 = 1 := by
  have hsingle :
      (Ideal.finite_setOfPred_absNorm_eq (S := O) 1).toFinset = {⊤} := by
    ext I
    simp [Ideal.absNorm_eq_one_iff]
  unfold normFiberCoeff
  rw [hsingle]
  simp [baseChangeWeight, ← Ideal.one_eq_top]

theorem baseChange_normFiber_isMultiplicative {q : ℕ}
    (χ : DirichletCharacter ℂ q) :
    (toArithmeticFunction (normFiberCoeff (baseChangeWeight χ))).IsMultiplicative := by
  constructor
  · simp [toArithmeticFunction, normFiberCoeff_baseChangeWeight_one]
  · intro m n hcop
    by_cases hm : m = 0
    · simp [hm, toArithmeticFunction]
    by_cases hn : n = 0
    · simp [hn, toArithmeticFunction]
    simpa [toArithmeticFunction, hm, hn, mul_ne_zero hm hn] using
      baseChange_normFiber_mul χ m n hcop

theorem baseChangeChar_prime_apply {q p : ℕ}
    (χ : DirichletCharacter ℂ q) (hp : p.Prime) :
    baseChangeChar χ p = χ p * chiMinusThree p := by
  by_cases hq : p ∣ q
  · rw [baseChangeChar_prime_zero_of_dvd_q χ hp hq,
      char_prime_zero_of_dvd_level χ hp hq, zero_mul]
  by_cases h3 : p = 3
  · subst p
    rw [baseChangeChar_three, chiMinusThree_three, mul_zero]
  have hn3 : ¬p ∣ 3 := by
    intro hd
    rcases (Nat.dvd_prime (by decide : Nat.Prime 3)).1 hd with h1 | h3'
    · exact hp.ne_one h1
    · exact h3 h3'
  have hnot : ¬p ∣ q * 3 := by
    intro hd
    rcases hp.dvd_mul.mp hd with hq' | h3'
    · exact hq hq'
    · exact hn3 h3'
  exact baseChangeChar_apply_of_coprime χ p
    (hp.coprime_iff_not_dvd.mpr hnot)

theorem normFiberCoeff_eq_pairAF_prime {q p : ℕ}
    (χ : DirichletCharacter ℂ q) (hp : p.Prime) :
    normFiberCoeff (baseChangeWeight χ) p =
      pairAF χ (baseChangeChar χ) p := by
  have hlt : p % 3 < 3 := Nat.mod_lt p (by decide)
  have hcase : p % 3 = 0 ∨ p % 3 = 1 ∨ p % 3 = 2 := by omega
  rcases hcase with h0 | h1 | h2
  · have hdiv : 3 ∣ p := Nat.dvd_of_mod_eq_zero h0
    have heq : p = 3 := by
      rcases (Nat.dvd_prime hp).1 hdiv with h1' | h3
      · norm_num at h1'
      · exact h3.symm
    subst p
    rw [local_ramified_three χ,
      pairAF_prime χ (baseChangeChar χ) (by decide),
      baseChangeChar_three χ]
    ring_nf
  · rw [local_split_p χ hp h1, pairAF_prime χ (baseChangeChar χ) hp,
      baseChangeChar_prime_apply χ hp, chiMinusThree_mod_one p h1]
    ring
  · rw [local_inert_p χ hp h2, pairAF_prime χ (baseChangeChar χ) hp,
      baseChangeChar_prime_apply χ hp, chiMinusThree_mod_two p h2]
    ring

theorem normFiberCoeff_eq_pairAF_prime_sq {q p : ℕ}
    (χ : DirichletCharacter ℂ q) (hp : p.Prime) :
    normFiberCoeff (baseChangeWeight χ) (p ^ 2) =
      pairAF χ (baseChangeChar χ) (p ^ 2) := by
  have hlt : p % 3 < 3 := Nat.mod_lt p (by decide)
  have hcase : p % 3 = 0 ∨ p % 3 = 1 ∨ p % 3 = 2 := by omega
  rcases hcase with h0 | h1 | h2
  · have hdiv : 3 ∣ p := Nat.dvd_of_mod_eq_zero h0
    have heq : p = 3 := by
      rcases (Nat.dvd_prime hp).1 hdiv with h1' | h3
      · norm_num at h1'
      · exact h3.symm
    subst p
    have h3 : pairAF χ (baseChangeChar χ) 9 =
        χ (3 : ℕ) * baseChangeChar χ (3 : ℕ) := by
      simpa only [show (3 : ℕ) ^ 2 = 9 by norm_num] using
        (pairAF_prime_sq χ (baseChangeChar χ) (by decide : Nat.Prime 3))
    rw [show (3 : ℕ) ^ 2 = 9 by norm_num, local_ramified_nine χ,
      h3, baseChangeChar_three χ]
    ring
  · rw [local_split_p_sq χ hp h1, pairAF_prime_sq χ (baseChangeChar χ) hp,
      baseChangeChar_prime_apply χ hp, chiMinusThree_mod_one p h1]
    simp only [map_pow]
    ring
  · rw [local_inert_p_sq χ hp h2, pairAF_prime_sq χ (baseChangeChar χ) hp,
      baseChangeChar_prime_apply χ hp, chiMinusThree_mod_two p h2]
    simp only [map_pow]
    ring

theorem normFiberCoeff_eq_pairInverseCoeff_of_local
    {q : ℕ} (χ : DirichletCharacter ℂ q)
    (hprime : ∀ p : ℕ, p.Prime →
      normFiberCoeff (baseChangeWeight χ) p = pairAF χ (baseChangeChar χ) p)
    (hprimeSq : ∀ p : ℕ, p.Prime →
      normFiberCoeff (baseChangeWeight χ) (p ^ 2) =
        pairAF χ (baseChangeChar χ) (p ^ 2))
    (n : ℕ) (hn : n ≠ 0) :
    normFiberCoeff (baseChangeWeight χ) n =
      pairInverseCoeff χ (baseChangeChar χ) n := by
  apply normFiber_eq_pair_of_prime_powers χ (baseChangeChar χ)
    (baseChangeWeight χ) (baseChange_normFiber_isMultiplicative χ) ?_ n hn
  intro p k hp
  by_cases hk0 : k = 0
  · simpa [hk0] using
      (baseChange_normFiber_isMultiplicative χ).map_one.trans
        ((pairAF_mult χ (baseChangeChar χ)).map_one).symm
  by_cases hk1 : k = 1
  · simpa [hk1, toArithmeticFunction, hp.ne_zero] using hprime p hp
  by_cases hk2 : k = 2
  · simpa [hk2, toArithmeticFunction, hp.ne_zero] using hprimeSq p hp
  have hk3 : 3 ≤ k := by omega
  change (if p ^ k = 0 then (0 : ℂ) else
    normFiberCoeff (baseChangeWeight χ) (p ^ k)) = _
  rw [if_neg (pow_ne_zero k hp.ne_zero)]
  exact normFiberCoeff_eq_pairAF_prime_pow_ge_three χ hp hk3

theorem normFiberCoeff_baseChange_eq_pairInverseCoeff
    {q : ℕ} (χ : DirichletCharacter ℂ q)
    (n : ℕ) (hn : n ≠ 0) :
    normFiberCoeff (baseChangeWeight χ) n =
      pairInverseCoeff χ (baseChangeChar χ) n := by
  exact normFiberCoeff_eq_pairInverseCoeff_of_local χ
    (fun p hp => normFiberCoeff_eq_pairAF_prime χ hp)
    (fun p hp => normFiberCoeff_eq_pairAF_prime_sq χ hp) n hn

theorem dirichletTarget_of_normFiber_exp_bound
    (hbound : ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q)
      (ρ : ℂ), (23 / 24 : ℝ) < ρ.re → ρ.re < 1 →
        ∃ σ : ℝ, 0 < σ ∧ σ < ρ.re ∧
          (fun D : ℝ => normFiberExpSum (baseChangeWeight χ) D⁻¹) =O[atTop]
            (fun D : ℝ => D ^ σ)) :
    ShortDraft.DirichletTarget := by
  apply dirichletTarget_of_ideal_base_change ?_ hbound
  intro q _ χ n hn
  exact normFiberCoeff_baseChange_eq_pairInverseCoeff χ n hn

end ShortDraftHeckeBridge
open Filter Asymptotics

namespace ShortDraftHeckeBridge

private theorem rpow_le_one_add_of_exponent_Icc (x σ : ℝ)
    (hx : 0 ≤ x) (hσ0 : 0 ≤ σ) (hσ1 : σ ≤ 1) : x ^ σ ≤ 1 + x := by
  by_cases hx1 : x ≤ 1
  · have h := Real.rpow_le_one hx hx1 hσ0
    linarith
  · have h := Real.rpow_le_self_of_one_le (le_of_not_ge hx1) hσ1
    linarith

private theorem tsum_add_one_mul_geometric {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    (∑' n : ℕ, ((n : ℝ) + 1) * r ^ n) = 1 / (1 - r) ^ 2 := by
  have hr : ‖r‖ < 1 := by simpa [Real.norm_eq_abs, abs_of_nonneg hr0] using hr1
  simpa only [Nat.choose_one_right, Nat.cast_add, Nat.cast_one] using
    (tsum_choose_mul_geometric_of_norm_lt_one (𝕜 := ℝ) 1 hr)

private theorem summable_add_one_mul_geometric {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    Summable (fun n : ℕ => ((n : ℝ) + 1) * r ^ n) := by
  have hr : ‖r‖ < 1 := by simpa [Real.norm_eq_abs, abs_of_nonneg hr0] using hr1
  simpa only [Nat.choose_one_right, Nat.cast_add, Nat.cast_one] using
    (summable_choose_mul_geometric_of_norm_lt_one (R := ℝ) 1 hr)

theorem geometric_rpow_moment_bound
    (σ D r : ℝ) (hσ0 : 0 ≤ σ) (hσ1 : σ ≤ 1)
    (hD : 1 ≤ D) (hr0 : 0 ≤ r) (hr1 : r < 1)
    (hscale : 1 / (D * (1 - r)) ≤ 2) :
    (1 - r) * (∑' n : ℕ, (((n : ℝ) + 1) ^ σ) * r ^ n) ≤
      3 * D ^ σ := by
  have hDpos : 0 < D := lt_of_lt_of_le zero_lt_one hD
  have hDpow : 0 ≤ D ^ σ := (Real.rpow_pos_of_pos hDpos σ).le
  have hrpow : ∀ n : ℕ,
      (((n : ℝ) + 1) ^ σ) * r ^ n ≤
      D ^ σ * (r ^ n + D⁻¹ * (((n : ℝ) + 1) * r ^ n)) := by
    intro n
    have hn : 0 ≤ ((n : ℝ) + 1) / D := by positivity
    have heq : D * (((n : ℝ) + 1) / D) = (n : ℝ) + 1 := by field_simp
    have hbase : ((n : ℝ) + 1) ^ σ ≤
        D ^ σ * (1 + ((n : ℝ) + 1) / D) := by
      calc
        ((n : ℝ) + 1) ^ σ =
            (D * (((n : ℝ) + 1) / D)) ^ σ := by rw [heq]
        _ = D ^ σ * (((n : ℝ) + 1) / D) ^ σ :=
          Real.mul_rpow hDpos.le hn
        _ ≤ D ^ σ * (1 + ((n : ℝ) + 1) / D) :=
          mul_le_mul_of_nonneg_left
            (rpow_le_one_add_of_exponent_Icc _ _ hn hσ0 hσ1) hDpow
    have hrn : 0 ≤ r ^ n := pow_nonneg hr0 _
    calc
      (((n : ℝ) + 1) ^ σ) * r ^ n ≤
          (D ^ σ * (1 + ((n : ℝ) + 1) / D)) * r ^ n :=
        mul_le_mul_of_nonneg_right hbase hrn
      _ = D ^ σ * (r ^ n + D⁻¹ * (((n : ℝ) + 1) * r ^ n)) := by ring
  have hrnorm : ‖r‖ < 1 := by simpa [Real.norm_eq_abs, abs_of_nonneg hr0] using hr1
  have hs0 : Summable (fun n : ℕ => r ^ n) := summable_geometric_of_norm_lt_one hrnorm
  have hs1 : Summable (fun n : ℕ => ((n : ℝ) + 1) * r ^ n) :=
    summable_add_one_mul_geometric hr0 hr1
  have hsdom : Summable (fun n : ℕ =>
      D ^ σ * (r ^ n + D⁻¹ * (((n : ℝ) + 1) * r ^ n))) :=
    ((hs0.add (hs1.mul_left D⁻¹)).mul_left (D ^ σ))
  have hslow : Summable (fun n : ℕ => (((n : ℝ) + 1) ^ σ) * r ^ n) :=
    Summable.of_nonneg_of_le (fun n => mul_nonneg
      (Real.rpow_nonneg (by positivity) σ) (pow_nonneg hr0 _)) hrpow hsdom
  have hsum := Summable.tsum_le_tsum hrpow hslow hsdom
  have hgap : 0 ≤ 1 - r := sub_nonneg.mpr hr1.le
  have hgeom : (∑' n : ℕ, r ^ n) = (1 - r)⁻¹ :=
    tsum_geometric_of_norm_lt_one hrnorm
  have hlin := tsum_add_one_mul_geometric hr0 hr1
  have hgap_ne : 1 - r ≠ 0 := ne_of_gt (sub_pos.mpr hr1)
  calc
    (1 - r) * (∑' n : ℕ, (((n : ℝ) + 1) ^ σ) * r ^ n) ≤
        (1 - r) * (∑' n : ℕ,
          D ^ σ * (r ^ n + D⁻¹ * (((n : ℝ) + 1) * r ^ n))) :=
      mul_le_mul_of_nonneg_left hsum hgap
    _ = D ^ σ * (1 + 1 / (D * (1 - r))) := by
      rw [tsum_mul_left, Summable.tsum_add hs0 (hs1.mul_left D⁻¹),
        tsum_mul_left, hgeom, hlin]
      field_simp
    _ ≤ 3 * D ^ σ := by
      nlinarith [mul_nonneg hDpow (sub_nonneg.mpr hscale)]

noncomputable def prefixCoeff (a : ℕ → ℂ) (n : ℕ) : ℂ :=
  ∑ k ∈ Finset.range (n + 1), a k

theorem tsum_eq_one_sub_mul_tsum_prefix
    (a : ℕ → ℂ) (r : ℝ) (hr0 : 0 ≤ r) (hr1 : r < 1)
    (hf : Summable (fun n : ℕ => a n * (r : ℂ) ^ n)) :
    (∑' n : ℕ, a n * (r : ℂ) ^ n) =
      (1 - (r : ℂ)) * (∑' n : ℕ, prefixCoeff a n * (r : ℂ) ^ n) := by
  have hrC : ‖(r : ℂ)‖ < 1 := by
    simpa only [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hr0] using hr1
  have hg : Summable (fun n : ℕ => (r : ℂ) ^ n) :=
    summable_geometric_of_norm_lt_one hrC
  have hconv := hasSum_sum_range_mul_of_summable_norm hf.norm hg.norm
  have hcoeff (n : ℕ) :
      (∑ k ∈ Finset.range (n + 1),
        (a k * (r : ℂ) ^ k) * (r : ℂ) ^ (n - k)) =
      prefixCoeff a n * (r : ℂ) ^ n := by
    calc
      (∑ k ∈ Finset.range (n + 1),
        (a k * (r : ℂ) ^ k) * (r : ℂ) ^ (n - k)) =
          ∑ k ∈ Finset.range (n + 1), a k * (r : ℂ) ^ n := by
        apply Finset.sum_congr rfl
        intro k hk
        have hkn : k ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hk)
        rw [mul_assoc, ← pow_add, Nat.add_sub_of_le hkn]
      _ = prefixCoeff a n * (r : ℂ) ^ n := by
        rw [prefixCoeff, Finset.sum_mul]
  have hconvEq := hconv.tsum_eq
  simp_rw [hcoeff] at hconvEq
  rw [tsum_geometric_of_norm_lt_one hrC] at hconvEq
  have hne : (1 - (r : ℂ)) ≠ 0 := by
    exact sub_ne_zero.mpr (by norm_cast; exact (ne_of_lt hr1).symm)
  calc
    (∑' n : ℕ, a n * (r : ℂ) ^ n) =
      (1 - (r : ℂ)) *
        ((∑' n : ℕ, a n * (r : ℂ) ^ n) * (1 - (r : ℂ))⁻¹) := by
          field_simp
    _ = (1 - (r : ℂ)) * (∑' n : ℕ, prefixCoeff a n * (r : ℂ) ^ n) := by
      rw [hconvEq]

theorem exp_inv_geometric_gap (D : ℝ) (hD : 1 ≤ D) :
    1 / (D * (1 - Real.exp (-D⁻¹))) ≤ 2 := by
  have hDpos : 0 < D := lt_of_lt_of_le zero_lt_one hD
  have hDne : D ≠ 0 := ne_of_gt hDpos
  have hden : 0 < D + 1 := by linarith
  have hx : 0 < D⁻¹ := inv_pos.mpr hDpos
  have hbase : 0 < 1 + D⁻¹ := by positivity
  have hexp : 1 + D⁻¹ ≤ Real.exp D⁻¹ := by
    linarith [Real.add_one_le_exp D⁻¹]
  have he : Real.exp (-D⁻¹) ≤ (1 + D⁻¹)⁻¹ := by
    rw [Real.exp_neg]
    simpa only [one_div] using one_div_le_one_div_of_le hbase hexp
  have hrew : (1 + D⁻¹)⁻¹ = D / (D + 1) := by
    field_simp
  rw [hrew] at he
  have hhalf : (1 / 2 : ℝ) ≤ D * (1 - Real.exp (-D⁻¹)) := by
    calc
      (1 / 2 : ℝ) ≤ D / (D + 1) := by
        apply (le_div_iff₀ hden).2
        nlinarith
      _ = D * (1 - D / (D + 1)) := by
        field_simp
        ring
      _ ≤ D * (1 - Real.exp (-D⁻¹)) :=
        mul_le_mul_of_nonneg_left (sub_le_sub_left he 1) hDpos.le
  have h := one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1 / 2) hhalf
  norm_num at h ⊢
  exact h

theorem normFiberExpSum_le_of_prefix_power
    {q r₀ : ℕ} [NeZero q] [NeZero r₀]
    (χ : DirichletCharacter ℂ q) (ψ : DirichletCharacter ℂ r₀)
    (weight : Ideal O → ℂ)
    (hcoeff : ∀ n : ℕ, n ≠ 0 → normFiberCoeff weight n = pairInverseCoeff χ ψ n)
    (ha0 : normFiberCoeff weight 0 = 0)
    (σ C : ℝ) (hσ0 : 0 ≤ σ) (hσ1 : σ ≤ 1) (hC : 0 ≤ C)
    (hprefix : ∀ n : ℕ,
      ‖prefixCoeff (normFiberCoeff weight) n‖ ≤ C * (((n : ℝ) + 1) ^ σ))
    (D : ℝ) (hD : 1 ≤ D) :
    ‖normFiberExpSum weight D⁻¹‖ ≤ 3 * C * D ^ σ := by
  let a : ℕ → ℂ := normFiberCoeff weight
  let r : ℝ := Real.exp (-D⁻¹)
  have hDpos : 0 < D := lt_of_lt_of_le zero_lt_one hD
  have ht : 0 < D⁻¹ := inv_pos.mpr hDpos
  have hr0 : 0 ≤ r := (Real.exp_pos _).le
  have hr1 : r < 1 := Real.exp_lt_one_iff.mpr (neg_lt_zero.mpr ht)
  have hpow (n : ℕ) : Real.exp (-(n : ℝ) * D⁻¹) = r ^ n := by
    dsimp [r]
    convert! Real.exp_nat_mul (-D⁻¹) n using 1 ; ring_nf
  have hf : Summable (fun n : ℕ => a n * (r : ℂ) ^ n) := by
    have h := normFiberExpSum_summable χ ψ weight hcoeff ha0 D⁻¹ ht
    simpa only [a, hpow, Complex.ofReal_pow] using h
  have hS : normFiberExpSum weight D⁻¹ =
      ∑' n : ℕ, a n * (r : ℂ) ^ n := by
    unfold normFiberExpSum
    apply tsum_congr
    intro n
    simp only [a, hpow, Complex.ofReal_pow]
  have habel := tsum_eq_one_sub_mul_tsum_prefix a r hr0 hr1 hf
  have hlin : Summable (fun n : ℕ => ((n : ℝ) + 1) * r ^ n) :=
    summable_add_one_mul_geometric hr0 hr1
  have hmoment : Summable (fun n : ℕ => (((n : ℝ) + 1) ^ σ) * r ^ n) := by
    apply Summable.of_nonneg_of_le
      (fun n => mul_nonneg (Real.rpow_nonneg (by positivity) σ) (pow_nonneg hr0 _))
      (fun n => ?_) hlin
    exact mul_le_mul_of_nonneg_right
      (Real.rpow_le_self_of_one_le (by
        have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
        linarith) hσ1) (pow_nonneg hr0 _)
  have hdom : Summable (fun n : ℕ => C * ((((n : ℝ) + 1) ^ σ) * r ^ n)) :=
    hmoment.mul_left C
  have hpoint (n : ℕ) :
      ‖prefixCoeff a n * (r : ℂ) ^ n‖ ≤
        C * ((((n : ℝ) + 1) ^ σ) * r ^ n) := by
    rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg hr0]
    have h := mul_le_mul_of_nonneg_right (hprefix n) (pow_nonneg hr0 n)
    convert! h using 1 ; ring
  have hnorm : Summable (fun n : ℕ => ‖prefixCoeff a n * (r : ℂ) ^ n‖) :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hpoint hdom
  have hgap : 0 ≤ 1 - r := sub_nonneg.mpr hr1.le
  have hmomentBound := geometric_rpow_moment_bound σ D r hσ0 hσ1 hD hr0 hr1
    (exp_inv_geometric_gap D hD)
  calc
    ‖normFiberExpSum weight D⁻¹‖ =
        ‖(1 - (r : ℂ)) * (∑' n : ℕ, prefixCoeff a n * (r : ℂ) ^ n)‖ := by
          rw [hS, habel]
    _ = (1 - r) * ‖∑' n : ℕ, prefixCoeff a n * (r : ℂ) ^ n‖ := by
      have hreal : (1 - (r : ℂ)) = ((1 - r : ℝ) : ℂ) := by push_cast; ring
      rw [norm_mul, hreal, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hgap]
    _ ≤ (1 - r) * (∑' n : ℕ, ‖prefixCoeff a n * (r : ℂ) ^ n‖) :=
      mul_le_mul_of_nonneg_left (norm_tsum_le_tsum_norm hnorm) hgap
    _ ≤ (1 - r) * (∑' n : ℕ,
          C * ((((n : ℝ) + 1) ^ σ) * r ^ n)) :=
      mul_le_mul_of_nonneg_left (Summable.tsum_le_tsum hpoint hnorm hdom) hgap
    _ = C * ((1 - r) * (∑' n : ℕ, (((n : ℝ) + 1) ^ σ) * r ^ n)) := by
      rw [tsum_mul_left]
      ring
    _ ≤ C * (3 * D ^ σ) := mul_le_mul_of_nonneg_left hmomentBound hC
    _ = 3 * C * D ^ σ := by ring

theorem normFiberExpSum_isBigO_of_prefix_power
    {q r₀ : ℕ} [NeZero q] [NeZero r₀]
    (χ : DirichletCharacter ℂ q) (ψ : DirichletCharacter ℂ r₀)
    (weight : Ideal O → ℂ)
    (hcoeff : ∀ n : ℕ, n ≠ 0 → normFiberCoeff weight n = pairInverseCoeff χ ψ n)
    (ha0 : normFiberCoeff weight 0 = 0)
    (σ C : ℝ) (hσ0 : 0 ≤ σ) (hσ1 : σ ≤ 1) (hC : 0 ≤ C)
    (hprefix : ∀ n : ℕ,
      ‖prefixCoeff (normFiberCoeff weight) n‖ ≤ C * (((n : ℝ) + 1) ^ σ)) :
    (fun D : ℝ => normFiberExpSum weight D⁻¹) =O[atTop]
      (fun D : ℝ => D ^ σ) := by
  apply IsBigO.of_bound (3 * C)
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with D hD
  have h := normFiberExpSum_le_of_prefix_power χ ψ weight hcoeff ha0
    σ C hσ0 hσ1 hC hprefix D hD
  have hDnonneg : 0 ≤ D := (zero_le_one.trans hD)
  simpa only [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg hDnonneg σ)] using h

end ShortDraftHeckeBridge

end

end OAI

end


