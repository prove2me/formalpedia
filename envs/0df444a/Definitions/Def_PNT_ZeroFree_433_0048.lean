-- Prove2me | Definitions.Def_PNT_ZeroFree_433_0048
-- name    : PNT_ZeroFree_433_0048
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-10T15:03:21.74398+00:00
-- url     : https://prove2.me/theorems/b259e142-a956-4d70-a72b-b62bfbcddfd6
-- title:
--   Zero-free region foundations: Arithmetic.IdealMobius [0048]
-- statement:
--   Definitions and proved supporting lemmas from the following source modules:
--
--   - OAI.NumberTheory.DirichletL.Arithmetic.IdealMobius
--
--   These declarations form part of the analytic and arithmetic foundations of the Dirichlet L-function nonvanishing argument in the half-plane Re(s) > 7/8. The original namespaces and hypotheses are retained. The code is ported to Lean 4.33.1 and the pinned Mathlib environment; every included lemma has a complete proof.
-- source:
--   https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/Arithmetic/IdealMobius.lean#L74-L614

import Definitions.Def_PNT_ZeroFree_433_0047

/- Supporting source modules for the zero-free-region proof.
Ported and checked against Lean 4.33.1 / Mathlib 0df444a.
Original source attribution:
https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/Arithmetic/IdealMobius.lean#L74-L614
-/

set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

-- Source module: OAI.NumberTheory.DirichletL.Arithmetic.IdealMobius
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
open scoped BigOperators Classical

open scoped BigOperators Classical
open ActualEisensteinCubic UniqueFactorizationMonoid

namespace IdealMobiusDivisorSum
abbrev O := ActualEisensteinCubic.O

def idealDivisors (I : Ideal O) : Finset (Ideal O) :=
  (Ideal.finite_setOfPred_absNorm_le (S := O) (Ideal.absNorm I)).toFinset.filter
    (fun J => J ∣ I)

theorem mem_idealDivisors {I J : Ideal O} (hI : I ≠ ⊥) :
    J ∈ idealDivisors I ↔ J ∣ I := by
  simp only [idealDivisors, Finset.mem_filter, Set.Finite.mem_toFinset, Set.mem_ofPred_eq]
  constructor
  · exact And.right
  · intro hJI
    have hn : 0 < Ideal.absNorm I := Nat.pos_iff_ne_zero.mpr
      (fun hz => hI (Ideal.absNorm_eq_zero_iff.mp hz))
    exact ⟨Nat.le_of_dvd hn (map_dvd Ideal.absNorm hJI), hJI⟩

def primeSupport (I : Ideal O) : Finset (Ideal O) := (normalizedFactors I).toFinset

theorem support_prime {I : Ideal O} {P : Ideal O} (hP : P ∈ primeSupport I) : Prime P :=
  prime_of_normalized_factor P (Multiset.mem_toFinset.mp hP)

theorem support_product_ne_zero {I : Ideal O} {S : Finset (Ideal O)}
    (hS : S ⊆ primeSupport I) : (∏ P ∈ S, P) ≠ 0 :=
  Finset.prod_ne_zero_iff.mpr (fun _P hP => (support_prime (hS hP)).ne_zero)

theorem factors_support_product {I : Ideal O} {S : Finset (Ideal O)}
    (hS : S ⊆ primeSupport I) : normalizedFactors (∏ P ∈ S, P) = S.val := by
  have hp : ∀ P ∈ S.val, Prime P := fun P hP => support_prime (hS hP)
  simpa using normalizedFactors_prod_of_prime hp

theorem squarefree_support_product {I : Ideal O} {S : Finset (Ideal O)}
    (hS : S ⊆ primeSupport I) : Squarefree (∏ P ∈ S, P) := by
  apply (squarefree_iff_nodup_normalizedFactors (support_product_ne_zero hS)).mpr
  rw [factors_support_product hS]
  exact S.nodup

theorem support_product_dvd {I : Ideal O} (hI : I ≠ ⊥) {S : Finset (Ideal O)}
    (hS : S ⊆ primeSupport I) : (∏ P ∈ S, P) ∣ I := by
  apply (dvd_iff_normalizedFactors_le_normalizedFactors (support_product_ne_zero hS) hI).mpr
  rw [factors_support_product hS]
  apply (Multiset.le_iff_subset S.nodup).mpr
  intro P hP
  exact Multiset.mem_toFinset.mp (hS hP)

theorem moebius_support_product {I : Ideal O} {S : Finset (Ideal O)}
    (hS : S ⊆ primeSupport I) :
    (moebius (∏ P ∈ S, P) : ℂ) = (-1 : ℂ) ^ S.card := by
  rw [(squarefree_support_product hS).moebius_eq, factors_eq_normalizedFactors,
    factors_support_product hS]
  simp

theorem support_product_injective {I : Ideal O}
    {S T : Finset (Ideal O)} (hS : S ⊆ primeSupport I) (hT : T ⊆ primeSupport I)
    (h : (∏ P ∈ S, P) = ∏ P ∈ T, P) : S = T := by
  have hf := congrArg normalizedFactors h
  rw [factors_support_product hS, factors_support_product hT] at hf
  exact Finset.val_inj.mp hf

theorem squarefree_divisor_support {I J : Ideal O} (hI : I ≠ ⊥)
    (hJ : Squarefree J) (hJI : J ∣ I) : primeSupport J ⊆ primeSupport I := by
  have hf := (dvd_iff_normalizedFactors_le_normalizedFactors hJ.ne_zero hI).mp hJI
  intro P hP
  exact Multiset.mem_toFinset.mpr (Multiset.mem_of_le hf (Multiset.mem_toFinset.mp hP))

theorem squarefree_support_product_self {J : Ideal O} (hJ : Squarefree J) :
    (∏ P ∈ primeSupport J, P) = J := by
  have hn : (normalizedFactors J).Nodup :=
    (squarefree_iff_nodup_normalizedFactors hJ.ne_zero).mp hJ
  have hv : (primeSupport J).val = normalizedFactors J := by
    simpa only [primeSupport, Multiset.toFinset_val] using hn.dedup
  calc
    _ = (primeSupport J).val.prod := (Finset.prod_val _).symm
    _ = (normalizedFactors J).prod := by rw [hv]
    _ = J := Ideal.prod_normalizedFactors_eq_self hJ.ne_zero

theorem squarefree_divisors_eq_image (I : Ideal O) (hI : I ≠ ⊥) :
    (idealDivisors I).filter Squarefree =
      (primeSupport I).powerset.image (fun S => ∏ P ∈ S, P) := by
  ext J
  simp only [Finset.mem_filter, mem_idealDivisors hI, Finset.mem_image, Finset.mem_powerset]
  constructor
  · rintro ⟨hJI, hJ⟩
    exact ⟨primeSupport J, squarefree_divisor_support hI hJ hJI,
      squarefree_support_product_self hJ⟩
  · rintro ⟨S, hS, rfl⟩
    exact ⟨support_product_dvd hI hS, squarefree_support_product hS⟩

theorem primeSupport_empty_iff (I : Ideal O) (hI : I ≠ ⊥) :
    primeSupport I = ∅ ↔ I = ⊤ := by
  constructor
  · intro h
    have hz : normalizedFactors I = 0 := by
      apply Multiset.toFinset_eq_empty.mp
      exact h
    have hp := Ideal.prod_normalizedFactors_eq_self hI
    rw [hz, Multiset.prod_zero] at hp
    simpa only [Ideal.one_eq_top] using hp.symm
  · intro h
    subst I
    simp [primeSupport, ← Ideal.one_eq_top]

theorem sum_moebius_divisors (I : Ideal O) (hI : I ≠ ⊥) :
    (∑ J ∈ idealDivisors I, (moebius J : ℂ)) = if I = ⊤ then 1 else 0 := by
  have hfilter : (∑ J ∈ idealDivisors I, (moebius J : ℂ)) =
      ∑ J ∈ (idealDivisors I).filter Squarefree, (moebius J : ℂ) := by
    symm
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro J hJ hnot
    have hn : ¬ Squarefree J := by simpa [hJ] using hnot
    rw [moebius_of_not_squarefree hn, Int.cast_zero]
  rw [hfilter, squarefree_divisors_eq_image I hI, Finset.sum_image]
  · have heq : (∑ S ∈ (primeSupport I).powerset, (moebius (∏ P ∈ S, P) : ℂ)) =
        ∑ S ∈ (primeSupport I).powerset, (-1 : ℂ) ^ S.card := by
      exact Finset.sum_congr rfl (fun S hS => moebius_support_product (Finset.mem_powerset.mp hS))
    rw [heq, CoprimeMobiusExtension.sum_subset_sign]
    simp only [primeSupport_empty_iff I hI]
  · intro S hS T hT hST
    exact support_product_injective (Finset.mem_powerset.mp hS)
      (Finset.mem_powerset.mp hT) hST

end IdealMobiusDivisorSum

open scoped BigOperators Classical

namespace CompletedGauss

section

abbrev O := ActualEisensteinCubic.O
open ActualEisensteinCubic

def primaryPrime (P : Ideal O) : O :=
  if h : P.IsMaximal ∧ lambda ∉ P then
    letI : P.IsMaximal := h.1
    (cubicJacobi_exists_primary_generator P h.2).choose
  else 0

theorem primaryPrime_spec (P : Ideal O) (h : primaryPrime P ≠ 0) :
    P.IsMaximal ∧ lambda ∉ P ∧
      Ideal.span {primaryPrime P} = P ∧ lambda ^ 2 ∣ primaryPrime P - 1 := by
  classical
  by_cases hg : P.IsMaximal ∧ lambda ∉ P
  · let : P.IsMaximal := hg.1
    have hs := (cubicJacobi_exists_primary_generator P hg.2).choose_spec
    simpa only [primaryPrime, dif_pos hg] using ⟨hg.1, hg.2, hs.1.symm, hs.2.1⟩
  · simp only [primaryPrime, dif_neg hg, ne_eq, not_true_eq_false] at h

theorem primaryPrime_ne_zero (P : Ideal O) [P.IsMaximal] (hg : lambda ∉ P) :
    primaryPrime P ≠ 0 := by
  classical
  have hs := (cubicJacobi_exists_primary_generator P hg).choose_spec
  have htest : P.IsMaximal ∧ lambda ∉ P := ⟨inferInstance, hg⟩
  intro hz
  have hp0 : (cubicJacobi_exists_primary_generator P hg).choose = 0 := by
    simpa only [primaryPrime, dif_pos htest] using hz
  rw [hp0] at hs
  exact (NeZero.ne P) (by simpa using hs.1)

def primaryGenerator (I : Ideal O) : O :=
  if I = 0 then 0 else ((UniqueFactorizationMonoid.normalizedFactors I).map primaryPrime).prod

@[simp] theorem primaryGenerator_zero : primaryGenerator 0 = 0 := by rw [primaryGenerator, if_pos rfl]

@[simp] theorem primaryGenerator_bot : primaryGenerator ⊥ = 0 := primaryGenerator_zero

@[simp] theorem primaryGenerator_one : primaryGenerator 1 = 1 := by
  rw [primaryGenerator, if_neg one_ne_zero, UniqueFactorizationMonoid.normalizedFactors_one]
  rfl

theorem primaryGenerator_mul (I J : Ideal O) :
    primaryGenerator (I * J) = primaryGenerator I * primaryGenerator J := by
  classical
  by_cases hI : I = 0
  · simp [hI]
  by_cases hJ : J = 0
  · simp [hJ]
  simp only [primaryGenerator, if_neg hI, if_neg hJ, if_neg (mul_ne_zero hI hJ),
    UniqueFactorizationMonoid.normalizedFactors_mul hI hJ, Multiset.map_add, Multiset.prod_add]

def primaryGeneratorHom : Ideal O →*₀ O where
  toFun := primaryGenerator
  map_zero' := primaryGenerator_zero
  map_one' := primaryGenerator_one
  map_mul' := primaryGenerator_mul

theorem primaryGenerator_ne_zero_ideal (I : Ideal O) (h : primaryGenerator I ≠ 0) : I ≠ 0 := by
  intro hI
  exact h (by simp [hI])

theorem primaryPrime_factor_ne_zero (I P : Ideal O) (hI : primaryGenerator I ≠ 0)
    (hP : P ∈ UniqueFactorizationMonoid.normalizedFactors I) : primaryPrime P ≠ 0 := by
  have hI0 := primaryGenerator_ne_zero_ideal I hI
  have hprod : ((UniqueFactorizationMonoid.normalizedFactors I).map primaryPrime).prod ≠ 0 := by
    simpa only [primaryGenerator, if_neg hI0] using hI
  intro hz
  exact hprod (Multiset.prod_eq_zero_iff.mpr (Multiset.mem_map.mpr ⟨P, hP, hz⟩))

theorem span_multiset_prod (s : Multiset O) :
    Ideal.span {s.prod} = (s.map (fun x => Ideal.span {x})).prod := by
  induction s using Multiset.induction_on with
  | empty => simp
  | @cons a s ih => simp only [Multiset.prod_cons, Multiset.map_cons,
      ← Ideal.span_singleton_mul_span_singleton, ih]

theorem primaryGenerator_spec (I : Ideal O) (h : primaryGenerator I ≠ 0) :
    Ideal.span {primaryGenerator I} = I ∧ lambda ^ 2 ∣ primaryGenerator I - 1 := by
  classical
  have hI0 := primaryGenerator_ne_zero_ideal I h
  have hprime : ∀ P ∈ UniqueFactorizationMonoid.normalizedFactors I,
      Ideal.span {primaryPrime P} = P ∧ lambda ^ 2 ∣ primaryPrime P - 1 := by
    intro P hP
    exact (primaryPrime_spec P (primaryPrime_factor_ne_zero I P h hP)).2.2
  rw [primaryGenerator, if_neg hI0]
  constructor
  · rw [span_multiset_prod, Multiset.map_map]
    have hm : (UniqueFactorizationMonoid.normalizedFactors I).map
        ((fun x => Ideal.span {x}) ∘ primaryPrime) =
        UniqueFactorizationMonoid.normalizedFactors I := by
      calc
        _ = (UniqueFactorizationMonoid.normalizedFactors I).map id :=
          Multiset.map_congr rfl (fun P hP => (hprime P hP).1)
        _ = _ := Multiset.map_id' _
    rw [hm]
    exact Ideal.prod_normalizedFactors_eq_self hI0
  · apply primary_multiset_prod
    intro r hr
    obtain ⟨P, hP, rfl⟩ := Multiset.mem_map.mp hr
    exact (hprime P hP).2

theorem primaryGenerator_span (n : O) (hn : n ≠ 0)
    (hprimary : lambda ^ 2 ∣ n - 1) : primaryGenerator (Ideal.span {n}) = n := by
  classical
  have hI0 : (Ideal.span {n} : Ideal O) ≠ 0 := Ideal.span_singleton_eq_bot.not.mpr hn
  have hgen : primaryGenerator (Ideal.span {n}) ≠ 0 := by
    rw [primaryGenerator, if_neg hI0]
    apply Multiset.prod_ne_zero
    intro hzero
    obtain ⟨P, hP, hz⟩ := Multiset.mem_map.mp hzero
    have hp := UniqueFactorizationMonoid.prime_of_normalized_factor P hP
    let : P.IsMaximal := (Ideal.isPrime_of_prime hp).isMaximal hp.ne_zero
    have hle := ((Ideal.mem_normalizedFactors_iff hI0).mp hP).2
    have hnP : n ∈ P := hle (Ideal.subset_span (by simp))
    exact primaryPrime_ne_zero P (primary_maximal_divisor_good n hprimary P hnP) hz
  have hspec := primaryGenerator_spec (Ideal.span {n}) hgen
  exact primary_associated_eq _ _ (Ideal.span_singleton_eq_span_singleton.mp hspec.1)
    hspec.2 hprimary

theorem primaryGenerator_norm_sq (I : Ideal O) (h : primaryGenerator I ≠ 0) :
    ‖ConcreteTraceCRT.eisEmbedding (primaryGenerator I)‖ ^ 2 = (Ideal.absNorm I : ℝ) := by
  rw [eisEmbedding_norm_sq_eq_absNorm_span, (primaryGenerator_spec I h).1]

open ActualEisensteinCubic

theorem compact_window_bound (W : ℝ → ℂ) (hW : HasCompactSupport W) :
    ∃ B : ℝ, 0 < B ∧ ∀ y, W y ≠ 0 → y ≤ B := by
  obtain ⟨B, hB⟩ := hW.bddAbove
  refine ⟨max B 1, lt_of_lt_of_le zero_lt_one (le_max_right _ _), ?_⟩
  intro y hy
  exact (hB (subset_tsupport W hy)).trans (le_max_left _ _)

theorem norm_at_least_one (I : Ideal O) (hI : I ≠ 0) :
    (1 : ℝ) ≤ Ideal.absNorm I := by
  exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hI)

theorem triple_scale_bounds (a b c : ℝ) (ha : 1 ≤ a) (hb : 1 ≤ b) (hc : 1 ≤ c) :
    a ≤ a * b ^ 3 * c ^ 3 ∧ b ≤ a * b ^ 3 * c ^ 3 ∧ c ≤ a * b ^ 3 * c ^ 3 := by
  have ha0 : 0 ≤ a := by linarith
  have hb0 : 0 ≤ b := by linarith
  have hc0 : 0 ≤ c := by linarith
  have hb3 : 1 ≤ b ^ 3 := one_le_pow₀ hb
  have hc3 : 1 ≤ c ^ 3 := one_le_pow₀ hc
  constructor
  · calc a = a * 1 * 1 := by ring
         _ ≤ a * b ^ 3 * c ^ 3 := by gcongr
  constructor
  · calc b ≤ b ^ 3 := le_self_pow₀ hb (by decide)
         _ = 1 * b ^ 3 * 1 := by ring
         _ ≤ a * b ^ 3 * c ^ 3 := by gcongr
  · calc c ≤ c ^ 3 := le_self_pow₀ hc (by decide)
         _ = 1 * 1 * c ^ 3 := by ring
         _ ≤ a * b ^ 3 * c ^ 3 := by gcongr

theorem finite_support_norm_triple (W : ℝ → ℂ) (hW : HasCompactSupport W)
    (X : ℝ) (hX : 0 < X) (F : Ideal O × Ideal O × Ideal O → ℂ)
    (hzero : ∀ I J H, I = 0 ∨ J = 0 ∨ H = 0 → F (I, J, H) = 0)
    (hwindow : ∀ I J H,
      W ((Ideal.absNorm I : ℝ) * (Ideal.absNorm J : ℝ) ^ 3 *
        (Ideal.absNorm H : ℝ) ^ 3 / X) = 0 → F (I, J, H) = 0) :
    (Function.support F).Finite := by
  obtain ⟨B, hB, hbound⟩ := compact_window_bound W hW
  obtain ⟨M, hM⟩ := exists_nat_gt (B * X)
  let S := {I : Ideal O | Ideal.absNorm I ≤ M}
  have hS : S.Finite := Ideal.finite_setOfPred_absNorm_le M
  apply (hS.prod (hS.prod hS)).subset
  rintro ⟨I, J, H⟩ hF
  have hF0 : F (I, J, H) ≠ 0 := hF
  have hI : I ≠ 0 := fun h => hF0 (hzero I J H (Or.inl h))
  have hJ : J ≠ 0 := fun h => hF0 (hzero I J H (Or.inr (Or.inl h)))
  have hH : H ≠ 0 := fun h => hF0 (hzero I J H (Or.inr (Or.inr h)))
  have hw : W ((Ideal.absNorm I : ℝ) * (Ideal.absNorm J : ℝ) ^ 3 *
      (Ideal.absNorm H : ℝ) ^ 3 / X) ≠ 0 := fun h => hF0 (hwindow I J H h)
  have hsize := (div_le_iff₀ hX).mp (hbound _ hw)
  have hb := triple_scale_bounds _ _ _ (norm_at_least_one I hI)
    (norm_at_least_one J hJ) (norm_at_least_one H hH)
  have hIM : Ideal.absNorm I ≤ M := by exact_mod_cast (hb.1.trans hsize).trans hM.le
  have hJM : Ideal.absNorm J ≤ M := by exact_mod_cast (hb.2.1.trans hsize).trans hM.le
  have hHM : Ideal.absNorm H ≤ M := by exact_mod_cast (hb.2.2.trans hsize).trans hM.le
  exact ⟨hIM, hJM, hHM⟩

end
section

open ActualEisensteinCubic ConcreteTraceCRT

def primeSupport (I : Ideal O) : Finset (Ideal O) :=
  (UniqueFactorizationMonoid.normalizedFactors I).toFinset

abbrev PrimeIndex (I : Ideal O) := {P : Ideal O // P ∈ primeSupport I}

instance primeIndexMaximal (I : Ideal O) (P : PrimeIndex I) : P.val.IsMaximal := by
  have hp := UniqueFactorizationMonoid.prime_of_normalized_factor P.val
    (Multiset.mem_toFinset.mp P.property)
  exact (Ideal.isPrime_of_prime hp).isMaximal hp.ne_zero

theorem primeIndex_good (I : Ideal O) (hI : primaryGenerator I ≠ 0) (P : PrimeIndex I) :
    lambda ∉ P.val :=
  (primaryPrime_spec P.val (primaryPrime_factor_ne_zero I P.val hI
    (Multiset.mem_toFinset.mp P.property))).2.1

theorem primeIndex_le (I : Ideal O) (hI : I ≠ 0) (P : PrimeIndex I) : I ≤ P.val :=
  ((Ideal.mem_normalizedFactors_iff hI).mp (Multiset.mem_toFinset.mp P.property)).2

def cubicRow (I : Ideal O) (hI : primaryGenerator I ≠ 0) (x : O ⧸ I) : ℂ :=
  ∏ P : PrimeIndex I,
    (canonicalSextic P.val (primeIndex_good I hI P) ^ 2)
      (Ideal.Quotient.factor (primeIndex_le I (primaryGenerator_ne_zero_ideal I hI) P) x)

def gaussTwo (I : Ideal O) (hI : primaryGenerator I ≠ 0) : ℂ := by
  let n := primaryGenerator I
  letI : Finite (O ⧸ Ideal.span {n}) := finite_quotient_span hI
  letI : Fintype (O ⧸ Ideal.span {n}) := Fintype.ofFinite _
  let e := Ideal.quotEquivOfEq (primaryGenerator_spec I hI).1
  let ψ := eisTraceModChar ShortDraftTrace.breveE ConcreteBreveE.breveE_period_coordinates n hI
  exact (∑ x : O ⧸ Ideal.span {n}, cubicRow I hI (e x) * ψ x) / (‖eisEmbedding n‖ : ℂ)

def squarefreeGaussCoefficient (I : Ideal O) : ℂ :=
  if h : Squarefree I ∧ primaryGenerator I ≠ 0 then
    star (FiniteGaussPhase.angularFactor (primaryGenerator I)) * gaussTwo I h.2
  else 0

@[simp] theorem squarefreeGaussCoefficient_zero : squarefreeGaussCoefficient 0 = 0 := by
  simp [squarefreeGaussCoefficient]

@[simp] theorem squarefreeGaussCoefficient_bot : squarefreeGaussCoefficient ⊥ = 0 :=
  squarefreeGaussCoefficient_zero

theorem squarefreeGaussCoefficient_eq (I : Ideal O) (hs : Squarefree I)
    (hI : primaryGenerator I ≠ 0) :
    squarefreeGaussCoefficient I =
      star (FiniteGaussPhase.angularFactor (primaryGenerator I)) * gaussTwo I hI := by
  rw [squarefreeGaussCoefficient, dif_pos ⟨hs, hI⟩]

theorem angularFactor_mul (a b : O) :
    FiniteGaussPhase.angularFactor (a * b) =
      FiniteGaussPhase.angularFactor a * FiniteGaussPhase.angularFactor b := by
  simp only [FiniteGaussPhase.angularFactor, map_mul, norm_mul, Complex.ofReal_mul]
  ring

def cubeWeight (Ψ : O →* ℂ) : Ideal O →* ℂ where
  toFun I := star (FiniteGaussPhase.angularFactor (primaryGenerator I)) ^ 3 *
    Ψ (primaryGenerator I) ^ 3 / (Ideal.absNorm I : ℂ)
  map_one' := by
    simp only [primaryGenerator_one, FiniteGaussPhase.angularFactor, map_one,
      norm_one, Complex.ofReal_one, div_one, star_one, one_pow, one_mul, Nat.cast_one]
  map_mul' I J := by
    simp only [primaryGenerator_mul, angularFactor_mul, map_mul, star_mul, mul_pow, Nat.cast_mul]
    ring

@[simp] theorem cubeWeight_zero (Ψ : O →* ℂ) : cubeWeight Ψ 0 = 0 := by
  simp [cubeWeight, FiniteGaussPhase.angularFactor]

@[simp] theorem cubeWeight_bot (Ψ : O →* ℂ) : cubeWeight Ψ ⊥ = 0 := cubeWeight_zero Ψ

def columnWeight (Ψ : O →* ℂ) (I : Ideal O) : ℂ :=
  squarefreeGaussCoefficient I * Ψ (primaryGenerator I)

@[simp] theorem columnWeight_zero (Ψ : O →* ℂ) : columnWeight Ψ 0 = 0 := by
  simp [columnWeight]

@[simp] theorem columnWeight_bot (Ψ : O →* ℂ) : columnWeight Ψ ⊥ = 0 := columnWeight_zero Ψ

def Vstar (W : ℝ → ℂ) (y : ℝ) : ℂ := (Real.sqrt y : ℂ) * W y

def summand (Ψ : O →* ℂ) (W : ℝ → ℂ) (X : ℝ) (I J : Ideal O) : ℂ :=
  columnWeight Ψ I / (Real.sqrt (Ideal.absNorm I : ℝ) : ℂ) * cubeWeight Ψ J *
    Vstar W ((Ideal.absNorm I : ℝ) * (Ideal.absNorm J : ℝ) ^ 3 / X)

def completedT (Ψ : O →* ℂ) (W : ℝ → ℂ) (X : ℝ) : ℂ :=
  ∑' I : Ideal O, ∑' J : Ideal O, summand Ψ W X I J

theorem summand_zero_left (Ψ : O →* ℂ) (W : ℝ → ℂ) (X : ℝ) (J : Ideal O) :
    summand Ψ W X 0 J = 0 := by simp [summand]

theorem summand_zero_right (Ψ : O →* ℂ) (W : ℝ → ℂ) (X : ℝ) (I : Ideal O) :
    summand Ψ W X I 0 = 0 := by simp [summand]

theorem summand_zero_window (Ψ : O →* ℂ) (W : ℝ → ℂ) (X : ℝ) (I J : Ideal O)
    (h : W ((Ideal.absNorm I : ℝ) * (Ideal.absNorm J : ℝ) ^ 3 / X) = 0) :
    summand Ψ W X I J = 0 := by simp [summand, Vstar, h]

theorem cubicRow_mk (I : Ideal O) (hI : primaryGenerator I ≠ 0) (a : O) :
    cubicRow I hI (Ideal.Quotient.mk I a) =
      ∏ P : PrimeIndex I, (canonicalSextic P.val (primeIndex_good I hI P) ^ 2)
        (Ideal.Quotient.mk P.val a) := by
  simp only [cubicRow, Ideal.Quotient.factor_mk]

theorem cubicRow_zero_iff (I : Ideal O) (hI : primaryGenerator I ≠ 0) (a : O) :
    cubicRow I hI (Ideal.Quotient.mk I a) = 0 ↔
      ∃ P ∈ primeSupport I, a ∈ P := by
  rw [cubicRow_mk, Finset.prod_eq_zero_iff]
  have hlocal (P : PrimeIndex I) :
      (canonicalSextic P.val (primeIndex_good I hI P) ^ 2) (Ideal.Quotient.mk P.val a) = 0 ↔ a ∈ P.val := by
    let : Field (O ⧸ P.val) := Ideal.Quotient.field P.val
    rw [MulChar.apply_eq_zero_iff]
    simp only [isUnit_iff_ne_zero, not_not, Ideal.Quotient.eq_zero_iff_mem]
  constructor
  · rintro ⟨P, _, hP⟩
    exact ⟨P.val, P.property, (hlocal P).mp hP⟩
  · rintro ⟨P, hP, ha⟩
    exact ⟨⟨P, hP⟩, Finset.mem_univ _, (hlocal ⟨P, hP⟩).mpr ha⟩

theorem primaryGenerator_norm (I : Ideal O) (hI : primaryGenerator I ≠ 0) :
    ‖eisEmbedding (primaryGenerator I)‖ = Real.sqrt (Ideal.absNorm I : ℝ) := by
  rw [← primaryGenerator_norm_sq I hI, Real.sqrt_sq_eq_abs, abs_of_nonneg (norm_nonneg _)]

theorem cubeWeight_span (Ψ : O →* ℂ) (n : O) (hn : n ≠ 0)
    (hp : lambda ^ 2 ∣ n - 1) :
    cubeWeight Ψ (Ideal.span {n}) =
      star (FiniteGaussPhase.angularFactor n) ^ 3 * Ψ n ^ 3 /
        (ShortDraftLatticeCount.qNat n : ℂ) := by
  change star (FiniteGaussPhase.angularFactor (primaryGenerator (Ideal.span {n}))) ^ 3 *
    Ψ (primaryGenerator (Ideal.span {n})) ^ 3 / (Ideal.absNorm (Ideal.span {n}) : ℂ) = _
  rw [primaryGenerator_span n hn hp, qNat_eq_absNorm_span]

theorem columnWeight_eq (Ψ : O →* ℂ) (I : Ideal O) (hs : Squarefree I)
    (hI : primaryGenerator I ≠ 0) :
    columnWeight Ψ I = star (FiniteGaussPhase.angularFactor (primaryGenerator I)) *
      gaussTwo I hI * Ψ (primaryGenerator I) := by
  rw [columnWeight, squarefreeGaussCoefficient_eq I hs hI]

theorem columnWeight_zero_of_mask (Ψ : O →* ℂ) (I : Ideal O)
    (h : Ψ (primaryGenerator I) = 0) : columnWeight Ψ I = 0 := by
  simp only [columnWeight, h, mul_zero]

theorem cubeWeight_zero_of_mask (Ψ : O →* ℂ) (I : Ideal O)
    (h : Ψ (primaryGenerator I) = 0) : cubeWeight Ψ I = 0 := by
  change _ * Ψ (primaryGenerator I) ^ 3 / _ = 0
  rw [h, zero_pow (by decide), mul_zero, zero_div]

end

open ActualEisensteinCubic
open IdealMobiusDivisorSum (idealDivisors mem_idealDivisors sum_moebius_divisors)

def MulFiber (B : Ideal O) := {p : Ideal O × Ideal O // p.1 * p.2 = B}

def mulFiberDivisorEquiv (B : Ideal O) (hB : B ≠ 0) :
    MulFiber B ≃ {D : Ideal O // D ∈ idealDivisors B} := by
  let f : MulFiber B → {D : Ideal O // D ∈ idealDivisors B} :=
    fun p => ⟨p.val.1, (mem_idealDivisors hB).mpr ⟨p.val.2, p.property.symm⟩⟩
  apply Equiv.ofBijective f
  constructor
  · intro p q hpq
    have hfst : p.val.1 = q.val.1 := congrArg Subtype.val hpq
    apply Subtype.ext
    apply Prod.ext hfst
    have hn : p.val.1 ≠ 0 := by
      intro hz
      have he := p.property
      rw [hz, zero_mul] at he
      exact hB he.symm
    apply mul_left_cancel₀ hn
    rw [p.property, hfst, q.property]
  · intro D
    obtain ⟨J, hJ⟩ := (mem_idealDivisors hB).mp D.property
    exact ⟨⟨(D.val, J), hJ.symm⟩, rfl⟩

theorem mulFiber_moebius_sum (B : Ideal O) (hB : B ≠ 0) :
    (∑' p : MulFiber B, (UniqueFactorizationMonoid.moebius p.val.1 : ℂ)) =
      if B = 1 then 1 else 0 := by
  let e := mulFiberDivisorEquiv B hB
  calc
    _ = ∑' D : {D : Ideal O // D ∈ idealDivisors B},
        (UniqueFactorizationMonoid.moebius D.val : ℂ) := by
      exact e.tsum_eq (fun D => (UniqueFactorizationMonoid.moebius D.val : ℂ))
    _ = ∑ D ∈ idealDivisors B, (UniqueFactorizationMonoid.moebius D : ℂ) := by
      rw [tsum_fintype]
      exact (Finset.sum_subtype (idealDivisors B) (fun D => Iff.rfl)
        (fun D => (UniqueFactorizationMonoid.moebius D : ℂ))).symm
    _ = if B = 1 then 1 else 0 := by
      simpa only [Ideal.one_eq_top] using sum_moebius_divisors B hB

theorem ideal_cube_convolution (c : Ideal O →* ℂ) (hc0 : c 0 = 0)
    (f : Ideal O → ℂ)
    (hfinite : (Function.support (fun p : Ideal O × Ideal O =>
      (UniqueFactorizationMonoid.moebius p.1 : ℂ) * c (p.1 * p.2) * f (p.1 * p.2))).Finite) :
    (∑' H : Ideal O, ∑' J : Ideal O,
      (UniqueFactorizationMonoid.moebius H : ℂ) * c (H * J) * f (H * J)) = f 1 := by
  let F : Ideal O × Ideal O → ℂ := fun p =>
    (UniqueFactorizationMonoid.moebius p.1 : ℂ) * c (p.1 * p.2) * f (p.1 * p.2)
  have hF : Summable F := summable_of_hasFiniteSupport hfinite
  have hfiber (B : Ideal O) : (∑' p : MulFiber B, F p.val) =
      if B = 1 then f 1 else 0 := by
    by_cases hB : B = 0
    · subst B
      have heach : ∀ p : MulFiber 0, F p.val = 0 := by
        intro p
        dsimp [F]
        rw [p.property, hc0, mul_zero, zero_mul]
      simp only [heach, tsum_zero, zero_ne_one, ite_false]
    · calc
        _ = ∑' p : MulFiber B, (UniqueFactorizationMonoid.moebius p.val.1 : ℂ) * (c B * f B) := by
          apply tsum_congr
          intro p
          dsimp [F]
          rw [p.property, mul_assoc]
        _ = (∑' p : MulFiber B, (UniqueFactorizationMonoid.moebius p.val.1 : ℂ)) * (c B * f B) := by
          rw [tsum_mul_right]
        _ = if B = 1 then f 1 else 0 := by
          rw [mulFiber_moebius_sum B hB]
          split_ifs with h
          · subst B; simp only [map_one, one_mul]
          · simp
  have hs := hF.hasSum.tsum_fiberwise (fun p : Ideal O × Ideal O => p.1 * p.2)
  change HasSum (fun B : Ideal O => ∑' p : MulFiber B, F p.val) (∑' p, F p) at hs
  simp_rw [hfiber] at hs
  have hsum : (∑' p, F p) = f 1 := by
    have he := hs.tsum_eq.symm
    simpa only [tsum_ite_eq, one_ne_zero] using he
  rw [← hF.tsum_prod]
  exact hsum

end CompletedGauss

end

end OAI

end


