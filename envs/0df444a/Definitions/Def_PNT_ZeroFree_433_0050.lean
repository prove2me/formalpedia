-- Prove2me | Definitions.Def_PNT_ZeroFree_433_0050
-- name    : PNT_ZeroFree_433_0050
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-10T15:09:50.183424+00:00
-- url     : https://prove2.me/theorems/21e27b43-c371-4adf-95ca-16c39fb7e6ef
-- title:
--   Zero-free region foundations: GaussSum.RayCharacters [0050]
-- statement:
--   Definitions and proved supporting lemmas from the following source modules:
--
--   - OAI.NumberTheory.DirichletL.GaussSum.RayCharacters
--
--   These declarations form part of the analytic and arithmetic foundations of the Dirichlet L-function nonvanishing argument in the half-plane Re(s) > 7/8. The original namespaces and hypotheses are retained. The code is ported to Lean 4.33.1 and the pinned Mathlib environment; every included lemma has a complete proof.
-- source:
--   https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/GaussSum/RayCharacters.lean#L78-L723

import Definitions.Def_PNT_ZeroFree_433_0049

/- Supporting source modules for the zero-free-region proof.
Ported and checked against Lean 4.33.1 / Mathlib 0df444a.
Original source attribution:
https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/GaussSum/RayCharacters.lean#L78-L723
-/

set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

-- Source module: OAI.NumberTheory.DirichletL.GaussSum.RayCharacters
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

open scoped BigOperators Classical

namespace RayFourExpansion
open ActualEisensteinCubic ConcreteTraceCRT FiniteGaussPhase QuadraticGaussRay
open ActualEisensteinCoordinates MixedCrossSeparation

theorem prime_unit_mod_four (p : O) [(Ideal.span {p}).IsMaximal]
    (hchar : ringChar (O ⧸ Ideal.span {p}) ≠ 2) :
    IsUnit (Ideal.Quotient.mk (Ideal.span {(4 : O)}) p) := by
  let : Field (O ⧸ Ideal.span {p}) := Ideal.Quotient.field _
  let : Fintype (O ⧸ Ideal.span {p}) := Fintype.ofFinite _
  have h2 : (2 : O) ∉ Ideal.span {p} := by
    intro hm
    have hz : (2 : O ⧸ Ideal.span {p}) = 0 := by
      simpa only [map_ofNat] using Ideal.Quotient.eq_zero_iff_mem.mpr hm
    apply hchar
    exact (Nat.prime_dvd_prime_iff_eq (CharP.char_is_prime (O ⧸ Ideal.span {p}) _)
      Nat.prime_two).mp ((ringChar.spec (O ⧸ Ideal.span {p}) 2).mp hz)
  let : (Ideal.span {(2 : O)}).IsMaximal := by
    simpa only [cubicTwoIdeal, Ideal.span_singleton_neg] using cubicTwoIdeal_isMaximal
  have hcop : IsCoprime (Ideal.span {p}) (Ideal.span {(2 : O)}) := by
    apply Ideal.isCoprime_of_isMaximal
    intro heq
    apply h2
    rw [heq]
    exact Ideal.subset_span (by simp)
  obtain ⟨a, b, hab⟩ := IdealGaussCRT.bezout_of_principal_coprime hcop
  have hcp : IsCoprime p (2 : O) := ⟨a, b, hab⟩
  have hcp4 : IsCoprime p (4 : O) := by
    simpa only [show (2 : O) ^ 2 = 4 by norm_num] using
      (hcp.pow_right : IsCoprime p ((2 : O) ^ 2))
  obtain ⟨a, b, hab⟩ := hcp4
  have hz : Ideal.Quotient.mk (Ideal.span {(4 : O)}) (4 : O) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (by simp))
  have hm := congrArg (Ideal.Quotient.mk (Ideal.span {(4 : O)})) hab
  simp only [map_add, map_mul, map_one, hz, mul_zero, add_zero] at hm
  exact IsUnit.of_mul_eq_one_right _ hm

theorem prime_product_unit_mod_four {ι : Type*} (p : ι → O)
    [∀ i, (Ideal.span {p i}).IsMaximal]
    (hchar : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2) (S : Finset ι) :
    IsUnit (Ideal.Quotient.mk (Ideal.span {(4 : O)}) (∏ i ∈ S, p i)) := by
  rw [map_prod]
  exact IsUnit.prod_iff.mpr (fun i _ => prime_unit_mod_four (p i) (hchar i))

theorem rayMask_prime_product {ι : Type*} (p : ι → O)
    [∀ i, (Ideal.span {p i}).IsMaximal]
    (hchar : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2) (S : Finset ι) :
    rayMask (∏ i ∈ S, p i) = 1 := by
  rw [rayMask, if_pos (prime_product_unit_mod_four p hchar S)]

theorem canonicalProductG_character_expansion
    {ι : Type*} [Fintype ι] (p : ι → O) (hp : ∀ i, p i ≠ 0)
    [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hgood : ∀ i, lambda ∉ Ideal.span {p i})
    (hchar : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
    (hprimary : ∀ i, lambda ^ 2 ∣ p i - 1) :
    canonicalProductG p hp hcop hgood =
      ∑ χ : RayCharacter, gCoeff χ * rayCharacter χ (∏ i, p i) := by
  rw [canonicalProductG_eq_fixed_quotient p hp hcop hgood hchar hprimary]
  have h := fixedG_character_expansion (∏ i, p i)
  rw [rayMask_prime_product p hchar Finset.univ, one_mul] at h
  exact h

theorem quadraticCrossPhase_character_expansion
    {ι : Type*} [DecidableEq ι] (p : ι → O) (hp : ∀ i, p i ≠ 0)
    [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i, lambda ∉ Ideal.span {p i})
    (hchar : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
    (A B : Finset ι) (hd : Disjoint A B) :
    quadraticCrossPhase p hg A B =
      ∑ χ : RayCharacter, ∑ η : RayCharacter,
        crossCoeff χ η * rayCharacter χ (∏ i ∈ A, p i) *
          rayCharacter η (∏ i ∈ B, p i) := by
  rw [quadraticCrossPhase_eq_rayPair p hp hcop hg hchar A B hd]
  have h := quadraticRayPair_character_expansion (∏ i ∈ A, p i) (∏ i ∈ B, p i)
  rw [rayMask_prime_product p hchar A, rayMask_prime_product p hchar B, one_mul, one_mul] at h
  exact h

end RayFourExpansion

namespace MixedCrossSeparation
open ActualEisensteinCubic ConcreteTraceCRT FiniteGaussPhase MixedGaussConversion
open QuadraticGaussRay ActualEisensteinCoordinates GaussGeneratorTransport

theorem converted_active_row_observations
    {ι : Type*} [DecidableEq ι] (p : ι → O) (hp : ∀ i, p i ≠ 0)
    [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i, lambda ∉ Ideal.span {p i})
    (hchar : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
    (hprimary : ∀ i, lambda ^ 2 ∣ p i - 1) (S T : Finset ι) (d h : O) :
    let q : activeSupport S T → O := fun i => p i.val
    let hq : ∀ i, q i ≠ 0 := fun i => hp i.val
    let hgood : ∀ i, lambda ∉ Ideal.span {q i} := fun i => hg i.val
    let A : Finset (activeSupport S T) := Finset.univ.filter fun i => i.val ∈ S \ T
    let B : Finset (activeSupport S T) := Finset.univ.filter fun i => i.val ∉ S \ T
    let P : ι → Ideal O := fun i => Ideal.span {p i}
    let row := finiteSexticRow (activePrimes P S T) (fun i => hg i.val) (activeExponent S T)
    let cA := star (convertedColumnBlock q hq hgood A true) *
      finiteSquarefreeRow P hg (S \ T) d
    let cB := convertedColumnBlock q hq hgood B false *
      finiteSquarefreeRow P hg (T \ S) d
    activeConvertedGauss p hp hg S T * (row d * star (row h)) =
      quadraticRayPair (residue (∏ i ∈ A, q i)) (residue (∏ i ∈ B, q i)) *
        star (cA * star (finiteSquarefreeRow P hg (S \ T) h)) *
        (cB * star (finiteSquarefreeRow P hg (T \ S) h)) := by
  dsimp only
  have hqcop : Pairwise (Function.onFun IsCoprime
      (fun i : activeSupport S T => Ideal.span {p i.val})) := by
    intro i k hik
    exact hcop (fun he => hik (Subtype.ext he))
  have hd : Disjoint
      (Finset.univ.filter (fun i : activeSupport S T => i.val ∈ S \ T))
      (Finset.univ.filter (fun i : activeSupport S T => i.val ∉ S \ T)) := by
    apply Finset.disjoint_left.mpr
    intro i hi hj
    exact (Finset.mem_filter.mp hj).2 (Finset.mem_filter.mp hi).2
  rw [activeConvertedGauss_separated p hp hg hprimary S T]
  rw [quadraticCrossPhase_eq_rayPair (fun i : activeSupport S T => p i.val)
    (fun i => hp i.val) hqcop (fun i => hg i.val) (fun i => hchar i.val) _ _ hd]
  rw [active_dual_row_factorization (fun i => Ideal.span {p i}) hg S T d h]
  simp only [star_mul, star_star]
  ring

theorem convertedColumnBlock_image
    {ι κ : Type*} [DecidableEq ι] [DecidableEq κ]
    (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hg : ∀ i, lambda ∉ Ideal.span {p i}) (e : κ → ι) (he : Function.Injective e)
    (A : Finset κ) (inverse : Bool) :
    convertedColumnBlock (fun i => p (e i)) (fun i => hp (e i)) (fun i => hg (e i)) A inverse =
      convertedColumnBlock p hp hg (A.image e) inverse := by
  unfold convertedColumnBlock
  rw [Finset.prod_image (fun a ha b hb hab => he hab)]
  apply Finset.prod_congr rfl
  intro i hi
  rw [← Finset.image_erase he A i, Finset.prod_image (fun a ha b hb hab => he hab)]
  rfl

theorem quadraticCrossPhase_image
    {ι κ : Type*} [DecidableEq ι] [DecidableEq κ]
    (p : ι → O) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hg : ∀ i, lambda ∉ Ideal.span {p i}) (e : κ → ι) (he : Function.Injective e)
    (A B : Finset κ) :
    quadraticCrossPhase (fun i => p (e i)) (fun i => hg (e i)) A B =
      quadraticCrossPhase p hg (A.image e) (B.image e) := by
  unfold quadraticCrossPhase
  rw [Finset.prod_image (fun a ha b hb hab => he hab)]
  apply Finset.prod_congr rfl
  intro i hi
  rw [Finset.prod_image (fun a ha b hb hab => he hab)]
  rfl

private theorem negative_active_image {ι : Type*} [DecidableEq ι] (S T : Finset ι) :
    (Finset.univ.filter (fun i : activeSupport S T => i.val ∈ S \ T)).image Subtype.val = S \ T := by
  ext i
  constructor
  · intro hi
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hi
    exact (Finset.mem_filter.mp ha).2
  · intro hi
    exact Finset.mem_image.mpr ⟨⟨i, Finset.mem_union_left _ hi⟩,
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩, rfl⟩

private theorem positive_active_image {ι : Type*} [DecidableEq ι] (S T : Finset ι) :
    (Finset.univ.filter (fun i : activeSupport S T => i.val ∉ S \ T)).image Subtype.val = T \ S := by
  ext i
  constructor
  · intro hi
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hi
    have hm := a.property
    rcases Finset.mem_union.mp hm with hleft | hright
    · exact ((Finset.mem_filter.mp ha).2 hleft).elim
    · exact hright
  · intro hi
    have hn : i ∉ S \ T := fun h => (Finset.mem_sdiff.mp hi).2 (Finset.mem_sdiff.mp h).1
    exact Finset.mem_image.mpr ⟨⟨i, Finset.mem_union_right _ hi⟩,
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, hn⟩, rfl⟩

theorem activeConvertedGauss_eq_columnBlocks
    {ι : Type*} [DecidableEq ι] (p : ι → O) (hp : ∀ i, p i ≠ 0)
    [∀ i, (Ideal.span {p i}).IsMaximal]
    (hg : ∀ i, lambda ∉ Ideal.span {p i})
    (hprimary : ∀ i, lambda ^ 2 ∣ p i - 1) (S T : Finset ι) :
    activeConvertedGauss p hp hg S T =
      convertedColumnBlock p hp hg (S \ T) true *
        convertedColumnBlock p hp hg (T \ S) false *
          quadraticCrossPhase p hg (S \ T) (T \ S) := by
  rw [activeConvertedGauss_separated p hp hg hprimary S T]
  rw [convertedColumnBlock_image p hp hg Subtype.val Subtype.val_injective,
    convertedColumnBlock_image p hp hg Subtype.val Subtype.val_injective,
    quadraticCrossPhase_image p hg Subtype.val Subtype.val_injective,
    negative_active_image, positive_active_image]

theorem activeConvertedGauss_disjoint_mod_four
    {ι : Type*} [DecidableEq ι] (p : ι → O) (hp : ∀ i, p i ≠ 0)
    [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i, lambda ∉ Ideal.span {p i})
    (hchar : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
    (hprimary : ∀ i, lambda ^ 2 ∣ p i - 1) (S T : Finset ι) (hd : Disjoint S T) :
    activeConvertedGauss p hp hg S T =
      convertedColumnBlock p hp hg S true * convertedColumnBlock p hp hg T false *
        quadraticRayPair (residue (∏ i ∈ S, p i)) (residue (∏ i ∈ T, p i)) := by
  rw [activeConvertedGauss_eq_columnBlocks p hp hg hprimary S T,
    Finset.sdiff_eq_self_of_disjoint hd, Finset.sdiff_eq_self_of_disjoint hd.symm,
    quadraticCrossPhase_eq_rayPair p hp hcop hg hchar S T hd]

end MixedCrossSeparation

namespace FirstCauchyArithmetic

section
abbrev O := ActualEisensteinCubic.O
open ActualEisensteinCubic CoprimeMobiusExtension

def supportMobius {ι : Type*} (P : ι → Ideal O) (S : Finset ι) : ℂ :=
  (UniqueFactorizationMonoid.moebius (∏ i ∈ S, P i) : ℂ)

def supportConjugateSum {ι : Type*} [DecidableEq ι]
    (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
    (hg : ∀ i, lambda ∉ P i) (B : Finset ι) (C : Finset ι → ℂ) (h : O) : ℂ :=
  ∑ S ∈ B.powerset, supportMobius P S * C S * star (finiteSquarefreeRow P hg S h)

private theorem supportMobius_union {ι : Type*} [DecidableEq ι]
    (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
    (hprime : ∀ i, Prime (P i)) (hinj : Function.Injective P)
    (S T : Finset ι) (hd : Disjoint S T) :
    supportMobius P (S ∪ T) = supportMobius P S * supportMobius P T := by
  simp only [supportMobius, prime_product_moebius P hprime hinj,
    Finset.card_union_of_disjoint hd, pow_add]

theorem supportMobius_sq {ι : Type*} [DecidableEq ι]
    (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
    (hprime : ∀ i, Prime (P i)) (hinj : Function.Injective P) (S : Finset ι) :
    supportMobius P S * supportMobius P S = 1 := by
  rw [supportMobius, prime_product_moebius P hprime hinj, ← mul_pow]
  norm_num

theorem star_supportMobius {ι : Type*} (P : ι → Ideal O) (S : Finset ι) :
    star (supportMobius P S) = supportMobius P S := by
  simp [supportMobius]

private theorem finiteSquarefreeRow_union {ι : Type*} [DecidableEq ι]
    (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
    (hg : ∀ i, lambda ∉ P i) (S T : Finset ι) (hd : Disjoint S T) (h : O) :
    finiteSquarefreeRow P hg (S ∪ T) h =
      finiteSquarefreeRow P hg S h * finiteSquarefreeRow P hg T h := by
  exact Finset.prod_union hd

theorem coprime_pair_sum_reindexed
    {ι : Type*} [DecidableEq ι] (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
    (hprime : ∀ i, Prime (P i)) (hinj : Function.Injective P)
    (hg : ∀ i, lambda ∉ P i) (B : Finset ι) (C₁ C₂ : Finset ι → ℂ) (h : O) :
    (∑ S ∈ B.powerset, ∑ T ∈ B.powerset,
      if Disjoint S T then
        star (supportMobius P S * C₁ S * star (finiteSquarefreeRow P hg S h)) *
          (supportMobius P T * C₂ T * star (finiteSquarefreeRow P hg T h)) else 0) =
    ∑ D ∈ B.powerset, supportMobius P D * rowCoprimeMask P D h *
      star (supportConjugateSum P hg (B \ D) (fun U => C₁ (D ∪ U)) h) *
        supportConjugateSum P hg (B \ D) (fun V => C₂ (D ∪ V)) h := by
  rw [double_sum_disjoint_reindexed]
  apply Finset.sum_congr rfl
  intro D hD
  rw [← prime_product_moebius P hprime hinj D]
  change supportMobius P D * _ = _
  have ht (U V : Finset ι) (hU : U ∈ (B \ D).powerset) (hV : V ∈ (B \ D).powerset) :
      star (supportMobius P (D ∪ U) * C₁ (D ∪ U) *
        star (finiteSquarefreeRow P hg (D ∪ U) h)) *
      (supportMobius P (D ∪ V) * C₂ (D ∪ V) *
        star (finiteSquarefreeRow P hg (D ∪ V) h)) =
      rowCoprimeMask P D h *
        star (supportMobius P U * C₁ (D ∪ U) * star (finiteSquarefreeRow P hg U h)) *
          (supportMobius P V * C₂ (D ∪ V) * star (finiteSquarefreeRow P hg V h)) := by
    have hdU : Disjoint D U := Finset.disjoint_of_subset_right
      (Finset.mem_powerset.mp hU) disjoint_sdiff_self_right
    have hdV : Disjoint D V := Finset.disjoint_of_subset_right
      (Finset.mem_powerset.mp hV) disjoint_sdiff_self_right
    rw [supportMobius_union P hprime hinj D U hdU,
      supportMobius_union P hprime hinj D V hdV,
      finiteSquarefreeRow_union P hg D U hdU,
      finiteSquarefreeRow_union P hg D V hdV]
    simp only [star_mul, star_star, star_supportMobius]
    have hmu := supportMobius_sq P hprime hinj D
    have hrow := finiteSquarefreeRow_self_pair P hg D h
    calc
      _ = (supportMobius P D * supportMobius P D) *
          (star (finiteSquarefreeRow P hg D h) * finiteSquarefreeRow P hg D h) *
          (finiteSquarefreeRow P hg U h * star (C₁ (D ∪ U)) * supportMobius P U) *
          (supportMobius P V * C₂ (D ∪ V) * star (finiteSquarefreeRow P hg V h)) := by ring
      _ = _ := by rw [hmu, hrow]; ring
  have heq : (∑ U ∈ (B \ D).powerset, ∑ V ∈ (B \ D).powerset,
      star (supportMobius P (D ∪ U) * C₁ (D ∪ U) * star (finiteSquarefreeRow P hg (D ∪ U) h)) *
      (supportMobius P (D ∪ V) * C₂ (D ∪ V) * star (finiteSquarefreeRow P hg (D ∪ V) h))) =
    rowCoprimeMask P D h *
      star (supportConjugateSum P hg (B \ D) (fun U => C₁ (D ∪ U)) h) *
        supportConjugateSum P hg (B \ D) (fun V => C₂ (D ∪ V)) h := by
    simp only [supportConjugateSum, star_sum]
    rw [mul_assoc, Finset.sum_mul_sum]
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro U hU
    apply Finset.sum_congr rfl
    intro V hV
    simpa only [mul_assoc] using ht U V hU hV
  rw [heq]
  ring

theorem finite_phase_coprime_reindex
    {ι R : Type*} [DecidableEq ι] [Fintype R] [DecidableEq R]
    (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
    (hprime : ∀ i, Prime (P i)) (hinj : Function.Injective P)
    (hg : ∀ i, lambda ∉ P i) (B : Finset ι)
    (σ : Finset ι → R) (phase : R → R → ℂ) (C₁ C₂ : Finset ι → ℂ) (h : O) :
    (∑ S ∈ B.powerset, ∑ T ∈ B.powerset,
      if Disjoint S T then phase (σ S) (σ T) *
        star (supportMobius P S * C₁ S * star (finiteSquarefreeRow P hg S h)) *
          (supportMobius P T * C₂ T * star (finiteSquarefreeRow P hg T h)) else 0) =
    ∑ r : R × R, phase r.1 r.2 *
      ∑ D ∈ B.powerset, supportMobius P D * rowCoprimeMask P D h *
        star (supportConjugateSum P hg (B \ D)
          (fun U => if σ (D ∪ U) = r.1 then C₁ (D ∪ U) else 0) h) *
        supportConjugateSum P hg (B \ D)
          (fun V => if σ (D ∪ V) = r.2 then C₂ (D ∪ V) else 0) h := by
  let Z (r : R × R) (S T : Finset ι) : ℂ :=
    if Disjoint S T then
      star (supportMobius P S * (if σ S = r.1 then C₁ S else 0) *
        star (finiteSquarefreeRow P hg S h)) *
      (supportMobius P T * (if σ T = r.2 then C₂ T else 0) *
        star (finiteSquarefreeRow P hg T h)) else 0
  have ht (S T : Finset ι) :
      (if Disjoint S T then phase (σ S) (σ T) *
        star (supportMobius P S * C₁ S * star (finiteSquarefreeRow P hg S h)) *
          (supportMobius P T * C₂ T * star (finiteSquarefreeRow P hg T h)) else 0) =
      ∑ r : R × R, phase r.1 r.2 * Z r S T := by
    by_cases hd : Disjoint S T
    · simp only [Z, if_pos hd, Fintype.sum_prod_type]
      simp only [ mul_zero, ite_mul, zero_mul, apply_ite, star_zero]
      simp
      ring
    · simp [Z, hd]
  calc
    _ = ∑ S ∈ B.powerset, ∑ T ∈ B.powerset,
        ∑ r : R × R, phase r.1 r.2 * Z r S T := by
      apply Finset.sum_congr rfl
      intro S hS
      exact Finset.sum_congr rfl (fun T hT => ht S T)
    _ = ∑ r : R × R, phase r.1 r.2 *
        ∑ S ∈ B.powerset, ∑ T ∈ B.powerset, Z r S T := by
      simp only [Finset.mul_sum]
      calc
        _ = ∑ S ∈ B.powerset, ∑ r : R × R,
            ∑ T ∈ B.powerset, phase r.1 r.2 * Z r S T := by
          apply Finset.sum_congr rfl
          intro S hS
          exact Finset.sum_comm
        _ = _ := Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro r hr
      congr 1
      exact coprime_pair_sum_reindexed P hprime hinj hg B
        (fun S => if σ S = r.1 then C₁ S else 0)
        (fun T => if σ T = r.2 then C₂ T else 0) h

end
section

open ActualEisensteinCubic ConcreteTraceCRT FiniteGaussPhase MixedCrossSeparation RayFourExpansion

def supportRay {ι : Type*} (p : ι → O) (χ : RayCharacter) (S : Finset ι) : ℂ :=
  rayCharacter χ (∏ i ∈ S, p i)

private theorem supportRay_union {ι : Type*} [DecidableEq ι]
    (p : ι → O) (χ : RayCharacter) (S T : Finset ι) (hd : Disjoint S T) :
    supportRay p χ (S ∪ T) = supportRay p χ S * supportRay p χ T := by
  rw [supportRay, Finset.prod_union hd, rayCharacter_mul]
  rfl

theorem supportConjugateSum_ray_common
    {ι : Type*} [DecidableEq ι] (p : ι → O) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hg : ∀ i, lambda ∉ Ideal.span {p i}) (B D : Finset ι)
    (C : Finset ι → ℂ) (χ : RayCharacter) (h : O) :
    supportConjugateSum (fun i => Ideal.span {p i}) hg (B \ D)
      (fun U => supportRay p χ (D ∪ U) * C (D ∪ U)) h =
    supportRay p χ D * supportConjugateSum (fun i => Ideal.span {p i}) hg (B \ D)
      (fun U => supportRay p χ U * C (D ∪ U)) h := by
  rw [supportConjugateSum, supportConjugateSum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro U hU
  have hdU : Disjoint D U := Finset.disjoint_of_subset_right
    (Finset.mem_powerset.mp hU) disjoint_sdiff_self_right
  rw [supportRay_union p χ D U hdU]
  ring

theorem supportConjugateSum_star_ray_common
    {ι : Type*} [DecidableEq ι] (p : ι → O) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hg : ∀ i, lambda ∉ Ideal.span {p i}) (B D : Finset ι)
    (C : Finset ι → ℂ) (χ : RayCharacter) (h : O) :
    supportConjugateSum (fun i => Ideal.span {p i}) hg (B \ D)
      (fun U => star (supportRay p χ (D ∪ U)) * C (D ∪ U)) h =
    star (supportRay p χ D) * supportConjugateSum (fun i => Ideal.span {p i}) hg (B \ D)
      (fun U => star (supportRay p χ U) * C (D ∪ U)) h := by
  rw [supportConjugateSum, supportConjugateSum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro U hU
  have hdU : Disjoint D U := Finset.disjoint_of_subset_right
    (Finset.mem_powerset.mp hU) disjoint_sdiff_self_right
  rw [supportRay_union p χ D U hdU, star_mul]
  ring

theorem quadratic_phase_coprime_ray_reindex
    {ι : Type*} [DecidableEq ι] (p : ι → O) (hp : ∀ i, p i ≠ 0)
    [∀ i, (Ideal.span {p i}).IsMaximal]
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (hg : ∀ i, lambda ∉ Ideal.span {p i})
    (hchar : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
    (B : Finset ι) (C₁ C₂ : Finset ι → ℂ) (h : O) :
    let P : ι → Ideal O := fun i => Ideal.span {p i}
    (∑ S ∈ B.powerset, ∑ T ∈ B.powerset,
      if Disjoint S T then quadraticCrossPhase p hg S T *
        star (supportMobius P S * C₁ S * star (finiteSquarefreeRow P hg S h)) *
          (supportMobius P T * C₂ T * star (finiteSquarefreeRow P hg T h)) else 0) =
    ∑ r : RayCharacter × RayCharacter, crossCoeff r.1 r.2 *
      ∑ D ∈ B.powerset,
        (supportMobius P D * rowCoprimeMask P D h * supportRay p r.1 D * supportRay p r.2 D) *
        star (supportConjugateSum P hg (B \ D)
          (fun U => star (supportRay p r.1 U) * C₁ (D ∪ U)) h) *
        supportConjugateSum P hg (B \ D)
          (fun V => supportRay p r.2 V * C₂ (D ∪ V)) h := by
  dsimp only
  let P : ι → Ideal O := fun i => Ideal.span {p i}
  have hcop : Pairwise (Function.onFun IsCoprime P) := by
    intro i k hik
    exact Ideal.isCoprime_of_isMaximal (hinj.ne hik)
  have hprime (i : ι) : Prime (P i) :=
    Ideal.prime_of_isPrime (NeZero.ne (P i)) inferInstance
  let Z (r : RayCharacter × RayCharacter) (S T : Finset ι) : ℂ :=
    if Disjoint S T then
      star (supportMobius P S * (star (supportRay p r.1 S) * C₁ S) *
        star (finiteSquarefreeRow P hg S h)) *
      (supportMobius P T * (supportRay p r.2 T * C₂ T) *
        star (finiteSquarefreeRow P hg T h)) else 0
  have ht (S T : Finset ι) :
      (if Disjoint S T then quadraticCrossPhase p hg S T *
        star (supportMobius P S * C₁ S * star (finiteSquarefreeRow P hg S h)) *
          (supportMobius P T * C₂ T * star (finiteSquarefreeRow P hg T h)) else 0) =
      ∑ r : RayCharacter × RayCharacter, crossCoeff r.1 r.2 * Z r S T := by
    by_cases hd : Disjoint S T
    · rw [if_pos hd, quadraticCrossPhase_character_expansion p hp hcop hg hchar S T hd]
      simp only [Fintype.sum_prod_type, Z, if_pos hd, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro χ hχ
      apply Finset.sum_congr rfl
      intro η hη
      simp only [supportRay, star_mul, star_star]
      ring
    · simp [Z, hd]
  calc
    _ = ∑ S ∈ B.powerset, ∑ T ∈ B.powerset,
        ∑ r : RayCharacter × RayCharacter, crossCoeff r.1 r.2 * Z r S T := by
      apply Finset.sum_congr rfl
      intro S hS
      exact Finset.sum_congr rfl (fun T hT => ht S T)
    _ = ∑ r : RayCharacter × RayCharacter, crossCoeff r.1 r.2 *
        ∑ S ∈ B.powerset, ∑ T ∈ B.powerset, Z r S T := by
      simp only [Finset.mul_sum]
      calc
        _ = ∑ S ∈ B.powerset, ∑ r : RayCharacter × RayCharacter,
            ∑ T ∈ B.powerset, crossCoeff r.1 r.2 * Z r S T := by
          apply Finset.sum_congr rfl
          intro S hS
          exact Finset.sum_comm
        _ = _ := Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro r hr
      congr 1
      change (∑ S ∈ B.powerset, ∑ T ∈ B.powerset,
        if Disjoint S T then star (supportMobius P S *
          (star (supportRay p r.1 S) * C₁ S) * star (finiteSquarefreeRow P hg S h)) *
          (supportMobius P T * (supportRay p r.2 T * C₂ T) *
            star (finiteSquarefreeRow P hg T h)) else 0) = _
      rw [coprime_pair_sum_reindexed P hprime hinj hg B]
      apply Finset.sum_congr rfl
      intro D hD
      rw [supportConjugateSum_star_ray_common p hg B D C₁ r.1 h,
        supportConjugateSum_ray_common p hg B D C₂ r.2 h]
      simp only [star_mul, star_star]
      ring

end

open ActualEisensteinCubic ConcretePrimeRowBridge

private theorem family_prime {ι : Type*} (P : ι → Ideal O) [∀ i, (P i).IsMaximal] (i : ι) :
    Prime (P i) := Ideal.prime_of_isPrime (NeZero.ne (P i)) inferInstance

private theorem family_prod_ne_zero {ι : Type*}
    (P : ι → Ideal O) [∀ i, (P i).IsMaximal] (S : Finset ι) :
    (∏ i ∈ S, P i) ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun i _ => (family_prime P i).ne_zero)

theorem family_prime_dvd_product_iff {ι : Type*} [DecidableEq ι]
    (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
    (hinj : Function.Injective P) (S : Finset ι) (i : ι) :
    P i ∣ ∏ j ∈ S, P j ↔ i ∈ S := by
  constructor
  · intro h
    obtain ⟨j, hj, hd⟩ := ((family_prime P i).dvd_finsetProd_iff P).mp h
    have he : P i = P j := associated_iff_eq.mp
      ((family_prime P i).associated_of_dvd (family_prime P j) hd)
    exact hinj he ▸ hj
  · exact fun hi => Finset.dvd_prod_of_mem P hi

theorem family_product_injective {ι : Type*} [DecidableEq ι]
    (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
    (hinj : Function.Injective P) : Function.Injective (fun S : Finset ι => ∏ i ∈ S, P i) := by
  intro S T h
  change (∏ i ∈ S, P i) = (∏ i ∈ T, P i) at h
  ext i
  rw [← family_prime_dvd_product_iff P hinj S i, h, family_prime_dvd_product_iff P hinj T i]

def supportIdealFamily {ι : Type*} [DecidableEq ι]
    (P : ι → Ideal O) (B : Finset ι) : Finset (Ideal O) :=
  B.powerset.image (fun S => ∏ i ∈ S, P i)

theorem supportIdealFamily_pos {ι : Type*} [DecidableEq ι]
    (P : ι → Ideal O) [∀ i, (P i).IsMaximal] (B : Finset ι) :
    ∀ I ∈ supportIdealFamily P B, I ≠ ⊥ := by
  intro I hI
  obtain ⟨S, hS, rfl⟩ := Finset.mem_image.mp hI
  exact family_prod_ne_zero P S

private theorem factor_family_product_iff {ι : Type*} [DecidableEq ι]
    (P : ι → Ideal O) [∀ i, (P i).IsMaximal] (S : Finset ι) (Q : Ideal O) :
    Q ∈ UniqueFactorizationMonoid.normalizedFactors (∏ i ∈ S, P i) ↔
      ∃ i ∈ S, Q = P i := by
  rw [UniqueFactorizationMonoid.mem_normalizedFactors_iff (family_prod_ne_zero P S)]
  constructor
  · rintro ⟨hQ, hd⟩
    obtain ⟨i, hi, hdiv⟩ := (hQ.dvd_finsetProd_iff P).mp hd
    exact ⟨i, hi, associated_iff_eq.mp (hQ.associated_of_dvd (family_prime P i) hdiv)⟩
  · rintro ⟨i, hi, rfl⟩
    exact ⟨family_prime P i, Finset.dvd_prod_of_mem P hi⟩

theorem supportIdealFamily_good {ι : Type*} [DecidableEq ι]
    (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
    (hg : ∀ i, lambda ∉ P i) (B : Finset ι) :
    ∀ I ∈ supportIdealFamily P B,
      ∀ Q ∈ UniqueFactorizationMonoid.normalizedFactors I, goodLambda ∉ Q := by
  intro I hI Q hQ
  obtain ⟨S, hS, rfl⟩ := Finset.mem_image.mp hI
  obtain ⟨i, hi, rfl⟩ := (factor_family_product_iff P S Q).mp hQ
  exact hg i

def recoveredSupport {ι : Type*} [DecidableEq ι]
    (P : ι → Ideal O) (B : Finset ι) (I : Ideal O) : Finset ι :=
  B.filter (fun i => P i ∣ I)

theorem recoveredSupport_product {ι : Type*} [DecidableEq ι]
    (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
    (hinj : Function.Injective P) (B S : Finset ι) (hS : S ⊆ B) :
    recoveredSupport P B (∏ i ∈ S, P i) = S := by
  ext i
  simp only [recoveredSupport, Finset.mem_filter, family_prime_dvd_product_iff P hinj S i]
  exact and_iff_right_of_imp (fun hi => hS hi)

theorem idealSexticRow_support_product {ι : Type*} [DecidableEq ι]
    (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
    (hinj : Function.Injective P) (hg : ∀ i, lambda ∉ P i)
    (B S : Finset ι) (hS : S ⊆ B) (h : O) :
    idealSexticRow (supportIdealFamily P B) (supportIdealFamily_pos P B)
      (supportIdealFamily_good P hg B) (∏ i ∈ S, P i) h =
      finiteSquarefreeRow P hg S h := by
  let F := supportIdealFamily P B
  have hIF : (∏ i ∈ S, P i) ∈ F :=
    Finset.mem_image.mpr ⟨S, Finset.mem_powerset.mpr hS, rfl⟩
  let idx (i : ι) (hi : i ∈ S) : primePool F :=
    ⟨P i, mem_primePool_iff.mpr ⟨∏ j ∈ S, P j, hIF,
      (factor_family_product_iff P S (P i)).mpr ⟨i, hi, rfl⟩⟩⟩
  symm
  unfold idealSexticRow finiteSquarefreeRow
  apply Finset.prod_bij idx
  · intro i hi
    exact (mem_idealSupport_iff F _ (idx i hi)).mpr
      ((factor_family_product_iff P S (P i)).mpr ⟨i, hi, rfl⟩)
  · intro i hi j hj hij
    exact hinj (congrArg Subtype.val hij)
  · intro Q hQ
    have hm := (mem_idealSupport_iff F _ Q).mp hQ
    obtain ⟨i, hi, he⟩ := (factor_family_product_iff P S Q.val).mp hm
    exact ⟨i, hi, Subtype.ext he.symm⟩
  · intro i hi
    rfl

theorem supportConjugateSum_eq_conjugateIdealRowSum
    {ι : Type*} [DecidableEq ι] (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
    (hinj : Function.Injective P) (hg : ∀ i, lambda ∉ P i)
    (B : Finset ι) (C : Finset ι → ℂ) (h : O) :
    supportConjugateSum P hg B C h =
      conjugateIdealRowSum (supportIdealFamily P B) (supportIdealFamily_pos P B)
        (supportIdealFamily_good P hg B) (fun I => C (recoveredSupport P B I)) h := by
  let f : Ideal O → ℂ := fun I =>
    mobiusIdealColumn (fun I => C (recoveredSupport P B I)) I *
      star (idealSexticRow (supportIdealFamily P B) (supportIdealFamily_pos P B)
        (supportIdealFamily_good P hg B) I h)
  change supportConjugateSum P hg B C h =
    ∑ I ∈ B.powerset.image (fun S => ∏ i ∈ S, P i), f I
  rw [Finset.sum_image (fun S hS T hT h => family_product_injective P hinj h)]
  unfold supportConjugateSum
  apply Finset.sum_congr rfl
  intro S hS
  have hSB := Finset.mem_powerset.mp hS
  dsimp only [f]
  rw [idealSexticRow_support_product P hinj hg B S hSB h]
  simp only [mobiusIdealColumn, supportMobius, recoveredSupport_product P hinj B S hSB]

theorem quadratic_phase_reindex_to_ideal_rows
    {ι : Type*} [DecidableEq ι] (p : ι → O) (hp : ∀ i, p i ≠ 0)
    [∀ i, (Ideal.span {p i}).IsMaximal]
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (hg : ∀ i, lambda ∉ Ideal.span {p i})
    (hchar : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
    (B : Finset ι) (C₁ C₂ : Finset ι → ℂ) (h : O) :
    let P : ι → Ideal O := fun i => Ideal.span {p i}
    (∑ S ∈ B.powerset, ∑ T ∈ B.powerset,
      if Disjoint S T then MixedCrossSeparation.quadraticCrossPhase p hg S T *
        star (supportMobius P S * C₁ S * star (finiteSquarefreeRow P hg S h)) *
          (supportMobius P T * C₂ T * star (finiteSquarefreeRow P hg T h)) else 0) =
    ∑ r : RayFourExpansion.RayCharacter × RayFourExpansion.RayCharacter,
      RayFourExpansion.crossCoeff r.1 r.2 *
      ∑ D ∈ B.powerset,
        (supportMobius P D * rowCoprimeMask P D h * supportRay p r.1 D * supportRay p r.2 D) *
        star (conjugateIdealRowSum (supportIdealFamily P (B \ D))
          (supportIdealFamily_pos P (B \ D)) (supportIdealFamily_good P hg (B \ D))
          (fun I => star (supportRay p r.1 (recoveredSupport P (B \ D) I)) *
            C₁ (D ∪ recoveredSupport P (B \ D) I)) h) *
        conjugateIdealRowSum (supportIdealFamily P (B \ D))
          (supportIdealFamily_pos P (B \ D)) (supportIdealFamily_good P hg (B \ D))
          (fun I => supportRay p r.2 (recoveredSupport P (B \ D) I) *
            C₂ (D ∪ recoveredSupport P (B \ D) I)) h := by
  dsimp only
  rw [quadratic_phase_coprime_ray_reindex p hp hinj hg hchar B C₁ C₂ h]
  apply Finset.sum_congr rfl
  intro r hr
  congr 1
  apply Finset.sum_congr rfl
  intro D hD
  rw [supportConjugateSum_eq_conjugateIdealRowSum (fun i => Ideal.span {p i}) hinj hg,
    supportConjugateSum_eq_conjugateIdealRowSum (fun i => Ideal.span {p i}) hinj hg]

end FirstCauchyArithmetic

end

end OAI

end


