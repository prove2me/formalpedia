-- Prove2me | Definitions.Def_PNT_ZeroFree_433_0047
-- name    : PNT_ZeroFree_433_0047
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-10T15:00:51.960804+00:00
-- url     : https://prove2.me/theorems/4a1097fe-5ca7-4f19-a61d-a1a7ae3ce1d9
-- title:
--   Zero-free region foundations: QuadraticSieve.CrossSeparation [0047]
-- statement:
--   Definitions and proved supporting lemmas from the following source modules:
--
--   - OAI.NumberTheory.DirichletL.QuadraticSieve.CrossSeparation
--
--   These declarations form part of the analytic and arithmetic foundations of the Dirichlet L-function nonvanishing argument in the half-plane Re(s) > 7/8. The original namespaces and hypotheses are retained. The code is ported to Lean 4.33.1 and the pinned Mathlib environment; every included lemma has a complete proof.
-- source:
--   https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/QuadraticSieve/CrossSeparation.lean#L74-L634

import Definitions.Def_PNT_ZeroFree_433_0045
import Definitions.Def_PNT_ZeroFree_433_0046

/- Supporting source modules for the zero-free-region proof.
Ported and checked against Lean 4.33.1 / Mathlib 0df444a.
Original source attribution:
https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/QuadraticSieve/CrossSeparation.lean#L74-L634
-/

set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

-- Source module: OAI.NumberTheory.DirichletL.QuadraticSieve.CrossSeparation
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

namespace MixedCrossSeparation

abbrev O := ActualEisensteinCubic.O
open ActualEisensteinCubic ConcreteTraceCRT FiniteGaussPhase MixedGaussConversion

private theorem ordered_cross_partition {ι : Type*} [Fintype ι] [DecidableEq ι]
    (x : ι → ι → ℂ) (l : ι → ℂ) (A B : Finset ι)
    (hd : Disjoint A B) (hu : A ∪ B = Finset.univ) :
    (∏ i, ((∏ k ∈ Finset.univ.erase i, x i k ^ (if i ∈ A then 5 else 1)) * l i)) =
      (∏ i ∈ A, (∏ k ∈ A.erase i, x i k ^ 5) * l i) *
      (∏ i ∈ B, (∏ k ∈ B.erase i, x i k) * l i) *
      (∏ i ∈ A, ∏ k ∈ B, x i k ^ 5 * x k i) := by
  have hA (i : ι) (hi : i ∈ A) :
      (∏ k ∈ Finset.univ.erase i, x i k ^ (if i ∈ A then 5 else 1)) =
        (∏ k ∈ A.erase i, x i k ^ 5) * (∏ k ∈ B, x i k ^ 5) := by
    have hn : i ∉ B := fun hb => Finset.disjoint_left.mp hd hi hb
    have he : Finset.univ.erase i = A.erase i ∪ B := by
      rw [← hu]
      ext k
      by_cases hk : k = i
      · subst k; simp [hn]
      · simp [hk]
    rw [he, if_pos hi, Finset.prod_union (hd.mono_left (Finset.erase_subset _ _))]
  have hB (i : ι) (hi : i ∈ B) :
      (∏ k ∈ Finset.univ.erase i, x i k ^ (if i ∈ A then 5 else 1)) =
        (∏ k ∈ B.erase i, x i k) * (∏ k ∈ A, x i k) := by
    have hn : i ∉ A := fun ha => Finset.disjoint_left.mp hd ha hi
    have he : Finset.univ.erase i = B.erase i ∪ A := by
      rw [← hu]
      ext k
      by_cases hk : k = i
      · subst k; simp [hn]
      · simp [hk, or_comm]
    rw [he, if_neg hn, Finset.prod_union (hd.symm.mono_left (Finset.erase_subset _ _))]
    simp only [pow_one]
  have hpA : (∏ i ∈ A, ((∏ k ∈ Finset.univ.erase i,
      x i k ^ (if i ∈ A then 5 else 1)) * l i)) =
      (∏ i ∈ A, (∏ k ∈ A.erase i, x i k ^ 5) * l i) *
        (∏ i ∈ A, ∏ k ∈ B, x i k ^ 5) := by
    rw [← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro i hi
    rw [hA i hi]
    ring
  have hpB : (∏ i ∈ B, ((∏ k ∈ Finset.univ.erase i,
      x i k ^ (if i ∈ A then 5 else 1)) * l i)) =
      (∏ i ∈ B, (∏ k ∈ B.erase i, x i k) * l i) *
        (∏ i ∈ B, ∏ k ∈ A, x i k) := by
    rw [← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro i hi
    rw [hB i hi]
    ring
  calc
    _ = (∏ i ∈ A, ((∏ k ∈ Finset.univ.erase i,
            x i k ^ (if i ∈ A then 5 else 1)) * l i)) *
        (∏ i ∈ B, ((∏ k ∈ Finset.univ.erase i,
            x i k ^ (if i ∈ A then 5 else 1)) * l i)) := by
      rw [← Finset.prod_union hd, hu]
    _ = _ := by
      rw [hpA, hpB]
      rw [Finset.prod_comm (s := B) (t := A)]
      simp only [Finset.prod_mul_distrib]
      ring

def crossSymbol {ι : Type*} (p : ι → O) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hg : ∀ i, lambda ∉ Ideal.span {p i}) (i k : ι) : ℂ :=
  canonicalSextic (Ideal.span {p i}) (hg i)
    (Ideal.Quotient.mk (Ideal.span {p i}) (p k))

theorem mixed_cross_eq_quadratic {ι : Type*}
    (p : ι → O) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hg : ∀ i, lambda ∉ Ideal.span {p i}) (i k : ι)
    (hpi : lambda ^ 2 ∣ p i - 1) (hpk : lambda ^ 2 ∣ p k - 1) :
    crossSymbol p hg i k ^ 5 * crossSymbol p hg k i =
      crossSymbol p hg i k ^ 3 * crossSymbol p hg k i ^ 3 := by
  have hs : crossSymbol p hg i k ^ 2 = crossSymbol p hg k i ^ 2 :=
    canonicalSextic_sq_reciprocity_primary
      (Ideal.span {p i}) (Ideal.span {p k}) (hg i) (hg k)
      (p i) (p k) rfl rfl hpi hpk
  calc
    _ = crossSymbol p hg i k ^ 3 * crossSymbol p hg i k ^ 2 * crossSymbol p hg k i := by ring
    _ = _ := by rw [hs]; ring

def convertedColumnBlock {ι : Type*} [DecidableEq ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hg : ∀ i, lambda ∉ Ideal.span {p i}) (S : Finset ι) (inverse : Bool) : ℂ :=
  ∏ i ∈ S, (∏ k ∈ S.erase i, crossSymbol p hg i k ^ (if inverse then 5 else 1)) *
    convertedLocal (p i) (hp i) (hg i) inverse

def quadraticCrossPhase {ι : Type*}
    (p : ι → O) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hg : ∀ i, lambda ∉ Ideal.span {p i}) (A B : Finset ι) : ℂ :=
  ∏ i ∈ A, ∏ k ∈ B, crossSymbol p hg i k ^ 3 * crossSymbol p hg k i ^ 3

theorem mixed_converted_gauss_separation
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hg : ∀ i, lambda ∉ Ideal.span {p i}) (inverse : ι → Bool)
    (hprimary : ∀ i, lambda ^ 2 ∣ p i - 1) :
    (∏ i, ∏ k ∈ Finset.univ.erase i,
      (canonicalSextic (Ideal.span {p i}) (hg i) ^ (if inverse i then 5 else 1))
        (Ideal.Quotient.mk (Ideal.span {p i}) (p k))) *
      (∏ i, convertedLocal (p i) (hp i) (hg i) (inverse i)) =
    convertedColumnBlock p hp hg (Finset.univ.filter fun i => inverse i = true) true *
      convertedColumnBlock p hp hg (Finset.univ.filter fun i => inverse i = false) false *
      quadraticCrossPhase p hg (Finset.univ.filter fun i => inverse i = true)
        (Finset.univ.filter fun i => inverse i = false) := by
  let A := Finset.univ.filter (fun i => inverse i = true)
  let B := Finset.univ.filter (fun i => inverse i = false)
  have hA (i : ι) : i ∈ A ↔ inverse i = true := by simp [A]
  have hB (i : ι) : i ∈ B ↔ inverse i = false := by simp [B]
  have hd : Disjoint A B := by
    apply Finset.disjoint_left.mpr
    intro i hi hj
    have ht := (hA i).mp hi
    have hf := (hB i).mp hj
    rw [ht] at hf
    contradiction
  have hu : A ∪ B = Finset.univ := by
    ext i
    simp only [Finset.mem_union, hA, hB, Finset.mem_univ, iff_true]
    cases inverse i <;> simp
  have hpow (i k : ι) :
      (canonicalSextic (Ideal.span {p i}) (hg i) ^ (if inverse i then 5 else 1))
        (Ideal.Quotient.mk (Ideal.span {p i}) (p k)) =
      crossSymbol p hg i k ^ (if i ∈ A then 5 else 1) := by
    rw [MulChar.pow_apply' _ (by cases inverse i <;> decide)]
    simp only [hA,  crossSymbol]
  simp_rw [hpow]
  rw [← Finset.prod_mul_distrib,
    ordered_cross_partition (crossSymbol p hg)
      (fun i => convertedLocal (p i) (hp i) (hg i) (inverse i)) A B hd hu]
  have hn : (∏ i ∈ A, (∏ k ∈ A.erase i, crossSymbol p hg i k ^ 5) *
      convertedLocal (p i) (hp i) (hg i) (inverse i)) = convertedColumnBlock p hp hg A true := by
    apply Finset.prod_congr rfl
    intro i hi
    simp only [(hA i).mp hi,   ↓reduceIte]
  have hp' : (∏ i ∈ B, (∏ k ∈ B.erase i, crossSymbol p hg i k) *
      convertedLocal (p i) (hp i) (hg i) (inverse i)) = convertedColumnBlock p hp hg B false := by
    unfold convertedColumnBlock
    simp only [Bool.false_eq_true, ↓reduceIte, pow_one]
    apply Finset.prod_congr rfl
    intro i hi
    rw [(hB i).mp hi]
  have hc : (∏ i ∈ A, ∏ k ∈ B, crossSymbol p hg i k ^ 5 * crossSymbol p hg k i) =
      quadraticCrossPhase p hg A B := by
    apply Finset.prod_congr rfl
    intro i hi
    apply Finset.prod_congr rfl
    intro k hk
    exact mixed_cross_eq_quadratic p hg i k (hprimary i) (hprimary k)
  rw [hn, hp', hc]

theorem quadraticCrossPhase_sq
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (p : ι → O) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i, lambda ∉ Ideal.span {p i}) (A B : Finset ι) (hd : Disjoint A B) :
    quadraticCrossPhase p hg A B ^ 2 = 1 := by
  have hpow (i k : ι) (hik : i ≠ k) : crossSymbol p hg i k ^ 6 = 1 := by
    simpa only [crossSymbol, map_pow, if_neg (prime_generator_not_mem_other p hcop i k hik)]
      using canonicalSextic_sixth_power_mask (Ideal.span {p i}) (hg i) (p k)
  unfold quadraticCrossPhase
  rw [← Finset.prod_pow]
  apply Finset.prod_eq_one
  intro i hi
  rw [← Finset.prod_pow]
  apply Finset.prod_eq_one
  intro k hk
  have hik : i ≠ k := by
    intro h
    subst k
    exact Finset.disjoint_left.mp hd hi hk
  rw [mul_pow, ← pow_mul, ← pow_mul]
  norm_num only [show 3 * 2 = 6 by decide, hpow i k hik, hpow k i hik.symm, one_mul]

theorem quadraticCrossPhase_eq_one_or_neg_one
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (p : ι → O) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i, lambda ∉ Ideal.span {p i}) (A B : Finset ι) (hd : Disjoint A B) :
    quadraticCrossPhase p hg A B = 1 ∨ quadraticCrossPhase p hg A B = -1 := by
  exact sq_eq_one_iff.mp (quadraticCrossPhase_sq p hcop hg A B hd)

theorem activeConvertedGauss_separated
    {ι : Type*} [DecidableEq ι] (p : ι → O) (hp : ∀ i, p i ≠ 0)
    [∀ i, (Ideal.span {p i}).IsMaximal]
    (hg : ∀ i, lambda ∉ Ideal.span {p i})
    (hprimary : ∀ i, lambda ^ 2 ∣ p i - 1) (S T : Finset ι) :
    let q : activeSupport S T → O := fun i => p i.val
    let hq : ∀ i, q i ≠ 0 := fun i => hp i.val
    let hgood : ∀ i, lambda ∉ Ideal.span {q i} := fun i => hg i.val
    let A : Finset (activeSupport S T) := Finset.univ.filter fun i => i.val ∈ S \ T
    let B : Finset (activeSupport S T) := Finset.univ.filter fun i => i.val ∉ S \ T
    GaussGeneratorTransport.activeConvertedGauss p hp hg S T =
      convertedColumnBlock q hq hgood A true * convertedColumnBlock q hq hgood B false *
        quadraticCrossPhase q hgood A B := by
  dsimp only
  have h := mixed_converted_gauss_separation (fun i : activeSupport S T => p i.val)
    (fun i => hp i.val) (fun i => hg i.val) (fun i => decide (i.val ∈ S \ T))
    (fun i => hprimary i.val)
  simp only [GaussGeneratorTransport.activeConvertedGauss, activeExponent,
    decide_eq_true_eq, decide_eq_false_iff_not] at h ⊢
  convert! h using 1 ; congr 2
  funext i
  apply Finset.prod_congr
  · ext k; simp
  · intro k hk; rfl

theorem active_dual_row_factorization
    {ι : Type*} [DecidableEq ι] (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
    (hg : ∀ i, lambda ∉ P i) (S T : Finset ι) (d h : O) :
    let row := finiteSexticRow (activePrimes P S T) (fun i => hg i.val)
      (activeExponent S T)
    row d * star (row h) =
      star (finiteSquarefreeRow P hg (S \ T) d *
        star (finiteSquarefreeRow P hg (S \ T) h)) *
      (finiteSquarefreeRow P hg (T \ S) d *
        star (finiteSquarefreeRow P hg (T \ S) h)) := by
  dsimp only
  rw [finiteSexticRow_activeSupport, finiteSexticRow_activeSupport]
  simp only [star_mul, star_star]
  ring

open ActualEisensteinCubic ConcreteTraceCRT FiniteGaussPhase MixedGaussConversion
open QuadraticGaussRay ActualEisensteinCoordinates

private theorem prod_subtype_erase {ι M : Type*} [DecidableEq ι] [CommMonoid M]
    (A : Finset ι) (i : A) (f : ι → M) :
    (∏ k ∈ (Finset.univ : Finset A).erase i, f k.val) = ∏ k ∈ A.erase i.val, f k := by
  apply Finset.prod_bij (fun k _ => k.val)
  · intro k hk
    apply Finset.mem_erase.mpr
    refine ⟨?_, k.property⟩
    exact fun h => (Finset.mem_erase.mp hk).1 (Subtype.ext h)
  · intro a ha b hb h
    exact Subtype.ext h
  · intro k hk
    refine ⟨⟨k, (Finset.mem_erase.mp hk).2⟩, ?_, rfl⟩
    apply Finset.mem_erase.mpr
    exact ⟨fun h => (Finset.mem_erase.mp hk).1 (congrArg Subtype.val h), Finset.mem_univ _⟩
  · intro a ha
    rfl

private theorem restricted_prime_coprime {ι : Type*} (p : ι → O)
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (A : Finset ι) :
    Pairwise (Function.onFun IsCoprime (fun i : A => Ideal.span {p i.val})) := by
  intro i k hik
  exact hcop (fun h => hik (Subtype.ext h))

def quadraticBlock {ι : Type*} [DecidableEq ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hg : ∀ i, lambda ∉ Ideal.span {p i}) (A : Finset ι) : ℂ :=
  ∏ i ∈ A, (∏ k ∈ A.erase i, crossSymbol p hg i k ^ 3) *
    localGauss (p i) (hp i) (hg i) 3

theorem quadraticBlock_eq_productGauss
    {ι : Type*} [DecidableEq ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i, lambda ∉ Ideal.span {p i}) (A : Finset ι) :
    quadraticBlock p hp hg A =
      canonicalProductGauss (fun i : A => p i.val) (fun i => hp i.val)
        (restricted_prime_coprime p hcop A) (fun i => hg i.val)
        (fun _ => 3) := by
  rw [canonicalProductGauss_cross_factors, ← Finset.prod_mul_distrib]
  unfold quadraticBlock
  rw [← Finset.prod_coe_sort A]
  apply Finset.prod_congr rfl
  intro i hi
  congr 1
  rw [← prod_subtype_erase A i (fun k => crossSymbol p hg i.val k ^ 3)]
  apply Finset.prod_congr
  · ext k; simp
  · intro k hk
    exact (MulChar.pow_apply' _ (by decide : (3 : ℕ) ≠ 0) _).symm

theorem quadraticBlock_eq_rayValue
    {ι : Type*} [DecidableEq ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i, lambda ∉ Ideal.span {p i})
    (hchar : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2) (A : Finset ι) :
    quadraticBlock p hp hg A = quadraticRayValue (residue (∏ i ∈ A, p i)) := by
  rw [quadraticBlock_eq_productGauss p hp hcop hg A,
    canonicalProductGauss_three_eq_rayValue (fun i : A => p i.val) (fun i => hp i.val)
      (restricted_prime_coprime p hcop A) (fun i => hg i.val)
      (fun i => hchar i.val), Finset.prod_coe_sort]

theorem quadraticBlock_union
    {ι : Type*} [DecidableEq ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hg : ∀ i, lambda ∉ Ideal.span {p i}) (A B : Finset ι) (hd : Disjoint A B) :
    quadraticBlock p hp hg (A ∪ B) = quadraticBlock p hp hg A *
      quadraticBlock p hp hg B * quadraticCrossPhase p hg A B := by
  let x := crossSymbol p hg
  let l := fun i => localGauss (p i) (hp i) (hg i) 3
  have hA (i : ι) (hi : i ∈ A) :
      (∏ k ∈ (A ∪ B).erase i, x i k ^ 3) =
        (∏ k ∈ A.erase i, x i k ^ 3) * (∏ k ∈ B, x i k ^ 3) := by
    have hn : i ∉ B := fun hb => Finset.disjoint_left.mp hd hi hb
    have he : (A ∪ B).erase i = A.erase i ∪ B := by
      ext k
      by_cases hk : k = i
      · subst k; simp [hn]
      · simp [hk]
    rw [he, Finset.prod_union (hd.mono_left (Finset.erase_subset _ _))]
  have hB (i : ι) (hi : i ∈ B) :
      (∏ k ∈ (A ∪ B).erase i, x i k ^ 3) =
        (∏ k ∈ B.erase i, x i k ^ 3) * (∏ k ∈ A, x i k ^ 3) := by
    have hn : i ∉ A := fun ha => Finset.disjoint_left.mp hd ha hi
    have he : (A ∪ B).erase i = B.erase i ∪ A := by
      ext k
      by_cases hk : k = i
      · subst k; simp [hn]
      · simp [hk, or_comm]
    rw [he, Finset.prod_union (hd.symm.mono_left (Finset.erase_subset _ _))]
  have hpA : (∏ i ∈ A, ((∏ k ∈ (A ∪ B).erase i, x i k ^ 3) * l i)) =
      (∏ i ∈ A, (∏ k ∈ A.erase i, x i k ^ 3) * l i) *
        (∏ i ∈ A, ∏ k ∈ B, x i k ^ 3) := by
    rw [← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro i hi
    rw [hA i hi]
    ring
  have hpB : (∏ i ∈ B, ((∏ k ∈ (A ∪ B).erase i, x i k ^ 3) * l i)) =
      (∏ i ∈ B, (∏ k ∈ B.erase i, x i k ^ 3) * l i) *
        (∏ i ∈ B, ∏ k ∈ A, x i k ^ 3) := by
    rw [← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro i hi
    rw [hB i hi]
    ring
  change (∏ i ∈ A ∪ B, ((∏ k ∈ (A ∪ B).erase i, x i k ^ 3) * l i)) = _
  rw [Finset.prod_union hd, hpA, hpB, Finset.prod_comm (s := B) (t := A)]
  unfold quadraticBlock quadraticCrossPhase
  simp only [Finset.prod_mul_distrib]
  dsimp only [x, l]
  ring

theorem norm_quadraticBlock
    {ι : Type*} [DecidableEq ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i, lambda ∉ Ideal.span {p i})
    (hchar : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2) (A : Finset ι) :
    ‖quadraticBlock p hp hg A‖ = 1 := by
  rw [quadraticBlock_eq_productGauss p hp hcop hg A]
  exact norm_canonicalProductGauss (fun i : A => p i.val) (fun i => hp i.val)
    (restricted_prime_coprime p hcop A) (fun i => hg i.val)
    (fun i => hchar i.val) (fun _ => 3) (fun _ => by decide) (fun _ => by decide)

def quadraticRayPair (a b : EisensteinEPrimaryPhase.Coord) : ℂ :=
  quadraticRayValue (EisensteinEPrimaryPhase.mul a b) /
    (quadraticRayValue a * quadraticRayValue b)

theorem quadraticCrossPhase_eq_rayPair
    {ι : Type*} [DecidableEq ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i, lambda ∉ Ideal.span {p i})
    (hchar : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
    (A B : Finset ι) (hd : Disjoint A B) :
    quadraticCrossPhase p hg A B =
      quadraticRayPair (residue (∏ i ∈ A, p i)) (residue (∏ i ∈ B, p i)) := by
  have hA0 : quadraticBlock p hp hg A ≠ 0 := by
    intro hz
    have hn := norm_quadraticBlock p hp hcop hg hchar A
    rw [hz, norm_zero] at hn
    exact zero_ne_one hn
  have hB0 : quadraticBlock p hp hg B ≠ 0 := by
    intro hz
    have hn := norm_quadraticBlock p hp hcop hg hchar B
    rw [hz, norm_zero] at hn
    exact zero_ne_one hn
  have h := quadraticBlock_union p hp hg A B hd
  have hdiv : quadraticCrossPhase p hg A B = quadraticBlock p hp hg (A ∪ B) /
      (quadraticBlock p hp hg A * quadraticBlock p hp hg B) := by
    apply (eq_div_iff (mul_ne_zero hA0 hB0)).mpr
    rw [h]
    ring
  rw [hdiv, quadraticBlock_eq_rayValue p hp hcop hg hchar (A ∪ B),
    quadraticBlock_eq_rayValue p hp hcop hg hchar A,
    quadraticBlock_eq_rayValue p hp hcop hg hchar B, Finset.prod_union hd,
    residue_mul]
  rfl

theorem mixed_converted_gauss_separation_mod_four
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i, lambda ∉ Ideal.span {p i})
    (hchar : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
    (inverse : ι → Bool) (hprimary : ∀ i, lambda ^ 2 ∣ p i - 1) :
    (∏ i, ∏ k ∈ Finset.univ.erase i,
      (canonicalSextic (Ideal.span {p i}) (hg i) ^ (if inverse i then 5 else 1))
        (Ideal.Quotient.mk (Ideal.span {p i}) (p k))) *
      (∏ i, convertedLocal (p i) (hp i) (hg i) (inverse i)) =
    convertedColumnBlock p hp hg (Finset.univ.filter fun i => inverse i = true) true *
      convertedColumnBlock p hp hg (Finset.univ.filter fun i => inverse i = false) false *
      quadraticRayPair
        (residue (∏ i ∈ Finset.univ.filter (fun i => inverse i = true), p i))
        (residue (∏ i ∈ Finset.univ.filter (fun i => inverse i = false), p i)) := by
  rw [mixed_converted_gauss_separation p hp hg inverse hprimary]
  congr 1
  apply quadraticCrossPhase_eq_rayPair p hp hcop hg hchar
  apply Finset.disjoint_left.mpr
  intro i hi hj
  have ht := (Finset.mem_filter.mp hi).2
  have hf := (Finset.mem_filter.mp hj).2
  rw [ht] at hf
  contradiction

end MixedCrossSeparation

open scoped BigOperators Classical

namespace CoprimeMobiusExtension
abbrev O := ActualEisensteinCubic.O

theorem sum_subset_sign {ι : Type*} [DecidableEq ι] (S : Finset ι) :
    (∑ D ∈ S.powerset, (-1 : ℂ) ^ D.card) = if S = ∅ then 1 else 0 := by
  have hp := Finset.prod_sub (fun _ : ι => (1 : ℂ)) (fun _ => 1) S
  by_cases hS : S = ∅
  · simp [hS]
  · have hc : S.card ≠ 0 := Finset.card_ne_zero.mpr (Finset.nonempty_iff_ne_empty.mpr hS)
    simpa [hS, hc] using hp.symm

theorem disjoint_indicator_expansion {ι : Type*} [DecidableEq ι]
    (B S T : Finset ι) (hS : S ⊆ B) (_hT : T ⊆ B) :
    (if Disjoint S T then (1 : ℂ) else 0) =
      ∑ D ∈ B.powerset, if D ⊆ S ∧ D ⊆ T then (-1 : ℂ) ^ D.card else 0 := by
  have hsub : (S ∩ T).powerset ⊆ B.powerset :=
    Finset.powerset_mono.mpr (Finset.inter_subset_left.trans hS)
  have heq : (∑ D ∈ B.powerset, if D ⊆ S ∧ D ⊆ T then (-1 : ℂ) ^ D.card else 0) =
      ∑ D ∈ (S ∩ T).powerset, (-1 : ℂ) ^ D.card := by
    calc
      _ = ∑ D ∈ (S ∩ T).powerset,
            if D ⊆ S ∧ D ⊆ T then (-1 : ℂ) ^ D.card else 0 := by
        symm
        apply Finset.sum_subset hsub
        intro D hD hnot
        have hn : ¬(D ⊆ S ∧ D ⊆ T) := by
          simpa only [Finset.mem_powerset, Finset.subset_inter_iff] using hnot
        simp [hn]
      _ = _ := by
        apply Finset.sum_congr rfl
        intro D hD
        have hh : D ⊆ S ∧ D ⊆ T := by
          simpa only [Finset.mem_powerset, Finset.subset_inter_iff] using hD
        simp [hh]
  rw [heq, sum_subset_sign]
  simp only [Finset.disjoint_iff_inter_eq_empty]

theorem double_sum_disjoint_expansion {ι : Type*} [DecidableEq ι]
    (B : Finset ι) (Z : Finset ι → Finset ι → ℂ) :
    (∑ S ∈ B.powerset, ∑ T ∈ B.powerset, if Disjoint S T then Z S T else 0) =
      ∑ D ∈ B.powerset, (-1 : ℂ) ^ D.card *
        ∑ S ∈ B.powerset, ∑ T ∈ B.powerset,
          if D ⊆ S ∧ D ⊆ T then Z S T else 0 := by
  have hp (S T : Finset ι) (hS : S ∈ B.powerset) (hT : T ∈ B.powerset) :
      (if Disjoint S T then Z S T else 0) =
        ∑ D ∈ B.powerset, (-1 : ℂ) ^ D.card *
          if D ⊆ S ∧ D ⊆ T then Z S T else 0 := by
    calc
      _ = (if Disjoint S T then (1 : ℂ) else 0) * Z S T := by split_ifs <;> simp
      _ = (∑ D ∈ B.powerset,
          if D ⊆ S ∧ D ⊆ T then (-1 : ℂ) ^ D.card else 0) * Z S T := by
        rw [disjoint_indicator_expansion B S T (Finset.mem_powerset.mp hS)
          (Finset.mem_powerset.mp hT)]
      _ = _ := by
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro D hD
        split_ifs <;> simp
  calc
    _ = ∑ S ∈ B.powerset, ∑ T ∈ B.powerset, ∑ D ∈ B.powerset,
        (-1 : ℂ) ^ D.card * if D ⊆ S ∧ D ⊆ T then Z S T else 0 := by
      apply Finset.sum_congr rfl
      intro S hS
      exact Finset.sum_congr rfl (fun T hT => hp S T hS hT)
    _ = _ := by
      simp_rw [Finset.mul_sum]
      calc
        _ = ∑ S ∈ B.powerset, ∑ D ∈ B.powerset, ∑ T ∈ B.powerset,
            (-1 : ℂ) ^ D.card * if D ⊆ S ∧ D ⊆ T then Z S T else 0 := by
          apply Finset.sum_congr rfl
          intro S hS
          exact Finset.sum_comm
        _ = _ := Finset.sum_comm

theorem sum_supersets {ι : Type*} [DecidableEq ι]
    (B D : Finset ι) (hD : D ⊆ B) (f : Finset ι → ℂ) :
    (∑ S ∈ B.powerset, if D ⊆ S then f S else 0) =
      ∑ U ∈ (B \ D).powerset, f (D ∪ U) := by
  rw [← Finset.sum_filter]
  refine Finset.sum_bij (fun S _ => S \ D) ?_ ?_ ?_ ?_
  · intro S hS
    simp only [Finset.mem_filter, Finset.mem_powerset] at hS ⊢
    exact Finset.sdiff_subset_sdiff hS.1 (Finset.Subset.refl _)
  · intro S hS T hT heq
    simp only [Finset.mem_filter, Finset.mem_powerset] at hS hT
    have he := congrArg (fun U => D ∪ U) heq
    simpa [Finset.union_sdiff_of_subset hS.2, Finset.union_sdiff_of_subset hT.2] using he
  · intro U hU
    have hUB : U ⊆ B \ D := Finset.mem_powerset.mp hU
    refine ⟨D ∪ U, ?_, ?_⟩
    · simp only [Finset.mem_filter, Finset.mem_powerset]
      exact ⟨Finset.union_subset hD (hUB.trans Finset.sdiff_subset), Finset.subset_union_left⟩
    · apply Finset.union_sdiff_cancel_left
      exact (Finset.disjoint_of_subset_right hUB disjoint_sdiff_self_right)
  · intro S hS
    simp only [Finset.mem_filter, Finset.mem_powerset] at hS
    rw [Finset.union_sdiff_of_subset hS.2]

theorem double_sum_disjoint_reindexed {ι : Type*} [DecidableEq ι]
    (B : Finset ι) (Z : Finset ι → Finset ι → ℂ) :
    (∑ S ∈ B.powerset, ∑ T ∈ B.powerset, if Disjoint S T then Z S T else 0) =
      ∑ D ∈ B.powerset, (-1 : ℂ) ^ D.card *
        ∑ U ∈ (B \ D).powerset, ∑ V ∈ (B \ D).powerset, Z (D ∪ U) (D ∪ V) := by
  rw [double_sum_disjoint_expansion]
  apply Finset.sum_congr rfl
  intro D hD
  congr 1
  have hDB := Finset.mem_powerset.mp hD
  calc
    _ = ∑ S ∈ B.powerset, if D ⊆ S then
          (∑ T ∈ B.powerset, if D ⊆ T then Z S T else 0) else 0 := by
      apply Finset.sum_congr rfl
      intro S hS
      by_cases hh : D ⊆ S <;> simp [hh]
    _ = _ := by
      rw [sum_supersets B D hDB]
      apply Finset.sum_congr rfl
      intro U hU
      exact sum_supersets B D hDB (Z (D ∪ U))

open ActualEisensteinCubic

theorem ideal_mobius_coprime_reindex
    {ι : Type*} [DecidableEq ι] (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
    (hprime : ∀ i, Prime (P i)) (hinj : Function.Injective P)
    (B : Finset ι) (Z : Ideal O → Ideal O → ℂ) :
    (∑ S ∈ B.powerset, ∑ T ∈ B.powerset,
      if Disjoint S T then Z (∏ i ∈ S, P i) (∏ i ∈ T, P i) else 0) =
      ∑ D ∈ B.powerset, (UniqueFactorizationMonoid.moebius (∏ i ∈ D, P i) : ℂ) *
        ∑ U ∈ (B \ D).powerset, ∑ V ∈ (B \ D).powerset,
          Z ((∏ i ∈ D, P i) * ∏ i ∈ U, P i) ((∏ i ∈ D, P i) * ∏ i ∈ V, P i) := by
  rw [double_sum_disjoint_reindexed]
  apply Finset.sum_congr rfl
  intro D hD
  rw [prime_product_moebius P hprime hinj]
  congr 1
  apply Finset.sum_congr rfl
  intro U hU
  apply Finset.sum_congr rfl
  intro V hV
  rw [Finset.prod_union (Finset.disjoint_of_subset_right
    (Finset.mem_powerset.mp hU) disjoint_sdiff_self_right)]
  rw [Finset.prod_union (Finset.disjoint_of_subset_right
    (Finset.mem_powerset.mp hV) disjoint_sdiff_self_right)]

end CoprimeMobiusExtension

end

end OAI

end


