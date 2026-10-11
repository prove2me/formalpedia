-- Prove2me | Definitions.Def_PNT_ZeroFree_433_0060
-- name    : PNT_ZeroFree_433_0060
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-10T16:15:15.882863+00:00
-- url     : https://prove2.me/theorems/7ad5ce7c-03e1-4f13-a211-bd5ad2df7cbd
-- title:
--   Zero-free region foundations: CubicSieve.CrossFactorization [0060]
-- statement:
--   Definitions and proved supporting lemmas from the following source modules:
--
--   - OAI.NumberTheory.DirichletL.CubicSieve.CrossFactorization
--
--   These declarations form part of the analytic and arithmetic foundations of the Dirichlet L-function nonvanishing argument in the half-plane Re(s) > 7/8. The original namespaces and hypotheses are retained. The code is ported to Lean 4.33.1 and the pinned Mathlib environment; every included lemma has a complete proof.
-- source:
--   https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/CubicSieve/CrossFactorization.lean#L79-L733

import Definitions.Def_PNT_ZeroFree_433_0055
import Definitions.Def_PNT_ZeroFree_433_0059

/- Supporting source modules for the zero-free-region proof.
Ported and checked against Lean 4.33.1 / Mathlib 0df444a.
Original source attribution:
https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/CubicSieve/CrossFactorization.lean#L79-L733
-/

set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

-- Source module: OAI.NumberTheory.DirichletL.CubicSieve.CrossFactorization
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
namespace FirstPassCubeLabels
open ActualEisensteinCubic
open MixedCrossSeparation (crossSymbol quadraticCrossPhase columnPrimeCoprime)
open FiniteGaussPhase (canonicalProductGauss)

theorem blockCross_union_left {ι : Type*} [DecidableEq ι]
    (p : ι → O) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hg : ∀ i, lambda ∉ Ideal.span {p i}) (S T C : Finset ι)
    (hd : Disjoint S T) (e : ι → ℕ) :
    blockCross p hg (S ∪ T) C e = blockCross p hg S C e * blockCross p hg T C e :=
  Finset.prod_union hd

def threeBlockExponent {ι : Type*} [DecidableEq ι] (N P : Finset ι)
    (v : ι → ℕ) (ε₁ ε₂ : ι → Bool) (i : ι) : ℕ :=
  if i ∈ N then 5 else if i ∈ P then 1
  else (conductorExponent (parity (v i)) (ε₁ i) (ε₂ i)).val

theorem gaussBlock_three_cube_partition {ι : Type*} [DecidableEq ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hg : ∀ i, lambda ∉ Ideal.span {p i})
    (hpr : ∀ i, lambda ^ 2 ∣ p i - 1)
    (N P B : Finset ι) (hNP : Disjoint N P) (hNB : Disjoint N B) (hPB : Disjoint P B)
    (v : ι → ℕ) (ε₁ ε₂ : ι → Bool) :
    gaussBlock p hp hg ((N ∪ P) ∪ cubeActiveSupport B v ε₁ ε₂)
      (threeBlockExponent N P v ε₁ ε₂) =
    gaussBlock p hp hg N (fun _ => 5) * gaussBlock p hp hg P (fun _ => 1) *
      gaussBlock p hp hg (cubeActiveSupport B v ε₁ ε₂)
        (fun k => (conductorExponent (parity (v k)) (ε₁ k) (ε₂ k)).val) *
      quadraticCrossPhase p hg N P * mixedCubeCross p hg N B v ε₁ ε₂ true *
        mixedCubeCross p hg P B v ε₁ ε₂ false := by
  let C := cubeActiveSupport B v ε₁ ε₂
  let e := threeBlockExponent N P v ε₁ ε₂
  have hNC : Disjoint N C := hNB.mono_right (Finset.filter_subset _ _)
  have hPC : Disjoint P C := hPB.mono_right (Finset.filter_subset _ _)
  have hNPC : Disjoint (N ∪ P) C := Finset.disjoint_union_left.mpr ⟨hNC, hPC⟩
  have hN (i : ι) (hi : i ∈ N) : e i = 5 := by simp [e, threeBlockExponent, hi]
  have hP (i : ι) (hi : i ∈ P) : e i = 1 := by
    have hn : i ∉ N := fun h => Finset.disjoint_left.mp hNP h hi
    simp [e, threeBlockExponent, hn, hi]
  have hC (i : ι) (hi : i ∈ C) : e i =
      (conductorExponent (parity (v i)) (ε₁ i) (ε₂ i)).val := by
    have hn : i ∉ N := fun h => Finset.disjoint_left.mp hNC h hi
    have hp' : i ∉ P := fun h => Finset.disjoint_left.mp hPC h hi
    simp [e, threeBlockExponent, hn, hp']
  have hcrossNP : blockCross p hg N P e = quadraticCrossPhase p hg N P := by
    apply Finset.prod_congr rfl
    intro i hi
    apply Finset.prod_congr rfl
    intro k hk
    rw [hN i hi, hP k hk, pow_one]
    exact MixedCrossSeparation.mixed_cross_eq_quadratic p hg i k (hpr i) (hpr k)
  have hcrossNC : blockCross p hg N C e = mixedCubeCross p hg N B v ε₁ ε₂ true := by
    apply Finset.prod_congr rfl
    intro i hi
    apply Finset.prod_congr rfl
    intro k hk
    rw [hN i hi, hC k hk]
    rfl
  have hcrossPC : blockCross p hg P C e = mixedCubeCross p hg P B v ε₁ ε₂ false := by
    apply Finset.prod_congr rfl
    intro i hi
    apply Finset.prod_congr rfl
    intro k hk
    rw [hP i hi, hC k hk]
    rfl
  change gaussBlock p hp hg ((N ∪ P) ∪ C) e = _
  rw [gaussBlock_union p hp hg (N ∪ P) C hNPC, gaussBlock_union p hp hg N P hNP,
    blockCross_union_left p hg N P C hNP,
    gaussBlock_congr p hp hg N e (fun _ => 5) hN,
    gaussBlock_congr p hp hg P e (fun _ => 1) hP,
    gaussBlock_congr p hp hg C e _ hC, hcrossNP, hcrossNC, hcrossPC]
  ring

theorem canonicalProductGauss_three_cube_partition {ι : Type*} [DecidableEq ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i, lambda ∉ Ideal.span {p i})
    (hpr : ∀ i, lambda ^ 2 ∣ p i - 1)
    (N P B : Finset ι) (hNP : Disjoint N P) (hNB : Disjoint N B) (hPB : Disjoint P B)
    (v : ι → ℕ) (ε₁ ε₂ : ι → Bool) :
    canonicalProductGauss
      (fun i : ↥((N ∪ P) ∪ cubeActiveSupport B v ε₁ ε₂) => p i.val)
      (fun i => hp i.val) (columnPrimeCoprime p hcop _) (fun i => hg i.val)
      (fun i => threeBlockExponent N P v ε₁ ε₂ i.val) =
    gaussBlock p hp hg N (fun _ => 5) * gaussBlock p hp hg P (fun _ => 1) *
      gaussBlock p hp hg (cubeActiveSupport B v ε₁ ε₂)
        (fun k => (conductorExponent (parity (v k)) (ε₁ k) (ε₂ k)).val) *
      quadraticCrossPhase p hg N P *
      (star (finiteSquarefreeRow (fun i => Ideal.span {p i}) hg N (crtLabel p B v ε₁ ε₂ true)) *
        quadraticCrossPhase p hg N (cubeOddSupport B v ε₁ ε₂)) *
      (finiteSquarefreeRow (fun i => Ideal.span {p i}) hg P (crtLabel p B v ε₁ ε₂ false) *
        quadraticCrossPhase p hg P (cubeOddSupport B v ε₁ ε₂)) := by
  have he : ∀ i ∈ (N ∪ P) ∪ cubeActiveSupport B v ε₁ ε₂,
      threeBlockExponent N P v ε₁ ε₂ i ≠ 0 := by
    intro i hi
    by_cases hn : i ∈ N
    · simp [threeBlockExponent, hn]
    by_cases hp' : i ∈ P
    · simp [threeBlockExponent, hn, hp']
    · have hiC : i ∈ cubeActiveSupport B v ε₁ ε₂ := by simpa [hn, hp'] using hi
      simp only [threeBlockExponent, if_neg hn, if_neg hp']
      exact (ZMod.val_eq_zero _).not.mpr (Finset.mem_filter.mp hiC).2
  rw [canonicalProductGauss_eq_gaussBlock p hp hcop hg _ _ he,
    gaussBlock_three_cube_partition p hp hg hpr N P B hNP hNB hPB,
    mixedCubeCross_eq_row_quadratic p hcop hg hpr N B hNB,
    mixedCubeCross_eq_row_quadratic p hcop hg hpr P B hPB]
  rfl

theorem gaussBlock_eq_mobius_converted {ι : Type*} [DecidableEq ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i, lambda ∉ Ideal.span {p i})
    (hc : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
    (hpr : ∀ i, lambda ^ 2 ∣ p i - 1) (S : Finset ι) (side : Bool) :
    gaussBlock p hp hg S (fun _ => if side then 5 else 1) =
      FirstCauchyArithmetic.supportMobius (fun i => Ideal.span {p i}) S *
        MixedCrossSeparation.convertedColumnBlock p hp hg S side := by
  have hinj : Function.Injective (fun i => Ideal.span {p i}) := by
    intro i k hik
    by_contra hne
    have ht := (hcop hne).sup_eq
    rw [hik, sup_idem] at ht
    exact (inferInstance : (Ideal.span {p k}).IsMaximal).ne_top ht
  have hprime (i : ι) : Prime (Ideal.span {p i}) :=
    Ideal.prime_of_isPrime (NeZero.ne (Ideal.span {p i})) inferInstance
  rw [FirstCauchyArithmetic.supportMobius,
    prime_product_moebius (fun i => Ideal.span {p i}) hprime hinj S]
  unfold gaussBlock MixedCrossSeparation.convertedColumnBlock
  rw [← Finset.prod_neg]
  apply Finset.prod_congr rfl
  intro i hi
  have hl := MixedGaussConversion.neg_localGauss_eq_converted (p i) (hp i) (hg i) (hc i) (hpr i) side
  change (∏ k ∈ S.erase i, crossSymbol p hg i k ^ (if side then 5 else 1)) *
      MixedGaussConversion.localGauss (p i) (hp i) (hg i) (if side then 5 else 1) =
    -((∏ k ∈ S.erase i, crossSymbol p hg i k ^ (if side then 5 else 1)) *
      MixedGaussConversion.convertedLocal (p i) (hp i) (hg i) side)
  rw [← hl]
  ring

theorem a_weighted_three_cube_gauss {ι : Type*} [DecidableEq ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i, lambda ∉ Ideal.span {p i})
    (hc : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
    (hpr : ∀ i, lambda ^ 2 ∣ p i - 1)
    (N P B : Finset ι) (hNP : Disjoint N P) (hNB : Disjoint N B) (hPB : Disjoint P B)
    (v : ι → ℕ) (ε₁ ε₂ : ι → Bool) (C₁ C₂ : Finset ι → ℂ) :
    star (MixedCrossSeparation.columnCoefficient p hp hcop hg N * C₁ N) *
      (MixedCrossSeparation.columnCoefficient p hp hcop hg P * C₂ P) *
      canonicalProductGauss
        (fun i : ↥((N ∪ P) ∪ cubeActiveSupport B v ε₁ ε₂) => p i.val)
        (fun i => hp i.val) (columnPrimeCoprime p hcop _) (fun i => hg i.val)
        (fun i => threeBlockExponent N P v ε₁ ε₂ i.val) =
    (gaussBlock p hp hg (cubeActiveSupport B v ε₁ ε₂)
        (fun k => (conductorExponent (parity (v k)) (ε₁ k) (ε₂ k)).val) *
      quadraticCrossPhase p hg N P *
      quadraticCrossPhase p hg N (cubeOddSupport B v ε₁ ε₂) *
      quadraticCrossPhase p hg P (cubeOddSupport B v ε₁ ε₂)) *
      star (FirstCauchyArithmetic.supportMobius (fun i => Ideal.span {p i}) N *
        FirstCauchyArithmetic.firstPassColumnMinus p hp hcop hg C₁ (crtLabel p B v ε₁ ε₂ true) N) *
      (FirstCauchyArithmetic.supportMobius (fun i => Ideal.span {p i}) P *
        FirstCauchyArithmetic.firstPassColumnPlus p hp hcop hg C₂ (crtLabel p B v ε₁ ε₂ false) P) := by
  rw [canonicalProductGauss_three_cube_partition p hp hcop hg hpr N P B hNP hNB hPB]
  have hconvN := gaussBlock_eq_mobius_converted p hp hcop hg hc hpr N true
  have hconvP := gaussBlock_eq_mobius_converted p hp hcop hg hc hpr P false
  simp only [Bool.false_eq_true, ↓reduceIte] at hconvN hconvP
  rw [hconvN, hconvP]
  have hn := MixedCrossSeparation.columnCoefficient_cancel_true p hp hcop hg hc hpr N
  have hp' := MixedCrossSeparation.columnCoefficient_cancel_false p hp hcop hg hc hpr P
  simp only [FirstCauchyArithmetic.firstPassColumnMinus, FirstCauchyArithmetic.firstPassColumnPlus,
    star_mul, star_star, FirstCauchyArithmetic.star_supportMobius]
  calc
    _ = (star (MixedCrossSeparation.columnCoefficient p hp hcop hg N) *
        MixedCrossSeparation.convertedColumnBlock p hp hg N true) *
      (MixedCrossSeparation.columnCoefficient p hp hcop hg P *
        MixedCrossSeparation.convertedColumnBlock p hp hg P false) *
      (star (C₁ N) * C₂ P *
        FirstCauchyArithmetic.supportMobius (fun i => Ideal.span {p i}) N *
        FirstCauchyArithmetic.supportMobius (fun i => Ideal.span {p i}) P *
        gaussBlock p hp hg (cubeActiveSupport B v ε₁ ε₂)
          (fun k => (conductorExponent (parity (v k)) (ε₁ k) (ε₂ k)).val) *
        quadraticCrossPhase p hg N P *
        quadraticCrossPhase p hg N (cubeOddSupport B v ε₁ ε₂) *
        quadraticCrossPhase p hg P (cubeOddSupport B v ε₁ ε₂) *
        star (finiteSquarefreeRow (fun i => Ideal.span {p i}) hg N (crtLabel p B v ε₁ ε₂ true)) *
        finiteSquarefreeRow (fun i => Ideal.span {p i}) hg P (crtLabel p B v ε₁ ε₂ false)) := by ring
    _ = _ := by rw [hn, hp']; ring

end FirstPassCubeLabels

namespace QuadraticGaussRay
open EisensteinEPrimaryPhase ActualEisensteinCoordinates ActualEisensteinCubic

theorem quadraticRayValue_square (r : Coord) (hr : odd r) :
    quadraticRayValue (mul r r) = 1 := by
  have hi : (Complex.I : ℂ)⁻¹ = -Complex.I := by
    apply inv_eq_of_mul_eq_one_right
    norm_num
  have h : mul r r = (1, 0) ∨ mul r r = (3, 3) ∨ mul r r = (0, 1) := by
    decide +revert
  rcases h with h | h | h
  · rw [h]
    change breveGaussianFourTerms 1 0 = 1
    rw [breveGaussianFourTerms_formula]
    norm_num [hi]
  · rw [h]
    change breveGaussianFourTerms 3 3 = 1
    rw [breveGaussianFourTerms_formula]
    norm_num [hi]
  · rw [h]
    change breveGaussianFourTerms 0 1 = 1
    rw [breveGaussianFourTerms_formula]
    norm_num [hi]
    ring

theorem quadraticRayValue_same_residue_product (a b : ActualEisensteinCubic.O)
    (ha : odd (residue a)) (hab : residue a = residue b) :
    quadraticRayValue (residue (a * b)) = 1 := by
  rw [residue_mul, ← hab]
  exact quadraticRayValue_square _ ha

end QuadraticGaussRay

namespace QuadraticMainBoundaryFibers
abbrev O := ActualEisensteinCubic.O
open IdealMobiusDivisorSum QuadraticMainBoundary

def productIdeal (x : Ideal O × Ideal O × Ideal O) : Ideal O := x.1 * x.2.1 * x.2.2

theorem product_fiber_card_le (s : Finset (Ideal O × Ideal O × Ideal O))
    (G : Ideal O) (hG : G ≠ 0)
    (hdiv : ∀ x ∈ s, x.2.1 ∣ G ∧ x.2.2 ∣ G) (B : Ideal O) :
    (s.filter (fun x => productIdeal x = B)).card ≤ (idealDivisors G).card ^ 2 := by
  have hle : (s.filter (fun x => productIdeal x = B)).card ≤
      ((idealDivisors G) ×ˢ (idealDivisors G)).card := by
    apply Finset.card_le_card_of_injOn (fun x => (x.2.1, x.2.2))
    · intro x hx
      have hd := hdiv x (Finset.mem_filter.mp hx).1
      exact Finset.mem_product.mpr ⟨(mem_idealDivisors hG).mpr hd.1,
        (mem_idealDivisors hG).mpr hd.2⟩
    · intro x hx y hy hde
      obtain ⟨hD, hE⟩ := Prod.mk.inj hde
      have hd := hdiv x (Finset.mem_filter.mp hx).1
      have hD0 := ne_zero_of_dvd_ne_zero hG hd.1
      have hE0 := ne_zero_of_dvd_ne_zero hG hd.2
      have hprod := (Finset.mem_filter.mp hx).2.trans (Finset.mem_filter.mp hy).2.symm
      change x.1 * x.2.1 * x.2.2 = y.1 * y.2.1 * y.2.2 at hprod
      rw [← hD, ← hE] at hprod
      have hH : x.1 = y.1 := mul_right_cancel₀ hD0 (mul_right_cancel₀ hE0 hprod)
      exact Prod.ext hH (Prod.ext hD hE)
  simpa only [Finset.card_product, pow_two] using hle

theorem product_fiber_small_power (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (s : Finset (Ideal O × Ideal O × Ideal O)) (G : Ideal O),
      G ≠ 0 → (∀ x ∈ s, x.2.1 ∣ G ∧ x.2.2 ∣ G) → ∀ B : Ideal O,
      ((s.filter (fun x => productIdeal x = B)).card : ℝ) ≤
        C * (Ideal.absNorm G : ℝ) ^ ε := by
  obtain ⟨C, hC, hbound⟩ := IdealDivisorBound.ideal_divisor_small_power (ε / 2) (by linarith)
  refine ⟨C ^ 2, by positivity, ?_⟩
  intro s G hG hdiv B
  have hc : ((s.filter (fun x => productIdeal x = B)).card : ℝ) ≤
      ((idealDivisors G).card : ℝ) ^ 2 := by
    exact_mod_cast product_fiber_card_le s G hG hdiv B
  have hb := pow_le_pow_left₀ (by positivity : 0 ≤ ((idealDivisors G).card : ℝ))
    (hbound G hG) 2
  have heq : ((Ideal.absNorm G : ℝ) ^ (ε / 2)) ^ 2 = (Ideal.absNorm G : ℝ) ^ ε := by
    rw [← Real.rpow_natCast]
    rw [← Real.rpow_mul (Nat.cast_nonneg _)]
    congr 1
    norm_num
  apply hc.trans
  simpa only [mul_pow, heq] using hb

def boundaryCoefficient (K : ℝ) (s : Finset (Ideal O × Ideal O × Ideal O))
    (B : Ideal O) : ℂ :=
  ∑ x ∈ s.filter (fun x => productIdeal x = B),
    (UniqueFactorizationMonoid.moebius x.2.2 : ℂ) * (cutoffDifference K x.1 x.2.1 : ℝ)

theorem norm_cutoffDifference_le (K : ℝ) (H D : Ideal O) :
    ‖(cutoffDifference K H D : ℂ)‖ ≤ 1 := by
  unfold cutoffDifference
  split_ifs <;> norm_num

theorem boundaryCoefficient_norm_le_card (K : ℝ)
    (s : Finset (Ideal O × Ideal O × Ideal O)) (B : Ideal O) :
    ‖boundaryCoefficient K s B‖ ≤ (s.filter (fun x => productIdeal x = B)).card := by
  unfold boundaryCoefficient
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ _x ∈ s.filter (fun x => productIdeal x = B), (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro x _
      rw [norm_mul]
      have hm : ‖(UniqueFactorizationMonoid.moebius x.2.2 : ℂ)‖ ≤ 1 := by
        unfold UniqueFactorizationMonoid.moebius
        split_ifs <;> simp
      exact (mul_le_of_le_one_left (norm_nonneg _) hm).trans (norm_cutoffDifference_le _ _ _)
    _ = _ := by simp

theorem boundaryCoefficient_small_power (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (K : ℝ) (s : Finset (Ideal O × Ideal O × Ideal O)) (G : Ideal O),
      G ≠ 0 → (∀ x ∈ s, x.2.1 ∣ G ∧ x.2.2 ∣ G) → ∀ B : Ideal O,
      ‖boundaryCoefficient K s B‖ ≤ C * (Ideal.absNorm G : ℝ) ^ ε := by
  obtain ⟨C, hC, hbound⟩ := product_fiber_small_power ε hε
  exact ⟨C, hC, fun K s G hG hdiv B =>
    (boundaryCoefficient_norm_le_card K s B).trans (hbound s G hG hdiv B)⟩

theorem boundaryCoefficient_eq_zero_below (K : ℝ)
    (s : Finset (Ideal O × Ideal O × Ideal O)) (G : Ideal O) (hG : G ≠ 0)
    (hdiv : ∀ x ∈ s, x.2.1 ∣ G ∧ x.2.2 ∣ G)
    (B : Ideal O) (hB : (Ideal.absNorm B : ℝ) ≤ K) : boundaryCoefficient K s B = 0 := by
  apply Finset.sum_eq_zero
  intro x hx
  have hx' := Finset.mem_filter.mp hx
  have hd := hdiv x hx'.1
  have hz := cutoffDifference_eq_zero_of_product_le K
    (ne_zero_of_dvd_ne_zero hG hd.1) (ne_zero_of_dvd_ne_zero hG hd.2)
    (by simpa only [← hx'.2, productIdeal] using hB)
  rw [hz, Complex.ofReal_zero, mul_zero]

end QuadraticMainBoundaryFibers

namespace CoprimeSieveOperator
open FiniteSieveOperator CoprimeMobiusExtension

theorem square_norm_sum {n : Type*} [Fintype n] (z : n → ℂ) :
    (↑(‖∑ j, z j‖ ^ 2) : ℂ) = ∑ j, ∑ k, star (z j) * z k := by
  rw [Complex.sq_norm, Complex.normSq_eq_conj_mul_self]
  simp only [map_sum, starRingEnd_apply]
  rw [Finset.sum_mul_sum]

theorem disjoint_gram_expansion {ι n : Type*} [DecidableEq ι] [Fintype n]
    (B : Finset ι) (support : n → Finset ι) (hs : ∀ j, support j ⊆ B) (z : n → ℂ) :
    (∑ j, ∑ k, if Disjoint (support j) (support k) then star (z j) * z k else 0) =
      ∑ D ∈ B.powerset, (-1 : ℂ) ^ D.card *
        (↑(‖∑ j, if D ⊆ support j then z j else 0‖ ^ 2) : ℂ) := by
  have hp (j k : n) :
      (if Disjoint (support j) (support k) then star (z j) * z k else 0) =
      ∑ D ∈ B.powerset, (-1 : ℂ) ^ D.card *
        (if D ⊆ support j ∧ D ⊆ support k then star (z j) * z k else 0) := by
    calc
      _ = (if Disjoint (support j) (support k) then (1 : ℂ) else 0) * (star (z j) * z k) := by
        split_ifs <;> simp
      _ = _ := by
        rw [disjoint_indicator_expansion B _ _ (hs j) (hs k), Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro D _
        split_ifs <;> simp
  simp_rw [hp]
  calc
    _ = ∑ j, ∑ D ∈ B.powerset, ∑ k,
        (-1 : ℂ) ^ D.card *
          (if D ⊆ support j ∧ D ⊆ support k then star (z j) * z k else 0) := by
      apply Finset.sum_congr rfl
      intro j _
      exact Finset.sum_comm
    _ = ∑ D ∈ B.powerset, ∑ j, ∑ k,
        (-1 : ℂ) ^ D.card *
          (if D ⊆ support j ∧ D ⊆ support k then star (z j) * z k else 0) :=
      Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro D _
      simp_rw [← Finset.mul_sum]
      congr 1
      rw [square_norm_sum]
      apply Finset.sum_congr rfl
      intro j _
      apply Finset.sum_congr rfl
      intro k _
      by_cases hj : D ⊆ support j <;> by_cases hk : D ⊆ support k <;> simp [hj, hk]

theorem masked_coefficient_energy {ι n : Type*} [DecidableEq ι] [Fintype n]
    (B : Finset ι) (support : n → Finset ι) (hs : ∀ j, support j ⊆ B) (a : n → ℂ) :
    (∑ D ∈ B.powerset, ∑ j, ‖if D ⊆ support j then a j else 0‖ ^ 2) =
      ∑ j, (2 : ℝ) ^ (support j).card * ‖a j‖ ^ 2 := by
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  have heq : B.powerset.filter (fun D => D ⊆ support j) = (support j).powerset := by
    ext D
    simp only [Finset.mem_filter, Finset.mem_powerset]
    exact ⟨And.right, fun h => ⟨h.trans (hs j), h⟩⟩
  have hite (D : Finset ι) : ‖if D ⊆ support j then a j else 0‖ ^ 2 =
      if D ⊆ support j then ‖a j‖ ^ 2 else 0 := by split_ifs <;> simp
  simp_rw [hite]
  rw [← Finset.sum_filter, heq]
  simp

theorem weighted_energy_bound {m n : Type*} [Fintype m] [Fintype n]
    [DecidableEq m] [DecidableEq n]
    (A : Matrix m n ℂ) (a : n → ℂ) (w : m → ℂ) (W : ℝ)
    (hW : 0 ≤ W) (hw : ∀ i, ‖w i‖ ≤ W) :
    ‖∑ i, w i * (↑(‖∑ j, A i j * a j‖ ^ 2) : ℂ)‖ ≤
      W * ‖operator A‖ ^ 2 * ∑ j, ‖a j‖ ^ 2 := by
  calc
    _ ≤ ∑ i, ‖w i * (↑(‖∑ j, A i j * a j‖ ^ 2) : ℂ)‖ := norm_sum_le _ _
    _ ≤ ∑ i, W * ‖∑ j, A i j * a j‖ ^ 2 := by
      apply Finset.sum_le_sum
      intro i _
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      exact mul_le_mul_of_nonneg_right (hw i) (sq_nonneg _)
    _ = W * ∑ i, ‖∑ j, A i j * a j‖ ^ 2 := (Finset.mul_sum ..).symm
    _ ≤ _ := by
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_left (energy_bound A a) hW

theorem coprime_gram_operator_bound {ι m n : Type*} [DecidableEq ι]
    [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    (B : Finset ι) (support : n → Finset ι) (hs : ∀ j, support j ⊆ B)
    (A : Matrix m n ℂ) (a : n → ℂ) (w : m → ℂ) (W : ℝ)
    (hW : 0 ≤ W) (hw : ∀ i, ‖w i‖ ≤ W) :
    ‖∑ i, w i * (∑ j, ∑ k,
      if Disjoint (support j) (support k) then
        star (A i j * a j) * (A i k * a k) else 0)‖ ≤
      W * ‖operator A‖ ^ 2 * ∑ j, (2 : ℝ) ^ (support j).card * ‖a j‖ ^ 2 := by
  have heq : (∑ i, w i * (∑ j, ∑ k,
      if Disjoint (support j) (support k) then
        star (A i j * a j) * (A i k * a k) else 0)) =
      ∑ D ∈ B.powerset, (-1 : ℂ) ^ D.card *
        ∑ i, w i * (↑(‖∑ j, A i j * (if D ⊆ support j then a j else 0)‖ ^ 2) : ℂ) := by
    simp_rw [disjoint_gram_expansion B support hs, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro D _
    apply Finset.sum_congr rfl
    intro i _
    have hz : (∑ j, if D ⊆ support j then A i j * a j else 0) =
        ∑ j, A i j * (if D ⊆ support j then a j else 0) := by
      apply Finset.sum_congr rfl
      intro j _
      split_ifs <;> simp
    rw [hz]
    ring
  rw [heq]
  calc
    _ ≤ ∑ D ∈ B.powerset, ‖(-1 : ℂ) ^ D.card *
        ∑ i, w i * (↑(‖∑ j, A i j * (if D ⊆ support j then a j else 0)‖ ^ 2) : ℂ)‖ := norm_sum_le _ _
    _ ≤ ∑ D ∈ B.powerset,
        W * ‖operator A‖ ^ 2 * ∑ j, ‖if D ⊆ support j then a j else 0‖ ^ 2 := by
      apply Finset.sum_le_sum
      intro D _
      simp only [norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul]
      exact weighted_energy_bound A (fun j => if D ⊆ support j then a j else 0) w W hW hw
    _ = _ := by
      rw [← Finset.mul_sum, masked_coefficient_energy B support hs a]

end CoprimeSieveOperator

namespace IdealCoprimeSieveOperator
abbrev O := ActualEisensteinCubic.O
open IdealMobiusDivisorSum CoprimeSieveOperator FiniteSieveOperator
open UniqueFactorizationMonoid

theorem primeSupport_disjoint_iff {I J : Ideal O} (hI : I ≠ 0) (hJ : J ≠ 0) :
    Disjoint (primeSupport I) (primeSupport J) ↔ IsCoprime I J := by
  constructor
  · intro h
    have hr : IsRelPrime I J := (isRelPrime_iff_no_prime_factors hI).mpr (by
      intro P hPI hPJ hP
      apply Finset.disjoint_left.mp h
      · apply Multiset.mem_toFinset.mpr
        exact (Ideal.mem_normalizedFactors_iff hI).mpr
          ⟨Ideal.isPrime_of_prime hP, Ideal.dvd_iff_le.mp hPI⟩
      · apply Multiset.mem_toFinset.mpr
        exact (Ideal.mem_normalizedFactors_iff hJ).mpr
          ⟨Ideal.isPrime_of_prime hP, Ideal.dvd_iff_le.mp hPJ⟩)
    apply Ideal.isCoprime_iff_gcd.mpr
    exact associated_iff_eq.mp (associated_one_iff_isUnit.mpr (gcd_isUnit_iff_isRelPrime.mpr hr))
  · intro h
    exact Multiset.disjoint_toFinset.mpr (disjoint_normalizedFactors h.isRelPrime)

def supportConstant (ε : ℝ) (hε : 0 < ε) : ℝ :=
  (SquarefreeDivisorBound.prime_support_subsets_bound ε hε).choose

theorem supportConstant_pos (ε : ℝ) (hε : 0 < ε) : 0 < supportConstant ε hε :=
  (SquarefreeDivisorBound.prime_support_subsets_bound ε hε).choose_spec.1

theorem support_card_bound (ε : ℝ) (hε : 0 < ε) (I : Ideal O) (hI : I ≠ 0) :
    (2 : ℝ) ^ (primeSupport I).card ≤ supportConstant ε hε * (Ideal.absNorm I : ℝ) ^ ε :=
  (SquarefreeDivisorBound.prime_support_subsets_bound ε hε).choose_spec.2 I hI

theorem ideal_coprime_gram_operator_bound {m n : Type*}
    [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    (ε : ℝ) (hε : 0 < ε) (column : n → Ideal O) (hcol : ∀ j, column j ≠ 0)
    (N : ℝ) (_hN : 0 ≤ N) (hnorm : ∀ j, (Ideal.absNorm (column j) : ℝ) ≤ N)
    (A : Matrix m n ℂ) (a : n → ℂ) (w : m → ℂ) (W : ℝ)
    (hW : 0 ≤ W) (hw : ∀ i, ‖w i‖ ≤ W) :
    ‖∑ i, w i * (∑ j, ∑ k,
      if IsCoprime (column j) (column k) then
        star (A i j * a j) * (A i k * a k) else 0)‖ ≤
      W * ‖operator A‖ ^ 2 * (supportConstant ε hε * N ^ ε) * ∑ j, ‖a j‖ ^ 2 := by
  let B : Finset (Ideal O) := Finset.univ.biUnion (fun j => primeSupport (column j))
  have hs (j : n) : primeSupport (column j) ⊆ B := by
    intro P hP
    exact Finset.mem_biUnion.mpr ⟨j, Finset.mem_univ j, hP⟩
  have h := coprime_gram_operator_bound B (fun j => primeSupport (column j)) hs A a w W hW hw
  simp_rw [primeSupport_disjoint_iff (hcol _) (hcol _)] at h
  apply h.trans
  have hmass : (∑ j, (2 : ℝ) ^ (primeSupport (column j)).card * ‖a j‖ ^ 2) ≤
      (supportConstant ε hε * N ^ ε) * ∑ j, ‖a j‖ ^ 2 := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro j _
    apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
    exact (support_card_bound ε hε (column j) (hcol j)).trans
      (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (Nat.cast_nonneg _) (hnorm j) hε.le)
        (supportConstant_pos ε hε).le)
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hmass
    (mul_nonneg hW (sq_nonneg ‖operator A‖))

open ConcretePrimeRowBridge

theorem actual_quadratic_coprime_gram_bound {m : Type*}
    [Fintype m] [DecidableEq m]
    (ε : ℝ) (hε : 0 < ε)
    (F : Finset (Ideal O)) (hFpos : ∀ I ∈ F, I ≠ ⊥)
    (hFgood : ∀ I ∈ F, ∀ P ∈ normalizedFactors I, goodLambda ∉ P)
    (r : m → O) (N : ℝ) (hN : 0 ≤ N)
    (hnorm : ∀ I ∈ F, (Ideal.absNorm I : ℝ) ≤ N)
    (a : F → ℂ) (w : m → ℂ) (W : ℝ) (hW : 0 ≤ W) (hw : ∀ i, ‖w i‖ ≤ W) :
    let A : Matrix m F ℂ := fun i J => (idealSexticRow F hFpos hFgood J.val (r i)) ^ 3
    ‖∑ i, w i * (∑ J : F, ∑ columnTwo : F,
      if IsCoprime J.val columnTwo.val then star (A i J * a J) * (A i columnTwo * a columnTwo) else 0)‖ ≤
      W * ‖operator A‖ ^ 2 * (supportConstant ε hε * N ^ ε) * ∑ J : F, ‖a J‖ ^ 2 := by
  dsimp only
  exact ideal_coprime_gram_operator_bound ε hε (fun J : F => J.val)
    (fun J => hFpos J.val J.property) N hN (fun J => hnorm J.val J.property)
    (fun i J => (idealSexticRow F hFpos hFgood J.val (r i)) ^ 3) a w W hW hw

end IdealCoprimeSieveOperator

open scoped BigOperators Classical
namespace QuadraticMainOperatorBound
abbrev O := ActualEisensteinCubic.O
open IdealMobiusDivisorSum QuadraticMainBoundary IdealCoprimeSieveOperator FiniteSieveOperator

def mainWeight (K : ℝ) (H D E : Ideal O) : ℂ :=
  (cutoffDifference K H D : ℂ) / (Real.sqrt (Ideal.absNorm (H * D * E) : ℝ) : ℂ)

theorem mainWeight_eq_zero_of_row_gt (K : ℝ) (H D E : Ideal O) (hD : D ≠ 0)
    (hH : K < (Ideal.absNorm H : ℝ)) : mainWeight K H D E = 0 := by
  have hc : cutoffDifference K H D = 0 := by
    by_contra h
    exact (not_le.mpr hH) ((cutoffDifference_nonzero_iff K H D hD).mp h).1
  simp [mainWeight, hc]

theorem mainWeight_norm_le (K : ℝ) (hK : 0 < K) (H D E : Ideal O)
    (hD : D ≠ 0) (hE : E ≠ 0) : ‖mainWeight K H D E‖ ≤ 1 / Real.sqrt K := by
  by_cases hc : cutoffDifference K H D = 0
  · simp [mainWeight, hc]
  have hn : K < (Ideal.absNorm (H * D * E) : ℝ) := by
    exact lt_of_not_ge (fun h => hc (cutoffDifference_eq_zero_of_product_le K hD hE h))
  have hsq : 0 < Real.sqrt K := Real.sqrt_pos.mpr hK
  have hle := Real.sqrt_le_sqrt hn.le
  rw [mainWeight, cutoffDifference_eq_neg_one_of_nonzero K H D hD hc]
  simp only [norm_div, Complex.ofReal_neg, Complex.ofReal_one, norm_neg, norm_one,
    Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
  exact one_div_le_one_div_of_le hsq hle

theorem main_difference_operator_bound {m n : Type*}
    [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    (ε : ℝ) (hε : 0 < ε) (K : ℝ) (hK : 0 < K)
    (G : Ideal O) (hG : G ≠ 0) (H : m → Ideal O)
    (column : n → Ideal O) (hcol : ∀ j, column j ≠ 0)
    (N : ℝ) (hN : 0 ≤ N) (hnorm : ∀ j, (Ideal.absNorm (column j) : ℝ) ≤ N)
    (A : Matrix m n ℂ) (a : n → ℂ)
    (r : Ideal O → Ideal O → n → ℂ) (hr : ∀ D E j, ‖r D E j‖ ≤ 1) :
    ‖∑ D ∈ idealDivisors G, ∑ E ∈ idealDivisors G,
      (UniqueFactorizationMonoid.moebius E : ℂ) *
      (∑ i, mainWeight K (H i) D E *
        (∑ j, ∑ k, if IsCoprime (column j) (column k) then
          star (A i j * (a j * r D E j)) * (A i k * (a k * r D E k)) else 0))‖ ≤
      ((idealDivisors G).card : ℝ) ^ 2 *
        ((1 / Real.sqrt K) * ‖operator A‖ ^ 2 * (supportConstant ε hε * N ^ ε) *
          ∑ j, ‖a j‖ ^ 2) := by
  let B := (1 / Real.sqrt K) * ‖operator A‖ ^ 2 * (supportConstant ε hε * N ^ ε) *
    ∑ j, ‖a j‖ ^ 2
  have hB : 0 ≤ B := by
    have hC := (supportConstant_pos ε hε).le
    dsimp [B]
    positivity
  have hterm (D : Ideal O) (hD : D ∈ idealDivisors G)
      (E : Ideal O) (hE : E ∈ idealDivisors G) :
      ‖(UniqueFactorizationMonoid.moebius E : ℂ) *
        (∑ i, mainWeight K (H i) D E *
          (∑ j, ∑ k, if IsCoprime (column j) (column k) then
            star (A i j * (a j * r D E j)) * (A i k * (a k * r D E k)) else 0))‖ ≤ B := by
    have hD0 := IdealDivisorBound.divisor_ne_zero hG hD
    have hE0 := IdealDivisorBound.divisor_ne_zero hG hE
    have he := ideal_coprime_gram_operator_bound ε hε column hcol N hN hnorm A
      (fun j => a j * r D E j) (fun i => mainWeight K (H i) D E) (1 / Real.sqrt K)
      (by positivity) (fun i => mainWeight_norm_le K hK (H i) D E hD0 hE0)
    have hm : (∑ j, ‖a j * r D E j‖ ^ 2) ≤ ∑ j, ‖a j‖ ^ 2 := by
      apply Finset.sum_le_sum
      intro j _
      apply pow_le_pow_left₀ (norm_nonneg _)
      rw [norm_mul]
      exact mul_le_of_le_one_right (norm_nonneg _) (hr D E j)
    have heB : ‖∑ i, mainWeight K (H i) D E *
        (∑ j, ∑ k, if IsCoprime (column j) (column k) then
          star (A i j * (a j * r D E j)) * (A i k * (a k * r D E k)) else 0)‖ ≤ B := by
      apply he.trans
      exact mul_le_mul_of_nonneg_left hm (by
        have hC := (supportConstant_pos ε hε).le
        positivity)
    have hmu : ‖(UniqueFactorizationMonoid.moebius E : ℂ)‖ ≤ 1 := by
      unfold UniqueFactorizationMonoid.moebius
      split_ifs <;> simp
    rw [norm_mul]
    calc
      _ ≤ 1 * B := mul_le_mul hmu heB (norm_nonneg _) (by norm_num)
      _ = B := one_mul B
  calc
    _ ≤ ∑ D ∈ idealDivisors G, ‖∑ E ∈ idealDivisors G,
        (UniqueFactorizationMonoid.moebius E : ℂ) *
        (∑ i, mainWeight K (H i) D E *
          (∑ j, ∑ k, if IsCoprime (column j) (column k) then
            star (A i j * (a j * r D E j)) * (A i k * (a k * r D E k)) else 0))‖ := norm_sum_le _ _
    _ ≤ ∑ D ∈ idealDivisors G, ∑ E ∈ idealDivisors G, B := by
      apply Finset.sum_le_sum
      intro D hD
      exact (norm_sum_le _ _).trans (Finset.sum_le_sum (fun E hE => hterm D hD E hE))
    _ = _ := by simp only [Finset.sum_const, nsmul_eq_mul, B]; ring

open ConcretePrimeRowBridge ActualEisensteinCubic

theorem ideal_quadraticRow_norm_le_one (F : Finset (Ideal O))
    (hFpos : ∀ I ∈ F, I ≠ ⊥)
    (hFgood : ∀ I ∈ F, ∀ P ∈ UniqueFactorizationMonoid.normalizedFactors I, goodLambda ∉ P)
    (J : Ideal O) (z : O) : ‖(idealSexticRow F hFpos hFgood J z) ^ 3‖ ≤ 1 := by
  let : ∀ i : primePool F, (i.val).IsMaximal := primePool_maximal F hFpos
  rw [norm_pow]
  apply pow_le_one₀ (norm_nonneg _)
  exact finiteSquarefreeRow_norm_le_one (fun i : primePool F => i.val)
    (primePool_good F hFgood) (idealSupport F J) z

theorem actual_quadratic_main_difference_bound {m : Type*}
    [Fintype m] [DecidableEq m]
    (ε : ℝ) (hε : 0 < ε) (K : ℝ) (hK : 0 < K)
    (G : Ideal O) (hG : G ≠ 0) (H : m → Ideal O) (g : Ideal O → O)
    (F : Finset (Ideal O)) (hFpos : ∀ I ∈ F, I ≠ ⊥)
    (hFgood : ∀ I ∈ F, ∀ P ∈ UniqueFactorizationMonoid.normalizedFactors I, goodLambda ∉ P)
    (N : ℝ) (hN : 0 ≤ N) (hnorm : ∀ J ∈ F, (Ideal.absNorm J : ℝ) ≤ N)
    (a : F → ℂ) :
    let A : Matrix m F ℂ := fun i J => (idealSexticRow F hFpos hFgood J.val (g (H i))) ^ 3
    let r : Ideal O → Ideal O → F → ℂ := fun D E J =>
      (idealSexticRow F hFpos hFgood J.val (g D * g E)) ^ 3
    ‖∑ D ∈ idealDivisors G, ∑ E ∈ idealDivisors G,
      (UniqueFactorizationMonoid.moebius E : ℂ) *
      (∑ i, mainWeight K (H i) D E *
        (∑ J : F, ∑ columnTwo : F, if IsCoprime J.val columnTwo.val then
          star (A i J * (a J * r D E J)) * (A i columnTwo * (a columnTwo * r D E columnTwo)) else 0))‖ ≤
      ((idealDivisors G).card : ℝ) ^ 2 *
        ((1 / Real.sqrt K) * ‖operator A‖ ^ 2 * (supportConstant ε hε * N ^ ε) *
          ∑ J : F, ‖a J‖ ^ 2) := by
  dsimp only
  apply main_difference_operator_bound ε hε K hK G hG H (fun J : F => J.val)
    (fun J => hFpos J.val J.property) N hN (fun J => hnorm J.val J.property)
  intro D E J
  exact ideal_quadraticRow_norm_le_one F hFpos hFgood J.val (g D * g E)

end QuadraticMainOperatorBound

end

end OAI

end


