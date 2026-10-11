-- Prove2me | Definitions.Def_PNT_ZeroFree_433_0061
-- name    : PNT_ZeroFree_433_0061
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-10T16:16:28.86946+00:00
-- url     : https://prove2.me/theorems/a3b06147-8f90-4e80-bc92-caac2f3a1151
-- title:
--   Zero-free region foundations: CubicSieve.LocalBrackets [0061]
-- statement:
--   Definitions and proved supporting lemmas from the following source modules:
--
--   - OAI.NumberTheory.DirichletL.CubicSieve.LocalBrackets
--
--   These declarations form part of the analytic and arithmetic foundations of the Dirichlet L-function nonvanishing argument in the half-plane Re(s) > 7/8. The original namespaces and hypotheses are retained. The code is ported to Lean 4.33.1 and the pinned Mathlib environment; every included lemma has a complete proof.
-- source:
--   https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/CubicSieve/LocalBrackets.lean#L80-L637

import Definitions.Def_PNT_ZeroFree_433_0060

/- Supporting source modules for the zero-free-region proof.
Ported and checked against Lean 4.33.1 / Mathlib 0df444a.
Original source attribution:
https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/CubicSieve/LocalBrackets.lean#L80-L637
-/

set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

-- Source module: OAI.NumberTheory.DirichletL.CubicSieve.LocalBrackets
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

open scoped BigOperators Classical SchwartzMap ContDiff
namespace FirstPassCubeLabels
open ActualEisensteinCubic
open MixedCrossSeparation (columnPrimeCoprime quadraticCrossPhase)
open FiniteGaussPhase (canonicalProductGauss)
open ConcreteTraceCRT (eisEmbedding)
open EisensteinSchwartzPoisson (paperRadialFourier)

def blockRow {ι : Type*} (p : ι → O) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hg : ∀ i, lambda ∉ Ideal.span {p i}) (S : Finset ι) (e : ι → ℕ) (u : O) : ℂ :=
  finiteSexticRow (fun i : S => Ideal.span {p i.val}) (fun i => hg i.val) (fun i => e i.val) u

theorem blockRow_eq_product {ι : Type*} (p : ι → O) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hg : ∀ i, lambda ∉ Ideal.span {p i}) (S : Finset ι) (e : ι → ℕ) (u : O) :
    blockRow p hg S e u = ∏ i ∈ S,
      (canonicalSextic (Ideal.span {p i}) (hg i) ^ e i) (Ideal.Quotient.mk (Ideal.span {p i}) u) :=
  Finset.prod_coe_sort S (fun i =>
    (canonicalSextic (Ideal.span {p i}) (hg i) ^ e i) (Ideal.Quotient.mk (Ideal.span {p i}) u))

theorem blockRow_union {ι : Type*} [DecidableEq ι]
    (p : ι → O) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hg : ∀ i, lambda ∉ Ideal.span {p i}) (S T : Finset ι) (hd : Disjoint S T)
    (e : ι → ℕ) (u : O) :
    blockRow p hg (S ∪ T) e u = blockRow p hg S e u * blockRow p hg T e u := by
  simp only [blockRow_eq_product, Finset.prod_union hd]

theorem blockRow_congr {ι : Type*} (p : ι → O) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hg : ∀ i, lambda ∉ Ideal.span {p i}) (S : Finset ι) (e f : ι → ℕ)
    (hef : ∀ i ∈ S, e i = f i) (u : O) : blockRow p hg S e u = blockRow p hg S f u := by
  simp only [blockRow_eq_product]
  exact Finset.prod_congr rfl (fun i hi => by rw [hef i hi])

theorem blockRow_one {ι : Type*} (p : ι → O) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hg : ∀ i, lambda ∉ Ideal.span {p i}) (S : Finset ι) (u : O) :
    blockRow p hg S (fun _ => 1) u = finiteSquarefreeRow (fun i => Ideal.span {p i}) hg S u := by
  simp only [blockRow_eq_product, pow_one, finiteSquarefreeRow]

theorem blockRow_five {ι : Type*} (p : ι → O) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hg : ∀ i, lambda ∉ Ideal.span {p i}) (S : Finset ι) (u : O) :
    blockRow p hg S (fun _ => 5) u = star (finiteSquarefreeRow (fun i => Ideal.span {p i}) hg S u) := by
  simp only [blockRow_eq_product, finiteSquarefreeRow, star_prod]
  apply Finset.prod_congr rfl
  intro i hi
  rw [MulChar.pow_apply' _ (by decide : (5 : ℕ) ≠ 0), canonicalSextic_conj_as_row_label]
  ring

theorem threeBlockRow_factor {ι : Type*} [DecidableEq ι]
    (p : ι → O) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hg : ∀ i, lambda ∉ Ideal.span {p i})
    (N P B : Finset ι) (hNP : Disjoint N P) (hNB : Disjoint N B) (hPB : Disjoint P B)
    (v : ι → ℕ) (ε₁ ε₂ : ι → Bool) (u : O) :
    blockRow p hg ((N ∪ P) ∪ cubeActiveSupport B v ε₁ ε₂)
      (threeBlockExponent N P v ε₁ ε₂) u =
    star (finiteSquarefreeRow (fun i => Ideal.span {p i}) hg N u) *
      finiteSquarefreeRow (fun i => Ideal.span {p i}) hg P u *
      blockRow p hg (cubeActiveSupport B v ε₁ ε₂)
        (fun i => (conductorExponent (parity (v i)) (ε₁ i) (ε₂ i)).val) u := by
  have hNC : Disjoint N (cubeActiveSupport B v ε₁ ε₂) := hNB.mono_right (Finset.filter_subset _ _)
  have hPC : Disjoint P (cubeActiveSupport B v ε₁ ε₂) := hPB.mono_right (Finset.filter_subset _ _)
  have hN : ∀ i ∈ N, threeBlockExponent N P v ε₁ ε₂ i = 5 := by
    intro i hi; simp [threeBlockExponent, hi]
  have hP : ∀ i ∈ P, threeBlockExponent N P v ε₁ ε₂ i = 1 := by
    intro i hi
    simp [threeBlockExponent, hi, show i ∉ N from fun hn => Finset.disjoint_left.mp hNP hn hi]
  have hC : ∀ i ∈ cubeActiveSupport B v ε₁ ε₂, threeBlockExponent N P v ε₁ ε₂ i =
      (conductorExponent (parity (v i)) (ε₁ i) (ε₂ i)).val := by
    intro i hi
    simp [threeBlockExponent,
      show i ∉ N from fun hn => Finset.disjoint_left.mp hNC hn hi,
      show i ∉ P from fun hp => Finset.disjoint_left.mp hPC hp hi]
  rw [blockRow_union p hg (N ∪ P) _ (Finset.disjoint_union_left.mpr ⟨hNC, hPC⟩),
    blockRow_union p hg N P hNP, blockRow_congr p hg N _ _ hN,
    blockRow_congr p hg P _ _ hP, blockRow_congr p hg _ _ _ hC,
    blockRow_five, blockRow_one]

theorem masked_block_radial_poisson_product {ι : Type*} [DecidableEq ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i, lambda ∉ Ideal.span {p i})
    (hc : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
    (M S : Finset ι) (e : ι → ℕ) (he : ∀ i ∈ S, e i ≠ 0) (he6 : ∀ i ∈ S, e i < 6)
    (W : 𝓢(ℝ, ℂ)) (lengthScale : ℝ) (hL : 0 < lengthScale) :
    (∑' z : O, rowCoprimeMask (fun i => Ideal.span {p i}) M z * blockRow p hg S e z *
      W (‖eisEmbedding z‖ ^ 2 / lengthScale)) =
    ((lengthScale : ℂ) * canonicalProductGauss (fun i : S => p i.val) (fun i => hp i.val)
      (columnPrimeCoprime p hcop S) (fun i => hg i.val) (fun i => e i.val) /
        (‖eisEmbedding (∏ i ∈ S, p i)‖ : ℂ)) *
      ∑ E ∈ M.powerset,
        let d := primeSubsetGenerator (fun i => Ideal.span {p i}) E
        ((UniqueFactorizationMonoid.moebius (∏ i ∈ E, Ideal.span {p i}) : ℂ) * blockRow p hg S e d /
          (‖eisEmbedding d‖ ^ 2 : ℝ)) *
          ∑' h : O, star (blockRow p hg S e h) * paperRadialFourier W
            (lengthScale * ‖eisEmbedding h‖ ^ 2 / (‖eisEmbedding d‖ ^ 2 * ‖eisEmbedding (∏ i ∈ S, p i)‖ ^ 2)) := by
  let Q := fun i : S => Ideal.span {p i.val}
  let q := fun i : S => p i.val
  let hQ := columnPrimeCoprime p hcop S
  let j := fun i : S => e i.val
  have h := canonical_masked_radial_poisson_collected (fun i => Ideal.span {p i}) hinj M
    Q hQ (fun i => hg i.val) (fun i => hc i.val) j
    (fun i => he i.val i.property) (fun i => he6 i.val i.property) W lengthScale hL
  have hn : ‖eisEmbedding (finitePrimeModulus Q)‖ = ‖eisEmbedding (∏ i ∈ S, p i)‖ := by
    rw [GaussGeneratorTransport.finitePrimeModulus_norm_eq_product q, Finset.prod_coe_sort]
  dsimp only at h
  rw [hn] at h
  have hrow : finiteSexticRow Q (fun i => hg i.val) j = blockRow p hg S e := rfl
  rw [hrow] at h
  rw [h]
  let a := fun E : Finset ι =>
    let d := primeSubsetGenerator (fun i => Ideal.span {p i}) E
    (UniqueFactorizationMonoid.moebius (∏ i ∈ E, Ideal.span {p i}) : ℂ) * blockRow p hg S e d /
      (‖eisEmbedding d‖ ^ 2 : ℝ)
  let F := fun E : Finset ι => fun t : ℝ =>
    let d := primeSubsetGenerator (fun i => Ideal.span {p i}) E
    paperRadialFourier W (lengthScale * t / (‖eisEmbedding d‖ ^ 2 * ‖eisEmbedding (∏ i ∈ S, p i)‖ ^ 2))
  have ht := GaussGeneratorTransport.gauss_weighted_finite_radial_sum_transport
    q (fun i => hp i.val) hQ (fun i => hg i.val) j M.powerset a F
  rw [hrow] at ht
  change ((lengthScale : ℂ) * canonicalNormalizedGauss Q hQ (fun i => hg i.val) j /
      (‖eisEmbedding (∏ i ∈ S, p i)‖ : ℂ)) * _ = _
  calc
    _ = ((lengthScale : ℂ) / (‖eisEmbedding (∏ i ∈ S, p i)‖ : ℂ)) *
      (canonicalNormalizedGauss Q hQ (fun i => hg i.val) j *
        ∑ E ∈ M.powerset, a E * ∑' h : O, star (blockRow p hg S e h) * F E (‖eisEmbedding h‖ ^ 2)) := by ring
    _ = _ := by rw [ht]; ring

def cubeBaseFactor {ι : Type*} [DecidableEq ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hg : ∀ i, lambda ∉ Ideal.span {p i}) (B : Finset ι)
    (v : ι → ℕ) (ε₁ ε₂ : ι → Bool) (d h : O) : ℂ :=
  let C := cubeActiveSupport B v ε₁ ε₂
  let e := fun i => (conductorExponent (parity (v i)) (ε₁ i) (ε₂ i)).val
  gaussBlock p hp hg C e * blockRow p hg C e d * star (blockRow p hg C e h)

def threeGaussRowFactor {ι : Type*} [DecidableEq ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i, lambda ∉ Ideal.span {p i}) (N P B : Finset ι)
    (v : ι → ℕ) (ε₁ ε₂ : ι → Bool) (C₁ C₂ : Finset ι → ℂ) (d h : O) : ℂ :=
  let S := (N ∪ P) ∪ cubeActiveSupport B v ε₁ ε₂
  let e := threeBlockExponent N P v ε₁ ε₂
  star (MixedCrossSeparation.columnCoefficient p hp hcop hg N * C₁ N) *
    (MixedCrossSeparation.columnCoefficient p hp hcop hg P * C₂ P) *
    canonicalProductGauss (fun i : S => p i.val) (fun i => hp i.val)
      (columnPrimeCoprime p hcop S) (fun i => hg i.val) (fun i => e i.val) *
    (blockRow p hg S e d * star (blockRow p hg S e h))

def cubeTransformedPair {ι : Type*} [DecidableEq ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i, lambda ∉ Ideal.span {p i}) (N P B : Finset ι)
    (v : ι → ℕ) (ε₁ ε₂ : ι → Bool) (C₁ C₂ : Finset ι → ℂ) (d h : O) : ℂ :=
  cubeBaseFactor p hp hg B v ε₁ ε₂ d h * quadraticCrossPhase p hg N P *
    quadraticCrossPhase p hg N (cubeOddSupport B v ε₁ ε₂) *
    quadraticCrossPhase p hg P (cubeOddSupport B v ε₁ ε₂) *
    star (FirstCauchyArithmetic.supportMobius (fun i => Ideal.span {p i}) N *
      FirstCauchyArithmetic.firstPassColumnMinus p hp hcop hg C₁ (d * crtLabel p B v ε₁ ε₂ true) N *
      star (finiteSquarefreeRow (fun i => Ideal.span {p i}) hg N h)) *
    (FirstCauchyArithmetic.supportMobius (fun i => Ideal.span {p i}) P *
      FirstCauchyArithmetic.firstPassColumnPlus p hp hcop hg C₂ (d * crtLabel p B v ε₁ ε₂ false) P *
      star (finiteSquarefreeRow (fun i => Ideal.span {p i}) hg P h))

theorem threeGaussRowFactor_eq_transformedPair {ι : Type*} [DecidableEq ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i, lambda ∉ Ideal.span {p i})
    (hc : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
    (hpr : ∀ i, lambda ^ 2 ∣ p i - 1)
    (N P B : Finset ι) (hNP : Disjoint N P) (hNB : Disjoint N B) (hPB : Disjoint P B)
    (v : ι → ℕ) (ε₁ ε₂ : ι → Bool) (C₁ C₂ : Finset ι → ℂ) (d h : O) :
    threeGaussRowFactor p hp hcop hg N P B v ε₁ ε₂ C₁ C₂ d h =
      cubeTransformedPair p hp hcop hg N P B v ε₁ ε₂ C₁ C₂ d h := by
  unfold threeGaussRowFactor
  dsimp only
  rw [a_weighted_three_cube_gauss p hp hcop hg hc hpr N P B hNP hNB hPB,
    threeBlockRow_factor p hg N P B hNP hNB hPB,
    threeBlockRow_factor p hg N P B hNP hNB hPB]
  simp only [cubeTransformedPair, cubeBaseFactor,
    FirstCauchyArithmetic.firstPassColumnMinus, FirstCauchyArithmetic.firstPassColumnPlus,
    finiteSquarefreeRow_mul, star_mul, star_star]
  ring

theorem a_weighted_three_block_radial_poisson {ι : Type*} [DecidableEq ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i, lambda ∉ Ideal.span {p i})
    (hc : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
    (hpr : ∀ i, lambda ^ 2 ∣ p i - 1)
    (M N P B : Finset ι) (hNP : Disjoint N P) (hNB : Disjoint N B) (hPB : Disjoint P B)
    (v : ι → ℕ) (ε₁ ε₂ : ι → Bool) (C₁ C₂ : Finset ι → ℂ)
    (W : 𝓢(ℝ, ℂ)) (lengthScale : ℝ) (hL : 0 < lengthScale) :
    let S := (N ∪ P) ∪ cubeActiveSupport B v ε₁ ε₂
    let e := threeBlockExponent N P v ε₁ ε₂
    star (MixedCrossSeparation.columnCoefficient p hp hcop hg N * C₁ N) *
      (MixedCrossSeparation.columnCoefficient p hp hcop hg P * C₂ P) *
      (∑' z : O, rowCoprimeMask (fun i => Ideal.span {p i}) M z * blockRow p hg S e z *
        W (‖eisEmbedding z‖ ^ 2 / lengthScale)) =
    ((lengthScale : ℂ) / (‖eisEmbedding (∏ i ∈ S, p i)‖ : ℂ)) *
      ∑ E ∈ M.powerset,
        let d := primeSubsetGenerator (fun i => Ideal.span {p i}) E
        ((UniqueFactorizationMonoid.moebius (∏ i ∈ E, Ideal.span {p i}) : ℂ) /
          (‖eisEmbedding d‖ ^ 2 : ℝ)) *
          ∑' h : O, paperRadialFourier W
            (lengthScale * ‖eisEmbedding h‖ ^ 2 / (‖eisEmbedding d‖ ^ 2 * ‖eisEmbedding (∏ i ∈ S, p i)‖ ^ 2)) *
              cubeTransformedPair p hp hcop hg N P B v ε₁ ε₂ C₁ C₂ d h := by
  dsimp only
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
  have he6 : ∀ i ∈ (N ∪ P) ∪ cubeActiveSupport B v ε₁ ε₂,
      threeBlockExponent N P v ε₁ ε₂ i < 6 := by
    intro i hi
    unfold threeBlockExponent
    split_ifs <;> first | omega | exact ZMod.val_lt _
  rw [masked_block_radial_poisson_product p hp hinj hcop hg hc M _ _ he he6 W lengthScale hL]
  simp_rw [← threeGaussRowFactor_eq_transformedPair p hp hcop hg hc hpr N P B hNP hNB hPB]
  simp only [Finset.mul_sum, ← tsum_mul_left]
  apply Finset.sum_congr rfl
  intro E hE
  apply tsum_congr
  intro h
  unfold threeGaussRowFactor
  dsimp only
  ring

end FirstPassCubeLabels

section
open MeasureTheory
open scoped FourierTransform SchwartzMap ContDiff
namespace LocalLogFourier

theorem coupled_positive_log_separation_schwartz
    {ι : Type*} [Fintype ι]
    (W : ι → ℝ → ℂ) (F : ℝ → ℂ) (a M : ι → ℝ)
    (hM : ∀ j, 0 ≤ M j)
    (hWwindow : ∀ j z, W j z ≠ 0 → |z| ≤ M j)
    (hFpos : ContDiffOn ℝ ∞ F (Set.Ioi 0))
    (A J : ℕ) (CF : ℝ) (hCF : 0 ≤ CF)
    (hEuler : ∀ i ≤ J + (volume : Measure ℝ).integrablePower,
      ∀ x : ℝ, 0 < x →
        (1 + x) ^ A * ‖eulerDeriv F i x‖ ≤ CF) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ R : ℝ, 0 < R →
      ∃ b : 𝓢(ℝ, ℂ),
        (∀ y : ι → ℝ,
          (∏ j : ι, W j (y j)) *
            F (R * Real.exp (∑ j : ι, a j * y j)) =
          ∫ t : ℝ,
            (∏ j : ι, W j (y j) *
              FourierBridge.logPhase t (a j * y j)) * b t) ∧
        Integrable (fun t : ℝ => (1 + ‖t‖) ^ J * ‖b t‖) volume ∧
        (1 + R) ^ A *
          (∫ t : ℝ, (1 + ‖t‖) ^ J * ‖b t‖) ≤ C := by
  classical
  let T : ℝ := ∑ j : ι, |a j| * M j
  have hT : 0 ≤ T := by
    dsimp [T]
    apply Finset.sum_nonneg
    intro j hj
    exact mul_nonneg (abs_nonneg _) (hM j)
  let K : ℕ := J + (volume : Measure ℝ).integrablePower
  let Lwin : ℝ := T + 1
  let m : ℝ := Real.exp (-Lwin)
  have hL : 0 ≤ Lwin := by dsimp [Lwin]; linarith
  have hm : 0 < m := Real.exp_pos _
  have hm1 : m ≤ 1 := by
    dsimp [m]
    simpa using (Real.exp_le_exp.mpr (show -Lwin ≤ 0 by linarith))
  obtain ⟨V, CW, hVc, hVs, hVone, hCW, hVderiv, hwindow⟩ :=
    FourierBridge.exists_complex_smooth_cutoff_with_derivative_bounds T K hT
  let P : ℝ := momentConstant K Lwin CW CF
  let B : ℝ := (2 : ℝ) ^ J *
    (FourierBridge.coefficientMomentBound 0 P +
      FourierBridge.coefficientMomentBound J P)
  let C : ℝ := B / m ^ A
  have hP : 0 ≤ P := momentConstant_nonneg K Lwin CW CF hL hCW hCF
  have hB : 0 ≤ B := by
    dsimp [B]
    exact mul_nonneg (by positivity)
      (add_nonneg
        (FourierBridge.coefficientMomentBound_nonneg 0 P hP)
        (FourierBridge.coefficientMomentBound_nonneg J P hP))
  have hC : 0 ≤ C := by dsimp [C]; positivity
  refine ⟨C, hC, ?_⟩
  intro R hR
  let b : 𝓢(ℝ, ℂ) := 𝓕 (positiveLogProfile V F R hVc hVs hFpos hR)
  refine ⟨b, ?_, ?_, ?_⟩
  · intro y
    have hactive : (∏ j : ι, W j (y j)) ≠ 0 →
        V (∑ j : ι, a j * y j) = 1 :=
      FourierBridge.coupled_cutoff_active W V a y M hWwindow
        (by simpa [T] using hVone)
    simpa [b] using coupled_positive_log_separation W F V R a y
      hVc hVs hFpos hR hactive
  · exact AnalyticBridge.schwartz_fourier_one_plus_integrable
      (positiveLogProfile V F R hVc hVs hFpos hR) J
  · have hwindow' : ∀ s,
        (∃ i ≤ K, ‖iteratedFDeriv ℝ i V s‖ ≠ 0) →
          m ≤ Real.exp s ∧ |s| ≤ Lwin := by
      intro s hs
      exact ⟨(hwindow s hs).1, (hwindow s hs).2.2⟩
    have hbound := positive_log_fourier_bound V F R m Lwin CW CF A J
      hVc hVs hFpos hR hm hm1 hL hCW hCF
      (by simpa [K] using hVderiv)
      (by simpa only [K] using hwindow')
      (by simpa [K] using hEuler)
    simpa [C, B, P, b, K, Lwin, m] using hbound

end LocalLogFourier

namespace EisensteinSchwartzPoisson

theorem paperRadialFourier_log_separation_schwartz
    {ι : Type*} [Fintype ι]
    (W : 𝓢(ℝ, ℂ)) (V : ι → ℝ → ℂ) (a M : ι → ℝ)
    (hM : ∀ j, 0 ≤ M j)
    (hVwindow : ∀ j z, V j z ≠ 0 → |z| ≤ M j)
    (A J : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ R : ℝ, 0 < R →
      ∃ b : 𝓢(ℝ, ℂ),
        (∀ y : ι → ℝ,
          (∏ j : ι, V j (y j)) *
            paperRadialFourier W (R * Real.exp (∑ j : ι, a j * y j)) =
          ∫ t : ℝ,
            (∏ j : ι, V j (y j) *
              FourierBridge.logPhase t (a j * y j)) * b t) ∧
        Integrable (fun t : ℝ => (1 + ‖t‖) ^ J * ‖b t‖) volume ∧
        (1 + R) ^ A *
          (∫ t : ℝ, (1 + ‖t‖) ^ J * ‖b t‖) ≤ C := by
  obtain ⟨CF, hCF, hEuler⟩ := paperRadialFourier_euler_bound W A
    (J + (MeasureTheory.volume : MeasureTheory.Measure ℝ).integrablePower)
  exact LocalLogFourier.coupled_positive_log_separation_schwartz V (paperRadialFourier W)
    a M hM hVwindow (paperRadialFourier_contDiffOn W) A J CF hCF hEuler

end EisensteinSchwartzPoisson
end

open scoped Classical BigOperators
open AddChar MulChar
namespace LocalReflectionBrackets

section
abbrev O := ActualEisensteinCubic.O

variable {F : Type*} [Field F] [Fintype F]

def rootCard (F : Type*) [Fintype F] : ℝ := Real.sqrt (Fintype.card F)

theorem rootCard_pos : 0 < rootCard F := by
  apply Real.sqrt_pos.mpr
  exact_mod_cast Fintype.card_pos_iff.mpr ⟨(0 : F)⟩

theorem rootCard_sq : rootCard F ^ 2 = (Fintype.card F : ℝ) := Real.sq_sqrt (by positivity)

def tau (χ : MulChar F ℂ) (ψ : AddChar F ℂ) (j : ℕ) : ℂ :=
  (rootCard F : ℂ)⁻¹ * gaussSum (χ ^ j) ψ

def bracket (χ : MulChar F ℂ) (j : ℕ) (x : F) : ℂ :=
  if j = 4 then
    (rootCard F : ℂ)⁻¹ * (-1 + (Fintype.card F : ℂ) * if x = 0 then 1 else 0)
  else if j = 0 then (rootCard F : ℂ)⁻¹ * (χ ^ 2)⁻¹ x
  else (χ ^ (j + 2))⁻¹ x

def phase (χ : MulChar F ℂ) (ψ : AddChar F ℂ) (j : ℕ) (ε : Fˣ) : ℂ :=
  if j = 4 then tau χ (ψ.mulShift (-1)) 4
  else if j = 0 then -tau χ ψ 2 * (χ ^ 2)⁻¹ ε
  else tau χ (ψ.mulShift (-1)) j * tau χ ψ (j + 2) * (χ ^ (j + 2))⁻¹ ε

theorem norm_tau (χ : MulChar F ℂ) (ψ : AddChar F ℂ) (j : ℕ)
    (hχ : χ ^ j ≠ 1) (hψ : ψ.IsPrimitive) : ‖tau χ ψ j‖ = 1 :=
  ShortDraftGauss.norm_normalized_gaussSum (χ ^ j) ψ hχ hψ

theorem bracket_four_split (χ : MulChar F ℂ) (x : F) :
    bracket χ 4 x = -(rootCard F : ℂ)⁻¹ + (rootCard F : ℂ) * if x = 0 then 1 else 0 := by
  have hr : (rootCard F : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt rootCard_pos)
  have hsq : (rootCard F : ℂ) ^ 2 = (Fintype.card F : ℂ) := by exact_mod_cast (rootCard_sq (F := F))
  simp only [bracket, ↓reduceIte]
  rw [← hsq]
  field_simp

theorem bracket_four_cube_split (χ : MulChar F ℂ) (n b : F) :
    bracket χ 4 (n * b ^ 3) = -(rootCard F : ℂ)⁻¹ +
      (rootCard F : ℂ) * (if n = 0 then 1 else 0) +
      (rootCard F : ℂ) * (if n ≠ 0 ∧ b = 0 then 1 else 0) := by
  rw [bracket_four_split]
  by_cases hn : n = 0 <;> by_cases hb : b = 0 <;> simp [hn, hb]

theorem bracket_zero_mask (χ : MulChar F ℂ) (j : ℕ) (hj : j ≠ 4) :
    bracket χ j 0 = 0 := by simp [bracket, hj]

theorem norm_bracket_nonexceptional (χ : MulChar F ℂ) (j : ℕ)
    (hj4 : j ≠ 4) (hj0 : j ≠ 0) (x : F) :
    ‖bracket χ j x‖ = if x = 0 then 0 else 1 := by
  simp only [bracket, if_neg hj4, if_neg hj0]
  by_cases hx : x = 0
  · simp [hx]
  · rw [if_neg hx]
    exact FiniteRayExpansion.norm_char_unit ((χ ^ (j + 2))⁻¹) (Units.mk0 x hx)

theorem norm_bracket_zero (χ : MulChar F ℂ) (x : F) :
    ‖bracket χ 0 x‖ = (rootCard F)⁻¹ * if x = 0 then 0 else 1 := by
  simp only [bracket, show (0 : ℕ) ≠ 4 by decide, ↓reduceIte, norm_mul, norm_inv,
    Complex.norm_real, Real.norm_of_nonneg rootCard_pos.le]
  congr 1
  by_cases hx : x = 0
  · simp [hx]
  · rw [if_neg hx]
    exact FiniteRayExpansion.norm_char_unit ((χ ^ 2)⁻¹) (Units.mk0 x hx)

theorem norm_bracket_four_nonzero (χ : MulChar F ℂ) (x : F) (hx : x ≠ 0) :
    ‖bracket χ 4 x‖ = (rootCard F)⁻¹ := by
  rw [bracket_four_split]
  simp [hx, Complex.norm_real, Real.norm_of_nonneg rootCard_pos.le]

theorem norm_bracket_four_zero (χ : MulChar F ℂ) :
    ‖bracket χ 4 (0 : F)‖ = ((Fintype.card F : ℝ) - 1) / rootCard F := by
  have hq : (1 : ℝ) ≤ Fintype.card F := by exact_mod_cast Fintype.card_pos_iff.mpr ⟨(0 : F)⟩
  simp only [bracket, ↓reduceIte, mul_one, norm_mul, norm_inv, Complex.norm_real,
    Real.norm_of_nonneg rootCard_pos.le]
  have heq : (-1 + (Fintype.card F : ℂ)) = (((Fintype.card F : ℝ) - 1 : ℝ) : ℂ) := by push_cast; ring
  rw [heq, Complex.norm_real, Real.norm_of_nonneg (sub_nonneg.mpr hq)]
  ring

end

section
variable {F : Type*} [Field F] [Fintype F]

omit [Fintype F] in
theorem shifted_power_nontrivial (χ : MulChar F ℂ) (h6 : χ ^ 6 = 1)
    (hn : ∀ k : ℕ, k ≠ 0 → k < 6 → χ ^ k ≠ 1)
    (j : ℕ) (hj0 : j ≠ 0) (hj6 : j < 6) (hj4 : j ≠ 4) : χ ^ (j + 2) ≠ 1 := by
  by_cases hj : j = 5
  · subst j
    have heq : χ ^ (5 + 2) = χ ^ 1 := by
      rw [show (5 + 2 : ℕ) = 6 + 1 by decide, pow_add, h6, one_mul]
    rw [heq]
    exact hn 1 (by decide) (by decide)
  · exact hn (j + 2) (by omega) (by omega)

theorem phase_norm (χ : MulChar F ℂ) (ψ : AddChar F ℂ)
    (h6 : χ ^ 6 = 1) (hn : ∀ k : ℕ, k ≠ 0 → k < 6 → χ ^ k ≠ 1)
    (hψ : ψ.IsPrimitive) (j : ℕ) (hj6 : j < 6) (ε : Fˣ) :
    ‖phase χ ψ j ε‖ = 1 := by
  have hψminus : (ψ.mulShift (-1)).IsPrimitive :=
    AddChar.IsPrimitive.of_ne_one (hψ (a := (-1 : F)) (by simp))
  by_cases hj4 : j = 4
  · subst j
    simp only [phase, ↓reduceIte]
    exact norm_tau χ _ 4 (hn 4 (by decide) (by decide)) hψminus
  by_cases hj0 : j = 0
  · subst j
    simp only [phase, if_neg hj4, ↓reduceIte, norm_mul, norm_neg]
    rw [norm_tau χ ψ 2 (hn 2 (by decide) (by decide)) hψ,
      FiniteRayExpansion.norm_char_unit]
    norm_num
  · simp only [phase, if_neg hj4, if_neg hj0, norm_mul]
    rw [norm_tau χ _ j (hn j hj0 hj6) hψminus,
      norm_tau χ ψ (j + 2) (shifted_power_nontrivial χ h6 hn j hj0 hj6 hj4) hψ,
      FiniteRayExpansion.norm_char_unit]
    norm_num

end

open ActualEisensteinCubic

noncomputable local instance quotientField (P : Ideal O) [P.IsMaximal] : Field (O ⧸ P) := Ideal.Quotient.field P

noncomputable local instance quotientFintype (P : Ideal O) [P.IsMaximal] : Fintype (O ⧸ P) := Fintype.ofFinite _

theorem canonical_phase_norm (P : Ideal O) [P.IsMaximal]
    (hgood : lambda ∉ P) (hchar : ringChar (O ⧸ P) ≠ 2)
    (ψ : AddChar (O ⧸ P) ℂ) (hψ : ψ.IsPrimitive)
    (j : ℕ) (hj6 : j < 6) (ε : (O ⧸ P)ˣ) :
    ‖phase (canonicalSextic P hgood) ψ j ε‖ = 1 := by
  let : Field (O ⧸ P) := Ideal.Quotient.field P
  exact phase_norm (canonicalSextic P hgood) ψ (canonicalSextic_pow_six P hgood)
    (fun k hk0 hk6 => canonicalSextic_pow_ne_one P hgood hchar hk0 hk6) hψ j hj6 ε

end LocalReflectionBrackets

open scoped Classical BigOperators
open AddChar MulChar
namespace LocalReflectionBrackets

variable {F : Type*} [Field F] [Fintype F]

def activeRow (χ : MulChar F ℂ) (ψ : AddChar F ℂ) (j : ℕ) (σ ε : Fˣ) (x : F) : ℂ :=
  (Fintype.card F : ℂ)⁻¹ *
    ∑ h : Fˣ, (∑ t : F, (χ ^ j) t * ψ (-(h * t))) *
      (((χ⁻¹) ^ 2) (σ * h)) * ψ (((ε : F) * x) * ((h⁻¹ : Fˣ) : F))

open ActualEisensteinCubic
noncomputable local instance quotientFieldNormalized (P : Ideal O) [P.IsMaximal] : Field (O ⧸ P) := Ideal.Quotient.field P
noncomputable local instance quotientFintypeNormalized (P : Ideal O) [P.IsMaximal] : Fintype (O ⧸ P) := Fintype.ofFinite _

theorem canonical_A5_normalized (P : Ideal O) [P.IsMaximal]
    (hgood : lambda ∉ P) (hchar : ringChar (O ⧸ P) ≠ 2)
    (ψ : AddChar (O ⧸ P) ℂ) (hψ : ψ.IsPrimitive)
    (j : ℕ) (hj6 : j < 6) (σ ε : (O ⧸ P)ˣ) (x : O ⧸ P) :
    activeRow (canonicalSextic P hgood) ψ j σ ε x =
      (((canonicalSextic P hgood)⁻¹) ^ 2) σ *
        phase (canonicalSextic P hgood) ψ j ε * bracket (canonicalSextic P hgood) j x := by
  let χ := canonicalSextic P hgood
  have hψne : ψ ≠ 1 := by simpa only [AddChar.mulShift_one] using hψ (a := 1) one_ne_zero
  have hr : (rootCard (O ⧸ P) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt rootCard_pos)
  have hsq : (rootCard (O ⧸ P) : ℂ) ^ 2 = (Fintype.card (O ⧸ P) : ℂ) := by
    exact_mod_cast (rootCard_sq (F := O ⧸ P))
  by_cases hj0 : j = 0
  · subst j
    have hh := canonical_A5_jzero_active P hgood hchar ψ hψne σ ε x
    simp only [Nat.card_eq_fintype_card] at hh
    rw [activeRow, hh]
    simp only [phase, bracket, tau, show (0 : ℕ) ≠ 4 by decide, ↓reduceIte]
    rw [← hsq]
    field_simp
  by_cases hj4 : j = 4
  · subst j
    have hh := canonical_A5_jfour P hgood hchar ψ hψne σ ε x
    simp only [Nat.card_eq_fintype_card] at hh
    rw [activeRow, hh]
    have hqNat : 1 ≤ Fintype.card (O ⧸ P) := Fintype.card_pos_iff.mpr ⟨0⟩
    have hcardunits : (Fintype.card (O ⧸ P)ˣ : ℂ) = (Fintype.card (O ⧸ P) : ℂ) - 1 := by
      rw [Fintype.card_units, Nat.cast_sub hqNat, Nat.cast_one]
    have hsum : (if (ε : O ⧸ P) * x = 0 then (Fintype.card (O ⧸ P)ˣ : ℂ) else -1) =
        -1 + (Fintype.card (O ⧸ P) : ℂ) * if x = 0 then 1 else 0 := by
      by_cases hx : x = 0
      · simp [hx, hcardunits]
        ring
      · simp [hx, mul_ne_zero (Units.ne_zero ε) hx]
    rw [hsum]
    simp only [phase, bracket, tau,  ↓reduceIte]
    rw [← hsq]
    field_simp
  · have hh := canonical_A5_nonexceptional P hgood hchar ψ j hj0 hj6 hj4 σ ε x
    simp only [Nat.card_eq_fintype_card] at hh
    rw [activeRow, hh]
    simp only [phase, bracket, tau, if_neg hj4, if_neg hj0]
    rw [← hsq]
    field_simp

theorem canonical_A5_norm_eq_bracket (P : Ideal O) [P.IsMaximal]
    (hgood : lambda ∉ P) (hchar : ringChar (O ⧸ P) ≠ 2)
    (ψ : AddChar (O ⧸ P) ℂ) (hψ : ψ.IsPrimitive)
    (j : ℕ) (hj6 : j < 6) (σ ε : (O ⧸ P)ˣ) (x : O ⧸ P) :
    ‖activeRow (canonicalSextic P hgood) ψ j σ ε x‖ =
      ‖bracket (canonicalSextic P hgood) j x‖ := by
  rw [canonical_A5_normalized P hgood hchar ψ hψ j hj6 σ ε x,
    norm_mul, norm_mul, canonical_phase_norm P hgood hchar ψ hψ j hj6 ε,
    FiniteRayExpansion.norm_char_unit, one_mul, one_mul]

theorem canonical_bracket_four_cube_split (P : Ideal O) [P.IsMaximal]
    (hgood : lambda ∉ P) (n b : O) :
    bracket (canonicalSextic P hgood) 4 (Ideal.Quotient.mk P (n * b ^ 3)) =
      -(rootCard (O ⧸ P) : ℂ)⁻¹ + (rootCard (O ⧸ P) : ℂ) * (if n ∈ P then 1 else 0) +
      (rootCard (O ⧸ P) : ℂ) * (if n ∉ P ∧ b ∈ P then 1 else 0) := by
  rw [map_mul, map_pow, bracket_four_cube_split]
  simp only [ne_eq, Ideal.Quotient.eq_zero_iff_mem]

end LocalReflectionBrackets

end

end OAI

end


