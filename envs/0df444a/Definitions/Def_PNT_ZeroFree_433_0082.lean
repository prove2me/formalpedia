-- Prove2me | Definitions.Def_PNT_ZeroFree_433_0082
-- name    : PNT_ZeroFree_433_0082
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-11T10:45:23.937565+00:00
-- url     : https://prove2.me/theorems/d68f1180-de3e-4fd6-b059-477bc89c6751
-- title:
--   Zero-free region foundations: QuadraticSieve.GcdReduction [0082]
-- statement:
--   Definitions and proved supporting lemmas from the following source modules:
--
--   - OAI.NumberTheory.DirichletL.QuadraticSieve.GcdReduction
--
--   These declarations form part of the analytic and arithmetic foundations of the Dirichlet L-function nonvanishing argument in the half-plane Re(s) > 7/8. The original namespaces and hypotheses are retained. The code is ported to Lean 4.33.1 and the pinned Mathlib environment; every included lemma has a complete proof.
-- source:
--   https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/QuadraticSieve/GcdReduction.lean#L77-L672

import Definitions.Def_PNT_ZeroFree_433_0081

/- Supporting source modules for the zero-free-region proof.
Ported and checked against Lean 4.33.1 / Mathlib 0df444a.
Original source attribution:
https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/QuadraticSieve/GcdReduction.lean#L77-L672
-/

set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

-- Source module: OAI.NumberTheory.DirichletL.QuadraticSieve.GcdReduction
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
open scoped BigOperators

open scoped BigOperators Classical
namespace CanonicalQuadraticSieve
open ActualEisensteinCubic CompletedGauss FiniteSieveOperator IdealCoprimeSieveOperator DivisorBlockCauchy

def gcdPool {n : Type*} [Fintype n] (cols : n → Ideal O) : Finset (Ideal O) :=
  Finset.univ.image (fun p : n × n => gcd (cols p.1) (cols p.2))

theorem mem_gcdPool {n : Type*} [Fintype n] (cols : n → Ideal O) (j k : n) :
    gcd (cols j) (cols k) ∈ gcdPool cols :=
  Finset.mem_image.mpr ⟨(j, k), Finset.mem_univ _, rfl⟩

theorem gcdPool_ne_zero {n : Type*} [Fintype n] (cols : n → Ideal O)
    (hcols : ∀ j, cols j ≠ 0) (D : Ideal O) (hD : D ∈ gcdPool cols) : D ≠ 0 := by
  obtain ⟨⟨j, k⟩, _, rfl⟩ := Finset.mem_image.mp hD
  intro h
  have hd := gcd_dvd_left (cols j) (cols k)
  rw [h, zero_dvd_iff] at hd
  exact hcols j hd

theorem energy_eq_gcd_blocks {m n : Type*} [Fintype m] [Fintype n]
    (rows : m → Ideal O) (cols : n → Ideal O) (a : n → ℂ) :
    ((∑ i, ‖∑ j, quadraticRow (cols j) (primaryGenerator (rows i)) * a j‖ ^ 2 : ℝ) : ℂ) =
      ∑ D ∈ gcdPool cols, gcdBlock D rows cols a := by
  have hp (i : m) (j k : n) : (∑ D ∈ gcdPool cols, gcdTerm D rows cols a i j k) =
      star (quadraticRow (cols j) (primaryGenerator (rows i)) * a j) *
        (quadraticRow (cols k) (primaryGenerator (rows i)) * a k) := by
    rw [Finset.sum_eq_single (gcd (cols j) (cols k))]
    · simp only [gcdTerm, ite_true]
    · intro D hD hne
      exact if_neg (Ne.symm hne)
    · exact fun h => (h (mem_gcdPool cols j k)).elim
  have hi (i : m) : (∑ D ∈ gcdPool cols, ∑ j, ∑ k, gcdTerm D rows cols a i j k) =
      ∑ j, ∑ k, star (quadraticRow (cols j) (primaryGenerator (rows i)) * a j) *
        (quadraticRow (cols k) (primaryGenerator (rows i)) * a k) := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j _
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl (fun k _ => hp i j k)
  simp only [gcdBlock]
  rw [Finset.sum_comm]
  simp_rw [hi]
  push_cast
  apply Finset.sum_congr rfl
  intro i _
  simpa only [Complex.ofReal_pow] using CoprimeSieveOperator.square_norm_sum
    (fun j => quadraticRow (cols j) (primaryGenerator (rows i)) * a j)

theorem energy_le_gcd_blocks {m n : Type*} [Fintype m] [Fintype n]
    (rows : m → Ideal O) (cols : n → Ideal O) (a : n → ℂ) :
    (∑ i, ‖∑ j, quadraticRow (cols j) (primaryGenerator (rows i)) * a j‖ ^ 2) ≤
      ∑ D ∈ gcdPool cols, ‖gcdBlock D rows cols a‖ := by
  have he := congrArg norm (energy_eq_gcd_blocks rows cols a)
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)] at he
  rw [he]
  exact norm_sum_le _ _

theorem highKernel_large_gcd_blocks {m n : Type*} [Fintype m] [Fintype n]
    [DecidableEq m] [DecidableEq n]
    (ε : ℝ) (hε : 0 < ε) (S : Finset (Ideal O)) (G : ℝ) (hG : 0 < G)
    (hS : ∀ D ∈ S, G ≤ (Ideal.absNorm D : ℝ))
    (rows : m → Ideal O) (cols : n → Ideal O)
    (hr : Function.Injective rows) (hc : Function.Injective cols)
    (M N K : ℝ) (hN : 1 ≤ N) (hrows : ∀ i, rows i ∈ highKernelRange M K)
    (hcols : ∀ j, Admissible (cols j) ∧ (Ideal.absNorm (cols j) : ℝ) ≤ N) (a : n → ℂ) :
    (∑ D ∈ S, ‖gcdBlock D rows cols a‖) ≤
      highKernelNorm M (N / G) K * (supportConstant ε hε * divisorConstant ε hε) *
        (N ^ ε) ^ 2 * ∑ j, ‖a j‖ ^ 2 := by
  have hfac : 0 ≤ supportConstant ε hε * N ^ ε :=
    mul_nonneg (supportConstant_pos ε hε).le (Real.rpow_nonneg (by linarith) _)
  have hB : 0 ≤ highKernelNorm M (N / G) K := highKernelNorm_nonneg _ _ _
  have hb (D : Ideal O) (hD : D ∈ S) : ‖gcdBlock D rows cols a‖ ≤
      highKernelNorm M (N / G) K * (supportConstant ε hε * N ^ ε) *
        ∑ j, ‖if D ∣ cols j then a j else 0‖ ^ 2 := by
    have hn : 0 < (Ideal.absNorm D : ℝ) := hG.trans_le (hS D hD)
    have hD0 : D ≠ 0 := by intro hz; simp [hz] at hn
    have hmono := highKernelNorm_mono (M := M) (K := K) (M' := M) (K' := K) le_rfl
      (div_le_div_of_nonneg_left (by linarith : 0 ≤ N) hG (hS D hD)) le_rfl
    exact (highKernel_gcdBlock_bound ε hε D hD0 rows cols hr hc M N K hN hrows hcols a).trans
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hmono hfac) (by positivity))
  calc
    _ ≤ ∑ D ∈ S, highKernelNorm M (N / G) K * (supportConstant ε hε * N ^ ε) *
        ∑ j, ‖if D ∣ cols j then a j else 0‖ ^ 2 := Finset.sum_le_sum hb
    _ = highKernelNorm M (N / G) K * (supportConstant ε hε * N ^ ε) *
        ∑ D ∈ S, ∑ j, ‖if D ∣ cols j then a j else 0‖ ^ 2 := (Finset.mul_sum ..).symm
    _ ≤ highKernelNorm M (N / G) K * (supportConstant ε hε * N ^ ε) *
        ((divisorConstant ε hε * N ^ ε) * ∑ j, ‖a j‖ ^ 2) :=
      mul_le_mul_of_nonneg_left
        (divisor_mask_energy_small_power ε hε S cols (fun j => (hcols j).1.1) N (fun j => (hcols j).2) a)
        (mul_nonneg hB hfac)
    _ = _ := by ring

theorem highKernel_energy_gcd_reduction {m n : Type*} [Fintype m] [Fintype n]
    [DecidableEq m] [DecidableEq n]
    (ε : ℝ) (hε : 0 < ε) (G : ℝ) (hG : 0 < G)
    (rows : m → Ideal O) (cols : n → Ideal O)
    (hr : Function.Injective rows) (hc : Function.Injective cols)
    (M N K : ℝ) (hN : 1 ≤ N) (hrows : ∀ i, rows i ∈ highKernelRange M K)
    (hcols : ∀ j, Admissible (cols j) ∧ (Ideal.absNorm (cols j) : ℝ) ≤ N) (a : n → ℂ) :
    (∑ i, ‖∑ j, quadraticRow (cols j) (primaryGenerator (rows i)) * a j‖ ^ 2) ≤
      (∑ D ∈ (gcdPool cols).filter (fun D => (Ideal.absNorm D : ℝ) ≤ G), ‖gcdBlock D rows cols a‖) +
      highKernelNorm M (N / G) K * (supportConstant ε hε * divisorConstant ε hε) *
        (N ^ ε) ^ 2 * ∑ j, ‖a j‖ ^ 2 := by
  have he := energy_le_gcd_blocks rows cols a
  rw [← Finset.sum_filter_add_sum_filter_not (gcdPool cols) (fun D => (Ideal.absNorm D : ℝ) ≤ G)] at he
  exact he.trans (add_le_add le_rfl (highKernel_large_gcd_blocks ε hε _ G hG
    (fun D hD => (lt_of_not_ge (Finset.mem_filter.mp hD).2).le)
    rows cols hr hc M N K hN hrows hcols a))

end CanonicalQuadraticSieve

namespace FiniteSieveRestriction

def sectorCoefficient {n r : Type*} [DecidableEq r] (σ : n → r) (c : r) (a : n → ℂ) (j : n) : ℂ :=
  if σ j = c then a j else 0

theorem sectorCoefficient_energy {n r : Type*} [Fintype n] [Fintype r] [DecidableEq r]
    (σ : n → r) (a : n → ℂ) :
    (∑ c, ∑ j, ‖sectorCoefficient σ c a j‖ ^ 2) = ∑ j, ‖a j‖ ^ 2 := by
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  rw [Finset.sum_eq_single (σ j)]
  · simp [sectorCoefficient]
  · intro c hc hne
    simp [sectorCoefficient, Ne.symm hne]
  · simp

private theorem norm_sum_square_card {r : Type*} [Fintype r] (f : r → ℂ) :
    ‖∑ c, f c‖ ^ 2 ≤ (Fintype.card r : ℝ) * ∑ c, ‖f c‖ ^ 2 := by
  have h := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun _ : r => (1 : ℝ)) (fun c => ‖f c‖)
  have hh : ‖∑ c, f c‖ ^ 2 ≤ (∑ c, ‖f c‖) ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) (norm_sum_le _ _) 2
  exact hh.trans (by simpa using h)

theorem sector_energy_bound {m n r : Type*} [Fintype m] [Fintype n] [Fintype r] [DecidableEq r]
    (A : Matrix m n ℂ) (σ : n → r) (a : n → ℂ) :
    (∑ i, ‖∑ j, A i j * a j‖ ^ 2) ≤
      (Fintype.card r : ℝ) * ∑ c, ∑ i, ‖∑ j, A i j * sectorCoefficient σ c a j‖ ^ 2 := by
  have hi (i : m) : (∑ j, A i j * a j) = ∑ c, ∑ j, A i j * sectorCoefficient σ c a j := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j _
    rw [← Finset.mul_sum, Finset.sum_eq_single (σ j)]
    · simp [sectorCoefficient]
    · intro c hc hne
      simp [sectorCoefficient, Ne.symm hne]
    · simp
  calc
    _ ≤ ∑ i, (Fintype.card r : ℝ) * ∑ c, ‖∑ j, A i j * sectorCoefficient σ c a j‖ ^ 2 := by
      apply Finset.sum_le_sum
      intro i _
      rw [hi]
      exact norm_sum_square_card _
    _ = _ := by rw [← Finset.mul_sum, Finset.sum_comm]
end FiniteSieveRestriction

namespace CanonicalQuadraticSieve
open ActualEisensteinCubic CompletedGauss IdealCoprimeSieveOperator DivisorBlockCauchy
open FiniteSieveRestriction

def columnRay (I : Ideal O) : EisensteinEPrimaryPhase.Coord := ActualEisensteinCoordinates.residue (primaryGenerator I)

def rayGcdBlock {m n : Type*} [Fintype m] [Fintype n]
    (D : Ideal O) (c : EisensteinEPrimaryPhase.Coord)
    (rows : m → Ideal O) (cols : n → Ideal O) (a : n → ℂ) : ℂ :=
  gcdBlock D rows cols (sectorCoefficient (fun j => columnRay (cols j)) c a)

theorem rayGcdBlock_eq {m n : Type*} [Fintype m] [Fintype n]
    (D : Ideal O) (c : EisensteinEPrimaryPhase.Coord)
    (rows : m → Ideal O) (cols : n → Ideal O) (a : n → ℂ) :
    rayGcdBlock D c rows cols a = ∑ i, ∑ j, ∑ k,
      if gcd (cols j) (cols k) = D ∧ columnRay (cols j) = c ∧ columnRay (cols k) = c then
        star (quadraticRow (cols j) (primaryGenerator (rows i)) * a j) *
          (quadraticRow (cols k) (primaryGenerator (rows i)) * a k) else 0 := by
  unfold rayGcdBlock gcdBlock gcdTerm sectorCoefficient
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro k _
  by_cases hg : gcd (cols j) (cols k) = D <;>
    by_cases hj : columnRay (cols j) = c <;> by_cases hk : columnRay (cols k) = c <;>
      simp only [hg, hj, hk, ↓reduceIte, true_and, false_and, and_false,
        mul_zero, zero_mul, star_zero]

theorem highKernel_energy_ray_gcd_reduction {m n : Type*} [Fintype m] [Fintype n]
    [DecidableEq m] [DecidableEq n]
    (ε : ℝ) (hε : 0 < ε) (G : ℝ) (hG : 0 < G)
    (rows : m → Ideal O) (cols : n → Ideal O)
    (hr : Function.Injective rows) (hc : Function.Injective cols)
    (M N K : ℝ) (hN : 1 ≤ N) (hrows : ∀ i, rows i ∈ highKernelRange M K)
    (hcols : ∀ j, Admissible (cols j) ∧ (Ideal.absNorm (cols j) : ℝ) ≤ N) (a : n → ℂ) :
    (∑ i, ‖∑ j, quadraticRow (cols j) (primaryGenerator (rows i)) * a j‖ ^ 2) ≤
      16 * ((∑ c : EisensteinEPrimaryPhase.Coord,
        ∑ D ∈ (gcdPool cols).filter (fun D => (Ideal.absNorm D : ℝ) ≤ G), ‖rayGcdBlock D c rows cols a‖) +
        highKernelNorm M (N / G) K * (supportConstant ε hε * divisorConstant ε hε) *
          (N ^ ε) ^ 2 * ∑ j, ‖a j‖ ^ 2) := by
  let σ : n → EisensteinEPrimaryPhase.Coord := fun j => columnRay (cols j)
  let C := highKernelNorm M (N / G) K * (supportConstant ε hε * divisorConstant ε hε) * (N ^ ε) ^ 2
  have hs := sector_energy_bound
    (fun i j => quadraticRow (cols j) (primaryGenerator (rows i))) σ a
  have hcard : Fintype.card EisensteinEPrimaryPhase.Coord = 16 := by decide
  rw [hcard] at hs
  norm_num only [Nat.cast_ofNat] at hs
  apply hs.trans
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  calc
    _ ≤ ∑ c : EisensteinEPrimaryPhase.Coord,
        ((∑ D ∈ (gcdPool cols).filter (fun D => (Ideal.absNorm D : ℝ) ≤ G),
          ‖rayGcdBlock D c rows cols a‖) + C * ∑ j, ‖sectorCoefficient σ c a j‖ ^ 2) := by
      apply Finset.sum_le_sum
      intro c _
      exact highKernel_energy_gcd_reduction ε hε G hG rows cols hr hc M N K hN hrows hcols
        (sectorCoefficient σ c a)
    _ = _ := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, sectorCoefficient_energy]

end CanonicalQuadraticSieve

namespace FiniteSieveOperator

theorem quadratic_form_bound {n : Type*} [Fintype n] [DecidableEq n]
    (H : Matrix n n ℂ) (a : n → ℂ) :
    ‖∑ j, ∑ k, star (a j) * H j k * a k‖ ≤ ‖operator H‖ * ∑ j, ‖a j‖ ^ 2 := by
  let u : EuclideanSpace ℂ n := WithLp.toLp 2 a
  have he : inner ℂ u (operator H u) = ∑ j, ∑ k, star (a j) * H j k * a k := by
    rw [EuclideanSpace.inner_eq_star_dotProduct]
    change (∑ j, (∑ k, H j k * a k) * star (a j)) = _
    simp only [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro k _
    ring
  rw [← he]
  calc
    _ ≤ ‖u‖ * ‖operator H u‖ := norm_inner_le_norm _ _
    _ ≤ ‖u‖ * (‖operator H‖ * ‖u‖) := mul_le_mul_of_nonneg_left ((operator H).le_opNorm u) (norm_nonneg _)
    _ = ‖operator H‖ * ‖u‖ ^ 2 := by ring
    _ = _ := by rw [EuclideanSpace.norm_sq_eq]
end FiniteSieveOperator

namespace CanonicalQuadraticSieve

open ActualEisensteinCubic CompletedGauss FiniteSieveOperator
open IdealCoprimeSieveOperator DivisorBlockCauchy

def rayGramMatrix {m n : Type*} [Fintype m]
    (D : Ideal O) (c : EisensteinEPrimaryPhase.Coord) (rows : m → Ideal O) (cols : n → Ideal O) : Matrix n n ℂ :=
  fun j k => ∑ i, if gcd (cols j) (cols k) = D ∧ columnRay (cols j) = c ∧ columnRay (cols k) = c then
    star (quadraticRow (cols j) (primaryGenerator (rows i))) *
      quadraticRow (cols k) (primaryGenerator (rows i)) else 0

theorem rayGcdBlock_eq_quadraticForm {m n : Type*} [Fintype m] [Fintype n]
    (D : Ideal O) (c : EisensteinEPrimaryPhase.Coord) (rows : m → Ideal O) (cols : n → Ideal O) (a : n → ℂ) :
    rayGcdBlock D c rows cols a =
      ∑ j, ∑ k, star (a j) * rayGramMatrix D c rows cols j k * a k := by
  rw [rayGcdBlock_eq, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  simp only [rayGramMatrix, Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  by_cases h : gcd (cols j) (cols k) = D ∧ columnRay (cols j) = c ∧ columnRay (cols k) = c
  · simp only [if_pos h, star_mul]
    ring
  · simp only [if_neg h, mul_zero, zero_mul]

theorem rayGcdBlock_norm_le {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n]
    (D : Ideal O) (c : EisensteinEPrimaryPhase.Coord) (rows : m → Ideal O) (cols : n → Ideal O) (a : n → ℂ) :
    ‖rayGcdBlock D c rows cols a‖ ≤ ‖operator (rayGramMatrix D c rows cols)‖ * ∑ j, ‖a j‖ ^ 2 := by
  rw [rayGcdBlock_eq_quadraticForm]
  exact quadratic_form_bound _ _

def rayThirdNorm (M N K : ℝ) (D : Ideal O) (c : EisensteinEPrimaryPhase.Coord) : ℝ :=
  sSup (Set.range (fun a : idealRange N → ℂ =>
    ‖rayGcdBlock D c (fun I : highKernelRange M K => I.val) (fun J : idealRange N => J.val) a‖ /
      (∑ J, ‖a J‖ ^ 2)))

def thirdNorm (M N K : ℝ) (D : Ideal O) : ℝ :=
  ∑ c : EisensteinEPrimaryPhase.Coord, rayThirdNorm M N K D c

theorem rayThirdNorm_bddAbove (M N K : ℝ) (D : Ideal O) (c : EisensteinEPrimaryPhase.Coord) :
    BddAbove (Set.range (fun a : idealRange N → ℂ =>
      ‖rayGcdBlock D c (fun I : highKernelRange M K => I.val) (fun J : idealRange N => J.val) a‖ /
        (∑ J, ‖a J‖ ^ 2))) := by
  refine ⟨‖operator (rayGramMatrix D c (fun I : highKernelRange M K => I.val)
    (fun J : idealRange N => J.val))‖, ?_⟩
  rintro x ⟨a, rfl⟩
  dsimp only
  have he : 0 ≤ ∑ J, ‖a J‖ ^ 2 := by positivity
  rcases he.eq_or_lt with he | he
  · rw [← he, div_zero]
    exact norm_nonneg _
  · exact (div_le_iff₀ he).mpr (rayGcdBlock_norm_le D c _ _ a)

theorem rayThirdNorm_nonneg (M N K : ℝ) (D : Ideal O) (c : EisensteinEPrimaryPhase.Coord) :
    0 ≤ rayThirdNorm M N K D c := by
  unfold rayThirdNorm
  apply le_csSup (rayThirdNorm_bddAbove M N K D c)
  refine ⟨(fun _ => 0), ?_⟩
  simp only [norm_zero, zero_pow (by decide : 2 ≠ 0), Finset.sum_const_zero, div_zero]

theorem thirdNorm_nonneg (M N K : ℝ) (D : Ideal O) : 0 ≤ thirdNorm M N K D :=
  Finset.sum_nonneg (fun c _ => rayThirdNorm_nonneg M N K D c)

theorem rayThirdNorm_bound (M N K : ℝ) (D : Ideal O) (c : EisensteinEPrimaryPhase.Coord)
    (a : idealRange N → ℂ) :
    ‖rayGcdBlock D c (fun I : highKernelRange M K => I.val) (fun J : idealRange N => J.val) a‖ ≤
      rayThirdNorm M N K D c * ∑ J, ‖a J‖ ^ 2 := by
  have he : 0 ≤ ∑ J, ‖a J‖ ^ 2 := by positivity
  rcases he.eq_or_lt with he | he
  · have hb := rayGcdBlock_norm_le D c (fun I : highKernelRange M K => I.val)
      (fun J : idealRange N => J.val) a
    simpa only [← he, mul_zero] using hb
  · exact (div_le_iff₀ he).mp (le_csSup (rayThirdNorm_bddAbove M N K D c)
      (Set.mem_range_self a))

theorem highKernelNorm_le_thirdNorm (M N K G : ℝ) (hN : 1 ≤ N) (hG : 0 < G)
    (ε : ℝ) (hε : 0 < ε) :
    highKernelNorm M N K ≤ 16 *
      ((∑ D ∈ (gcdPool (fun J : idealRange N => J.val)).filter (fun D => (Ideal.absNorm D : ℝ) ≤ G),
          thirdNorm M N K D) +
        highKernelNorm M (N / G) K * (supportConstant ε hε * divisorConstant ε hε) * (N ^ ε) ^ 2) := by
  apply squared_norm_le_of_energy _ _
  · have hb := highKernelNorm_nonneg M (N / G) K
    have hs := (supportConstant_pos ε hε).le
    have hd := (divisorConstant_pos ε hε).le
    have ht : 0 ≤ ∑ D ∈ (gcdPool (fun J : idealRange N => J.val)).filter (fun D => (Ideal.absNorm D : ℝ) ≤ G),
        thirdNorm M N K D := Finset.sum_nonneg (fun D _ => thirdNorm_nonneg M N K D)
    positivity
  · intro a
    have h := highKernel_energy_ray_gcd_reduction ε hε G hG
      (fun I : highKernelRange M K => I.val) (fun J : idealRange N => J.val)
      Subtype.val_injective Subtype.val_injective M N K hN (fun I => I.property)
      (fun J => mem_idealRange.mp J.property) a
    apply h.trans
    have hsum : (∑ c : EisensteinEPrimaryPhase.Coord,
        ∑ D ∈ (gcdPool (fun J : idealRange N => J.val)).filter (fun D => (Ideal.absNorm D : ℝ) ≤ G),
          ‖rayGcdBlock D c (fun I : highKernelRange M K => I.val) (fun J : idealRange N => J.val) a‖) ≤
        (∑ D ∈ (gcdPool (fun J : idealRange N => J.val)).filter (fun D => (Ideal.absNorm D : ℝ) ≤ G),
          thirdNorm M N K D) * ∑ J, ‖a J‖ ^ 2 := by
      calc
        _ ≤ ∑ c : EisensteinEPrimaryPhase.Coord,
            ∑ D ∈ (gcdPool (fun J : idealRange N => J.val)).filter (fun D => (Ideal.absNorm D : ℝ) ≤ G),
              rayThirdNorm M N K D c * ∑ J, ‖a J‖ ^ 2 := by
          apply Finset.sum_le_sum
          intro c _
          exact Finset.sum_le_sum (fun D _ => rayThirdNorm_bound M N K D c a)
        _ = _ := by rw [Finset.sum_comm]; simp only [thirdNorm, Finset.sum_mul]
    nlinarith

open ActualEisensteinCubic CompletedGauss FiniteSieveOperator IdealCoprimeSieveOperator DivisorBlockCauchy

def weightedGcdBlock {m n : Type*} [Fintype m] [Fintype n]
    (D : Ideal O) (rows : m → Ideal O) (cols : n → Ideal O) (w : m → ℂ) (a : n → ℂ) : ℂ :=
  ∑ i, w i * ∑ j, ∑ k, gcdTerm D rows cols a i j k

theorem highKernel_weightedGcdBlock_bound {m n : Type*} [Fintype m] [Fintype n]
    [DecidableEq m] [DecidableEq n]
    (ε : ℝ) (hε : 0 < ε) (D : Ideal O) (hD : D ≠ 0)
    (rows : m → Ideal O) (cols : n → Ideal O)
    (hr : Function.Injective rows) (hc : Function.Injective cols)
    (M N K : ℝ) (hN : 1 ≤ N) (hrows : ∀ i, rows i ∈ highKernelRange M K)
    (hcols : ∀ j, Admissible (cols j) ∧ (Ideal.absNorm (cols j) : ℝ) ≤ N)
    (w : m → ℂ) (W : ℝ) (hW : 0 ≤ W) (hw : ∀ i, ‖w i‖ ≤ W) (a : n → ℂ) :
    ‖weightedGcdBlock D rows cols w a‖ ≤ W * highKernelNorm M (N / (Ideal.absNorm D : ℝ)) K *
      (supportConstant ε hε * N ^ ε) * ∑ j, ‖if D ∣ cols j then a j else 0‖ ^ 2 := by
  let v : m → ℂ := fun i => w i *
    (star (quadraticRow D (primaryGenerator (rows i))) * quadraticRow D (primaryGenerator (rows i)))
  have hv (i : m) : ‖v i‖ ≤ W := by
    dsimp only [v]
    simp only [norm_mul, norm_star]
    calc
      _ ≤ W * (1 * 1) := by
        apply mul_le_mul (hw i)
        · exact mul_le_mul (quadraticRow_norm_le_one D _) (quadraticRow_norm_le_one D _) (norm_nonneg _) (by norm_num)
        · positivity
        · exact hW
      _ = W := by ring
  have he : weightedGcdBlock D rows cols w a = ∑ i, v i * ∑ j, ∑ k,
      if IsCoprime (totalQuotient D (cols j)) (totalQuotient D (cols k)) then
        star (quotientMatrix D rows cols i j * (if D ∣ cols j then a j else 0)) *
          (quotientMatrix D rows cols i k * (if D ∣ cols k then a k else 0)) else 0 := by
    unfold weightedGcdBlock
    simp_rw [gcdTerm_eq_quotient D hD rows cols (fun j => (hcols j).1) a]
    simp only [v, ← Finset.mul_sum, mul_assoc]
  rw [he]
  have hb := ideal_coprime_gram_operator_bound ε hε (fun j => totalQuotient D (cols j))
    (fun j => totalQuotient_ne_zero D _ (hcols j).1) N (by linarith)
    (fun j => totalQuotient_norm_le D _ (hcols j).1 N hN (hcols j).2)
    (quotientMatrix D rows cols) (fun j => if D ∣ cols j then a j else 0) v W hW hv
  apply hb.trans
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left
        (highKernel_quotientMatrix_squared_norm_le D hD rows cols hr hc M N K hrows hcols) hW)
      (mul_nonneg (supportConstant_pos ε hε).le (Real.rpow_nonneg (by linarith) _)))
    (Finset.sum_nonneg (fun _ _ => sq_nonneg _))

theorem highKernel_large_weighted_gcd_blocks {m n : Type*} [Fintype m] [Fintype n]
    [DecidableEq m] [DecidableEq n]
    (ε : ℝ) (hε : 0 < ε) (S : Finset (Ideal O)) (G : ℝ) (hG : 0 < G)
    (hS : ∀ D ∈ S, G ≤ (Ideal.absNorm D : ℝ))
    (rows : m → Ideal O) (cols : n → Ideal O)
    (hr : Function.Injective rows) (hc : Function.Injective cols)
    (M N K : ℝ) (hN : 1 ≤ N) (hrows : ∀ i, rows i ∈ highKernelRange M K)
    (hcols : ∀ j, Admissible (cols j) ∧ (Ideal.absNorm (cols j) : ℝ) ≤ N)
    (w : m → ℂ) (W : ℝ) (hW : 0 ≤ W) (hw : ∀ i, ‖w i‖ ≤ W) (a : n → ℂ) :
    (∑ D ∈ S, ‖weightedGcdBlock D rows cols w a‖) ≤
      W * highKernelNorm M (N / G) K * (supportConstant ε hε * divisorConstant ε hε) *
        (N ^ ε) ^ 2 * ∑ j, ‖a j‖ ^ 2 := by
  have hfac : 0 ≤ supportConstant ε hε * N ^ ε :=
    mul_nonneg (supportConstant_pos ε hε).le (Real.rpow_nonneg (by linarith) _)
  have hB : 0 ≤ highKernelNorm M (N / G) K := highKernelNorm_nonneg _ _ _
  have hb (D : Ideal O) (hD : D ∈ S) : ‖weightedGcdBlock D rows cols w a‖ ≤
      W * highKernelNorm M (N / G) K * (supportConstant ε hε * N ^ ε) *
        ∑ j, ‖if D ∣ cols j then a j else 0‖ ^ 2 := by
    have hn : 0 < (Ideal.absNorm D : ℝ) := hG.trans_le (hS D hD)
    have hD0 : D ≠ 0 := by intro hz; simp [hz] at hn
    have hmono := highKernelNorm_mono (M := M) (K := K) (M' := M) (K' := K) le_rfl
      (div_le_div_of_nonneg_left (by linarith : 0 ≤ N) hG (hS D hD)) le_rfl
    exact (highKernel_weightedGcdBlock_bound ε hε D hD0 rows cols hr hc M N K hN hrows hcols w W hW hw a).trans
      (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hmono hW) hfac) (by positivity))
  calc
    _ ≤ ∑ D ∈ S, W * highKernelNorm M (N / G) K * (supportConstant ε hε * N ^ ε) *
        ∑ j, ‖if D ∣ cols j then a j else 0‖ ^ 2 := Finset.sum_le_sum hb
    _ = W * highKernelNorm M (N / G) K * (supportConstant ε hε * N ^ ε) *
        ∑ D ∈ S, ∑ j, ‖if D ∣ cols j then a j else 0‖ ^ 2 := (Finset.mul_sum ..).symm
    _ ≤ W * highKernelNorm M (N / G) K * (supportConstant ε hε * N ^ ε) *
        ((divisorConstant ε hε * N ^ ε) * ∑ j, ‖a j‖ ^ 2) :=
      mul_le_mul_of_nonneg_left
        (divisor_mask_energy_small_power ε hε S cols (fun j => (hcols j).1.1) N (fun j => (hcols j).2) a)
        (mul_nonneg (mul_nonneg hW hB) hfac)
    _ = _ := by ring

end CanonicalQuadraticSieve

namespace FiniteSieveRestriction

theorem sector_weighted_energy_bound {m n r : Type*} [Fintype m] [Fintype n] [Fintype r] [DecidableEq r]
    (A : Matrix m n ℂ) (σ : n → r) (a : n → ℂ) (v : m → ℝ) (hv : ∀ i, 0 ≤ v i) :
    (∑ i, v i * ‖∑ j, A i j * a j‖ ^ 2) ≤
      (Fintype.card r : ℝ) * ∑ c, ∑ i, v i * ‖∑ j, A i j * sectorCoefficient σ c a j‖ ^ 2 := by
  have hi (i : m) : ‖∑ j, A i j * a j‖ ^ 2 ≤
      (Fintype.card r : ℝ) * ∑ c, ‖∑ j, A i j * sectorCoefficient σ c a j‖ ^ 2 := by
    simpa only [Fintype.sum_unique] using sector_energy_bound (fun _ : Unit => A i) σ a
  calc
    _ ≤ ∑ i, v i * ((Fintype.card r : ℝ) * ∑ c, ‖∑ j, A i j * sectorCoefficient σ c a j‖ ^ 2) :=
      Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left (hi i) (hv i))
    _ = _ := by
      simp only [Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro c _
      apply Finset.sum_congr rfl
      intro i _
      ring
end FiniteSieveRestriction

namespace CanonicalQuadraticSieve

section
open ActualEisensteinCubic CompletedGauss IdealCoprimeSieveOperator DivisorBlockCauchy FiniteSieveRestriction

theorem weighted_energy_eq_gcd_blocks {m n : Type*} [Fintype m] [Fintype n]
    (rows : m → Ideal O) (cols : n → Ideal O) (v : m → ℝ) (a : n → ℂ) :
    ((∑ i, v i * ‖∑ j, quadraticRow (cols j) (primaryGenerator (rows i)) * a j‖ ^ 2 : ℝ) : ℂ) =
      ∑ D ∈ gcdPool cols, weightedGcdBlock D rows cols (fun i => (v i : ℂ)) a := by
  have hi (i : m) : ((‖∑ j, quadraticRow (cols j) (primaryGenerator (rows i)) * a j‖ ^ 2 : ℝ) : ℂ) =
      ∑ D ∈ gcdPool cols, ∑ j, ∑ k, gcdTerm D rows cols a i j k := by
    simpa only [gcdBlock, Fintype.sum_unique, gcdTerm] using energy_eq_gcd_blocks (fun _ : Unit => rows i) cols a
  simp only [Complex.ofReal_sum, Complex.ofReal_mul, hi, Finset.mul_sum, weightedGcdBlock]
  rw [Finset.sum_comm]

theorem weighted_energy_le_gcd_blocks {m n : Type*} [Fintype m] [Fintype n]
    (rows : m → Ideal O) (cols : n → Ideal O) (v : m → ℝ) (hv : ∀ i, 0 ≤ v i) (a : n → ℂ) :
    (∑ i, v i * ‖∑ j, quadraticRow (cols j) (primaryGenerator (rows i)) * a j‖ ^ 2) ≤
      ∑ D ∈ gcdPool cols, ‖weightedGcdBlock D rows cols (fun i => (v i : ℂ)) a‖ := by
  have he := congrArg norm (weighted_energy_eq_gcd_blocks rows cols v a)
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Finset.sum_nonneg (fun i _ => mul_nonneg (hv i) (sq_nonneg _)))] at he
  rw [he]
  exact norm_sum_le _ _

theorem highKernel_weighted_energy_gcd_reduction {m n : Type*} [Fintype m] [Fintype n]
    [DecidableEq m] [DecidableEq n]
    (ε : ℝ) (hε : 0 < ε) (G : ℝ) (hG : 0 < G)
    (rows : m → Ideal O) (cols : n → Ideal O)
    (hr : Function.Injective rows) (hc : Function.Injective cols)
    (M N K : ℝ) (hN : 1 ≤ N) (hrows : ∀ i, rows i ∈ highKernelRange M K)
    (hcols : ∀ j, Admissible (cols j) ∧ (Ideal.absNorm (cols j) : ℝ) ≤ N)
    (v : m → ℝ) (W : ℝ) (hW : 0 ≤ W) (hv : ∀ i, 0 ≤ v i ∧ v i ≤ W) (a : n → ℂ) :
    (∑ i, v i * ‖∑ j, quadraticRow (cols j) (primaryGenerator (rows i)) * a j‖ ^ 2) ≤
      (∑ D ∈ (gcdPool cols).filter (fun D => (Ideal.absNorm D : ℝ) ≤ G),
        ‖weightedGcdBlock D rows cols (fun i => (v i : ℂ)) a‖) +
      W * highKernelNorm M (N / G) K * (supportConstant ε hε * divisorConstant ε hε) *
        (N ^ ε) ^ 2 * ∑ j, ‖a j‖ ^ 2 := by
  have he := weighted_energy_le_gcd_blocks rows cols v (fun i => (hv i).1) a
  rw [← Finset.sum_filter_add_sum_filter_not (gcdPool cols) (fun D => (Ideal.absNorm D : ℝ) ≤ G)] at he
  exact he.trans (add_le_add le_rfl (highKernel_large_weighted_gcd_blocks ε hε _ G hG
    (fun D hD => (lt_of_not_ge (Finset.mem_filter.mp hD).2).le)
    rows cols hr hc M N K hN hrows hcols (fun i => (v i : ℂ)) W hW
    (fun i => by simpa only [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hv i).1] using (hv i).2) a))

def weightedRayGcdBlock {m n : Type*} [Fintype m] [Fintype n]
    (D : Ideal O) (c : EisensteinEPrimaryPhase.Coord)
    (rows : m → Ideal O) (cols : n → Ideal O) (v : m → ℝ) (a : n → ℂ) : ℂ :=
  weightedGcdBlock D rows cols (fun i => (v i : ℂ))
    (sectorCoefficient (fun j => columnRay (cols j)) c a)

theorem highKernel_weighted_energy_ray_gcd_reduction {m n : Type*} [Fintype m] [Fintype n]
    [DecidableEq m] [DecidableEq n]
    (ε : ℝ) (hε : 0 < ε) (G : ℝ) (hG : 0 < G)
    (rows : m → Ideal O) (cols : n → Ideal O)
    (hr : Function.Injective rows) (hc : Function.Injective cols)
    (M N K : ℝ) (hN : 1 ≤ N) (hrows : ∀ i, rows i ∈ highKernelRange M K)
    (hcols : ∀ j, Admissible (cols j) ∧ (Ideal.absNorm (cols j) : ℝ) ≤ N)
    (v : m → ℝ) (W : ℝ) (hW : 0 ≤ W) (hv : ∀ i, 0 ≤ v i ∧ v i ≤ W) (a : n → ℂ) :
    (∑ i, v i * ‖∑ j, quadraticRow (cols j) (primaryGenerator (rows i)) * a j‖ ^ 2) ≤
      16 * ((∑ c : EisensteinEPrimaryPhase.Coord,
        ∑ D ∈ (gcdPool cols).filter (fun D => (Ideal.absNorm D : ℝ) ≤ G), ‖weightedRayGcdBlock D c rows cols v a‖) +
        W * highKernelNorm M (N / G) K * (supportConstant ε hε * divisorConstant ε hε) *
          (N ^ ε) ^ 2 * ∑ j, ‖a j‖ ^ 2) := by
  let σ : n → EisensteinEPrimaryPhase.Coord := fun j => columnRay (cols j)
  let C := W * highKernelNorm M (N / G) K * (supportConstant ε hε * divisorConstant ε hε) * (N ^ ε) ^ 2
  have hs := sector_weighted_energy_bound
    (fun i j => quadraticRow (cols j) (primaryGenerator (rows i))) σ a v (fun i => (hv i).1)
  have hcard : Fintype.card EisensteinEPrimaryPhase.Coord = 16 := by decide
  rw [hcard] at hs
  norm_num only [Nat.cast_ofNat] at hs
  apply hs.trans
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  calc
    _ ≤ ∑ c : EisensteinEPrimaryPhase.Coord,
        ((∑ D ∈ (gcdPool cols).filter (fun D => (Ideal.absNorm D : ℝ) ≤ G),
          ‖weightedRayGcdBlock D c rows cols v a‖) + C * ∑ j, ‖sectorCoefficient σ c a j‖ ^ 2) := by
      apply Finset.sum_le_sum
      intro c _
      exact highKernel_weighted_energy_gcd_reduction ε hε G hG rows cols hr hc M N K hN hrows hcols v W hW hv
        (sectorCoefficient σ c a)
    _ = _ := by rw [Finset.sum_add_distrib, ← Finset.mul_sum, sectorCoefficient_energy]

end

open ActualEisensteinCubic CompletedGauss IdealCoprimeSieveOperator DivisorBlockCauchy

def smoothHighWeight (M : ℝ) (I : Ideal O) : ℝ :=
  QuadraticInitialBound.sieveBump ((Ideal.absNorm I : ℝ) / M)

def smoothHighEnergy (M N K : ℝ) (a : idealRange N → ℂ) : ℝ :=
  ∑ I : highKernelRange (2 * M) K, smoothHighWeight M I.val *
    ‖∑ J : idealRange N, quadraticRow J.val (primaryGenerator I.val) * a J‖ ^ 2

theorem highKernel_energy_le_smooth (M N K : ℝ) (hM : 0 < M) (a : idealRange N → ℂ) :
    (∑ I : highKernelRange M K, ‖∑ J : idealRange N, quadraticRow J.val (primaryGenerator I.val) * a J‖ ^ 2) ≤
      smoothHighEnergy M N K a := by
  let E : Ideal O → ℝ := fun I => ‖∑ J : idealRange N, quadraticRow J.val (primaryGenerator I) * a J‖ ^ 2
  have hsub : highKernelRange M K ⊆ highKernelRange (2 * M) K := by
    intro I hI
    obtain ⟨hs, hn, hk⟩ := mem_highKernelRange.mp hI
    exact mem_highKernelRange.mpr ⟨hs, by linarith, hk⟩
  have hv (I : Ideal O) (hI : I ∈ highKernelRange M K) : smoothHighWeight M I = 1 := by
    apply QuadraticInitialBound.sieveBump_eq_one (div_nonneg (Nat.cast_nonneg _) hM.le)
    exact (div_le_one hM).mpr (mem_highKernelRange.mp hI).2.1
  change (∑ I : highKernelRange M K, E I.val) ≤
    ∑ I : highKernelRange (2 * M) K, smoothHighWeight M I.val * E I.val
  rw [Finset.sum_coe_sort (highKernelRange M K) E,
    Finset.sum_coe_sort (highKernelRange (2 * M) K) (fun I => smoothHighWeight M I * E I)]
  calc
    _ = ∑ I ∈ highKernelRange M K, smoothHighWeight M I * E I :=
      Finset.sum_congr rfl (fun I hI => by rw [hv I hI, one_mul])
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg hsub (fun I hI hnot =>
      mul_nonneg QuadraticInitialBound.sieveBump.nonneg (sq_nonneg _))

def smoothRayGcdBlock (M N K : ℝ) (D : Ideal O) (c : EisensteinEPrimaryPhase.Coord)
    (a : idealRange N → ℂ) : ℂ :=
  weightedRayGcdBlock D c (fun I : highKernelRange (2 * M) K => I.val)
    (fun J : idealRange N => J.val) (fun I => smoothHighWeight M I.val) a

theorem highKernel_energy_smooth_gcd_reduction (M N K G : ℝ)
    (hM : 0 < M) (hN : 1 ≤ N) (hG : 0 < G) (ε : ℝ) (hε : 0 < ε) (a : idealRange N → ℂ) :
    (∑ I : highKernelRange M K, ‖∑ J : idealRange N, quadraticRow J.val (primaryGenerator I.val) * a J‖ ^ 2) ≤
      16 * ((∑ c : EisensteinEPrimaryPhase.Coord,
        ∑ D ∈ (gcdPool (fun J : idealRange N => J.val)).filter (fun D => (Ideal.absNorm D : ℝ) ≤ G),
          ‖smoothRayGcdBlock M N K D c a‖) +
        highKernelNorm (2 * M) (N / G) K * (supportConstant ε hε * divisorConstant ε hε) *
          (N ^ ε) ^ 2 * ∑ J, ‖a J‖ ^ 2) := by
  apply (highKernel_energy_le_smooth M N K hM a).trans
  have h := highKernel_weighted_energy_ray_gcd_reduction ε hε G hG
    (fun I : highKernelRange (2 * M) K => I.val) (fun J : idealRange N => J.val)
    Subtype.val_injective Subtype.val_injective (2 * M) N K hN (fun I => I.property)
    (fun J => mem_idealRange.mp J.property) (fun I => smoothHighWeight M I.val) 1 (by norm_num)
    (fun I => ⟨QuadraticInitialBound.sieveBump.nonneg, QuadraticInitialBound.sieveBump.le_one⟩) a
  simpa only [smoothHighEnergy, smoothRayGcdBlock, one_mul] using h

end CanonicalQuadraticSieve

end

end OAI

end


