-- Prove2me | Definitions.Def_PNT_ZeroFree_433_0056
-- name    : PNT_ZeroFree_433_0056
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-10T15:52:05.610686+00:00
-- url     : https://prove2.me/theorems/2c3d0c2f-7101-45fe-80ea-cbd598e2a48c
-- title:
--   Zero-free region foundations: CubicSieve.CubeLabels [0056]
-- statement:
--   Definitions and proved supporting lemmas from the following source modules:
--
--   - OAI.NumberTheory.DirichletL.CubicSieve.CubeLabels
--
--   These declarations form part of the analytic and arithmetic foundations of the Dirichlet L-function nonvanishing argument in the half-plane Re(s) > 7/8. The original namespaces and hypotheses are retained. The code is ported to Lean 4.33.1 and the pinned Mathlib environment; every included lemma has a complete proof.
-- source:
--   https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/CubicSieve/CubeLabels.lean#L354-L635

import Definitions.Def_PNT_ZeroFree_433_0056_1

/- Supporting zero-free-region estimates, split at Lean command boundaries.
Uniquely named private helpers in the first part are promoted
so the remaining estimates can use them across the module boundary.
https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/CubicSieve/CubeLabels.lean
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
open scoped BigOperators Classical
open scoped BigOperators Classical
open ActualEisensteinCubic UniqueFactorizationMonoid

section
open scoped BigOperators Classical
namespace FirstPassCubeLabels
open ActualEisensteinCubic
open MixedCrossSeparation (crossSymbol quadraticCrossPhase)


end FirstPassCubeLabels

open scoped BigOperators Classical
open UniqueFactorizationMonoid
namespace QuadraticSquarefreeKernel


open ActualEisensteinCubic QuadraticInitialBound CompletedGauss


theorem quadraticRow_square {ι : Type*} (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
    (hg : ∀ i, lambda ∉ P i) (S : Finset ι) (a : O) :
    quadraticRow P hg S (a ^ 2) = rowCoprimeMask P S a := by
  have heq : quadraticRow P hg S (a ^ 2) = finiteSquarefreeRow P hg S (a ^ 6) := by
    simp only [quadraticRow, finiteSquarefreeRow, map_pow, ← Finset.prod_pow, ← pow_mul]
  rw [heq, finiteSquarefreeRow_sixth_power]
  rfl

theorem quadraticRow_primary_decomposition {ι : Type*}
    (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
    (hg : ∀ i, lambda ∉ P i) (S : Finset ι) (I : Ideal O) :
    quadraticRow P hg S (primaryGenerator I) =
      rowCoprimeMask P S (primaryGenerator (squarePart I)) *
        quadraticRow P hg S (primaryGenerator (squarefreePart I)) := by
  conv_lhs => rw [← squarePart_sq_mul_squarefreePart I]
  rw [primaryGenerator_mul]
  have hpow : primaryGenerator (squarePart I ^ 2) = primaryGenerator (squarePart I) ^ 2 :=
    map_pow primaryGeneratorHom _ _
  rw [hpow, quadraticRow_mul, quadraticRow_square]

theorem quadraticRow_primary_tsum_decomposition {ι : Type*}
    (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
    (hg : ∀ i, lambda ∉ P i) (S : Finset ι) (W : ℝ → ℂ) (X : ℝ) :
    (∑' I : {I : Ideal O // I ≠ 0},
      quadraticRow P hg S (primaryGenerator I.val) * W ((Ideal.absNorm I.val : ℝ) / X)) =
    ∑' p : {A : Ideal O // A ≠ 0} × {D : Ideal O // Squarefree D},
      rowCoprimeMask P S (primaryGenerator p.1.val) *
      quadraticRow P hg S (primaryGenerator p.2.val) *
      W (((Ideal.absNorm p.1.val : ℝ) ^ 2 * Ideal.absNorm p.2.val) / X) := by
  rw [squarefree_decomposition_tsum (fun I =>
    quadraticRow P hg S (primaryGenerator I) * W ((Ideal.absNorm I : ℝ) / X))]
  apply tsum_congr
  intro p
  have hpow : primaryGenerator (p.1.val ^ 2) = primaryGenerator p.1.val ^ 2 :=
    map_pow primaryGeneratorHom _ _
  simp only [primaryGenerator_mul, hpow, quadraticRow_mul, quadraticRow_square,
    map_mul, map_pow, Nat.cast_mul, Nat.cast_pow]

end QuadraticSquarefreeKernel
end

namespace QuadraticMainBoundary
open scoped BigOperators Classical
open UniqueFactorizationMonoid
abbrev O := ActualEisensteinCubic.O
open QuadraticSquarefreeKernel

def cutoffDifference (K : ℝ) (H D : Ideal O) : ℝ :=
  (if (Ideal.absNorm (H * D) : ℝ) ≤ K then 1 else 0) -
    (if (Ideal.absNorm H : ℝ) ≤ K then 1 else 0)

theorem norm_pos {I : Ideal O} (hI : I ≠ 0) : 0 < (Ideal.absNorm I : ℝ) := by
  exact_mod_cast Nat.pos_iff_ne_zero.mpr
    (fun h => hI (Ideal.absNorm_eq_zero_iff.mp h))

theorem norm_one_le {I : Ideal O} (hI : I ≠ 0) : 1 ≤ (Ideal.absNorm I : ℝ) := by
  exact_mod_cast Nat.one_le_iff_ne_zero.mpr
    (fun h => hI (Ideal.absNorm_eq_zero_iff.mp h))

theorem norm_le_of_dvd {I J : Ideal O} (hJ : J ≠ 0) (hIJ : I ∣ J) :
    (Ideal.absNorm I : ℝ) ≤ Ideal.absNorm J := by
  exact_mod_cast Nat.le_of_dvd
    (Nat.pos_iff_ne_zero.mpr (fun h => hJ (Ideal.absNorm_eq_zero_iff.mp h)))
    (map_dvd Ideal.absNorm hIJ)

theorem cutoffDifference_nonzero_iff (K : ℝ) (H D : Ideal O) (hD : D ≠ 0) :
    cutoffDifference K H D ≠ 0 ↔
      (Ideal.absNorm H : ℝ) ≤ K ∧ K < (Ideal.absNorm (H * D) : ℝ) := by
  have hmono : (Ideal.absNorm H : ℝ) ≤ Ideal.absNorm (H * D) := by
    rw [map_mul, Nat.cast_mul]
    nlinarith [norm_one_le hD, Nat.cast_nonneg (α := ℝ) (Ideal.absNorm H)]
  unfold cutoffDifference
  split_ifs <;> simp_all ; linarith

theorem cutoffDifference_eq_neg_one_of_nonzero (K : ℝ) (H D : Ideal O) (hD : D ≠ 0)
    (h : cutoffDifference K H D ≠ 0) : cutoffDifference K H D = -1 := by
  obtain ⟨hH, hHD⟩ := (cutoffDifference_nonzero_iff K H D hD).mp h
  simp only [cutoffDifference, if_neg (not_le.mpr hHD), if_pos hH]
  norm_num

theorem squarePart_dvd {G H D E : Ideal O} (hG : G ≠ 0) (hH : Squarefree H)
    (hDG : D ∣ G) (hEG : E ∣ G) : squarePart (H * D * E) ∣ G := by
  have hD := ne_zero_of_dvd_ne_zero hG hDG
  have hE := ne_zero_of_dvd_ne_zero hG hEG
  have hB : H * D * E ≠ 0 := mul_ne_zero (mul_ne_zero hH.ne_zero hD) hE
  apply (dvd_iff_normalizedFactors_le_normalizedFactors (squarePart_ne_zero hB) hG).mpr
  apply Multiset.le_iff_count.mpr
  intro P
  have hfac := congrArg normalizedFactors (squarePart_sq_mul_squarefreePart (H * D * E))
  rw [normalizedFactors_mul (pow_ne_zero _ (squarePart_ne_zero hB))
    (squarefree_squarefreePart _).ne_zero, normalizedFactors_pow,
    normalizedFactors_mul (mul_ne_zero hH.ne_zero hD) hE,
    normalizedFactors_mul hH.ne_zero hD] at hfac
  have hcnt := congrArg (Multiset.count P) hfac
  simp only [Multiset.count_add, Multiset.count_nsmul] at hcnt
  have hd := (dvd_iff_normalizedFactors_le_normalizedFactors hD hG).mp hDG
  have he := (dvd_iff_normalizedFactors_le_normalizedFactors hE hG).mp hEG
  have hdc := Multiset.count_le_of_le P hd
  have hec := Multiset.count_le_of_le P he
  have hhc := Multiset.nodup_iff_count_le_one.mp
    ((squarefree_iff_nodup_normalizedFactors hH.ne_zero).mp hH) P
  omega

theorem cutoffDifference_eq_zero_of_product_le (K : ℝ) {H D E : Ideal O}
    (hD : D ≠ 0) (hE : E ≠ 0)
    (hB : (Ideal.absNorm (H * D * E) : ℝ) ≤ K) : cutoffDifference K H D = 0 := by
  by_contra h
  have hh := (cutoffDifference_nonzero_iff K H D hD).mp h
  have he := norm_one_le hE
  rw [map_mul, Nat.cast_mul] at hB
  have hp := Nat.cast_nonneg (Ideal.absNorm (H * D)) (α := ℝ)
  nlinarith

theorem main_boundary_localization (K : ℝ) {G H D E : Ideal O}
    (hG : G ≠ 0) (hH : Squarefree H) (hDG : D ∣ G) (hEG : E ∣ G)
    (h : cutoffDifference K H D ≠ 0) :
    K < (Ideal.absNorm (H * D * E) : ℝ) ∧
    (Ideal.absNorm (H * D * E) : ℝ) ≤ K * (Ideal.absNorm G : ℝ) ^ 2 ∧
    squarePart (H * D * E) ∣ G ∧
    K / (Ideal.absNorm G : ℝ) ^ 2 < (Ideal.absNorm (squarefreePart (H * D * E)) : ℝ) ∧
    (Ideal.absNorm (squarefreePart (H * D * E)) : ℝ) ≤ K * (Ideal.absNorm G : ℝ) ^ 2 := by
  have hD := ne_zero_of_dvd_ne_zero hG hDG
  have hE := ne_zero_of_dvd_ne_zero hG hEG
  have hB0 : H * D * E ≠ 0 := mul_ne_zero (mul_ne_zero hH.ne_zero hD) hE
  obtain ⟨hHK, hKHD⟩ := (cutoffDifference_nonzero_iff K H D hD).mp h
  have hHpos := norm_pos hH.ne_zero
  have hDpos := norm_pos hD
  have hEpos := norm_pos hE
  have hGone := norm_one_le hG
  have hEone := norm_one_le hE
  have hDle := norm_le_of_dvd hG hDG
  have hEle := norm_le_of_dvd hG hEG
  have hK : 0 ≤ K := le_trans hHpos.le hHK
  have hBlo : K < (Ideal.absNorm (H * D * E) : ℝ) := by
    rw [map_mul, Nat.cast_mul]
    have hp := Nat.cast_nonneg (Ideal.absNorm (H * D)) (α := ℝ)
    nlinarith
  have hBhi : (Ideal.absNorm (H * D * E) : ℝ) ≤ K * (Ideal.absNorm G : ℝ) ^ 2 := by
    simp only [map_mul, Nat.cast_mul]
    calc
      (Ideal.absNorm H : ℝ) * Ideal.absNorm D * Ideal.absNorm E ≤
        K * Ideal.absNorm G * Ideal.absNorm G :=
        mul_le_mul (mul_le_mul hHK hDle hDpos.le hK) hEle hEpos.le (by positivity)
      _ = _ := by ring
  have hroot := squarePart_dvd hG hH hDG hEG
  have hrootle := norm_le_of_dvd hG hroot
  have hrootone := norm_one_le (squarePart_ne_zero hB0)
  have hkerpos := norm_pos (squarefree_squarefreePart (H * D * E)).ne_zero
  have hdecomp : (Ideal.absNorm (squarePart (H * D * E)) : ℝ) ^ 2 *
      Ideal.absNorm (squarefreePart (H * D * E)) = Ideal.absNorm (H * D * E) := by
    exact_mod_cast norm_decomposition (H * D * E)
  have hrootpow : (Ideal.absNorm (squarePart (H * D * E)) : ℝ) ^ 2 ≤
      (Ideal.absNorm G : ℝ) ^ 2 := pow_le_pow_left₀ (le_trans zero_le_one hrootone) hrootle 2
  refine ⟨hBlo, hBhi, hroot, ?_, ?_⟩
  · apply (div_lt_iff₀ (by positivity : 0 < (Ideal.absNorm G : ℝ) ^ 2)).mpr
    nlinarith [mul_le_mul_of_nonneg_right hrootpow hkerpos.le]
  · have hrpow : 1 ≤ (Ideal.absNorm (squarePart (H * D * E)) : ℝ) ^ 2 := by nlinarith
    nlinarith

theorem cutoffDifference_of_common_one (K : ℝ) {H D : Ideal O} (hD : D ∣ 1) :
    cutoffDifference K H D = 0 := by
  have hD1 : D = 1 := associated_iff_eq.mp (associated_one_iff_isUnit.mpr (isUnit_of_dvd_one hD))
  simp [cutoffDifference, hD1]

end QuadraticMainBoundary

open scoped BigOperators Classical
namespace QuadraticDivisorCancellation
abbrev O := ActualEisensteinCubic.O
open ActualEisensteinCubic ConcreteTraceCRT QuadraticInitialBound QuadraticSquarefreeKernel

def normalizedRow {ι : Type*} (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
    (hg : ∀ i, lambda ∉ P i) (S : Finset ι) (z : O) : ℂ :=
  quadraticRow P hg S z / (‖eisEmbedding z‖ : ℂ)

theorem normalizedRow_mul {ι : Type*} (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
    (hg : ∀ i, lambda ∉ P i) (S : Finset ι) (a b : O) :
    normalizedRow P hg S (a * b) = normalizedRow P hg S a * normalizedRow P hg S b := by
  simp only [normalizedRow, quadraticRow_mul, map_mul, norm_mul, Complex.ofReal_mul,
    div_mul_div_comm]

theorem normalizedRow_one {ι : Type*} (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
    (hg : ∀ i, lambda ∉ P i) (S : Finset ι) : normalizedRow P hg S 1 = 1 := by
  simp [normalizedRow, quadraticRow, finiteSquarefreeRow]

def normalizedRowHom {ι : Type*} (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
    (hg : ∀ i, lambda ∉ P i) (S : Finset ι) : O →* ℂ where
  toFun := normalizedRow P hg S
  map_one' := normalizedRow_one P hg S
  map_mul' := normalizedRow_mul P hg S

theorem normalizedRow_prod {ι κ : Type*} (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
    (hg : ∀ i, lambda ∉ P i) (S : Finset ι) (q : κ → O) (T : Finset κ) :
    normalizedRow P hg S (∏ i ∈ T, q i) = ∏ i ∈ T, normalizedRow P hg S (q i) :=
  map_prod (normalizedRowHom P hg S) q T

theorem normalizedRow_sq {ι : Type*} (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
    (hg : ∀ i, lambda ∉ P i) (S : Finset ι) (z : O) :
    normalizedRow P hg S z ^ 2 = rowCoprimeMask P S z /
      (Ideal.absNorm (Ideal.span {z}) : ℂ) := by
  have hrow : quadraticRow P hg S z ^ 2 = rowCoprimeMask P S z := by
    simpa only [pow_two, quadraticRow_mul] using quadraticRow_square P hg S z
  have hn : (‖eisEmbedding z‖ : ℂ) ^ 2 = (Ideal.absNorm (Ideal.span {z}) : ℂ) := by
    exact_mod_cast eisEmbedding_norm_sq_eq_absNorm_span z
  rw [normalizedRow, div_pow, hrow, hn]

theorem double_divisor_factorization {κ : Type*} [DecidableEq κ]
    (z : κ → ℂ) (T U : Finset κ) (hTU : Disjoint T U) :
    (∑ D ∈ T.powerset, ∑ E ∈ (T ∪ U).powerset,
      (-1 : ℂ) ^ E.card * (∏ i ∈ D, z i) * ∏ i ∈ E, z i) =
    (∏ i ∈ T, (1 - z i ^ 2)) *
      ∑ E ∈ U.powerset, (-1 : ℂ) ^ E.card * ∏ i ∈ E, z i := by
  have hm (V : Finset κ) :
      (∑ E ∈ V.powerset, (-1 : ℂ) ^ E.card * ∏ i ∈ E, z i) =
      ∏ i ∈ V, (1 - z i) := by
    rw [Finset.prod_sub]
    simp only [Finset.prod_const_one, mul_one]
  calc
    _ = (∑ D ∈ T.powerset, ∏ i ∈ D, z i) *
        (∑ E ∈ (T ∪ U).powerset, (-1 : ℂ) ^ E.card * ∏ i ∈ E, z i) := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro D _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro E _
      ring
    _ = (∏ i ∈ T, (1 + z i)) * ((∏ i ∈ T, (1 - z i)) * ∏ i ∈ U, (1 - z i)) := by
      rw [← Finset.prod_one_add, hm, Finset.prod_union hTU]
    _ = (∏ i ∈ T, (1 - z i ^ 2)) * ∏ i ∈ U, (1 - z i) := by
      rw [← mul_assoc, ← Finset.prod_mul_distrib]
      congr 1
      apply Finset.prod_congr rfl
      intro i _
      ring
    _ = _ := by rw [hm]

theorem actual_double_divisor_cancellation {ι κ : Type*} [DecidableEq κ]
    (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
    (hg : ∀ i, lambda ∉ P i) (S : Finset ι)
    (q : κ → O) [∀ i, (Ideal.span {q i}).IsMaximal]
    (hprime : ∀ i, Prime (Ideal.span {q i}))
    (hinj : Function.Injective (fun i => (Ideal.span {q i} : Ideal O)))
    (T U : Finset κ) (hTU : Disjoint T U) :
    (∑ D ∈ T.powerset, ∑ E ∈ (T ∪ U).powerset,
      (UniqueFactorizationMonoid.moebius (∏ i ∈ E, Ideal.span {q i}) : ℂ) *
        normalizedRow P hg S ((∏ i ∈ D, q i) * ∏ i ∈ E, q i)) =
    (∏ i ∈ T, (1 - rowCoprimeMask P S (q i) /
        (Ideal.absNorm (Ideal.span {q i}) : ℂ))) *
      ∑ E ∈ U.powerset,
        (UniqueFactorizationMonoid.moebius (∏ i ∈ E, Ideal.span {q i}) : ℂ) *
          normalizedRow P hg S (∏ i ∈ E, q i) := by
  simp only [prime_product_moebius (fun i => Ideal.span {q i}) hprime hinj,
    normalizedRow_mul, normalizedRow_prod, ← mul_assoc]
  have h := double_divisor_factorization (normalizedRow P hg S ∘ q) T U hTU
  simpa only [Function.comp_apply, normalizedRow_sq] using h

theorem actual_double_divisor_cancellation_coprime {ι κ : Type*} [DecidableEq κ]
    (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
    (hg : ∀ i, lambda ∉ P i) (S : Finset ι)
    (q : κ → O) [∀ i, (Ideal.span {q i}).IsMaximal]
    (hprime : ∀ i, Prime (Ideal.span {q i}))
    (hinj : Function.Injective (fun i => (Ideal.span {q i} : Ideal O)))
    (T U : Finset κ) (hTU : Disjoint T U)
    (havoid : ∀ i ∈ T, ∀ j ∈ S, q i ∉ P j) :
    (∑ D ∈ T.powerset, ∑ E ∈ (T ∪ U).powerset,
      (UniqueFactorizationMonoid.moebius (∏ i ∈ E, Ideal.span {q i}) : ℂ) *
        normalizedRow P hg S ((∏ i ∈ D, q i) * ∏ i ∈ E, q i)) =
    (∏ i ∈ T, (1 - (1 : ℂ) / (Ideal.absNorm (Ideal.span {q i}) : ℂ))) *
      ∑ E ∈ U.powerset,
        (UniqueFactorizationMonoid.moebius (∏ i ∈ E, Ideal.span {q i}) : ℂ) *
          normalizedRow P hg S (∏ i ∈ E, q i) := by
  rw [actual_double_divisor_cancellation P hg S q hprime hinj T U hTU]
  congr 1
  apply Finset.prod_congr rfl
  intro i hi
  have hm : rowCoprimeMask P S (q i) = 1 := by
    simp only [rowCoprimeMask]
    rw [if_neg]
    push Not
    exact havoid i hi
  rw [hm]

end QuadraticDivisorCancellation

end

end OAI

end


