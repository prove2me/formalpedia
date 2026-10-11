-- Prove2me | Definitions.Def_PNT_ZeroFree_433_0090
-- name    : PNT_ZeroFree_433_0090
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-11T10:57:49.323909+00:00
-- url     : https://prove2.me/theorems/e7c30f7b-bfc3-46a8-90ff-7b83c17b612f
-- title:
--   Zero-free region foundations: QuadraticSieve.SquareParts [0090]
-- statement:
--   Definitions and proved supporting lemmas from the following source modules:
--
--   - OAI.NumberTheory.DirichletL.QuadraticSieve.SquareParts
--
--   These declarations form part of the analytic and arithmetic foundations of the Dirichlet L-function nonvanishing argument in the half-plane Re(s) > 7/8. The original namespaces and hypotheses are retained. The code is ported to Lean 4.33.1 and the pinned Mathlib environment; every included lemma has a complete proof.
-- source:
--   https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/QuadraticSieve/SquareParts.lean#L80-L659

import Definitions.Def_PNT_ZeroFree_433_0083
import Definitions.Def_PNT_ZeroFree_433_0089

/- Supporting source modules for the zero-free-region proof.
Ported and checked against Lean 4.33.1 / Mathlib 0df444a.
Original source attribution:
https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/QuadraticSieve/SquareParts.lean#L80-L659
-/

set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

-- Source module: OAI.NumberTheory.DirichletL.QuadraticSieve.SquareParts
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

section
open ActualEisensteinCubic CompletedGauss ConcretePrimeRowBridge QuadraticSquarefreeKernel

theorem supported_mul_iff (A B : Ideal O) : Supported (A * B) ↔ Supported A ∧ Supported B := by
  constructor
  · intro h
    have hA : A ≠ 0 := left_ne_zero_of_mul h.1
    have hB : B ≠ 0 := right_ne_zero_of_mul h.1
    refine ⟨⟨hA, ?_⟩, ⟨hB, ?_⟩⟩
    · intro P hP
      apply h.2 P
      rw [UniqueFactorizationMonoid.normalizedFactors_mul hA hB]
      exact Multiset.mem_add.mpr (Or.inl hP)
    · intro P hP
      apply h.2 P
      rw [UniqueFactorizationMonoid.normalizedFactors_mul hA hB]
      exact Multiset.mem_add.mpr (Or.inr hP)
  · rintro ⟨hA, hB⟩
    refine ⟨mul_ne_zero hA.1 hB.1, ?_⟩
    intro P hP
    rw [UniqueFactorizationMonoid.normalizedFactors_mul hA.1 hB.1] at hP
    rcases Multiset.mem_add.mp hP with hP | hP
    · exact hA.2 P hP
    · exact hB.2 P hP

theorem supported_sq_iff (A : Ideal O) : Supported (A ^ 2) ↔ Supported A := by
  rw [pow_two, supported_mul_iff, and_self]

theorem supported_square_parts (lengthScale : Ideal O) :
    Supported lengthScale ↔ Supported (squarePart lengthScale) ∧ Admissible (squarefreePart lengthScale) := by
  have he := supported_mul_iff (squarePart lengthScale ^ 2) (squarefreePart lengthScale)
  rw [squarePart_sq_mul_squarefreePart, supported_sq_iff] at he
  rw [he]
  have hsf := squarefree_squarefreePart lengthScale
  constructor
  · rintro ⟨hA, hB⟩
    exact ⟨hA, hB.1, hsf, hB.2⟩
  · rintro ⟨hA, hB⟩
    exact ⟨hA, hB.1, hB.2.2⟩

def supportedSquarefreeEquiv : {lengthScale : Ideal O // Supported lengthScale} ≃
    ({A : Ideal O // Supported A} × {B : Ideal O // Admissible B}) where
  toFun lengthScale := (⟨squarePart lengthScale.val, ((supported_square_parts lengthScale.val).mp lengthScale.property).1⟩,
    ⟨squarefreePart lengthScale.val, ((supported_square_parts lengthScale.val).mp lengthScale.property).2⟩)
  invFun p := ⟨p.1.val ^ 2 * p.2.val,
    (supported_mul_iff _ _).mpr ⟨(supported_sq_iff _).mpr p.1.property, admissible_supported p.2.property⟩⟩
  left_inv lengthScale := Subtype.ext (squarePart_sq_mul_squarefreePart lengthScale.val)
  right_inv p := by
    apply Prod.ext
    · exact Subtype.ext (squarePart_mul_squarefree p.1.property.1 p.2.property.2.1).1
    · exact Subtype.ext (squarePart_mul_squarefree p.1.property.1 p.2.property.2.1).2

theorem supported_tsum_squarefree_decomposition (f : Ideal O → ℂ) :
    (∑' lengthScale : Ideal O, if Supported lengthScale then f lengthScale else 0) =
      ∑' p : ({A : Ideal O // Supported A} × {B : Ideal O // Admissible B}), f (p.1.val ^ 2 * p.2.val) := by
  calc
    _ = ∑' lengthScale : {lengthScale : Ideal O // Supported lengthScale}, f lengthScale.val := by
      calc
        _ = ∑' lengthScale : Ideal O, ({lengthScale : Ideal O | Supported lengthScale} : Set (Ideal O)).indicator f lengthScale := by
          apply tsum_congr
          intro lengthScale
          rfl
        _ = _ := (tsum_subtype ({lengthScale : Ideal O | Supported lengthScale} : Set (Ideal O)) f).symm
    _ = _ := (supportedSquarefreeEquiv.symm.tsum_eq (fun lengthScale => f lengthScale.val)).symm

theorem canonical_quadraticRow_argument_mul (D : Ideal O) (hD : Admissible D) (a b : O) :
    quadraticRow D (a * b) = quadraticRow D a * quadraticRow D b := by
  let F : Finset (Ideal O) := {D}
  have hF : ∀ I ∈ F, Admissible I := by
    intro I hI
    have hID := Finset.mem_singleton.mp hI
    simpa only [hID] using hD
  simp only [quadraticRow_eq_pool F hF D (Finset.mem_singleton_self D)]
  exact QuadraticSquarefreeKernel.quadraticRow_mul _ _ _ a b

theorem canonical_quadraticRow_square_argument (D : Ideal O) (hD : Admissible D) (a : O) :
    quadraticRow D (a ^ 2) = idealZeroMask D a := by
  rw [pow_two, canonical_quadraticRow_argument_mul D hD, canonical_quadraticRow_squared D hD]

theorem canonical_quadraticRow_primary_squarefree (D : Ideal O) (hD : Admissible D)
    (A B : Ideal O) :
    quadraticRow D (primaryGenerator (A ^ 2 * B)) =
      idealZeroMask D (primaryGenerator A) * quadraticRow D (primaryGenerator B) := by
  rw [primaryGenerator_mul]
  have hpow : primaryGenerator (A ^ 2) = primaryGenerator A ^ 2 := map_pow primaryGeneratorHom A 2
  rw [hpow, canonical_quadraticRow_argument_mul D hD, canonical_quadraticRow_square_argument D hD]

theorem canonical_high_pair_squarefree_decomposition
    (I J : Ideal O) (hI : Admissible I) (hJ : Admissible J)
    (W : ℝ → ℂ) (M K : ℝ) :
    (∑' lengthScale : Ideal O, if Supported lengthScale ∧ K < (Ideal.absNorm (squarefreePart lengthScale) : ℝ) then
      (quadraticRow I (primaryGenerator lengthScale) * quadraticRow J (primaryGenerator lengthScale)) *
        W ((Ideal.absNorm lengthScale : ℝ) / M) else 0) =
    ∑' p : ({A : Ideal O // Supported A} × {B : Ideal O // Admissible B}),
      if K < (Ideal.absNorm p.2.val : ℝ) then
        (idealZeroMask I (primaryGenerator p.1.val) * idealZeroMask J (primaryGenerator p.1.val)) *
        (quadraticRow I (primaryGenerator p.2.val) * quadraticRow J (primaryGenerator p.2.val)) *
        W (((Ideal.absNorm p.1.val : ℝ) ^ 2 * (Ideal.absNorm p.2.val : ℝ)) / M) else 0 := by
  let f : Ideal O → ℂ := fun lengthScale => if K < (Ideal.absNorm (squarefreePart lengthScale) : ℝ) then
    (quadraticRow I (primaryGenerator lengthScale) * quadraticRow J (primaryGenerator lengthScale)) *
      W ((Ideal.absNorm lengthScale : ℝ) / M) else 0
  have he : (∑' lengthScale : Ideal O, if Supported lengthScale ∧ K < (Ideal.absNorm (squarefreePart lengthScale) : ℝ) then
      (quadraticRow I (primaryGenerator lengthScale) * quadraticRow J (primaryGenerator lengthScale)) *
        W ((Ideal.absNorm lengthScale : ℝ) / M) else 0) =
      ∑' lengthScale : Ideal O, if Supported lengthScale then f lengthScale else 0 := by
    apply tsum_congr
    intro lengthScale
    by_cases hL : Supported lengthScale <;> simp [hL, f]
  rw [he, supported_tsum_squarefree_decomposition]
  apply tsum_congr
  intro p
  dsimp only [f]
  rw [(squarePart_mul_squarefree p.1.property.1 p.2.property.2.1).2]
  by_cases hK : K < (Ideal.absNorm p.2.val : ℝ)
  · rw [if_pos hK, if_pos hK, canonical_quadraticRow_primary_squarefree I hI,
      canonical_quadraticRow_primary_squarefree J hJ]
    simp only [map_mul, map_pow, Nat.cast_mul, Nat.cast_pow]
    ring
  · simp only [if_neg hK]

end

section
open ActualEisensteinCubic ConcreteTraceCRT CompletedGauss
open EisensteinSchwartzPoisson PrimaryIdealUnitReindex QuadraticSquarefreeKernel

theorem supported_generator_injective :
    Function.Injective (fun lengthScale : {lengthScale : Ideal O // Supported lengthScale} => primaryGenerator lengthScale.val) := by
  intro I J h
  change primaryGenerator I.val = primaryGenerator J.val at h
  have hi := primaryGenerator_ne_zero_of_good_factors I.val I.property.1 (fun P hP => (I.property.2 P hP).1)
  have hj := primaryGenerator_ne_zero_of_good_factors J.val J.property.1 (fun P hP => (J.property.2 P hP).1)
  apply Subtype.ext
  rw [← (primaryGenerator_spec I.val hi).1, ← (primaryGenerator_spec J.val hj).1, h]

theorem supported_radial_norm_summable (W : 𝓢(ℝ, ℂ)) (M : ℝ) (hM : 0 < M) :
    Summable (fun lengthScale : Ideal O => if Supported lengthScale then ‖W ((Ideal.absNorm lengthScale : ℝ) / M)‖ else 0) := by
  have hs : Summable (fun z : O => ‖W (‖eisEmbedding z‖ ^ 2 / M)‖) := by
    simpa only [scaledRadialTest_apply] using actual_eisenstein_summable_norm (scaledRadialTest W M hM)
  have hp := hs.comp_injective supported_generator_injective
  have hi : Summable (fun lengthScale : {lengthScale : Ideal O // Supported lengthScale} => ‖W ((Ideal.absNorm lengthScale.val : ℝ) / M)‖) := by
    apply hp.congr
    intro lengthScale
    dsimp only [Function.comp_def]
    rw [primaryGenerator_norm_sq lengthScale.val (primaryGenerator_ne_zero_of_good_factors lengthScale.val
      lengthScale.property.1 (fun P hP => (lengthScale.property.2 P hP).1))]
  have ht : Summable (({lengthScale : Ideal O | Supported lengthScale} : Set (Ideal O)).indicator
      (fun lengthScale => ‖W ((Ideal.absNorm lengthScale : ℝ) / M)‖)) := (summable_subtype_iff_indicator).mp hi
  exact ht

def originalPairSource (I J : Ideal O) (W : ℝ → ℂ) (M : ℝ) (lengthScale : Ideal O) : ℂ :=
  if Supported lengthScale then (star (quadraticRow I (primaryGenerator lengthScale)) *
    quadraticRow J (primaryGenerator lengthScale)) * W ((Ideal.absNorm lengthScale : ℝ) / M) else 0

def originalPairLow (I J : Ideal O) (W : ℝ → ℂ) (M K : ℝ) (lengthScale : Ideal O) : ℂ :=
  if (Ideal.absNorm (squarefreePart lengthScale) : ℝ) ≤ K then originalPairSource I J W M lengthScale else 0

def originalPairHigh (I J : Ideal O) (W : ℝ → ℂ) (M K : ℝ) (lengthScale : Ideal O) : ℂ :=
  if K < (Ideal.absNorm (squarefreePart lengthScale) : ℝ) then originalPairSource I J W M lengthScale else 0

theorem originalPairSource_summable (I J : Ideal O) (W : 𝓢(ℝ, ℂ)) (M : ℝ) (hM : 0 < M) :
    Summable (originalPairSource I J W M) := by
  apply Summable.of_norm
  apply Summable.of_nonneg_of_le (fun lengthScale => norm_nonneg _) _ (supported_radial_norm_summable W M hM)
  intro lengthScale
  by_cases hL : Supported lengthScale
  · simp only [originalPairSource, if_pos hL, norm_mul, norm_star]
    calc
      _ ≤ (1 * 1) * ‖W ((Ideal.absNorm lengthScale : ℝ) / M)‖ := by
        gcongr
        · exact quadraticRow_norm_le_one I _
        · exact quadraticRow_norm_le_one J _
      _ = _ := by ring
  · simp only [originalPairSource, if_neg hL, norm_zero, le_refl]

theorem originalPairLow_summable (I J : Ideal O) (W : 𝓢(ℝ, ℂ)) (M K : ℝ) (hM : 0 < M) :
    Summable (originalPairLow I J W M K) :=
  (originalPairSource_summable I J W M hM).indicator _

theorem originalPairHigh_summable (I J : Ideal O) (W : 𝓢(ℝ, ℂ)) (M K : ℝ) (hM : 0 < M) :
    Summable (originalPairHigh I J W M K) :=
  (originalPairSource_summable I J W M hM).indicator _

theorem originalPairHigh_eq_source_sub_low (I J : Ideal O) (W : 𝓢(ℝ, ℂ))
    (M K : ℝ) (hM : 0 < M) :
    (∑' lengthScale : Ideal O, originalPairHigh I J W M K lengthScale) =
      (∑' lengthScale : Ideal O, originalPairSource I J W M lengthScale) -
        ∑' lengthScale : Ideal O, originalPairLow I J W M K lengthScale := by
  calc
    _ = ∑' lengthScale : Ideal O, (originalPairSource I J W M lengthScale - originalPairLow I J W M K lengthScale) := by
      apply tsum_congr
      intro lengthScale
      by_cases hK : (Ideal.absNorm (squarefreePart lengthScale) : ℝ) ≤ K
      · simp [originalPairHigh, originalPairLow, hK, not_lt.mpr hK]
      · simp [originalPairHigh, originalPairLow, hK, lt_of_not_ge hK]
    _ = _ := (originalPairSource_summable I J W M hM).tsum_sub (originalPairLow_summable I J W M K hM)

end

section
open ActualEisensteinCubic ConcreteTraceCRT CompletedGauss
open EisensteinSchwartzPoisson GaussGeneratorTransport

theorem canonical_gcd_masked_pair_poisson
    (D I J : Ideal O) (hI : Admissible I) (hJ : Admissible J)
    (hcop : IsCoprime I J) (hray : columnRay I = columnRay J)
    (W : 𝓢(ℝ, ℂ)) (M : ℝ) (hM : 0 < M) :
    let n := primaryGenerator I * primaryGenerator J
    let χ := fun z => quadraticRow I z * quadraticRow J z
    let R := fun P : gcdMaskPrimes D => P.val
    (∑' lengthScale : Ideal O, if Supported lengthScale then idealZeroMask D (primaryGenerator lengthScale) *
      χ (primaryGenerator lengthScale) * W ((Ideal.absNorm lengthScale : ℝ) / M) else 0) =
      ((M : ℂ) / (6 * ‖eisEmbedding n‖ : ℂ)) *
        ∑ E ∈ (Finset.univ : Finset (gcdMaskPrimes D)).powerset,
          let d := primeSubsetGenerator R E
          ((UniqueFactorizationMonoid.moebius (∏ i ∈ E, R i) : ℂ) * χ d /
            (‖eisEmbedding d‖ ^ 2 : ℝ)) *
          ∑' h : O, χ h * paperRadialFourier W
            (M * ‖eisEmbedding h‖ ^ 2 / (‖eisEmbedding d‖ ^ 2 * ‖eisEmbedding n‖ ^ 2)) := by
  let R := fun P : gcdMaskPrimes D => P.val
  have hm (z : O) (hz : lambda ∣ z) : rowCoprimeMask R Finset.univ z = 0 := by
    rw [gcdMaskPrimes_mask, badPrime_mask]
    have hns : ¬Supported (Ideal.span {z}) := fun h => (supported_span_iff z).mp h |>.1 hz
    simp only [if_neg hns, zero_mul]
  have hlat := canonical_same_ray_pair_poisson R Subtype.val_injective Finset.univ I J hI hJ hcop hray W M hM
  have hid := canonical_mask_lattice_eq_six_all_ideals R Finset.univ hm I J hI hJ hray W M hM
  have he : (∑' lengthScale : Ideal O, rowCoprimeMask R Finset.univ (primaryGenerator lengthScale) *
      (quadraticRow I (primaryGenerator lengthScale) * quadraticRow J (primaryGenerator lengthScale)) *
      W ((Ideal.absNorm lengthScale : ℝ) / M)) =
      ∑' lengthScale : Ideal O, if Supported lengthScale then idealZeroMask D (primaryGenerator lengthScale) *
        (quadraticRow I (primaryGenerator lengthScale) * quadraticRow J (primaryGenerator lengthScale)) *
        W ((Ideal.absNorm lengthScale : ℝ) / M) else 0 := by
    apply tsum_congr
    intro lengthScale
    rw [gcdMaskPrimes_mask, badPrime_mask_primaryGenerator]
    by_cases hL : Supported lengthScale <;> simp [hL]
  rw [he] at hid
  dsimp only at hlat ⊢
  rw [hid] at hlat
  calc
    _ = (6 : ℂ)⁻¹ * ((M : ℂ) / ‖eisEmbedding (primaryGenerator I * primaryGenerator J)‖ * _) := by
      rw [← hlat]
      ring
    _ = _ := by ring

theorem canonical_pair_divisor_mask (D I J : Ideal O) (hI : Admissible I) (hJ : Admissible J)
    (hDI : D ∣ I) (hDJ : D ∣ J) (z : O) :
    star (quadraticRow I z) * quadraticRow J z =
      idealZeroMask D z *
        (quadraticRow (idealQuotient D I) z * quadraticRow (idealQuotient D J) z) := by
  rw [canonical_quadraticRow_star I hI, quadraticRow_divisor_factor I D hI hDI,
    quadraticRow_divisor_factor J D hJ hDJ]
  calc
    _ = (quadraticRow D z * quadraticRow D z) *
        (quadraticRow (idealQuotient D I) z * quadraticRow (idealQuotient D J) z) := by ring
    _ = _ := by rw [canonical_quadraticRow_squared D (admissible_of_dvd hI hDI)]

theorem canonical_original_pair_poisson
    (D I J : Ideal O) (hI : Admissible I) (hJ : Admissible J)
    (hgcd : gcd I J = D) (hray : columnRay I = columnRay J)
    (W : 𝓢(ℝ, ℂ)) (M : ℝ) (hM : 0 < M) :
    let I' := idealQuotient D I
    let J' := idealQuotient D J
    let n := primaryGenerator I' * primaryGenerator J'
    let χ := fun z => quadraticRow I' z * quadraticRow J' z
    let R := fun P : gcdMaskPrimes D => P.val
    (∑' lengthScale : Ideal O, if Supported lengthScale then
      (star (quadraticRow I (primaryGenerator lengthScale)) * quadraticRow J (primaryGenerator lengthScale)) *
        W ((Ideal.absNorm lengthScale : ℝ) / M) else 0) =
      ((M : ℂ) / (6 * ‖eisEmbedding n‖ : ℂ)) *
        ∑ E ∈ (Finset.univ : Finset (gcdMaskPrimes D)).powerset,
          let d := primeSubsetGenerator R E
          ((UniqueFactorizationMonoid.moebius (∏ i ∈ E, R i) : ℂ) * χ d /
            (‖eisEmbedding d‖ ^ 2 : ℝ)) *
          ∑' h : O, χ h * paperRadialFourier W
            (M * ‖eisEmbedding h‖ ^ 2 / (‖eisEmbedding d‖ ^ 2 * ‖eisEmbedding n‖ ^ 2)) := by
  have hDI : D ∣ I := hgcd ▸ gcd_dvd_left I J
  have hDJ : D ∣ J := hgcd ▸ gcd_dvd_right I J
  have hD := admissible_of_dvd hI hDI
  have hIq := admissible_idealQuotient hI hDI
  have hJq := admissible_idealQuotient hJ hDJ
  have hcop := (gcd_eq_iff_quotient_coprime D I J hD.1 hDI hDJ).mp hgcd
  have hqray := columnRay_idealQuotient_eq D I J hI hJ hDI hDJ hray
  have h := canonical_gcd_masked_pair_poisson D (idealQuotient D I) (idealQuotient D J)
    hIq hJq hcop hqray W M hM
  simpa only [canonical_pair_divisor_mask D I J hI hJ hDI hDJ] using h

theorem residual_pair_nontrivial (D I J : Ideal O) (hDI : D ∣ I) (hDJ : D ∣ J)
    (hIJ : I ≠ J) : idealQuotient D I ≠ 1 ∨ idealQuotient D J ≠ 1 := by
  by_contra hn
  push Not at hn
  apply hIJ
  calc
    I = D * idealQuotient D I := (idealQuotient_mul hDI).symm
    _ = D := by rw [hn.1, mul_one]
    _ = D * idealQuotient D J := by rw [hn.2, mul_one]
    _ = J := idealQuotient_mul hDJ

theorem original_pair_dual_remove_zero (D I J : Ideal O) (hI : Admissible I) (hJ : Admissible J)
    (hDI : D ∣ I) (hDJ : D ∣ J) (hIJ : I ≠ J) (f : O → ℂ) :
    (∑' z : O, quadraticRow (idealQuotient D I) z * quadraticRow (idealQuotient D J) z * f z) =
      ∑' z : O, if z = 0 then 0 else
        quadraticRow (idealQuotient D I) z * quadraticRow (idealQuotient D J) z * f z :=
  quadratic_pair_tsum_remove_zero _ _ (admissible_idealQuotient hI hDI)
    (admissible_idealQuotient hJ hDJ) (residual_pair_nontrivial D I J hDI hDJ hIJ) f

end

section
open ActualEisensteinCubic ConcreteTraceCRT CompletedGauss QuadraticSquarefreeKernel

def rayPairCoefficient (N : ℝ) (D : Ideal O) (c : EisensteinEPrimaryPhase.Coord)
    (a : idealRange N → ℂ) (I J : idealRange N) : ℂ :=
  if gcd I.val J.val = D ∧ columnRay I.val = c ∧ columnRay J.val = c then star (a I) * a J else 0

theorem annularRayGcdBlock_eq_pair_high
    (M N K : ℝ) (hM : 0 < M) (D : Ideal O) (c : EisensteinEPrimaryPhase.Coord)
    (a : idealRange N → ℂ) :
    annularRayGcdBlock M N K D c a =
      ∑ I : idealRange N, ∑ J : idealRange N, rayPairCoefficient N D c a I J *
        ∑' lengthScale : Ideal O, originalPairHigh I.val J.val QuadraticInitialBound.annularSieveCutoff M K lengthScale := by
  let W := QuadraticInitialBound.annularSieveCutoff
  let f := fun (I J : idealRange N) (lengthScale : Ideal O) =>
    rayPairCoefficient N D c a I J * originalPairHigh I.val J.val W M K lengthScale
  have hf (I J : idealRange N) : Summable (f I J) :=
    (originalPairHigh_summable I.val J.val W M K hM).mul_left _
  have hterm (lengthScale : Ideal O) :
      (if Supported lengthScale ∧ K < (Ideal.absNorm (squarefreePart lengthScale) : ℝ) then
        W ((Ideal.absNorm lengthScale : ℝ) / M) * rayPairValue N D c a lengthScale else 0) =
      ∑ I : idealRange N, ∑ J : idealRange N, f I J lengthScale := by
    rw [rayPairValue_eq]
    by_cases hs : Supported lengthScale
    · by_cases hk : K < (Ideal.absNorm (squarefreePart lengthScale) : ℝ)
      · have hsk : Supported lengthScale ∧ K < (Ideal.absNorm (squarefreePart lengthScale) : ℝ) := ⟨hs, hk⟩
        rw [if_pos hsk]
        simp only [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro I _
        apply Finset.sum_congr rfl
        intro J _
        dsimp only [f, rayPairCoefficient, originalPairHigh, originalPairSource]
        rw [if_pos hk, if_pos hs]
        by_cases hc : gcd I.val J.val = D ∧ columnRay I.val = c ∧ columnRay J.val = c
        · rw [if_pos hc, if_pos hc]
          simp only [star_mul]
          ring
        · rw [if_neg hc, if_neg hc, zero_mul, mul_zero]
      · simp [f, originalPairHigh, hk]
    · simp [f, originalPairHigh, originalPairSource, hs]
  rw [annularRayGcdBlock_eq_tsum M N K hM D c a]
  change (∑' lengthScale : Ideal O, if Supported lengthScale ∧ K < (Ideal.absNorm (squarefreePart lengthScale) : ℝ) then
    W ((Ideal.absNorm lengthScale : ℝ) / M) * rayPairValue N D c a lengthScale else 0) = _
  calc
    _ = ∑' lengthScale : Ideal O, ∑ I : idealRange N, ∑ J : idealRange N, f I J lengthScale := tsum_congr hterm
    _ = ∑ I : idealRange N, ∑' lengthScale : Ideal O, ∑ J : idealRange N, f I J lengthScale :=
      Summable.tsum_finsetSum (fun I _ => summable_sum (fun J _ => hf I J))
    _ = _ := by
      apply Finset.sum_congr rfl
      intro I _
      rw [Summable.tsum_finsetSum (fun J _ => hf I J)]
      apply Finset.sum_congr rfl
      intro J _
      exact tsum_mul_left

theorem annularRayGcdBlock_eq_source_sub_low
    (M N K : ℝ) (hM : 0 < M) (D : Ideal O) (c : EisensteinEPrimaryPhase.Coord)
    (a : idealRange N → ℂ) :
    annularRayGcdBlock M N K D c a =
      ∑ I : idealRange N, ∑ J : idealRange N, rayPairCoefficient N D c a I J *
        ((∑' lengthScale : Ideal O, originalPairSource I.val J.val QuadraticInitialBound.annularSieveCutoff M lengthScale) -
          ∑' lengthScale : Ideal O, originalPairLow I.val J.val QuadraticInitialBound.annularSieveCutoff M K lengthScale) := by
  rw [annularRayGcdBlock_eq_pair_high M N K hM D c a]
  apply Finset.sum_congr rfl
  intro I _
  apply Finset.sum_congr rfl
  intro J _
  rw [originalPairHigh_eq_source_sub_low I.val J.val _ M K hM]

end

open ActualEisensteinCubic ConcreteTraceCRT CompletedGauss
open EisensteinSchwartzPoisson GaussGeneratorTransport

def originalPairDualKernel (D I J : Ideal O) (W : ℝ → ℂ) (M : ℝ) : ℂ :=
  let I' := idealQuotient D I
  let J' := idealQuotient D J
  let n := primaryGenerator I' * primaryGenerator J'
  let χ := fun z => quadraticRow I' z * quadraticRow J' z
  let R := fun P : gcdMaskPrimes D => P.val
  ((M : ℂ) / (6 * ‖eisEmbedding n‖ : ℂ)) *
    ∑ E ∈ (Finset.univ : Finset (gcdMaskPrimes D)).powerset,
      let d := primeSubsetGenerator R E
      ((UniqueFactorizationMonoid.moebius (∏ i ∈ E, R i) : ℂ) * χ d /
        (‖eisEmbedding d‖ ^ 2 : ℝ)) *
      ∑' h : O, χ h * paperRadialFourier W
        (M * ‖eisEmbedding h‖ ^ 2 / (‖eisEmbedding d‖ ^ 2 * ‖eisEmbedding n‖ ^ 2))

theorem originalPairSource_poisson (D I J : Ideal O) (hI : Admissible I) (hJ : Admissible J)
    (hgcd : gcd I J = D) (hray : columnRay I = columnRay J)
    (W : 𝓢(ℝ, ℂ)) (M : ℝ) (hM : 0 < M) :
    (∑' lengthScale : Ideal O, originalPairSource I J W M lengthScale) = originalPairDualKernel D I J W M :=
  canonical_original_pair_poisson D I J hI hJ hgcd hray W M hM

theorem annularRayGcdBlock_poisson
    (M N K : ℝ) (hM : 0 < M) (D : Ideal O) (c : EisensteinEPrimaryPhase.Coord)
    (a : idealRange N → ℂ) :
    annularRayGcdBlock M N K D c a =
      ∑ I : idealRange N, ∑ J : idealRange N, rayPairCoefficient N D c a I J *
        (originalPairDualKernel D I.val J.val QuadraticInitialBound.annularSieveCutoff M -
          ∑' lengthScale : Ideal O, originalPairLow I.val J.val QuadraticInitialBound.annularSieveCutoff M K lengthScale) := by
  rw [annularRayGcdBlock_eq_source_sub_low M N K hM D c a]
  apply Finset.sum_congr rfl
  intro I _
  apply Finset.sum_congr rfl
  intro J _
  by_cases hc : gcd I.val J.val = D ∧ columnRay I.val = c ∧ columnRay J.val = c
  · have hray : columnRay I.val = columnRay J.val := hc.2.1.trans hc.2.2.symm
    rw [originalPairSource_poisson D I.val J.val (mem_idealRange.mp I.property).1
      (mem_idealRange.mp J.property).1 hc.1 hray _ M hM]
  · simp only [rayPairCoefficient, if_neg hc, zero_mul]

end CanonicalQuadraticSieve

open scoped BigOperators Classical SchwartzMap ContDiff
namespace SecondPassIntegration
open ActualEisensteinCubic FirstPassCubeLabels JointLogSeparation

theorem columnLog_extract_common {ι : Type*} [DecidableEq ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0) (G N : Finset ι) (hd : Disjoint G N)
    (X : ℝ) (hX : 0 < X) :
    columnLog p X (G∪N) = columnLog p (X / primeProductNorm p G) N := by
  have hG := primeProductNorm_pos p hp G
  unfold columnLog
  rw [primeProductNorm_union p G N hd]
  congr 1
  field_simp

theorem normalizedColumn_extract_fixed_profile {ι : Type*} [DecidableEq ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0) (G N : Finset ι) (hd : Disjoint G N)
    (X : ℝ) (hX : 0 < X) (U : ℝ → ℂ) (hUc : HasCompactSupport U)
    (hUs : ContDiff ℝ ∞ U) (g : 𝓢(ℝ, ℂ)) (hU : ∀ s, g s ≠ 0 → U s = 1) :
    normalizedColumn p (fun S => g (columnLog p X S)) (G∪N) =
      halfNormalizationCLM U g (columnLog p (X / primeProductNorm p G) N) /
        (Real.sqrt X : ℂ) := by
  have hG := primeProductNorm_pos p hp G
  rw [normalizedColumn_union_test p hp G N hd X (X / primeProductNorm p G)
    hX (div_pos hX hG) U hUc hUs g hU]
  have he : primeProductNorm p G * (X / primeProductNorm p G) / X = 1 := by field_simp
  rw [he, Real.log_one, zero_add]

theorem normalizedColumn_pair_extract_fixed_profiles {ι : Type*} [DecidableEq ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0) (G N M : Finset ι)
    (hGN : Disjoint G N) (hGM : Disjoint G M) (X : ℝ) (hX : 0 < X)
    (U : ℝ → ℂ) (hUc : HasCompactSupport U) (hUs : ContDiff ℝ ∞ U)
    (g₁ g₂ : 𝓢(ℝ, ℂ)) (hU₁ : ∀ s, g₁ s ≠ 0 → U s = 1)
    (hU₂ : ∀ s, g₂ s ≠ 0 → U s = 1) :
    star (normalizedColumn p (fun S => g₁ (columnLog p X S)) (G∪N)) *
      normalizedColumn p (fun S => g₂ (columnLog p X S)) (G∪M) =
      (X : ℂ)⁻¹ * conjugateProfile (halfNormalizationCLM U g₁)
        (columnLog p (X / primeProductNorm p G) N) *
      halfNormalizationCLM U g₂ (columnLog p (X / primeProductNorm p G) M) := by
  have hG := primeProductNorm_pos p hp G
  rw [normalizedColumn_pair_union p hp G N M hGN hGM X (X / primeProductNorm p G)
    hX (div_pos hX hG) U hUc hUs g₁ g₂ hU₁ hU₂]
  have he : primeProductNorm p G * (X / primeProductNorm p G) / X = 1 := by field_simp
  rw [he, Real.log_one, zero_add, zero_add]

end SecondPassIntegration

open MeasureTheory
open scoped BigOperators Classical SchwartzMap FourierTransform
namespace SecondPassArithmetic
open ActualEisensteinCubic
open SecondPassIntegration (tupleSourceSum tupleSource_uniform_transfer childGeometricMean)
open JointLogSeparation
open FirstPassCubeLabels (b0Label)

variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i, lambda ∉ Ideal.span {p i})

def actualSecondVariableSectorSource
    (B : Finset ι) (v₁ v₂ : ι → ℕ) (ε₁ ε₂ : ι → Bool)
    (s : Finset (SecondSupportData ι)) (w : SecondSupportData ι → ℂ)
    (F : Finset ι) (Ψ₁ Ψ₂ : O →* ℂ) (m : O)
    (A₁ A₂ W : 𝓢(ℝ, ℂ)) (windows : Fin 7 → ℝ → ℂ)
    (D₀ E₀ V₀ : ℝ) (X : SecondSupportData ι → ℝ) (X₀ K Y : ℝ) : ℂ :=
  ∑ x ∈ s, w x * postCommonSmoothPair p hp hcop hg F Ψ₁ Ψ₂ m
    (secondSupportLabel p B v₁ v₂ ε₁ ε₂ x) (secondSupportRow p x) (-secondSupportRow p x)
    A₁ A₂ W windows (secondSectorZ p (X x) X₀ x) (secondSectorUd p D₀ x)
    (secondSectorUe p E₀ x) (secondSectorUv p V₀ x) (secondSectorKap p K x)
    X₀ X₀ (Y*K/(D₀*E₀^2*V₀^2*X₀^2))

theorem actual_second_variable_sector_uniform_transfer
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (ε : ℝ) (hε : 0 < ε) (A₁ A₂ W : 𝓢(ℝ, ℂ))
    (windows : Fin 7 → ℝ → ℂ) (M : Fin 7 → ℝ)
    (hM : ∀ j, 0 ≤ M j) (hwindows : ∀ j x, windows j x ≠ 0 → |x| ≤ M j) (A J : ℕ) :
    ∃ Cₐ : ℝ, 0 < Cₐ ∧ ∃ Cₛ : ℝ, 0 ≤ Cₛ ∧
      ∀ D₀ E₀ V₀ X₀ K Y : ℝ,
      0 < D₀ → 0 < E₀ → 0 < V₀ → 0 < X₀ → 0 < K → 0 < Y →
      ∃ b : 𝓢(ℝ, ℂ),
      (∀ t₁ t₂ t₃ : ℝ,
        (1 + Y*K/(D₀*E₀^2*V₀^2*X₀^2))^A * ‖(𝓕 A₁) t₁ * (𝓕 A₂) t₂ * b t₃‖ ≤
          Cₛ * FirstPassCubeLabels.firstLogDensity J t₁ *
            FirstPassCubeLabels.firstLogDensity J t₂ * FirstPassCubeLabels.firstLogDensity J t₃) ∧
      ∀ (B : Finset ι) (v₁ v₂ : ι → ℕ) (ε₁ ε₂ : ι → Bool)
        (s : Finset (SecondSupportData ι)) (T : Finset (Ideal O × O))
        (w : SecondSupportData ι → ℂ) (Bnd lengthScale : ℝ)
        (F : Finset ι) (Ψ₁ Ψ₂ : O →* ℂ) (m : O) (X : SecondSupportData ι → ℝ),
        (∀ i ∈ B, 0 < v₁ i + v₂ i) →
        (∀ x ∈ s, Disjoint x.common B) →
        (∀ x ∈ s, x.firstDivisor ⊆ x.common ∪ B) →
        0 ≤ Bnd → 0 ≤ lengthScale →
        (∀ x ∈ s, (secondSupportNewLabel p B v₁ v₂ ε₁ ε₂ x, secondSupportRow p x) ∈ T) →
        (∀ z ∈ T, z.1 ≠ ⊥) → (∀ z ∈ T, (Ideal.absNorm z.1 : ℝ) ≤ lengthScale) →
        (∀ x ∈ s, ‖w x‖ * ‖outerWindow windows
          (secondSectorZ p (X x) X₀ x) (secondSectorUd p D₀ x) (secondSectorUe p E₀ x)
          (secondSectorUv p V₀ x) (secondSectorKap p K x)‖ ≤ Bnd) →
        ‖actualSecondVariableSectorSource p hp hcop hg B v₁ v₂ ε₁ ε₂ s w F Ψ₁ Ψ₂ m
          A₁ A₂ W windows D₀ E₀ V₀ X X₀ K Y‖ ≤
        (Bnd * Cₐ * (lengthScale * Ideal.absNorm (Ideal.span {b0Label p B (fun i => v₁ i + v₂ i) ε₁ ε₂}))^ε) *
        (∫ t₁ : ℝ, ∫ t₂ : ℝ, ∫ t₃ : ℝ,
          ‖tripleCoefficient (𝓕 A₁) (𝓕 A₂) b (t₁,t₂,t₃)‖ *
            childGeometricMean p hp hcop hg F Ψ₁ Ψ₂ m T (windows 5) (windows 6) X₀ X₀ (t₁,t₂,t₃)) := by
  obtain ⟨Cₐ, hCₐ, Cₛ, hCₛ, htrans⟩ :=
    tupleSource_uniform_transfer p hp hcop hg ε hε A₁ A₂ W windows M hM hwindows A J
  refine ⟨Cₐ, hCₐ, Cₛ, hCₛ, ?_⟩
  intro D₀ E₀ V₀ X₀ K Y hD₀ hE₀ hV₀ hX₀ hK hY
  have hR : 0 < Y*K/(D₀*E₀^2*V₀^2*X₀^2) := by positivity
  obtain ⟨b, hb, hbound⟩ := htrans _ hR
  refine ⟨b, hb, ?_⟩
  intro B v₁ v₂ ε₁ ε₂ s T w Bnd lengthScale F Ψ₁ Ψ₂ m X hv hCB hD hBnd hL hmap hT0 hnorm hw
  let encode := secondSupportTuple p B v₁ v₂ ε₁ ε₂
  have hi : Function.Injective encode := secondSupportTuple_injective p hinj B v₁ v₂ ε₁ ε₂
  let decode := Function.invFun encode
  have hdec (x : SecondSupportData ι) : decode (encode x) = x := Function.leftInverse_invFun hi x
  let s' := s.image encode
  let w' := fun x => w (decode x)
  let label' := fun x => secondSupportLabel p B v₁ v₂ ε₁ ε₂ (decode x)
  let z' := fun x => secondSectorZ p (X (decode x)) X₀ (decode x)
  let ud' := fun x => secondSectorUd p D₀ (decode x)
  let ue' := fun x => secondSectorUe p E₀ (decode x)
  let uv' := fun x => secondSectorUv p V₀ (decode x)
  let kap' := fun x => secondSectorKap p K (decode x)
  have hsvalid : ∀ x ∈ s', SecondPassFiber.Valid x (SecondPassFiber.newLabel x)
      (Ideal.span {b0Label p B (fun i => v₁ i + v₂ i) ε₁ ε₂}) (SecondPassFiber.newRow x) := by
    intro x hx
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hx
    exact secondSupportTuple_valid p B v₁ v₂ ε₁ ε₂ hv a (hCB a ha) (hD a ha)
  have hsmap : ∀ x ∈ s', (SecondPassFiber.newLabel x, SecondPassFiber.newRow x) ∈ T := by
    intro x hx
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hx
    exact hmap a ha
  have hsw : ∀ x ∈ s', ‖w' x‖ * ‖outerWindow windows (z' x) (ud' x) (ue' x) (uv' x) (kap' x)‖ ≤ Bnd := by
    intro x hx
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hx
    dsimp only [w', z', ud', ue', uv', kap']
    rw [hdec]
    exact hw a ha
  have hslabel : ∀ x ∈ s', Ideal.span {label' x} = SecondPassFiber.newLabel x := by
    intro x hx
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hx
    dsimp only [label']
    rw [hdec]
    exact secondSupportLabel_span p B v₁ v₂ ε₁ ε₂ a
  have hout := hbound s' T (Ideal.span {b0Label p B (fun i => v₁ i + v₂ i) ε₁ ε₂})
    w' Bnd lengthScale label' F Ψ₁ Ψ₂ m z' ud' ue' uv' kap' X₀ X₀
    (sector_b0_ne_bot p hp B v₁ v₂ ε₁ ε₂) hBnd hL hsvalid hsmap hT0 hnorm hsw hslabel
  have hsource : tupleSourceSum p hp hcop hg s' w' label' F Ψ₁ Ψ₂ m
      A₁ A₂ W windows z' ud' ue' uv' kap' X₀ X₀ (Y*K/(D₀*E₀^2*V₀^2*X₀^2)) =
      actualSecondVariableSectorSource p hp hcop hg B v₁ v₂ ε₁ ε₂ s w F Ψ₁ Ψ₂ m
        A₁ A₂ W windows D₀ E₀ V₀ X X₀ K Y := by
    unfold tupleSourceSum actualSecondVariableSectorSource
    rw [Finset.sum_image (fun a ha c hc h => hi h)]
    apply Finset.sum_congr rfl
    intro a ha
    dsimp only [w', label', z', ud', ue', uv', kap']
    rw [hdec]
    rfl
  rw [hsource] at hout
  exact hout

end SecondPassArithmetic

end

end OAI

end


