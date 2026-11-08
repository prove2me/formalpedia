-- Prove2me | Definitions.Def_OAI_NumberTheory_DirichletL_Fourier_LogDensity
-- name    : OAI_NumberTheory_DirichletL_Fourier_LogDensity
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-07T10:20:38.326535+00:00
-- url     : https://prove2.me/theorems/dcb9edbf-5365-429a-a749-8988c546f8c8
-- title:
--   Log Density
-- statement:
--   Definitions and structural lemmas for Log Density, from LW56e2 and the credited OpenAI and dependency authors's pinned QRH LW56e2 refinement development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/Fourier/LogDensity.lean

import Definitions.Def_OAI_NumberTheory_DirichletL_QuadraticSieve_TruncatedSecondTransfer
import Theorems.Thm_OAI_ActualEisensteinCubic_principalSexticRow_mk
import Theorems.Thm_OAI_CanonicalQuadraticSieve_gcd_eq_iff_quotient_coprime
import Theorems.Thm_OAI_CanonicalQuadraticSieve_idealQuotient_dvd
import Theorems.Thm_OAI_CanonicalQuadraticSieve_idealQuotient_mul
import Theorems.Thm_OAI_CanonicalQuadraticSieve_unrestrictedPairCharacter_mul
import Theorems.Thm_OAI_CanonicalQuadraticSieve_unrestrictedPairCharacter_span
import Theorems.Thm_OAI_CubicReflectionKernel_logSchwartz_apply
import Theorems.Thm_OAI_EisensteinSchwartzPoisson_halfEulerIterateCLM_apply
import Theorems.Thm_OAI_EisensteinSchwartzPoisson_paperFourierRayCLM_apply
import Theorems.Thm_OAI_EisensteinSchwartzPoisson_paperRealRayCLM_apply
import Theorems.Thm_OAI_EisensteinSchwartzPoisson_verticalSlice_apply
import Theorems.Thm_OAI_FiniteGaussPhase_productElementCRT_mk
import Theorems.Thm_OAI_FiniteRayExpansion_zeroExtendUnits_nonunit
import Theorems.Thm_OAI_FiniteRayExpansion_zeroExtendUnits_unit
import Theorems.Thm_OAI_FirstPassCubeLabels_coreRayTwist_prod
import Theorems.Thm_OAI_FirstPassCubeLabels_twisted_core_product
import Theorems.Thm_OAI_IdealGaussCRT_quotientProdEquivPi_mk
import Theorems.Thm_OAI_IdealGaussCRT_traceProdChar_mk
import Theorems.Thm_OAI_JointLogSeparation_frequencyTwist_apply
import Theorems.Thm_OAI_JointLogSeparation_frequencyTwist_norm
import Theorems.Thm_OAI_JointLogSeparation_frequencyTwist_twice
import Theorems.Thm_OAI_LocalLogFourier_positiveLogProfile_apply
import Theorems.Thm_OAI_QuadraticGaussRay_residueQuotientFour_mk
import Theorems.Thm_OAI_QuadraticInitialBound_annularSieveCutoff_apply
import Theorems.Thm_OAI_QuadraticInitialBound_annularSieveCutoff_zero
import Theorems.Thm_OAI_QuadraticInitialBound_sieveCutoff_apply
import Theorems.Thm_OAI_SecondPassArithmetic_secondSupportTuple_newLabel
import Theorems.Thm_OAI_SecondPassArithmetic_secondSupportTuple_newRow
import Theorems.Thm_OAI_SecondPassIntegration_conjugateProfile_apply
attribute [local simp] OAI.ActualEisensteinCubic.principalSexticRow_mk
attribute [local simp] OAI.CubicReflectionKernel.logSchwartz_apply
attribute [local simp] OAI.EisensteinSchwartzPoisson.halfEulerIterateCLM_apply
attribute [local simp] OAI.EisensteinSchwartzPoisson.paperFourierRayCLM_apply
attribute [local simp] OAI.EisensteinSchwartzPoisson.paperRealRayCLM_apply
attribute [local simp] OAI.EisensteinSchwartzPoisson.verticalSlice_apply
attribute [local simp] OAI.FiniteGaussPhase.productElementCRT_mk
attribute [local simp] OAI.FiniteRayExpansion.zeroExtendUnits_nonunit
attribute [local simp] OAI.FiniteRayExpansion.zeroExtendUnits_unit
attribute [local simp] OAI.FirstPassCubeLabels.coreRayTwist_prod
attribute [local simp] OAI.FirstPassCubeLabels.twisted_core_product
attribute [local simp] OAI.IdealGaussCRT.quotientProdEquivPi_mk
attribute [local simp] OAI.IdealGaussCRT.traceProdChar_mk
attribute [local simp] OAI.JointLogSeparation.frequencyTwist_apply
attribute [local simp] OAI.JointLogSeparation.frequencyTwist_norm
attribute [local simp] OAI.JointLogSeparation.frequencyTwist_twice
attribute [local simp] OAI.LocalLogFourier.positiveLogProfile_apply
attribute [local simp] OAI.QuadraticGaussRay.residueQuotientFour_mk
attribute [local simp] OAI.QuadraticInitialBound.annularSieveCutoff_apply
attribute [local simp] OAI.QuadraticInitialBound.annularSieveCutoff_zero
attribute [local simp] OAI.QuadraticInitialBound.sieveCutoff_apply
attribute [local simp] OAI.SecondPassArithmetic.secondSupportTuple_newLabel
attribute [local simp] OAI.SecondPassArithmetic.secondSupportTuple_newRow
attribute [local simp] OAI.SecondPassIntegration.conjugateProfile_apply


set_option autoImplicit false
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
section
open MeasureTheory
open scoped BigOperators Classical SchwartzMap FourierTransform
namespace JointLogSeparation
open FirstPassCubeLabels
def tripleLogDensity (J : ℕ) (t : Frequency) : ℝ :=
  firstLogDensity J t.1 * (firstLogDensity J t.2.1 * firstLogDensity J t.2.2)
end JointLogSeparation
namespace SecondPassIntegration
open ActualEisensteinCubic SecondPassArithmetic JointLogSeparation
def densityChildEnergy {ι : Type*} [DecidableEq ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i, lambda ∉ Ideal.span {p i})
    (F : Finset ι) (Ψ₁ Ψ₂ : O →* ℂ) (m : O) (T : Finset (Ideal O × O))
    (V₁ V₂ : ℝ → ℂ) (X₁ X₂ : ℝ) (J : ℕ) : ℝ :=
  ∫ t₁ : ℝ, ∫ t₂ : ℝ, ∫ t₃ : ℝ,
    tripleLogDensity J (t₁,t₂,t₃) *
      childGeometricMean p hp hcop hg F Ψ₁ Ψ₂ m T V₁ V₂ X₁ X₂ (t₁,t₂,t₃)
end SecondPassIntegration
namespace JointLogSeparation
open FirstPassCubeLabels
end JointLogSeparation
end
open scoped BigOperators Classical
namespace CanonicalQuadraticSieve
section
open ActualEisensteinCubic CompletedGauss IdealMobiusDivisorSum
theorem ideals_coprime_of_relprime (A B : Ideal O) (h : IsRelPrime A B) : IsCoprime A B := by
  apply Ideal.isCoprime_iff_gcd.mpr
  simpa only [Ideal.one_eq_top] using Ideal.isUnit_iff.mp (h (GCDMonoid.gcd_dvd_left A B) (GCDMonoid.gcd_dvd_right A B))
theorem squarefree_quotient_gcd_coprime (B G : Ideal O) (hB : Squarefree B) :
    IsCoprime (idealQuotient (gcd B G) B) G := by
  let D := gcd B G
  have hDB : D ∣ B := GCDMonoid.gcd_dvd_left B G
  have hDG : D ∣ G := GCDMonoid.gcd_dvd_right B G
  have hD : D ≠ 0 := ne_zero_of_dvd_ne_zero hB.ne_zero hDB
  have hc : IsCoprime (idealQuotient D B) (idealQuotient D G) :=
    (gcd_eq_iff_quotient_coprime D B G hD hDB hDG).mp rfl
  have hmul : Squarefree (D * idealQuotient D B) := by rw [idealQuotient_mul hDB]; exact hB
  have hdq : IsCoprime D (idealQuotient D B) :=
    ideals_coprime_of_relprime _ _ (squarefree_mul_iff.mp hmul).1
  have hh := hdq.symm.mul_right hc
  rw [idealQuotient_mul hDG] at hh
  exact hh
theorem gcd_mul_of_coprime_divisor (D H G : Ideal O) (hDG : D ∣ G) (hHG : IsCoprime H G) :
    gcd (D * H) G = D := by
  have hleft : D ∣ gcd (D * H) G := GCDMonoid.dvd_gcd (dvd_mul_right D H) hDG
  have hcop : IsCoprime (gcd (D * H) G) H :=
    (hHG.mono (dvd_refl H) (GCDMonoid.gcd_dvd_right (D * H) G)).symm
  have hright : gcd (D * H) G ∣ D := hcop.dvd_of_dvd_mul_right (GCDMonoid.gcd_dvd_left _ _)
  exact associated_iff_eq.mp (associated_of_dvd_dvd hright hleft)
def squarefreeGcdEquiv (G : Ideal O) (hG : Squarefree G) :
    {B : Ideal O // Squarefree B} ≃
      (idealDivisors G) × {H : Ideal O // Squarefree H ∧ IsCoprime H G} where
  toFun B := (⟨gcd B.val G, (mem_idealDivisors hG.ne_zero).mpr (GCDMonoid.gcd_dvd_right _ _)⟩,
    ⟨idealQuotient (gcd B.val G) B.val,
      B.property.squarefree_of_dvd (idealQuotient_dvd (GCDMonoid.gcd_dvd_left _ _)),
      squarefree_quotient_gcd_coprime B.val G B.property⟩)
  invFun p := ⟨p.1.val * p.2.val, squarefree_mul_iff.mpr
    ⟨(p.2.property.2.mono (dvd_refl _) ((mem_idealDivisors hG.ne_zero).mp p.1.property)).symm.isRelPrime,
      hG.squarefree_of_dvd ((mem_idealDivisors hG.ne_zero).mp p.1.property), p.2.property.1⟩⟩
  left_inv B := Subtype.ext (idealQuotient_mul (GCDMonoid.gcd_dvd_left B.val G))
  right_inv p := by
    apply Prod.ext
    · apply Subtype.ext
      exact gcd_mul_of_coprime_divisor p.1.val p.2.val G
        ((mem_idealDivisors hG.ne_zero).mp p.1.property) p.2.property.2
    · apply Subtype.ext
      change idealQuotient (gcd (p.1.val * p.2.val) G) (p.1.val * p.2.val) = p.2.val
      rw [gcd_mul_of_coprime_divisor p.1.val p.2.val G
        ((mem_idealDivisors hG.ne_zero).mp p.1.property) p.2.property.2]
      have hD : p.1.val ≠ 0 := ne_zero_of_dvd_ne_zero hG.ne_zero
        ((mem_idealDivisors hG.ne_zero).mp p.1.property)
      exact mul_left_cancel₀ hD (idealQuotient_mul (dvd_mul_right p.1.val p.2.val))
def coprimeSquarefreeRange (G : Ideal O) (K : ℝ) : Finset (Ideal O) :=
  (squarefreeIdealRange K).filter (fun H => IsCoprime H G)
end
section
open ActualEisensteinCubic ConcreteTraceCRT ConcretePrimeRowBridge CompletedGauss
open IdealMobiusDivisorSum
theorem canonical_quadraticRow_one (I : Ideal O) (hI : Admissible I) : quadraticRow I 1 = 1 := by
  rw [quadraticRow, dif_pos hI]
  simp [idealSexticRow, finiteSquarefreeRow]
theorem unrestrictedPairCharacter_one (I J : Ideal O) (hI : Admissible I) (hJ : Admissible J)
    (hray : columnRay I = columnRay J) : unrestrictedPairCharacter I J 1 = 1 := by
  have h := unrestrictedPairCharacter_span I J hI hJ hray 1
  simpa only [Ideal.span_singleton_one, canonical_quadraticRow_one I hI,
    canonical_quadraticRow_one J hJ, one_mul, Ideal.one_eq_top] using h
def normalizedIdealPair (I J lengthScale : Ideal O) : ℂ :=
  unrestrictedPairCharacter I J lengthScale / (Real.sqrt (Ideal.absNorm lengthScale : ℝ) : ℂ)
theorem normalizedIdealPair_mul (I J : Ideal O) (hI : Admissible I) (hJ : Admissible J)
    (hray : columnRay I = columnRay J) (A B : Ideal O) :
    normalizedIdealPair I J (A * B) = normalizedIdealPair I J A * normalizedIdealPair I J B := by
  simp only [normalizedIdealPair, unrestrictedPairCharacter_mul I J hI hJ hray,
    map_mul, Nat.cast_mul, Real.sqrt_mul (Nat.cast_nonneg _), Complex.ofReal_mul, div_mul_div_comm]
def normalizedIdealPairHom (I J : Ideal O) (hI : Admissible I) (hJ : Admissible J)
    (hray : columnRay I = columnRay J) : Ideal O →* ℂ where
  toFun := normalizedIdealPair I J
  map_one' := by
    rw [normalizedIdealPair, unrestrictedPairCharacter_one I J hI hJ hray, map_one]
    norm_num
  map_mul' := normalizedIdealPair_mul I J hI hJ hray
end
section
open ActualEisensteinCubic ConcreteTraceCRT CompletedGauss
open IdealMobiusDivisorSum QuadraticMainBoundary
def idealNormCutoff (K : ℝ) (H : Ideal O) : ℂ := if (Ideal.absNorm H : ℝ) ≤ K then 1 else 0
def normalizedPairPartial (I J : Ideal O) (K : ℝ) : ℂ :=
  ∑ B : squarefreeIdealRange K, normalizedIdealPair I J B.val
def normalizedPairCoprimePartial (I J G : Ideal O) (K : ℝ) : ℂ :=
  ∑ H : coprimeSquarefreeRange G K, normalizedIdealPair I J H.val
def normalizedPairDivisors (I J G : Ideal O) : ℂ :=
  ∑ E ∈ idealDivisors G, (UniqueFactorizationMonoid.moebius E : ℂ) * normalizedIdealPair I J E
def normalizedPairDensity (I J G : Ideal O) : ℂ :=
  ∏ P ∈ IdealMobiusDivisorSum.primeSupport G,
    (1 - (idealZeroMask I (ConcretePrimeRowBridge.idealGenerator P) *
      idealZeroMask J (ConcretePrimeRowBridge.idealGenerator P)) / (Ideal.absNorm P : ℂ))
end
open ActualEisensteinCubic ConcretePrimeRowBridge CompletedGauss IdealMobiusDivisorSum
def commonMaskIdeal (D : Ideal O) : Ideal O := ∏ P ∈ gcdMaskPrimes D, P
end CanonicalQuadraticSieve
end
end OAI


