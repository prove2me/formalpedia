-- Prove2me | Definitions.Def_OAI_NumberTheory_DirichletL_CubicSieve_ResidualSectors
-- name    : OAI_NumberTheory_DirichletL_CubicSieve_ResidualSectors
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-07T09:00:40.913485+00:00
-- url     : https://prove2.me/theorems/92c855e3-9d93-42d7-8035-c97941a3e39d
-- title:
--   Residual Sectors
-- statement:
--   Definitions and structural lemmas for Residual Sectors, from LW56e2 and the credited OpenAI and dependency authors's pinned QRH LW56e2 refinement development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/CubicSieve/ResidualSectors.lean

import Definitions.Def_OAI_NumberTheory_DirichletL_QuadraticSieve_SquareParts
import Theorems.Thm_OAI_ActualEisensteinCubic_principalSexticRow_mk
import Theorems.Thm_OAI_ConcretePrimeRowBridge_idealGenerator_ne_zero
import Theorems.Thm_OAI_ConcretePrimeRowBridge_span_idealGenerator
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
import Theorems.Thm_OAI_SecondPassIntegration_normalizedColumn_pair_extract_fixed_profiles
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
open scoped BigOperators Classical
namespace SecondPassArithmetic
section
open ActualEisensteinCubic
open ActualEisensteinCubic
open ConcreteTraceCRT (eisEmbedding)
open EisensteinSchwartzPoisson (paperRadialFourier)
open FirstPassCubeLabels (primeProductNorm)
variable {ι : Type*} [DecidableEq ι]
  (p : ι → OAI.SecondPassArithmetic.O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hg : ∀ i, lambda ∉ Ideal.span {p i})
  (hinj : Function.Injective (fun i => Ideal.span {p i}))
def secondSourcePairKernel (e k : O) (H₁ H₂ : Finset ι → ℂ)
    (W : 𝓢(ℝ, ℂ)) (Y : ℝ) (S T : Finset ι) : ℂ :=
  (star (H₁ S) * H₂ T /
    ((‖eisEmbedding (∏ i ∈ S, p i)‖ : ℂ) * (‖eisEmbedding (∏ i ∈ T, p i)‖ : ℂ))) *
    paperRadialFourier W (Y * ‖eisEmbedding k‖ ^ 2 /
      (‖eisEmbedding e‖ ^ 2 * (primeProductNorm p S * primeProductNorm p T)))
def secondSourceCommonCoefficient (Ψ : O →* ℂ) (m c d : O) (G E : Finset ι) : ℂ :=
  (↑(‖secondInputCoefficient p hg Ψ m c d (fun _ => 1) G‖ ^ 2) : ℂ) *
    ((UniqueFactorizationMonoid.moebius (∏ i ∈ E, Ideal.span {p i}) : ℂ) /
      (‖eisEmbedding (primeSubsetGenerator (fun i => Ideal.span {p i}) E)‖ ^ 2 : ℝ))
def truncatedSecondSource (F : Finset ι) (Ψ : O →* ℂ) (m c d : O)
    (H : Finset ι → ℂ) (W : 𝓢(ℝ, ℂ)) (Y : ℝ) (K : Finset ι → Finset ι → Finset O) : ℂ :=
  ∑ G ∈ F.powerset, ∑ E : G.powerset, ∑ k ∈ K G E.val,
    secondSourceCommonCoefficient p hg Ψ m c d G E.val *
      secondFrequencyKernel p hp hg hinj F Ψ Ψ m
        (secondMaskQuotient p E.val G (Finset.mem_powerset.mp E.property)) c d
        (primeSubsetGenerator (fun i => Ideal.span {p i}) E.val) k
        (fun U => H (G ∪ U)) (fun U => H (G ∪ U)) W Y
def secondSourceTail (F : Finset ι) (Ψ : O →* ℂ) (m c d : O)
    (H : Finset ι → ℂ) (W : 𝓢(ℝ, ℂ)) (Y : ℝ) (K : Finset ι → Finset ι → Finset O) : ℂ :=
  ∑ G ∈ F.powerset, ∑ E : G.powerset,
    secondSourceCommonCoefficient p hg Ψ m c d G E.val *
      ∑' k : {k : O // k ∉ K G E.val},
        secondFrequencyKernel p hp hg hinj F Ψ Ψ m
          (secondMaskQuotient p E.val G (Finset.mem_powerset.mp E.property)) c d
          (primeSubsetGenerator (fun i => Ideal.span {p i}) E.val) k.val
          (fun U => H (G ∪ U)) (fun U => H (G ∪ U)) W Y
end
open ActualEisensteinCubic
open FirstPassCubeLabels (primeProductNorm)
open ConcreteTraceCRT (eisEmbedding)
@[ext] structure SecondExpansionData (ι : Type*) where
  sourceCommon : Finset ι
  divisor : Finset ι
  overlap : Finset ι
  frequency : O
  deriving DecidableEq
section
variable {ι : Type*} [DecidableEq ι]
  (p : ι → OAI.SecondPassArithmetic.O) [∀ i, (Ideal.span {p i}).IsMaximal]
def InSecondQuotientSector (r : O) (x : SecondExpansionData ι) : Prop :=
  ∃ h : x.divisor ⊆ x.sourceCommon,
    Ideal.span {secondMaskQuotient p x.divisor x.sourceCommon h} = Ideal.span {r}
def expansionSupportData (C D : Finset ι) (x : SecondExpansionData ι) : SecondSupportData ι where
  common := C
  firstDivisor := D
  secondDivisor := x.divisor
  overlap := x.overlap
  frequency := x.frequency
end
end SecondPassArithmetic
open scoped BigOperators Classical SchwartzMap
namespace SecondPassIntegration
open ActualEisensteinCubic FirstPassCubeLabels
open SecondPassArithmetic (SecondSupportData secondSectorZ)
def residualColumnScale (X : ℝ) (e r : O) : ℝ :=
  X / (elementNorm e * elementNorm r)
end SecondPassIntegration
open scoped BigOperators Classical SchwartzMap ContDiff
namespace SecondPassArithmetic
section
open ActualEisensteinCubic
open FirstPassCubeLabels (jLabel)
open SecondPassIntegration (exists_fixed_normalized_child_tests elementNorm)
variable {ι : Type*} [DecidableEq ι]
  (p : ι → OAI.SecondPassArithmetic.O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i, lambda ∉ Ideal.span {p i})
def actualSecondRawVariableSector
    (B : Finset ι) (v₁ v₂ : ι → ℕ) (ε₁ ε₂ : ι → Bool)
    (s : Finset (SecondSupportData ι)) (w : SecondSupportData ι → ℂ)
    (F : Finset ι) (Ψ₁ Ψ₂ : O →* ℂ) (m r : O)
    (g₁ g₂ W : 𝓢(ℝ, ℂ)) (X : SecondSupportData ι → ℝ) (Y : ℝ) : ℂ :=
  ∑ x ∈ s, w x *
    secondChildKernelPair p hp hcop hg F x.overlap Ψ₁ Ψ₂ m r
      (primeSubsetGenerator (fun i => Ideal.span {p i}) x.common *
        jLabel p B (fun i => v₁ i + v₂ i) ε₁ ε₂)
      (primeSubsetGenerator (fun i => Ideal.span {p i}) x.firstDivisor)
      (primeSubsetGenerator (fun i => Ideal.span {p i}) x.secondDivisor)
      x.frequency (-x.frequency)
      (radialPairKernel p (primeSubsetGenerator (fun i => Ideal.span {p i}) x.secondDivisor)
        x.frequency W g₁ g₂ (X x) (X x) Y)
end
section
open MeasureTheory
open scoped BigOperators Classical SchwartzMap FourierTransform
open ActualEisensteinCubic
open FirstPassCubeLabels (b0Label firstLogDensity)
open SecondPassIntegration (childGeometricMean)
open JointLogSeparation
end
open ActualEisensteinCubic
open FirstPassCubeLabels (columnLog normalizedColumn primeProductNorm)
open JointLogSeparation (halfNormalizationCLM)
open SecondPassIntegration (normalizedColumn_pair_extract_fixed_profiles conjugateProfile)
end SecondPassArithmetic
open scoped BigOperators Classical
namespace UnrestrictedIdealReindex
abbrev O := ActualEisensteinCubic.O
open ActualEisensteinCubic ConcreteTraceCRT ConcretePrimeRowBridge
open PrimaryIdealUnitReindex CanonicalQuadraticSieve
abbrev NonzeroIdeal := {I : Ideal O // I ≠ 0}
abbrev NonzeroElement := {z : O // z ≠ 0}
theorem span_unit_generator (u : Oˣ) (I : NonzeroIdeal) :
    Ideal.span {u.val * idealGenerator I.val} = I.val := by
  rw [Ideal.span_singleton_mul_left_unit u.isUnit, span_idealGenerator]
def unitIdealToElement (p : Oˣ × NonzeroIdeal) : NonzeroElement :=
  ⟨p.1.val * idealGenerator p.2.val, mul_ne_zero p.1.ne_zero (idealGenerator_ne_zero p.2.val p.2.property)⟩
theorem unitIdealToElement_bijective : Function.Bijective unitIdealToElement := by
  constructor
  · intro p q hpq
    have he : p.1.val * idealGenerator p.2.val = q.1.val * idealGenerator q.2.val := congrArg Subtype.val hpq
    have hi : p.2 = q.2 := by
      apply Subtype.ext
      simpa only [span_unit_generator] using congrArg (fun z : O => Ideal.span {z}) he
    have hu : p.1 = q.1 := by
      apply Units.ext
      rw [hi] at he
      exact mul_right_cancel₀ (idealGenerator_ne_zero q.2.val q.2.property) he
    exact Prod.ext hu hi
  · intro z
    let I : NonzeroIdeal := ⟨Ideal.span {z.val}, Ideal.span_singleton_eq_bot.not.mpr z.property⟩
    have ha : Associated (idealGenerator I.val) z.val :=
      Ideal.span_singleton_eq_span_singleton.mp (span_idealGenerator I.val)
    obtain ⟨u, hu⟩ := ha
    refine ⟨(u, I), Subtype.ext ?_⟩
    change u.val * idealGenerator I.val = z.val
    simpa only [mul_comm] using hu
def unitIdealEquiv : Oˣ × NonzeroIdeal ≃ NonzeroElement :=
  Equiv.ofBijective unitIdealToElement unitIdealToElement_bijective
end UnrestrictedIdealReindex
end
end OAI


