-- Prove2me | Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_ReflectionBrackets
-- name    : OAI_NumberTheory_DirichletL_GaussSum_ReflectionBrackets
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-07T00:17:55.391864+00:00
-- url     : https://prove2.me/theorems/cbdd6581-ec1f-4b52-a74b-0995bd1094df
-- title:
--   Reflection Brackets
-- statement:
--   Definitions and structural lemmas for Reflection Brackets, from LW56e2 and the credited OpenAI and dependency authors's pinned QRH LW56e2 refinement development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/GaussSum/ReflectionBrackets.lean

import Definitions.Def_OAI_NumberTheory_DirichletL_CubicSieve_LocalBrackets
import Theorems.Thm_OAI_ActualEisensteinCubic_principalSexticRow_mk
import Theorems.Thm_OAI_CubicReflectionKernel_logSchwartz_apply
import Theorems.Thm_OAI_EisensteinSchwartzPoisson_halfEulerIterateCLM_apply
import Theorems.Thm_OAI_EisensteinSchwartzPoisson_paperFourierRayCLM_apply
import Theorems.Thm_OAI_EisensteinSchwartzPoisson_paperRadialFourier_square
import Theorems.Thm_OAI_EisensteinSchwartzPoisson_paperRealRayCLM_apply
import Theorems.Thm_OAI_EisensteinSchwartzPoisson_verticalSlice_apply
import Theorems.Thm_OAI_FiniteGaussPhase_productElementCRT_mk
import Theorems.Thm_OAI_FiniteRayExpansion_zeroExtendUnits_nonunit
import Theorems.Thm_OAI_FiniteRayExpansion_zeroExtendUnits_unit
import Theorems.Thm_OAI_IdealGaussCRT_quotientProdEquivPi_mk
import Theorems.Thm_OAI_IdealGaussCRT_traceProdChar_mk
import Theorems.Thm_OAI_LocalLogFourier_positiveLogProfile_apply
import Theorems.Thm_OAI_QuadraticGaussRay_residueQuotientFour_mk
import Theorems.Thm_OAI_QuadraticInitialBound_sieveCutoff_apply
attribute [local simp] OAI.ActualEisensteinCubic.principalSexticRow_mk
attribute [local simp] OAI.CubicReflectionKernel.logSchwartz_apply
attribute [local simp] OAI.EisensteinSchwartzPoisson.halfEulerIterateCLM_apply
attribute [local simp] OAI.EisensteinSchwartzPoisson.paperFourierRayCLM_apply
attribute [local simp] OAI.EisensteinSchwartzPoisson.paperRealRayCLM_apply
attribute [local simp] OAI.EisensteinSchwartzPoisson.verticalSlice_apply
attribute [local simp] OAI.FiniteGaussPhase.productElementCRT_mk
attribute [local simp] OAI.FiniteRayExpansion.zeroExtendUnits_nonunit
attribute [local simp] OAI.FiniteRayExpansion.zeroExtendUnits_unit
attribute [local simp] OAI.IdealGaussCRT.quotientProdEquivPi_mk
attribute [local simp] OAI.IdealGaussCRT.traceProdChar_mk
attribute [local simp] OAI.LocalLogFourier.positiveLogProfile_apply
attribute [local simp] OAI.QuadraticGaussRay.residueQuotientFour_mk
attribute [local simp] OAI.QuadraticInitialBound.sieveCutoff_apply


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
namespace LocalReflectionBrackets
open scoped Classical BigOperators
open AddChar MulChar
section
variable {F : Type*} [Field F] [Fintype F]
open ActualEisensteinCubic
noncomputable local instance quotientFieldBounds (P : Ideal O) [P.IsMaximal] : Field (O ⧸ P) := Ideal.Quotient.field P
noncomputable local instance quotientFintypeBounds (P : Ideal O) [P.IsMaximal] : Fintype (O ⧸ P) := Fintype.ofFinite _
end
variable {F : Type*} [Field F] [Fintype F]
def zeroFourierCoefficient (χ : MulChar F ℂ) (j : ℕ) : ℂ :=
  (Fintype.card F : ℂ)⁻¹ * ∑ t : F, (χ ^ j) t
open ActualEisensteinCubic
noncomputable local instance quotientFieldInactive (P : Ideal O) [P.IsMaximal] : Field (O ⧸ P) := Ideal.Quotient.field P
noncomputable local instance quotientFintypeInactive (P : Ideal O) [P.IsMaximal] : Fintype (O ⧸ P) := Fintype.ofFinite _
end LocalReflectionBrackets
namespace EisensteinSchwartzPoisson
open MeasureTheory MeasureTheory.Measure Set Real
open scoped SchwartzMap FourierTransform
def quadraticSquareProfile (W : 𝓢(ℝ, ℂ)) : 𝓢(ℝ, ℂ) :=
  horizontalSlice (radialTest W) 0
@[simp] theorem quadraticSquareProfile_apply (W : 𝓢(ℝ, ℂ)) (x : ℝ) :
    quadraticSquareProfile W x = W (x ^ 2) := by
  simp [quadraticSquareProfile, horizontalSlice_apply, complexPoint_eq,
    radialTest_apply, Complex.norm_real, Real.norm_eq_abs, sq_abs]
def quadraticTransformedSquareProfile (W : 𝓢(ℝ, ℂ)) : 𝓢(ℝ, ℂ) :=
  (2 / Real.sqrt 3 : ℝ) •
    SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
      (ContinuousLinearEquiv.unitsEquivAut ℝ (Units.mk0 (2 / Real.sqrt 3) (by positivity)))
      (horizontalSlice (𝓕 (radialTest W)) 0)
@[simp] theorem quadraticTransformedSquareProfile_apply (W : 𝓢(ℝ, ℂ)) (x : ℝ) :
    quadraticTransformedSquareProfile W x = paperRadialFourier W (x ^ 2) := by
  simp only [quadraticTransformedSquareProfile, _root_.smul_apply,
    SchwartzMap.compCLMOfContinuousLinearEquiv_apply, Function.comp_apply,
    ContinuousLinearEquiv.unitsEquivAut_apply, Units.val_mk0, horizontalSlice_apply]
  rw [paperRadialFourier_square]
  simp only [complexPoint_eq, Complex.ofReal_zero, mul_zero, add_zero,
    SchwartzMap.fourier_coe, mul_comm x (2 / Real.sqrt 3)]
  rfl
end EisensteinSchwartzPoisson
open scoped BigOperators Classical SchwartzMap
namespace ActualEisensteinCubic
open ConcreteTraceCRT ConcretePrimeRowBridge ActualEisensteinCoordinates EisensteinSchwartzPoisson
def maskedPrincipalRemainder {ι : Type*} [DecidableEq ι]
    (P : ι → Ideal O) (S : Finset ι) (V : ℝ → ℂ) (M : ℝ) : ℂ :=
  (M : ℂ) * ∑ E ∈ S.powerset,
    ((UniqueFactorizationMonoid.moebius (∏ i ∈ E, P i) : ℂ) /
      (Ideal.absNorm (∏ i ∈ E, P i) : ℂ)) *
    ∑' h : O, if h = 0 then 0 else paperRadialFourier V
      (M * ‖eisEmbedding h‖ ^ 2 / (Ideal.absNorm (∏ i ∈ E, P i) : ℝ))
end ActualEisensteinCubic
open scoped BigOperators Classical
namespace PrimaryIdealUnitReindex
abbrev O := ActualEisensteinCubic.O
open ActualEisensteinCubic CompletedGauss ConcretePrimeRowBridge
abbrev GoodIdeal := {I : Ideal O // primaryGenerator I ≠ 0}
abbrev GoodElement := {z : O // primaryGenerator (Ideal.span {z}) ≠ 0}
theorem span_unit_primary (u : Oˣ) (I : GoodIdeal) :
    Ideal.span {(u : O) * primaryGenerator I.val} = I.val := by
  rw [Ideal.span_singleton_mul_left_unit u.isUnit]
  exact (primaryGenerator_spec I.val I.property).1
def unitIdealToElement (p : Oˣ × GoodIdeal) : GoodElement :=
  ⟨p.1.val * primaryGenerator p.2.val, by rw [span_unit_primary]; exact p.2.property⟩
theorem unitIdealToElement_injective : Function.Injective unitIdealToElement := by
  intro p q hpq
  have he : p.1.val * primaryGenerator p.2.val = q.1.val * primaryGenerator q.2.val :=
    congrArg Subtype.val hpq
  have hI : p.2 = q.2 := by
    apply Subtype.ext
    simpa only [span_unit_primary] using congrArg (fun z : O => Ideal.span {z}) he
  have hu : p.1 = q.1 := by
    apply Units.ext
    rw [hI] at he
    exact mul_right_cancel₀ q.2.property he
  exact Prod.ext hu hI
theorem unitIdealToElement_surjective : Function.Surjective unitIdealToElement := by
  intro z
  let I : GoodIdeal := ⟨Ideal.span {z.val}, z.property⟩
  have ha : Associated (primaryGenerator I.val) z.val :=
    Ideal.span_singleton_eq_span_singleton.mp (primaryGenerator_spec I.val I.property).1
  obtain ⟨u, hu⟩ := ha
  refine ⟨(u, I), Subtype.ext ?_⟩
  change u.val * primaryGenerator I.val = z.val
  simpa only [mul_comm] using hu
def unitIdealEquiv : Oˣ × GoodIdeal ≃ GoodElement :=
  Equiv.ofBijective unitIdealToElement ⟨unitIdealToElement_injective, unitIdealToElement_surjective⟩
end PrimaryIdealUnitReindex
open scoped BigOperators Classical
namespace QuadraticUnitInvariance
abbrev O := ActualEisensteinCubic.O
open ActualEisensteinCubic ConcreteTraceCRT FiniteGaussPhase ActualEisensteinCoordinates
open GaussGeneratorTransport QuadraticGaussRay
end QuadraticUnitInvariance
end
end OAI


