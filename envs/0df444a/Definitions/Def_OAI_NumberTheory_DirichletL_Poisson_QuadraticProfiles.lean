-- Prove2me | Definitions.Def_OAI_NumberTheory_DirichletL_Poisson_QuadraticProfiles
-- name    : OAI_NumberTheory_DirichletL_Poisson_QuadraticProfiles
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-07T04:43:38.877589+00:00
-- url     : https://prove2.me/theorems/9fcd97c8-2903-4697-b6c2-dba21d846cb8
-- title:
--   Quadratic Profiles
-- statement:
--   Definitions and structural lemmas for Quadratic Profiles, from LW56e2 and the credited OpenAI and dependency authors's pinned QRH LW56e2 refinement development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/Poisson/QuadraticProfiles.lean

import Definitions.Def_OAI_NumberTheory_DirichletL_Reciprocity_RamifiedSymbol
import Definitions.Def_OAI_NumberTheory_DirichletL_CubicSieve_KernelEnergy
import Theorems.Thm_OAI_ActualEisensteinCubic_principalSexticRow_mk
import Theorems.Thm_OAI_CubicReflectionKernel_logSchwartz_apply
import Theorems.Thm_OAI_EisensteinSchwartzPoisson_halfEulerIterateCLM_apply
import Theorems.Thm_OAI_EisensteinSchwartzPoisson_paperFourierRayCLM_apply
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
import Theorems.Thm_OAI_RayFourExpansion_rayCharacter_mul
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
open scoped BigOperators Classical SchwartzMap FourierTransform
namespace EisensteinSchwartzPoisson
open ActualEisensteinCubic ConcreteTraceCRT
def quadraticSquareProfileCLM : 𝓢(ℝ, ℂ) →L[ℝ] 𝓢(ℝ, ℂ) :=
  SchwartzMap.compCLM ℝ
    (show (fun x : ℝ => x ^ 2).HasTemperateGrowth by fun_prop)
    ⟨1, 1, fun x => by
      simp only [pow_one, one_mul, norm_pow]
      nlinarith [sq_nonneg (‖x‖ - 1)]⟩
@[simp] theorem quadraticSquareProfileCLM_apply (W : 𝓢(ℝ, ℂ)) :
    quadraticSquareProfileCLM W = quadraticSquareProfile W := by
  ext x
  rw [quadraticSquareProfile_apply]
  rfl
def realAxisProfileCLM : 𝓢(ℂ, ℂ) →L[ℝ] 𝓢(ℝ, ℂ) :=
  SchwartzMap.compCLM ℝ
    (show (fun x : ℝ => (x : ℂ)).HasTemperateGrowth by fun_prop)
    ⟨1, 1, fun x => by simp only [pow_one, one_mul, Complex.norm_real]; linarith⟩
@[simp] theorem realAxisProfileCLM_apply (f : 𝓢(ℂ, ℂ)) :
    realAxisProfileCLM f = horizontalSlice f 0 := by
  ext x
  simp only [realAxisProfileCLM, SchwartzMap.compCLM_apply, Function.comp_apply,
    horizontalSlice_apply, complexPoint_eq, Complex.ofReal_zero, mul_zero, add_zero]
def squareFrequencyScaleCLM : 𝓢(ℝ, ℂ) →L[ℝ] 𝓢(ℝ, ℂ) :=
  (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
    (ContinuousLinearEquiv.unitsEquivAut ℝ (Units.mk0 (2 / Real.sqrt 3) (by positivity)))).restrictScalars ℝ
def quadraticTransformedSquareProfileCLM : 𝓢(ℝ, ℂ) →L[ℝ] 𝓢(ℝ, ℂ) :=
  (2 / Real.sqrt 3 : ℝ) •
    squareFrequencyScaleCLM.comp (realAxisProfileCLM.comp radialFourierCLM)
@[simp] theorem quadraticTransformedSquareProfileCLM_apply (W : 𝓢(ℝ, ℂ)) :
    quadraticTransformedSquareProfileCLM W = quadraticTransformedSquareProfile W := by
  simp only [quadraticTransformedSquareProfileCLM, _root_.smul_apply,
    ContinuousLinearMap.comp_apply, radialFourierCLM_apply, realAxisProfileCLM_apply,
    squareFrequencyScaleCLM, quadraticTransformedSquareProfile]
  rfl
open ActualEisensteinCubic ConcreteTraceCRT QuadraticInitialBound
end EisensteinSchwartzPoisson
open scoped BigOperators Classical
namespace FirstPassCubeLabels
open ActualEisensteinCubic MixedCrossSeparation FirstCauchyArithmetic RayFourExpansion
def coreRayCharacter (negative : Bool) (χ ξ : RayCharacter) : RayCharacter :=
  (if negative then star χ else χ) * ξ
def coreRayCoefficient {ι : Type*} (p : ι → ActualEisensteinCubic.O) (F : Finset ι) (negative : Bool)
    (χ η ξ : RayCharacter) : ℂ :=
  (if negative then star (crossCoeff χ η * supportRay p η F)
    else crossCoeff χ η * supportRay p η F) * gCoeff ξ
def coreRayTwist (negative : Bool) (χ ξ : RayCharacter) : ActualEisensteinCubic.O →* ℂ where
  toFun a := rayCharacter (coreRayCharacter negative χ ξ) a
  map_one' := by simp [rayCharacter]
  map_mul' a b := rayCharacter_mul _ a b
end FirstPassCubeLabels
open scoped BigOperators Classical SchwartzMap ContDiff
open MeasureTheory
namespace FirstPassCubeLabels
open ActualEisensteinCubic
open ConcreteTraceCRT (eisEmbedding eisEmbedding_ne_zero)
end FirstPassCubeLabels
open scoped BigOperators Classical SchwartzMap ContDiff
open MeasureTheory
namespace FirstPassCubeLabels
open ActualEisensteinCubic
open FirstCauchyArithmetic (supportConjugateSum)
open RayFourExpansion (RayCharacter crossCoeff)
section FixedColumn
variable {ι : Type*} [DecidableEq ι]
  (p : ι → OAI.FirstPassCubeLabels.O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i, lambda ∉ Ideal.span {p i})
  (F D B : Finset ι) (v : ι → ℕ) (ε₁ ε₂ : ι → Bool)
  (negative : Bool) (χ : RayCharacter) (C : Finset ι → ℂ)
  (V : ℝ → ℂ) (y : Finset ι → ℝ) (c d : OAI.FirstPassCubeLabels.O)
def dilatedCoreRow (t : ℝ) (z : O) : ℂ :=
  dilatedRayColumn p hg F D (cubeCoreCoefficient p hp hcop hg B v ε₁ ε₂ negative C V y t)
    negative χ p B v ε₁ ε₂ c d z
end FixedColumn
def firstRayIntegrand {ι : Type*} [DecidableEq ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i, lambda ∉ Ideal.span {p i}) (F D B : Finset ι)
    (v : ι → ℕ) (ε₁ ε₂ : ι → Bool) (negative : Bool)
    (r : RayCharacter × RayCharacter) (C : Finset ι → ℂ) (V : ℝ → ℂ)
    (y : Finset ι → ℝ) (c d f h : O) (b : 𝓢(ℝ, ℂ)) (t : ℝ) : ℝ :=
  ‖b t‖ * ‖cubeBaseFactor p hp hg B v ε₁ ε₂ d h‖ * ‖rayPairWeight p r D h‖ *
    ‖rayIdealRow p hg F
      (cubeLogCoefficient p hp hcop hg B v ε₁ ε₂ negative
        (originalLabelColumn p hg B ε₁ ε₂ negative C c f) V y t d)
      negative (if negative then r.1 else r.2) D h‖ ^ 2
end FirstPassCubeLabels
end
end OAI


