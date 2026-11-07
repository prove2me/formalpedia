-- Prove2me | Definitions.Def_OAI_NumberTheory_DirichletL_Poisson_RadialFourier
-- name    : OAI_NumberTheory_DirichletL_Poisson_RadialFourier
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-06T08:26:46.884198+00:00
-- url     : https://prove2.me/theorems/937cba5b-177c-4d93-abbe-ceedfa19732d
-- title:
--   Radial Fourier
-- statement:
--   Definitions and structural lemmas for Radial Fourier, from LW56e2 and the credited OpenAI and dependency authors's pinned QRH LW56e2 refinement development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/Poisson/RadialFourier.lean

import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_SexticRadialPoisson
import Definitions.Def_OAI_NumberTheory_DirichletL_Fourier_PositiveLogProfiles
import Theorems.Thm_OAI_ActualEisensteinCubic_principalSexticRow_mk
import Theorems.Thm_OAI_EisensteinSchwartzPoisson_paperFrequency_norm_sq
import Theorems.Thm_OAI_EisensteinSchwartzPoisson_verticalSlice_apply
import Theorems.Thm_OAI_IdealGaussCRT_quotientProdEquivPi_mk
import Theorems.Thm_OAI_IdealGaussCRT_traceProdChar_mk
import Theorems.Thm_OAI_LocalLogFourier_positiveLogProfile_apply
attribute [local simp] OAI.ActualEisensteinCubic.principalSexticRow_mk
attribute [local simp] OAI.EisensteinSchwartzPoisson.verticalSlice_apply
attribute [local simp] OAI.IdealGaussCRT.quotientProdEquivPi_mk
attribute [local simp] OAI.IdealGaussCRT.traceProdChar_mk
attribute [local simp] OAI.LocalLogFourier.positiveLogProfile_apply


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
namespace EisensteinSchwartzPoisson
section
open MeasureTheory
open scoped FourierTransform SchwartzMap RealInnerProductSpace ContDiff
def radialTestCLM : 𝓢(ℝ, ℂ) →L[ℝ] 𝓢(ℂ, ℂ) :=
  SchwartzMap.compCLM ℝ (Function.hasTemperateGrowth_norm_sq ℂ)
    ⟨1, 1, fun z => by
      simp only [pow_one, one_mul, norm_pow, Real.norm_of_nonneg (norm_nonneg z)]
      nlinarith [sq_nonneg (‖z‖ - 1)]⟩
@[simp] theorem radialTestCLM_apply (W : 𝓢(ℝ, ℂ)) : radialTestCLM W = radialTest W := by
  ext z
  rfl
def radialFourierCLM : 𝓢(ℝ, ℂ) →L[ℝ] 𝓢(ℂ, ℂ) :=
  (FourierTransform.fourierCLM ℝ 𝓢(ℂ, ℂ)).comp radialTestCLM
@[simp] theorem radialFourierCLM_apply (W : 𝓢(ℝ, ℂ)) :
    radialFourierCLM W = 𝓕 (radialTest W) := by
  simp [radialFourierCLM]
end
section
open MeasureTheory
open scoped SchwartzMap ContDiff
def halfEulerCLM : 𝓢(ℝ, ℂ) →L[ℂ] 𝓢(ℝ, ℂ) :=
  (SchwartzMap.smulLeftCLM ℂ (fun x : ℝ => ((x / 2 : ℝ) : ℂ))).comp
    (SchwartzMap.derivCLM ℂ ℂ)
@[simp] theorem halfEulerCLM_apply (g : 𝓢(ℝ, ℂ)) (s : ℝ) :
    halfEulerCLM g s = (s / 2 : ℝ) • deriv g s := by
  have hg : (fun x : ℝ => ((x / 2 : ℝ) : ℂ)).HasTemperateGrowth := by
    simp only [div_eq_mul_inv]
    fun_prop
  simp only [halfEulerCLM, ContinuousLinearMap.comp_apply,
    SchwartzMap.smulLeftCLM_apply_apply hg, SchwartzMap.derivCLM_apply]
  rfl
theorem paperFrequency_real_temperate :
    (fun s : ℝ => paperFrequency (s : ℂ)).HasTemperateGrowth := by
  have heq : (fun s : ℝ => paperFrequency (s : ℂ)) =
      fun s : ℝ => (2 * Complex.I / (Real.sqrt 3 : ℂ)) * (s : ℂ) := by
    funext s
    simp [paperFrequency]
  rw [heq]
  fun_prop
theorem paperFrequency_real_growth (s : ℝ) :
    ‖s‖ ≤ 1 + ‖paperFrequency (s : ℂ)‖ := by
  have hn := paperFrequency_norm_sq (s : ℂ)
  have heq : ‖(s : ℂ)‖ = ‖s‖ := by simp
  rw [heq] at hn
  have hns := norm_nonneg s
  have hnf := norm_nonneg (paperFrequency (s : ℂ))
  nlinarith [sq_nonneg (‖s‖ - ‖paperFrequency (s : ℂ)‖)]
def paperRealRayCLM : 𝓢(ℂ, ℂ) →L[ℝ] 𝓢(ℝ, ℂ) :=
  SchwartzMap.compCLM ℝ paperFrequency_real_temperate
    ⟨1, 1, by simpa using paperFrequency_real_growth⟩
def halfEulerIterateCLM : ℕ → 𝓢(ℝ, ℂ) →L[ℝ] 𝓢(ℝ, ℂ)
  | 0 => ContinuousLinearMap.id ℝ _
  | j + 1 => (halfEulerCLM.restrictScalars ℝ).comp (halfEulerIterateCLM j)
def paperFourierRayCLM : 𝓢(ℝ, ℂ) →L[ℝ] 𝓢(ℝ, ℂ) :=
  (2 / Real.sqrt 3 : ℝ) • (paperRealRayCLM.comp radialFourierCLM)
def paperEulerCLM (j : ℕ) : 𝓢(ℝ, ℂ) →L[ℝ] 𝓢(ℝ, ℂ) :=
  (halfEulerIterateCLM j).comp paperFourierRayCLM
end
open ConcreteTraceCRT ActualEisensteinCubic
open scoped SchwartzMap
def eisensteinCauchyMass : ℝ :=
  ∑' h : O, ((1 + ‖eisEmbedding h‖ ^ 2) ^ 2)⁻¹
end EisensteinSchwartzPoisson
open scoped BigOperators Classical SchwartzMap ContDiff
namespace ConcretePrimeRowBridge
open ActualEisensteinCubic ShortDraftHeckeBridge
end ConcretePrimeRowBridge
end
end OAI


