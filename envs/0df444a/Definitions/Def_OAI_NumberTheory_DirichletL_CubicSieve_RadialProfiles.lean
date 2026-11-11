-- Prove2me | Definitions.Def_OAI_NumberTheory_DirichletL_CubicSieve_RadialProfiles
-- name    : OAI_NumberTheory_DirichletL_CubicSieve_RadialProfiles
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-10T09:40:24.084958+00:00
-- url     : https://prove2.me/theorems/a89b8076-c56d-468c-af28-1c45f401d6a0
-- title:
--   Radial Profiles
-- statement:
--   Definitions and structural lemmas for Radial Profiles, from LW56e2 and the credited OpenAI and dependency authors's pinned QRH LW56e2 refinement development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/CubicSieve/RadialProfiles.lean

import Definitions.Def_OAI_NumberTheory_DirichletL_Eisenstein_CompactEnergyFamilies
import Theorems.Thm_OAI_ActualEisensteinCubic_principalSexticRow_mk
import Theorems.Thm_OAI_CubicEisenstein_finiteCubicMultiplier_coe
import Theorems.Thm_OAI_CubicEisenstein_hyperbolicSpatialChart_apply
import Theorems.Thm_OAI_CubicEisenstein_hyperbolicSpatialChart_source
import Theorems.Thm_OAI_CubicEisenstein_integralComplexMatrix_apply
import Theorems.Thm_OAI_CubicEisenstein_kernelLocalLift_symm
import Theorems.Thm_OAI_CubicEisenstein_kernelQuotientChart_symm
import Theorems.Thm_OAI_CubicEisenstein_spatialTriple_one
import Theorems.Thm_OAI_CubicEisenstein_spatialTriple_two
import Theorems.Thm_OAI_CubicEisenstein_spatialTriple_zero
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
import Theorems.Thm_OAI_InitialMeanSquare_initialLogProfile_apply
import Theorems.Thm_OAI_JointLogSeparation_frequencyTwist_apply
import Theorems.Thm_OAI_JointLogSeparation_frequencyTwist_norm
import Theorems.Thm_OAI_JointLogSeparation_frequencyTwist_twice
import Theorems.Thm_OAI_LocalLogFourier_positiveLogProfile_apply
import Theorems.Thm_OAI_QuadraticGaussRay_residueQuotientFour_mk
import Theorems.Thm_OAI_QuadraticInitialBound_annularSieveCutoff_apply
import Theorems.Thm_OAI_QuadraticInitialBound_annularSieveCutoff_zero
import Theorems.Thm_OAI_QuadraticInitialBound_sieveCutoff_apply
import Theorems.Thm_OAI_SecondPassArithmetic_GlobalSecondData_append_first
import Theorems.Thm_OAI_SecondPassArithmetic_GlobalSecondData_first_append
import Theorems.Thm_OAI_SecondPassArithmetic_GlobalSecondData_source_append
import Theorems.Thm_OAI_SecondPassArithmetic_secondSupportTuple_newLabel
import Theorems.Thm_OAI_SecondPassArithmetic_secondSupportTuple_newRow
import Theorems.Thm_OAI_SecondPassIntegration_conjugateProfile_apply
import Theorems.Thm_RellichKondrachov_Analysis_FunctionalSpaces_Sobolev_Euclidean_L2Compactness_smoothBCF_apply
attribute [local simp] OAI.ActualEisensteinCubic.principalSexticRow_mk
attribute [local simp] OAI.CubicEisenstein.finiteCubicMultiplier_coe
attribute [local simp] OAI.CubicEisenstein.hyperbolicSpatialChart_apply
attribute [local simp] OAI.CubicEisenstein.hyperbolicSpatialChart_source
attribute [local simp] OAI.CubicEisenstein.integralComplexMatrix_apply
attribute [local simp] OAI.CubicEisenstein.kernelLocalLift_symm
attribute [local simp] OAI.CubicEisenstein.kernelQuotientChart_symm
attribute [local simp] OAI.CubicEisenstein.spatialTriple_one
attribute [local simp] OAI.CubicEisenstein.spatialTriple_two
attribute [local simp] OAI.CubicEisenstein.spatialTriple_zero
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
attribute [local simp] OAI.InitialMeanSquare.initialLogProfile_apply
attribute [local simp] OAI.JointLogSeparation.frequencyTwist_apply
attribute [local simp] OAI.JointLogSeparation.frequencyTwist_norm
attribute [local simp] OAI.JointLogSeparation.frequencyTwist_twice
attribute [local simp] OAI.LocalLogFourier.positiveLogProfile_apply
attribute [local simp] OAI.QuadraticGaussRay.residueQuotientFour_mk
attribute [local simp] OAI.QuadraticInitialBound.annularSieveCutoff_apply
attribute [local simp] OAI.QuadraticInitialBound.annularSieveCutoff_zero
attribute [local simp] OAI.QuadraticInitialBound.sieveCutoff_apply
attribute [local simp] OAI.SecondPassArithmetic.GlobalSecondData.append_first
attribute [local simp] OAI.SecondPassArithmetic.GlobalSecondData.first_append
attribute [local simp] OAI.SecondPassArithmetic.GlobalSecondData.source_append
attribute [local simp] OAI.SecondPassArithmetic.secondSupportTuple_newLabel
attribute [local simp] OAI.SecondPassArithmetic.secondSupportTuple_newRow
attribute [local simp] OAI.SecondPassIntegration.conjugateProfile_apply
attribute [local simp] RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.L2Compactness.smoothBCF_apply


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
open scoped BigOperators
open scoped BigOperators Classical SchwartzMap
open scoped BigOperators Classical
namespace SecondPassArithmetic
open scoped BigOperators Classical SchwartzMap ContDiff Topology
open Filter
def positiveRadialProfile (V : ℝ → ℂ) (x : ℝ) : ℂ :=
  if 0<x then V (Real.log x) else 0
theorem positiveRadialProfile_support (V : ℝ → ℂ) (A : ℝ)
    (hV : ∀s,V s≠0→|s|≤A) (x : ℝ) (hx : positiveRadialProfile V x≠0) :
    x∈Set.Icc (Real.exp (-A)) (Real.exp A) := by
  have hpos : 0<x := by
    by_contra hn
    exact hx (by simp [positiveRadialProfile,hn])
  have hlog : |Real.log x|≤A := hV _ (by simpa [positiveRadialProfile,hpos] using hx)
  constructor
  · calc
      Real.exp (-A) ≤ Real.exp (Real.log x) := Real.exp_le_exp.mpr (abs_le.mp hlog).1
      _ = x := Real.exp_log hpos
  · calc
      x = Real.exp (Real.log x) := (Real.exp_log hpos).symm
      _ ≤ Real.exp A := Real.exp_le_exp.mpr (abs_le.mp hlog).2
theorem positiveRadialProfile_compact (V : ℝ → ℂ) (A : ℝ)
    (hV : ∀s,V s≠0→|s|≤A) : HasCompactSupport (positiveRadialProfile V) :=
  HasCompactSupport.of_support_subset_isCompact isCompact_Icc
    (fun x hx=>positiveRadialProfile_support V A hV x hx)
theorem positiveRadialProfile_smooth (V : ℝ → ℂ) (hVs : ContDiff ℝ ∞ V)
    (A : ℝ) (hV : ∀s,V s≠0→|s|≤A) : ContDiff ℝ ∞ (positiveRadialProfile V) := by
  apply contDiff_iff_contDiffAt.mpr
  intro x
  by_cases hpos : 0<x
  · have he : positiveRadialProfile V =ᶠ[𝓝 x] (fun y=>V (Real.log y)) := by
      filter_upwards [Ioi_mem_nhds hpos] with y hy
      change 0<y at hy
      simp only [positiveRadialProfile,if_pos hy]
    exact (hVs.contDiffAt.comp x (Real.contDiffAt_log.mpr hpos.ne')).congr_of_eventuallyEq he
  · have hx : x<Real.exp (-A) := (le_of_not_gt hpos).trans_lt (Real.exp_pos _)
    have he : positiveRadialProfile V =ᶠ[𝓝 x] (fun _=>0) := by
      filter_upwards [Iio_mem_nhds hx] with y hy
      by_contra hn
      have hb := (positiveRadialProfile_support V A hV y hn).1
      exact (not_le_of_gt hy) hb
    exact (contDiffAt_const (c:=(0:ℂ))).congr_of_eventuallyEq he
def radialFromLog (V : ℝ → ℂ) (hVs : ContDiff ℝ ∞ V) (A : ℝ)
    (hV : ∀s,V s≠0→|s|≤A) : 𝓢(ℝ,ℂ) :=
  (positiveRadialProfile_compact V A hV).toSchwartzMap (positiveRadialProfile_smooth V hVs A hV)
@[simp] theorem radialFromLog_apply_pos (V : ℝ → ℂ) (hVs : ContDiff ℝ ∞ V) (A : ℝ)
    (hV : ∀s,V s≠0→|s|≤A) (x : ℝ) (hx : 0<x) :
    radialFromLog V hVs A hV x=V (Real.log x) := by
  change positiveRadialProfile V x=_
  simp only [positiveRadialProfile,if_pos hx]
end SecondPassArithmetic
namespace CubicEisenstein
open Filter MeasureTheory
open scoped BigOperators Classical Topology ContDiff Manifold
def kernelTestPartitionTerm {ι : Type*} {S : Set KernelQuotient}
    (ρ : SmoothPartitionOfUnity ι 𝓘(ℝ,SpatialCoordinates) KernelQuotient S)
    (f : kernelSmoothTests) (i : ι) : kernelSmoothTests :=
  ⟨fun q => ρ i q • f.1 q,(ρ i).contMDiff.smul f.2.1,
    HasCompactSupport.smul_left (f := fun q => ρ i q) (f' := f.1) f.2.2⟩
end CubicEisenstein
open Filter MeasureTheory
open scoped BigOperators Classical Topology ContDiff SchwartzMap LineDeriv
namespace CubicEisenstein
def kernelFullCutoffFun (χ : PositiveChartCutoff) (p : EuclideanSpatial) : ℝ :=
  Real.smoothTransition (4*χ.func p-1)
lemma kernelFullCutoffFun_smooth (χ : PositiveChartCutoff) :
    ContDiff ℝ ∞ (kernelFullCutoffFun χ) :=
  Real.smoothTransition.contDiff.comp ((contDiff_const.mul χ.smooth).sub contDiff_const)
lemma kernelFullCutoffFun_tsupport (χ : PositiveChartCutoff) :
    tsupport (kernelFullCutoffFun χ)⊆tsupport χ.func := by
  apply closure_mono
  intro p hp
  change kernelFullCutoffFun χ p≠0 at hp
  change χ.func p≠0
  intro hz
  apply hp
  simp only [kernelFullCutoffFun,hz,mul_zero,zero_sub]
  exact Real.smoothTransition.zero_of_nonpos (by norm_num)
lemma kernelFullCutoffFun_compact (χ : PositiveChartCutoff) :
    HasCompactSupport (kernelFullCutoffFun χ) :=
  χ.compact.of_isClosed_subset (isClosed_tsupport _) (kernelFullCutoffFun_tsupport χ)
def kernelFullCutoff (χ : PositiveChartCutoff) : PositiveChartCutoff where
  func := kernelFullCutoffFun χ
  smooth := kernelFullCutoffFun_smooth χ
  compact := kernelFullCutoffFun_compact χ
  positive := (kernelFullCutoffFun_tsupport χ).trans χ.positive
def kernelCoreLift (χ : PositiveChartCutoff) (f : kernelSmoothTests) :
    𝓢(EuclideanSpatial,ℂ) := kernelLocalizedSchwartz (kernelFullCutoff χ) f
def euclideanHeightCLM : EuclideanSpatial→L[ℝ]ℂ :=
  Complex.ofRealCLM.comp (PiLp.proj 2 (fun _ : Fin 3 => ℝ) 2)
lemma euclideanHeightCLM_apply (p : EuclideanSpatial) : euclideanHeightCLM p=(p 2:ℂ) := rfl
lemma upperHeightDivide_smooth (f : 𝓢(EuclideanSpatial,ℂ))
    (hpos : tsupport f⊆euclideanUpperHalf) :
    ContDiff ℝ ∞ (fun p : EuclideanSpatial => f p/(p 2:ℂ)) := by
  rw [contDiff_iff_contDiffAt]
  intro p
  by_cases hp : p 2=0
  · have hn : p∉tsupport f := by
      intro hf
      have hh := hpos hf
      change 0<p 2 at hh
      linarith
    have hz := notMem_tsupport_iff_eventuallyEq.mp hn
    apply (contDiffAt_const : ContDiffAt ℝ ∞ (fun _ : EuclideanSpatial => (0 : ℂ)) p).congr_of_eventuallyEq
    filter_upwards [hz] with q hq
    simp only [hq,Pi.zero_apply,zero_div]
  · simpa only [div_eq_mul_inv,Pi.inv_apply,euclideanHeightCLM_apply] using
      (f.smooth ⊤).contDiffAt.mul (euclideanHeightCLM.contDiff.contDiffAt.fun_inv
        (Complex.ofReal_ne_zero.mpr hp))
lemma upperHeightDivide_compact (f : 𝓢(EuclideanSpatial,ℂ))
    (hcompact : HasCompactSupport f) :
    HasCompactSupport (fun p : EuclideanSpatial => f p/(p 2:ℂ)) := by
  rw [hasCompactSupport_iff_eventuallyEq] at hcompact ⊢
  exact hcompact.mono (fun p hp => by simp only [hp,Pi.zero_apply,zero_div])
def upperHeightDivide (f : 𝓢(EuclideanSpatial,ℂ))
    (hcompact : HasCompactSupport f) (hpos : tsupport f⊆euclideanUpperHalf) :
    𝓢(EuclideanSpatial,ℂ) :=
  (upperHeightDivide_compact f hcompact).toSchwartzMap (upperHeightDivide_smooth f hpos)
lemma upperSchwartz_derivative_compact (f : 𝓢(EuclideanSpatial,ℂ))
    (hcompact : HasCompactSupport f) (u : EuclideanSpatial) :
    HasCompactSupport (∂_{u} f : 𝓢(EuclideanSpatial,ℂ)) :=
  hcompact.fderiv_apply ℝ u
def upperWeightedPartial (f : 𝓢(EuclideanSpatial,ℂ))
    (hcompact : HasCompactSupport f) (hpos : tsupport f⊆euclideanUpperHalf) (j : Fin 3) :
    𝓢(EuclideanSpatial,ℂ) :=
  upperHeightDivide (∂_{euclideanCoordinateVector j} f)
    (upperSchwartz_derivative_compact f hcompact _)
    ((SchwartzMap.tsupport_lineDerivOp_subset _ f).trans hpos)
def upperWeightedDivergence (f : 𝓢(EuclideanSpatial,ℂ))
    (hcompact : HasCompactSupport f) (hpos : tsupport f⊆euclideanUpperHalf) :
    𝓢(EuclideanSpatial,ℂ) :=
  -∑j : Fin 3,∂_{euclideanCoordinateVector j} (upperWeightedPartial f hcompact hpos j)
def complexHermitianBilin : ℂ→L[ℝ]ℂ→L[ℝ]ℂ :=
  (ContinuousLinearMap.mul ℝ ℂ).comp Complex.conjCLE.toContinuousLinearMap
def upperPositiveLaplacian (f : 𝓢(EuclideanSpatial,ℂ)) (p : EuclideanSpatial) : ℂ :=
  -(p 2:ℂ)^2*(∑j : Fin 3,(∂_{euclideanCoordinateVector j} (∂_{euclideanCoordinateVector j} f)) p)+
    (p 2:ℂ)*(∂_{euclideanCoordinateVector 2} f) p
end CubicEisenstein
open Filter MeasureTheory
open scoped BigOperators Classical Topology ContDiff SchwartzMap LineDeriv
namespace CubicEisenstein
end CubicEisenstein
end
end OAI


