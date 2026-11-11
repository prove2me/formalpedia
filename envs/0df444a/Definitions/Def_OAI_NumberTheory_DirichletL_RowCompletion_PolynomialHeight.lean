-- Prove2me | Definitions.Def_OAI_NumberTheory_DirichletL_RowCompletion_PolynomialHeight
-- name    : OAI_NumberTheory_DirichletL_RowCompletion_PolynomialHeight
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-10T10:10:12.47001+00:00
-- url     : https://prove2.me/theorems/b3eb58be-b98c-4fdd-a156-188ce8155742
-- title:
--   Polynomial Height
-- statement:
--   Definitions and structural lemmas for Polynomial Height, from LW56e2 and the credited OpenAI and dependency authors's pinned QRH LW56e2 refinement development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/RowCompletion/PolynomialHeight.lean

import Definitions.Def_OAI_NumberTheory_DirichletL_CubicSieve_LogSeparation
import Theorems.Thm_OAI_ActualEisensteinCubic_principalSexticRow_mk
import Theorems.Thm_OAI_CanonicalCubeSeparation_cubeFrequencyFactor_norm
import Theorems.Thm_OAI_CanonicalCubeSeparation_sourceLogProfile_apply
import Theorems.Thm_OAI_CanonicalRowCompletion_cubeIndex_apply
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
attribute [local simp] OAI.CanonicalCubeSeparation.cubeFrequencyFactor_norm
attribute [local simp] OAI.CanonicalCubeSeparation.sourceLogProfile_apply
attribute [local simp] OAI.CanonicalRowCompletion.cubeIndex_apply
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
open scoped BigOperators Classical
namespace CanonicalRowCompletion
open ActualEisensteinCubic
open CompletedGauss hiding O
open ConcretePrimeRowBridge hiding O columnWeight
open CanonicalCubeSeparation
end CanonicalRowCompletion
namespace CompletedHeight
open MeasureTheory Filter Set
open scoped BigOperators Classical SchwartzMap FourierTransform ContDiff Topology
open FourierBridge JointLogSeparation
def positiveCutoff (a b : ℝ) (ha : 0 < a) : ContDiffBump ((a+max a b)/2) where
  rIn := (max a b-a)/2+a/4
  rOut := (max a b-a)/2+a/2
  rIn_pos := by linarith [le_max_left a b]
  rIn_lt_rOut := by linarith
lemma positiveCutoff_zero (a b : ℝ) (ha : 0 < a) (x : ℝ) (hx : x < a/2) :
    positiveCutoff a b ha x=0 := by
  by_contra hn
  have hm : x∈Function.support (positiveCutoff a b ha) := hn
  rw [(positiveCutoff a b ha).support_eq] at hm
  change dist x ((a+max a b)/2) < (max a b-a)/2+a/2 at hm
  rw [Real.dist_eq,abs_lt] at hm
  linarith [hm.1]
def logCorrection (a b : ℝ) (ha : 0 < a) (x : ℝ) : ℝ :=
  positiveCutoff a b ha x*(Real.log x-x)
def patchedLog (a b : ℝ) (ha : 0 < a) (x : ℝ) : ℝ := x+logCorrection a b ha x
lemma logCorrection_compact (a b : ℝ) (ha : 0 < a) :
    HasCompactSupport (logCorrection a b ha) := (positiveCutoff a b ha).hasCompactSupport.mul_right
lemma logCorrection_smooth (a b : ℝ) (ha : 0 < a) :
    ContDiff ℝ ∞ (logCorrection a b ha) := by
  rw [contDiff_iff_contDiffAt]
  intro x
  by_cases hx : x=0
  · subst x
    have he : logCorrection a b ha =ᶠ[𝓝 (0:ℝ)] (fun _=>0) := by
      filter_upwards [isOpen_Iio.mem_nhds (by linarith : (0:ℝ)<a/2)] with y hy
      simp only [logCorrection,positiveCutoff_zero a b ha y hy,zero_mul]
    exact contDiffAt_const.congr_of_eventuallyEq he
  · exact (positiveCutoff a b ha).contDiff.contDiffAt.mul
      ((Real.contDiffAt_log.mpr hx).sub contDiffAt_id)
lemma patchedLog_temperate (a b : ℝ) (ha : 0 < a) :
    Function.HasTemperateGrowth (patchedLog a b ha) :=
  Function.HasTemperateGrowth.id'.add
    ((logCorrection_compact a b ha).hasTemperateGrowth (logCorrection_smooth a b ha))
lemma patchedLog_proper (a b : ℝ) (ha : 0 < a) :
    ∃k : ℕ, ∃C : ℝ, ∀x : ℝ, ‖x‖ ≤ C*(1+‖patchedLog a b ha x‖)^k := by
  obtain ⟨x₀,hx₀⟩ := (logCorrection_smooth a b ha).continuous.norm.exists_forall_ge_of_hasCompactSupport
    (logCorrection_compact a b ha).norm
  refine ⟨1,‖logCorrection a b ha x₀‖+1,?_⟩
  intro x
  have ht : ‖x‖ ≤ ‖patchedLog a b ha x‖+‖logCorrection a b ha x‖ := by
    simpa only [patchedLog,add_sub_cancel_right] using
      norm_sub_le (patchedLog a b ha x) (logCorrection a b ha x)
  have hb := hx₀ x
  simp only [pow_one]
  nlinarith [norm_nonneg (patchedLog a b ha x),norm_nonneg (logCorrection a b ha x₀)]
def sourceTwistCLM (W : 𝓢(ℝ,ℂ)) (a b : ℝ) (ha : 0 < a) :
    𝓢(ℝ,ℂ) →L[ℝ] 𝓢(ℝ,ℂ) :=
  ((SchwartzMap.smulLeftCLM ℂ (W : ℝ→ℂ)).restrictScalars ℝ).comp
    (SchwartzMap.compCLM ℝ (patchedLog_temperate a b ha) (patchedLog_proper a b ha))
def normTwistedSource (W : ℝ→ℂ) (t x : ℝ) : ℂ := logPhase t (Real.log x)*W x
end CompletedHeight
namespace LocalLogFourier
open MeasureTheory
open scoped BigOperators Classical FourierTransform SchwartzMap ContDiff
end LocalLogFourier
namespace CompletedHeight
open MeasureTheory
open scoped BigOperators Classical SchwartzMap FourierTransform ContDiff
open CompletedGauss
def HasPolynomialKernel (P : ℝ→ℝ→ℂ) : Prop :=
  (∀t,ContDiffOn ℝ ∞ (CubicReflectionKernel.paperKernel (Vstar (P t))) (Set.Ioi 0)) ∧
  ∀ A K : ℕ,∃n : ℕ,∃C : ℝ,0<C ∧ ∀t : ℝ,∀i≤K,∀x : ℝ,0<x →
    (1+x)^A*‖LocalLogFourier.eulerDeriv (CubicReflectionKernel.paperKernel (Vstar (P t))) i x‖≤
      C*(1+‖t‖)^n
end CompletedHeight
open MeasureTheory
open scoped BigOperators Classical SchwartzMap ContDiff
namespace CompletedHeight
open CompletedGauss hiding O
open ActualEisensteinCubic
open CanonicalQuadraticSieve hiding O
end CompletedHeight
open MeasureTheory
open scoped BigOperators Classical SchwartzMap ContDiff
namespace CompletedHeight
open CompletedGauss hiding O
open ActualEisensteinCubic CompletedDyadic
open CanonicalQuadraticSieve hiding O
end CompletedHeight
end
end OAI


