-- Prove2me | Definitions.Def_OAI_NumberTheory_DirichletL_Eisenstein_MeromorphicResolvent
-- name    : OAI_NumberTheory_DirichletL_Eisenstein_MeromorphicResolvent
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-10T14:56:25.687006+00:00
-- url     : https://prove2.me/theorems/30480f38-a6ea-40f0-831b-0bd9e9bb6738
-- title:
--   Meromorphic Resolvent
-- statement:
--   Definitions and structural lemmas for Meromorphic Resolvent, from LW56e2 and the credited OpenAI and dependency authors's pinned QRH LW56e2 refinement development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/Eisenstein/MeromorphicResolvent.lean

import Definitions.Def_OAI_NumberTheory_DirichletL_Eisenstein_FredholmAlternative
import Theorems.Thm_OAI_ActualEisensteinCubic_principalSexticRow_mk
import Theorems.Thm_OAI_CanonicalCubeSeparation_cubeFrequencyFactor_norm
import Theorems.Thm_OAI_CanonicalCubeSeparation_sourceLogProfile_apply
import Theorems.Thm_OAI_CanonicalRowCompletion_cubeIndex_apply
import Theorems.Thm_OAI_CompletedHeight_completedT_normHeight_norm
import Theorems.Thm_OAI_CompletedHeight_shortCompletedSum_normHeight_norm
import Theorems.Thm_OAI_CubicEisenstein_finiteCubicMultiplier_coe
import Theorems.Thm_OAI_CubicEisenstein_hyperbolicSpatialChart_apply
import Theorems.Thm_OAI_CubicEisenstein_hyperbolicSpatialChart_source
import Theorems.Thm_OAI_CubicEisenstein_integralComplexMatrix_apply
import Theorems.Thm_OAI_CubicEisenstein_kernelLocalLift_symm
import Theorems.Thm_OAI_CubicEisenstein_kernelQuotientChart_symm
import Theorems.Thm_OAI_CubicEisenstein_kernelTruncatedWeight_apply
import Theorems.Thm_OAI_CubicEisenstein_kernel_theta_spectral_fredholm
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
attribute [local simp] OAI.CompletedHeight.completedT_normHeight_norm
attribute [local simp] OAI.CompletedHeight.shortCompletedSum_normHeight_norm
attribute [local simp] OAI.CubicEisenstein.finiteCubicMultiplier_coe
attribute [local simp] OAI.CubicEisenstein.hyperbolicSpatialChart_apply
attribute [local simp] OAI.CubicEisenstein.hyperbolicSpatialChart_source
attribute [local simp] OAI.CubicEisenstein.integralComplexMatrix_apply
attribute [local simp] OAI.CubicEisenstein.kernelLocalLift_symm
attribute [local simp] OAI.CubicEisenstein.kernelQuotientChart_symm
attribute [local simp] OAI.CubicEisenstein.kernelTruncatedWeight_apply
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
namespace CubicEisenstein
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
open scoped Topology
section
open Filter MeasureTheory
open scoped BigOperators Classical Topology InnerProductSpace
def kernelMassGram : KernelEnergyGraph→L[ℂ]KernelEnergyGraph :=
  kernelEnergyMass.adjoint.comp kernelEnergyMass
lemma selfAdjoint_adjoint_comp {E F : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
    (A : E →L[ℂ] F) : IsSelfAdjoint (A.adjoint.comp A) := by
  rw [ContinuousLinearMap.isSelfAdjoint_iff']
  rw [ContinuousLinearMap.adjoint_comp,ContinuousLinearMap.adjoint_adjoint]
lemma kernelMassGram_selfAdjoint : IsSelfAdjoint kernelMassGram :=
  selfAdjoint_adjoint_comp kernelEnergyMass
def kernelThetaNull : Submodule ℂ KernelEnergyGraph :=
  (kernelSpectralFormOperator (8/9:ℂ)).ker
def kernelThetaRegular : Submodule ℂ KernelEnergyGraph := kernelThetaNullᗮ
instance kernelThetaNull_complete : CompleteSpace kernelThetaNull :=
  (kernelSpectralFormOperator (8/9:ℂ)).isClosed_ker.completeSpace_coe
instance kernelThetaRegular_complete : CompleteSpace kernelThetaRegular :=
  kernelThetaNull.isClosed_orthogonal.completeSpace_coe
instance kernelThetaNull_finiteDimensional : FiniteDimensional ℂ kernelThetaNull :=
  kernel_theta_spectral_fredholm.finite_ker
lemma kernelThetaNull_gram_eq (u : KernelEnergyGraph) (hu : u∈kernelThetaNull) :
    kernelMassGram u=(9/17:ℂ)•u := by
  have hh : u-(8/9+1:ℂ)•kernelMassGram u=0 := hu
  have he : u=(17/9:ℂ)•kernelMassGram u := by
    simpa only [show (8/9+1:ℂ)=17/9 by norm_num] using sub_eq_zero.mp hh
  calc
    _ = (9/17:ℂ)•((17/9:ℂ)•kernelMassGram u) := by rw [smul_smul]; norm_num
    _ = _ := by rw [←he]
lemma kernelMassGram_preserves_regular (u : KernelEnergyGraph) (hu : u∈kernelThetaRegular) :
    kernelMassGram u∈kernelThetaRegular := by
  apply (kernelThetaNull.mem_orthogonal _).mpr
  intro v hv
  have he : inner ℂ v (kernelMassGram u)=inner ℂ (kernelMassGram v) u := by
    simpa only [ContinuousLinearMap.coe_coe] using (kernelMassGram_selfAdjoint.isSymmetric v u).symm
  rw [he,kernelThetaNull_gram_eq v hv,inner_smul_left (𝕜 := ℂ) v u (9/17:ℂ)]
  rw [kernelThetaNull.inner_right_of_mem_orthogonal hv hu,mul_zero]
def kernelRegularGram : kernelThetaRegular→L[ℂ]kernelThetaRegular :=
  kernelMassGram.restrict kernelMassGram_preserves_regular
def kernelRegularPencil (z : ℂ) : kernelThetaRegular→L[ℂ]kernelThetaRegular :=
  ContinuousLinearMap.id ℂ kernelThetaRegular-(z+1)•kernelRegularGram
abbrev endomorphismNormedSpace (E : Type*) [NormedAddCommGroup E]
    [NormedSpace ℂ E] : NormedSpace ℂ (E →L[ℂ] E) := inferInstance
local instance _p2m_local_instance_ed212497e0_190 : NormedSpace ℂ (kernelThetaRegular →L[ℂ] kernelThetaRegular) :=
  endomorphismNormedSpace kernelThetaRegular
def continuousLinearSandwich {H G : Type*}
    [NormedAddCommGroup H] [NormedSpace ℂ H]
    [NormedAddCommGroup G] [NormedSpace ℂ G]
    (A : H →L[ℂ] G) (B : G →L[ℂ] H) :
    (H →L[ℂ] H) →L[ℂ] (G →L[ℂ] G) :=
  (ContinuousLinearMap.compL ℂ G H G A).comp
    ((ContinuousLinearMap.compL ℂ G H H).flip B)
def kernelRegularLiftCLM :
    (kernelThetaRegular→L[ℂ]kernelThetaRegular)→L[ℂ](KernelEnergyGraph→L[ℂ]KernelEnergyGraph) :=
  continuousLinearSandwich (H := kernelThetaRegular) (G := KernelEnergyGraph)
    kernelThetaRegular.subtypeL
    kernelThetaRegular.orthogonalProjectionOnto
def kernelRegularInverseLift (z : ℂ) : KernelEnergyGraph→L[ℂ]KernelEnergyGraph :=
  kernelRegularLiftCLM (Ring.inverse (kernelRegularPencil z))
def kernelLocalEnergyResolvent (z : ℂ) : KernelEnergyGraph→L[ℂ]KernelEnergyGraph :=
  ((17/9)/(8/9-z):ℂ) • kernelThetaNull.starProjection + kernelRegularInverseLift z
end
open scoped Topology
open Filter MeasureTheory
open scoped BigOperators Classical Topology InnerProductSpace
def kernelL2SandwichCLM : (KernelEnergyGraph→L[ℂ]KernelEnergyGraph)→L[ℂ]
    (KernelQuotientL2→L[ℂ]KernelQuotientL2) :=
  continuousLinearSandwich kernelEnergyMass kernelEnergyMass.adjoint
def kernelSpectralResolvent (z : ℂ) : KernelQuotientL2→L[ℂ]KernelQuotientL2 :=
  kernelL2SandwichCLM (Ring.inverse (kernelSpectralFormOperator z))
def kernelEisensteinSpectralParameter (s : ℂ) : ℂ := s*(2-s)
def kernelEisensteinResolvent (s : ℂ) : KernelQuotientL2→L[ℂ]KernelQuotientL2 :=
  kernelSpectralResolvent (kernelEisensteinSpectralParameter s)
def kernelEisensteinL2Correction (a b : ℝ) (ha : 0<a) (hab : a<b) (s : ℂ) :
    KernelQuotientL2 :=
  kernelEisensteinResolvent s (kernelL2Defect a b ha hab s)
open Filter MeasureTheory
open scoped BigOperators Classical Topology InnerProductSpace
def kernelThetaMassProjection : KernelQuotientL2→L[ℂ]KernelQuotientL2 :=
  kernelL2SandwichCLM kernelThetaNull.starProjection
def kernelRegularL2Resolvent (z : ℂ) : KernelQuotientL2→L[ℂ]KernelQuotientL2 :=
  kernelL2SandwichCLM (kernelRegularInverseLift z)
def kernelEisensteinCorrectionNumerator (a b : ℝ) (ha : 0<a) (hab : a<b) (s : ℂ) :
    KernelQuotientL2 :=
  ((17/9)/(s-2/3):ℂ)•kernelThetaMassProjection (kernelL2Defect a b ha hab s)+
    (s-4/3)•kernelRegularL2Resolvent (kernelEisensteinSpectralParameter s)
      (kernelL2Defect a b ha hab s)
def kernelEisensteinResidueVector (a b : ℝ) (ha : 0<a) (hab : a<b) : KernelQuotientL2 :=
  (17/6:ℂ)•kernelThetaMassProjection (kernelL2Defect a b ha hab (4/3))
instance kernelThetaMassProjection_range_finiteDimensional :
    FiniteDimensional ℂ kernelThetaMassProjection.range := by
  let B : kernelThetaNull→L[ℂ]KernelQuotientL2 := kernelEnergyMass.comp kernelThetaNull.subtypeL
  have : FiniteDimensional ℂ B.range := LinearMap.finiteDimensional_range B.toLinearMap
  apply Submodule.finiteDimensional_of_le (S₂ := B.range)
  rintro y ⟨x,rfl⟩
  exact ⟨kernelThetaNull.orthogonalProjectionOnto (kernelEnergyMass.adjoint x),rfl⟩
end CubicEisenstein
end
end OAI


