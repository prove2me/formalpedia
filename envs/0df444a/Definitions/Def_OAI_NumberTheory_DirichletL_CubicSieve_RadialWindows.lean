-- Prove2me | Definitions.Def_OAI_NumberTheory_DirichletL_CubicSieve_RadialWindows
-- name    : OAI_NumberTheory_DirichletL_CubicSieve_RadialWindows
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-09T12:51:25.118463+00:00
-- url     : https://prove2.me/theorems/1b6f57a2-5d6b-4cdf-905d-6c7acfe890ea
-- title:
--   Radial Windows
-- statement:
--   Definitions and structural lemmas for Radial Windows, from LW56e2 and the credited OpenAI and dependency authors's pinned QRH LW56e2 refinement development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/CubicSieve/RadialWindows.lean

import Definitions.Def_RellichKondrachov_Analysis_FunctionalSpaces_Sobolev_Euclidean_Rellich
import Definitions.Def_OAI_NumberTheory_DirichletL_MeanSquare_PoissonSource
import Theorems.Thm_OAI_ActualEisensteinCubic_principalSexticRow_mk
import Theorems.Thm_OAI_CubicEisenstein_finiteCubicMultiplier_coe
import Theorems.Thm_OAI_CubicEisenstein_hyperbolicEuclideanCoordinates_continuous
import Theorems.Thm_OAI_CubicEisenstein_hyperbolicHeight_pos
import Theorems.Thm_OAI_CubicEisenstein_hyperbolicSpatialChart_apply
import Theorems.Thm_OAI_CubicEisenstein_hyperbolicSpatialChart_source
import Theorems.Thm_OAI_CubicEisenstein_integralComplexMatrix_apply
import Theorems.Thm_OAI_CubicEisenstein_kernelGradientAt_norm_sq
import Theorems.Thm_OAI_CubicEisenstein_kernelLocalLift_symm
import Theorems.Thm_OAI_CubicEisenstein_kernelQuotientChart_symm
import Theorems.Thm_OAI_CubicEisenstein_kernelQuotientEnergyDensity_integrable
import Theorems.Thm_OAI_CubicEisenstein_quotient_projection_measurePreserving
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
import Theorems.Thm_P2M_MeasureTheory_Lp_extendByZero___ae_eq_8fb970118384
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
namespace SecondPassArithmetic
open ActualEisensteinCubic
open FirstPassCubeLabels
variable {ι : Type*} [DecidableEq ι]
  (p : ι→OAI.SecondPassArithmetic.O) (hp : ∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
  (hg : ∀i,lambda∉Ideal.span {p i})
end SecondPassArithmetic
open scoped BigOperators Classical SchwartzMap
namespace FirstPassCubeLabels
open ActualEisensteinCubic
variable {ι:Type*} (p:ι→OAI.FirstPassCubeLabels.O) (B:Finset ι) (v:ι→ℕ) (ε₁ ε₂:ι→Bool)
end FirstPassCubeLabels
namespace SecondPassArithmetic
section
open ActualEisensteinCubic FirstPassCubeLabels
namespace CubeCoordinates
variable {ι:Type*}
def swap (b:CubeCoordinates ι) : CubeCoordinates ι :=
  ⟨b.rightExponent,b.leftExponent,b.rightDivisor,b.leftDivisor⟩
@[simp] lemma swap_swap (b:CubeCoordinates ι) : b.swap.swap=b := by cases b;rfl
end CubeCoordinates
end
section
open ActualEisensteinCubic
open FirstPassCubeLabels (primeProductNorm actualFirstKernel originalLabelColumn cubeActiveSupport dilationLabel columnLog)
open ConcreteTraceCRT (eisEmbedding)
section
variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) (hp : ∀ i,p i ≠ 0) [∀ i,(Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i,lambda ∉ Ideal.span {p i})
def orientedCubeFirstBlock (pool : Finset ι) (b : GlobalCubeBlock ι)
    (s : Finset (Ideal O × O)) (a : Ideal O × O → ℂ)
    (Ψ₁ Ψ₂ : O →* ℂ) (m₁ m₂ : O) (g₁ g₂ W V₁ V₂ : 𝓢(ℝ,ℂ)) (K ell : ℝ) : ℂ :=
  let c := primeSubsetGenerator (fun i => Ideal.span {p i}) b.common
  let d := primeSubsetGenerator (fun i => Ideal.span {p i}) b.firstDivisor
  let X₁ := globalCubeColumnScale p ell true b
  let X₂ := globalCubeColumnScale p ell false b
  (primeProductNorm p b.firstDivisor : ℂ)⁻¹ * ∑ x∈s,a x*actualFirstKernel p hp hcop hg (globalCubePool pool b) b.cube.support
    (fun i => b.cube.leftExponent i+b.cube.rightExponent i) b.cube.rightBit b.cube.leftBit
    (originalLabelColumn p hg b.cube.support b.cube.rightBit b.cube.leftBit true
      (multiplicativeCoreColumn p Ψ₁ m₁ (fun S => g₁ (columnLog p X₁ S))) c (ConcretePrimeRowBridge.idealGenerator x.1))
    (originalLabelColumn p hg b.cube.support b.cube.rightBit b.cube.leftBit false
      (multiplicativeCoreColumn p Ψ₂ m₂ (fun S => g₂ (columnLog p X₂ S))) c (ConcretePrimeRowBridge.idealGenerator x.1))
    W V₁ V₂ X₁ X₂ K d x.2
end
end
open ActualEisensteinCubic
open FirstPassCubeLabels (primeProduct dilationLabel)
open ConcreteTraceCRT (eisEmbedding)
end SecondPassArithmetic
namespace CubicEisenstein
open Filter MeasureTheory
open scoped BigOperators Classical Topology ENNReal
open RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean
local instance _p2m_local_instance_a77077472d_474 : MeasurableSpace EuclideanSpatial := borel EuclideanSpatial
local instance _p2m_local_instance_a77077472d_475 : BorelSpace EuclideanSpatial := ⟨rfl⟩
def euclideanC1cToH1 (f : C1c (E := EuclideanSpatial)) :
    h1 (E := EuclideanSpatial) («μ» := (volume : Measure EuclideanSpatial)) := by
  let gr := graph (E := EuclideanSpatial) («μ» := (volume : Measure EuclideanSpatial))
  refine ⟨gr f,?_⟩
  exact (LinearMap.range gr).le_topologicalClosure ⟨f,rfl⟩
lemma euclideanC1c_supported_range (K : Set EuclideanSpatial) (hK : MeasurableSet K)
    (f : C1c (E := EuclideanSpatial)) (hf : Function.support f.1⊆K) :
    toL2 («μ» := volume) f∈LinearMap.range
      (Lp.extendByZeroₗᵢ («μ» := (volume : Measure EuclideanSpatial)) (p := (2:ℝ≥0∞)) hK).toLinearMap := by
  have hmem := memLp_of_mem_C1c («μ» := (volume : Measure EuclideanSpatial)) f.2
  have hres : MemLp f.1 2 (volume.restrict K) := hmem.mono_measure Measure.restrict_le_self
  refine ⟨hres.toLp f.1,?_⟩
  apply Lp.ext
  have hext := Lp.extendByZeroₗᵢ_ae_eq («μ» := (volume : Measure EuclideanSpatial)) hK (hres.toLp f.1)
  have hr : ∀ᵐx ∂(volume : Measure EuclideanSpatial),x∈K→hres.toLp f.1 x=f.1 x :=
    (ae_restrict_iff' hK).mp hres.coeFn_toLp
  have hg : (toL2 («μ» := volume) f : EuclideanSpatial→ℝ)=ᵐ[volume]f.1 := hmem.coeFn_toLp
  filter_upwards [hext,hr,hg] with x hx hrx hgx
  simp only [LinearIsometry.coe_toLinearMap]
  rw [hx,hgx]
  by_cases hxm : x∈K
  · simpa only [Set.indicator_of_mem hxm] using hrx hxm
  · rw [Set.indicator_of_notMem hxm]
    symm
    by_contra hne
    exact hxm (hf hne)
def euclideanC1cToSupportedH1 (K : Set EuclideanSpatial) (hK : MeasurableSet K)
    (f : C1c (E := EuclideanSpatial)) (hf : Function.support f.1⊆K) :
    h1On (E := EuclideanSpatial) K hK :=
  ⟨euclideanC1cToH1 f,euclideanC1c_supported_range K hK f hf⟩
end CubicEisenstein
open Filter MeasureTheory
open scoped BigOperators Classical Topology ContDiff Manifold ENNReal InnerProductSpace
namespace CubicEisenstein
abbrev KernelFundamentalVolume : Measure HyperbolicSpace :=
  hyperbolicVolume.restrict (hyperbolicFundamentalSet globalKubotaKernel)
abbrev KernelGradientL2 := Lp (EuclideanSpace ℂ (Fin 3)) 2 KernelFundamentalVolume
lemma kernelTestPartial_continuous (f : kernelSmoothTests) (j : Fin 3) :
    Continuous (fun w => kernelTestPartial f w j) := by
  rw [continuous_iff_continuousAt]
  intro w
  exact (((kernelTestField_contDiffAt f _ (hyperbolicHeight_pos w)).continuousAt_fderiv
    (by simp)).clm_apply continuousAt_const).comp
      hyperbolicEuclideanCoordinates_continuous.continuousAt
lemma kernelGradientAt_continuous (f : kernelSmoothTests) :
    Continuous (fun w => kernelGradientAt w f) := by
  apply (PiLp.continuousLinearEquiv 2 ℂ (fun _ : Fin 3 => ℂ)).symm.continuous.comp
  apply continuous_pi
  intro j
  exact (Complex.continuous_ofReal.comp hyperbolicHeight_continuous).mul
    (kernelTestPartial_continuous f j)
lemma kernelGradientAt_memLp (f : kernelSmoothTests) :
    MemLp (fun w => kernelGradientAt w f) 2 KernelFundamentalVolume := by
  apply (memLp_two_iff_integrable_sq_norm
    (kernelGradientAt_continuous f).aestronglyMeasurable).mpr
  have hh := (quotient_projection_measurePreserving globalKubotaKernel).integrable_comp_of_integrable
    (kernelQuotientEnergyDensity_integrable f)
  have he : (fun w => kernelQuotientEnergyDensity f (integralOrbitProjection globalKubotaKernel w))=
      kernelTestEnergyDensity f := rfl
  dsimp only [Function.comp_def] at hh
  rw [he] at hh
  simpa only [kernelGradientAt_norm_sq] using hh
def kernelGradientToL2 (f : kernelSmoothTests) : KernelGradientL2 :=
  (kernelGradientAt_memLp f).toLp (fun w => kernelGradientAt w f)
lemma kernelGradientToL2_coe (f : kernelSmoothTests) :
    (kernelGradientToL2 f : HyperbolicSpace → EuclideanSpace ℂ (Fin 3))=ᵐ[KernelFundamentalVolume]
      fun w => kernelGradientAt w f := (kernelGradientAt_memLp f).coeFn_toLp
def kernelGradientLinear : kernelSmoothTests →ₗ[ℂ] KernelGradientL2 where
  toFun := kernelGradientToL2
  map_add' f g := by
    apply Lp.ext
    filter_upwards [kernelGradientToL2_coe (f+g),kernelGradientToL2_coe f,
      kernelGradientToL2_coe g,Lp.coeFn_add (kernelGradientToL2 f) (kernelGradientToL2 g)]
      with w hfg hf hg hadd
    simp only [hfg,hadd,Pi.add_apply,hf,hg,map_add]
  map_smul' c f := by
    apply Lp.ext
    filter_upwards [kernelGradientToL2_coe (c•f),kernelGradientToL2_coe f,
      Lp.coeFn_smul c (kernelGradientToL2 f)] with w hcf hf hsmul
    simp only [RingHom.id_apply,hcf,hsmul,Pi.smul_apply,hf,map_smul]
def kernelInitialGradientGraph : Submodule ℂ (KernelQuotientL2 × KernelGradientL2) :=
  LinearMap.range (kernelSmoothTestsToL2.prod kernelGradientLinear)
def kernelInitialGradient : KernelQuotientL2 →ₗ.[ℂ] KernelGradientL2 :=
  kernelInitialGradientGraph.toLinearPMap
end CubicEisenstein
end
end OAI


