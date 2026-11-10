-- Prove2me | Definitions.Def_OAI_NumberTheory_DirichletL_Eisenstein_SmoothTests
-- name    : OAI_NumberTheory_DirichletL_Eisenstein_SmoothTests
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-09T10:51:28.934912+00:00
-- url     : https://prove2.me/theorems/944a15c6-15ac-4aea-94dc-b307580ee54b
-- title:
--   Smooth Tests
-- statement:
--   Definitions and structural lemmas for Smooth Tests, from LW56e2 and the credited OpenAI and dependency authors's pinned QRH LW56e2 refinement development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/Eisenstein/SmoothTests.lean

import Definitions.Def_OAI_NumberTheory_DirichletL_CubicSieve_RowCaps
import Theorems.Thm_OAI_ActualEisensteinCubic_principalSexticRow_mk
import Theorems.Thm_OAI_CubicEisenstein_actual_smoothCuspSeedDefect_contDiffAt
import Theorems.Thm_OAI_CubicEisenstein_finiteCubicMultiplier_coe
import Theorems.Thm_OAI_CubicEisenstein_hyperbolicSpatialChart_apply
import Theorems.Thm_OAI_CubicEisenstein_hyperbolicSpatialChart_source
import Theorems.Thm_OAI_CubicEisenstein_hyperbolicSpatialChart_target_positive
import Theorems.Thm_OAI_CubicEisenstein_hyperbolicSpatialCoordinates_reconstruct
import Theorems.Thm_OAI_CubicEisenstein_integralComplexMatrix_apply
import Theorems.Thm_OAI_CubicEisenstein_kernelLocalLift_symm
import Theorems.Thm_OAI_CubicEisenstein_kernelQuotientChart_contDiffOn
import Theorems.Thm_OAI_CubicEisenstein_kernelQuotientChart_symm
import Theorems.Thm_OAI_CubicEisenstein_kernelQuotientDefect_continuous
import Theorems.Thm_OAI_CubicEisenstein_kernelQuotientDefect_hasCompactSupport
import Theorems.Thm_OAI_CubicEisenstein_kernelQuotient_localHomeomorph
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
namespace CubicEisenstein
section
open Filter MeasureTheory
open scoped BigOperators Classical Topology MatrixGroups Matrix ContDiff Manifold
instance hyperbolicSpatialChartedSpace : ChartedSpace SpatialCoordinates HyperbolicSpace :=
  hyperbolicSpatialChart.singletonChartedSpace hyperbolicSpatialChart_source
instance hyperbolicSpatialIsManifold : IsManifold 𝓘(ℝ,SpatialCoordinates) ∞ HyperbolicSpace :=
  hyperbolicSpatialChart.isManifold_singleton hyperbolicSpatialChart_source
lemma kernelLocalLift_source_out (q : KernelQuotient) : q∈(kernelLocalLift q.out).source := by
  have h := kernelQuotient_localHomeomorph.apply_self_mem_localInverseAt_source (x := q.out)
  change integralOrbitProjection globalKubotaKernel q.out∈(kernelLocalLift q.out).source at h
  rwa [show integralOrbitProjection globalKubotaKernel q.out=q from Quotient.out_eq q] at h
instance kernelSpatialChartedSpace : ChartedSpace SpatialCoordinates KernelQuotient where
  atlas := Set.range kernelQuotientChart
  chartAt := kernelQuotientChart
  mem_chart_source q := ⟨kernelLocalLift_source_out q,Set.mem_univ _⟩
  chart_mem_atlas q := ⟨q,rfl⟩
instance kernelSpatialIsManifold : IsManifold 𝓘(ℝ,SpatialCoordinates) ∞ KernelQuotient := by
  apply isManifold_of_contDiffOn
  rintro e e' ⟨q,rfl⟩ ⟨r,rfl⟩
  simpa only [modelWithCornersSelf_coe,modelWithCornersSelf_coe_symm,Function.id_comp,
    Function.comp_id,Set.preimage_id_eq,Set.range_id,Set.inter_univ,id_eq] using
    kernelQuotientChart_contDiffOn q r
@[simp] lemma hyperbolicSpatial_chartAt (w : HyperbolicSpace) :
    chartAt SpatialCoordinates w=hyperbolicSpatialChart := rfl
@[simp] lemma kernelSpatial_chartAt (q : KernelQuotient) :
    chartAt SpatialCoordinates q=kernelQuotientChart q := rfl
end
section
open Filter MeasureTheory
open scoped BigOperators Classical Topology ContDiff Manifold ENNReal NNReal
def kernelSmoothTests : Submodule ℂ (KernelQuotient→ℂ) where
  carrier f := ContMDiff 𝓘(ℝ,SpatialCoordinates) 𝓘(ℝ,ℂ) ∞ f ∧ HasCompactSupport f
  zero_mem' := ⟨contMDiff_const,HasCompactSupport.zero⟩
  add_mem' hf hg := ⟨hf.1.add hg.1,hf.2.add hg.2⟩
  smul_mem' c f hf := by
    have hc : ContDiff ℝ ∞ (fun z : ℂ => c*z) := contDiff_const.mul contDiff_id
    exact ⟨hc.contMDiff.comp hf.1,hf.2.smul_left⟩
lemma kernelSmoothTests_memLp (f : kernelSmoothTests) :
    MemLp f.1 2 (integralQuotientVolume globalKubotaKernel) :=
  f.2.1.continuous.memLp_of_hasCompactSupport f.2.2
def kernelSmoothTestsToL2 : kernelSmoothTests→ₗ[ℂ]KernelQuotientL2 where
  toFun f := (kernelSmoothTests_memLp f).toLp f.1
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
end
open Filter MeasureTheory
open scoped BigOperators Classical Topology ContDiff Manifold ENNReal
lemma hyperbolicSpatialChart_symm_eq {p : SpatialCoordinates}
    (hp : p∈hyperbolicSpatialChart.target) :
    hyperbolicSpatialChart.symm p=upperPoint (spatialHorizontal p) (p 2)
      (hyperbolicSpatialChart_target_positive hp) := by
  have h := hyperbolicSpatialCoordinates_reconstruct (hyperbolicSpatialChart.symm p)
  have he : hyperbolicSpatialCoordinates (hyperbolicSpatialChart.symm p)=p :=
    hyperbolicSpatialChart.right_inv hp
  simpa only [he,spatialHorizontal] using h.symm
lemma kernelQuotientDefect_coordinate (a b : ℝ) (s : ℂ) (q : KernelQuotient)
    {p : SpatialCoordinates} (hp : p∈hyperbolicSpatialChart.target) :
    kernelQuotientDefect a b s ((kernelQuotientChart q).symm p)=smoothCuspSeedDefectField a b s p := by
  rw [kernelQuotientChart_symm,hyperbolicSpatialChart_symm_eq hp]
  change smoothCuspSeedDefect a b s _=smoothCuspSeedDefectField a b s p
  rw [smoothCuspSeedDefectField,dif_pos (hyperbolicSpatialChart_target_positive hp)]
  rfl
lemma kernelQuotientDefect_contMDiff (a b : ℝ) (s : ℂ) (ha : 1<a) (hab : a<b) :
    ContMDiff 𝓘(ℝ,SpatialCoordinates) 𝓘(ℝ,ℂ) ∞ (kernelQuotientDefect a b s) := by
  intro q
  rw [contMDiffAt_iff]
  refine ⟨(kernelQuotientDefect_continuous a b s ha hab).continuousAt,?_⟩
  have hq : q∈(kernelQuotientChart q).source := mem_chart_source SpatialCoordinates q
  have hp : kernelQuotientChart q q∈hyperbolicSpatialChart.target :=
    ((kernelQuotientChart q).map_source hq).1
  have hF := actual_smoothCuspSeedDefect_contDiffAt a b s ha hab _
    (hyperbolicSpatialChart_target_positive hp)
  have he : (fun p => kernelQuotientDefect a b s ((kernelQuotientChart q).symm p))=ᶠ[𝓝 (kernelQuotientChart q q)]
      smoothCuspSeedDefectField a b s := by
    filter_upwards [hyperbolicSpatialChart.open_target.mem_nhds hp] with p hp
    exact kernelQuotientDefect_coordinate a b s q hp
  have hh := hF.congr_of_eventuallyEq he
  have hh' := hh.contDiffWithinAt (s := Set.univ)
  simpa only [extChartAt_coe,extChartAt_coe_symm,modelWithCornersSelf_coe,
    modelWithCornersSelf_coe_symm,Function.id_comp,Function.comp_id,Set.range_id,
    chartAt_self_eq,kernelSpatial_chartAt,OpenPartialHomeomorph.refl_apply,Function.comp_def,id_eq] using hh'
def kernelDefectSmoothTest (a b : ℝ) (ha : 1<a) (hab : a<b) (s : ℂ) : kernelSmoothTests :=
  ⟨kernelQuotientDefect a b s,kernelQuotientDefect_contMDiff a b s ha hab,
    kernelQuotientDefect_hasCompactSupport a b (by linarith) hab s⟩
end CubicEisenstein
open scoped BigOperators Classical SchwartzMap
namespace InitialMeanSquare
section
open ActualEisensteinCubic SecondPassArithmetic
open SecondPassIntegration (elementNorm)
open ConcreteTraceCRT (eisEmbedding)
section
variable {ι : Type*} [DecidableEq ι]
  (p : ι→OAI.InitialMeanSquare.O) [∀i,(Ideal.span {p i}).IsMaximal]
variable (hp : ∀i,p i≠0)
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀i,lambda∉Ideal.span {p i})
end
end
section
open ActualEisensteinCubic SecondPassArithmetic
open FirstPassCubeLabels (primeProductNorm normalizedColumn columnLog)
open SecondPassIntegration (elementNorm)
section
variable {ι : Type*} [DecidableEq ι] (p : ι→OAI.InitialMeanSquare.O) [∀i,(Ideal.span {p i}).IsMaximal]
def sourceLogZ (Z X : ℝ) (x : SecondExpansionData ι) : ℝ :=
  Real.log (primeProductNorm p x.overlap*X/residualScale p Z x)
def sourceLogE (E : ℝ) (x : SecondExpansionData ι) : ℝ :=
  Real.log (elementNorm (primeSubsetGenerator (fun i => Ideal.span {p i}) x.divisor)/E)
def sourceLogV (V : ℝ) (x : SecondExpansionData ι) : ℝ :=
  Real.log (primeProductNorm p x.overlap/V)
def sourceLogK (K : ℝ) (x : SecondExpansionData ι) : ℝ :=
  Real.log (elementNorm (sourceObservation p x).1/K)
end
end
open MeasureTheory
open scoped BigOperators Classical SchwartzMap ContDiff FourierTransform
open ActualEisensteinCubic SecondPassArithmetic SecondPassIntegration JointLogSeparation
open FirstPassCubeLabels (normalizedColumn columnLog firstLogDensity)
end InitialMeanSquare
open scoped BigOperators Classical
namespace SecondPassArithmetic
open ActualEisensteinCubic
open ActualEisensteinCubic
open FirstPassCubeLabels (primeProductNorm primeProduct aLabel squarefreeLabel b0Label j2Label cubeActiveSupport)
open ConcreteTraceCRT (eisEmbedding)
open IdealMobiusDivisorSum (idealDivisors mem_idealDivisors)
variable {ι : Type*} [DecidableEq ι]
  (p : ι → OAI.SecondPassArithmetic.O) [∀ i,(Ideal.span {p i}).IsMaximal]
def cubeProductIdeal (x : CubeCoordinates ι) : Ideal O :=
  Ideal.span {primeProduct p x.support x.leftExponent}*
    Ideal.span {primeProduct p x.support x.rightExponent}
def cubeParityKey (x : CubeCoordinates ι) : Ideal O × Ideal O :=
  (Ideal.span {squarefreeLabel p x.support (fun i => x.leftExponent i+x.rightExponent i)},
   Ideal.span {b0Label p x.support (fun i => x.leftExponent i+x.rightExponent i) x.leftBit x.rightBit*
     j2Label p x.support (fun i => x.leftExponent i+x.rightExponent i) x.leftBit x.rightBit})
def cubeDivisorKey (x : CubeCoordinates ι) : Fin 3 → Ideal O :=
  ![Ideal.span {primeProduct p x.support x.leftExponent},
    Ideal.span {aLabel p x.support x.leftBit},Ideal.span {aLabel p x.support x.rightBit}]
variable (hp : ∀ i,p i≠0)
include hp
variable (hinj : Function.Injective (fun i => Ideal.span {p i}))
include hinj
end SecondPassArithmetic
end
end OAI


