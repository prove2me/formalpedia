-- Prove2me | Definitions.Def_OAI_NumberTheory_DirichletL_Eisenstein_IntegralCover
-- name    : OAI_NumberTheory_DirichletL_Eisenstein_IntegralCover
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-11T05:09:08.015374+00:00
-- url     : https://prove2.me/theorems/0e69fc58-b013-413e-8081-04afb995ca51
-- title:
--   Integral Cover
-- statement:
--   Definitions and structural lemmas for Integral Cover, from LW56e2 and the credited OpenAI and dependency authors's pinned QRH LW56e2 refinement development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/Eisenstein/IntegralCover.lean

import Definitions.Def_OAI_NumberTheory_DirichletL_Eisenstein_AffineCuspFourier
import Theorems.Thm_OAI_ActualEisensteinCubic_principalSexticRow_mk
import Theorems.Thm_OAI_CanonicalCubeSeparation_cubeFrequencyFactor_norm
import Theorems.Thm_OAI_CanonicalCubeSeparation_radiusIter_succ
import Theorems.Thm_OAI_CanonicalCubeSeparation_radiusIter_zero
import Theorems.Thm_OAI_CanonicalCubeSeparation_sourceLogProfile_apply
import Theorems.Thm_OAI_CanonicalRowCompletion_cubeIndex_apply
import Theorems.Thm_OAI_CompletedHeight_completedT_normHeight_norm
import Theorems.Thm_OAI_CompletedHeight_shortCompletedSum_normHeight_norm
import Theorems.Thm_OAI_CubicEisenstein_continuous_hyperbolic_action
import Theorems.Thm_OAI_CubicEisenstein_cubicUnitGaussSum_one
import Theorems.Thm_OAI_CubicEisenstein_finiteCubicMultiplier_coe
import Theorems.Thm_OAI_CubicEisenstein_hyperbolicHeight_pos
import Theorems.Thm_OAI_CubicEisenstein_hyperbolicSpatialChart_apply
import Theorems.Thm_OAI_CubicEisenstein_hyperbolicSpatialChart_source
import Theorems.Thm_OAI_CubicEisenstein_integralComplexMatrix_apply
import Theorems.Thm_OAI_CubicEisenstein_kernelEnergyGraphCore_dense
import Theorems.Thm_OAI_CubicEisenstein_kernelEnergyGraphCore_norm_sq
import Theorems.Thm_OAI_CubicEisenstein_kernelLocalLift_symm
import Theorems.Thm_OAI_CubicEisenstein_kernelProjection_contMDiff
import Theorems.Thm_OAI_CubicEisenstein_kernelQuotientChart_symm
import Theorems.Thm_OAI_CubicEisenstein_kernelTruncatedWeight_apply
import Theorems.Thm_OAI_CubicEisenstein_mobiusSpatial_contDiffAt
import Theorems.Thm_OAI_CubicEisenstein_mobiusSpatial_coordinates_global
import Theorems.Thm_OAI_CubicEisenstein_quadraticHeightDenominator_continuous
import Theorems.Thm_OAI_CubicEisenstein_spatialTriple_one
import Theorems.Thm_OAI_CubicEisenstein_spatialTriple_two
import Theorems.Thm_OAI_CubicEisenstein_spatialTriple_zero
import Theorems.Thm_OAI_CubicEisenstein_unit_eq_sign_omega
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
import Theorems.Thm_OAI_SixthPowerAverage_outsideWeight_zero
import Theorems.Thm_OAI_SixthPowerAverage_weightedCoeff_zero
import Theorems.Thm_OAI_SixthPowerAverage_weightedMoebius_zero
import Theorems.Thm_OAI_SmoothMobiusCorrection_mem_primeSet
import Theorems.Thm_RellichKondrachov_Analysis_FunctionalSpaces_Sobolev_Euclidean_L2Compactness_smoothBCF_apply
attribute [local fun_prop] OAI.CubicEisenstein.quadraticHeightDenominator_continuous
attribute [local simp] OAI.ActualEisensteinCubic.principalSexticRow_mk
attribute [local simp] OAI.CanonicalCubeSeparation.cubeFrequencyFactor_norm
attribute [local simp] OAI.CanonicalCubeSeparation.radiusIter_succ
attribute [local simp] OAI.CanonicalCubeSeparation.radiusIter_zero
attribute [local simp] OAI.CanonicalCubeSeparation.sourceLogProfile_apply
attribute [local simp] OAI.CanonicalRowCompletion.cubeIndex_apply
attribute [local simp] OAI.CompletedHeight.completedT_normHeight_norm
attribute [local simp] OAI.CompletedHeight.shortCompletedSum_normHeight_norm
attribute [local simp] OAI.CubicEisenstein.cubicUnitGaussSum_one
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
attribute [local simp] OAI.SixthPowerAverage.outsideWeight_zero
attribute [local simp] OAI.SixthPowerAverage.weightedCoeff_zero
attribute [local simp] OAI.SixthPowerAverage.weightedMoebius_zero
attribute [local simp] OAI.SmoothMobiusCorrection.mem_primeSet
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
namespace CubicEisenstein
section
open MeasureTheory Filter
open scoped BigOperators Classical MatrixGroups
open ActualEisensteinCubic ConcreteTraceCRT CubicJacobiGlobal CubicRamified
local notation "Eis" => ActualEisensteinCubic.O
def ramifiedOmegaUnit : Eisˣ := (omega_primitive.isUnit (by decide)).unit
lemma ramifiedOmegaUnit_val : (ramifiedOmegaUnit:Eis)=omega :=
  (omega_primitive.isUnit (by decide)).unit_spec
lemma onceCusp_q_as_scale (t:Eisˣ) (l:Fin 3) :
    onceCuspScale (t*ramifiedOmegaUnit^l.val)=onceCuspScale t*omega^l.val := by
  simp only [onceCuspScale,Units.val_mul,Units.val_pow_eq_pow_val,ramifiedOmegaUnit_val]
  ring
lemma onceCusp_q_congr_scale (t:Eisˣ) (l:Fin 3) :
    (3:Eis)∣onceCuspScale t*omega^l.val-onceCuspScale t := by
  obtain ⟨b,hb⟩:=halfPrimary_omega_pow l.val
  have he:onceCuspScale t*omega^l.val-onceCuspScale t=
      (onceCuspScale t*(omega-1))*b:=by
    linear_combination onceCuspScale t*hb
  rw [he]
  exact (onceCusp_scale_lambda t).mul_right b
lemma onceCusp_q_dvd_three (t:Eisˣ) (l:Fin 3) :
    onceCuspScale t*omega^l.val∣(3:Eis) := by
  rw [←onceCusp_q_as_scale]
  exact ⟨onceCuspComplement _,(onceCusp_scale_complement _).symm⟩
lemma onceCusp_q_dvd_frequency (t:Eisˣ) (l:Fin 3) (h:Eis)
    (hfreq:(3:Eis)∣h-onceCuspScale t) : onceCuspScale t*omega^l.val∣h := by
  have hd:(3:Eis)∣h-onceCuspScale t*omega^l.val:=by
    convert dvd_sub hfreq (onceCusp_q_congr_scale t l) using 1 ;ring
  have hh:onceCuspScale t*omega^l.val∣h-onceCuspScale t*omega^l.val:=
    (onceCusp_q_dvd_three t l).trans hd
  simpa only [sub_add_cancel] using dvd_add hh (dvd_refl (onceCuspScale t*omega^l.val))
def onceCuspFrequencyQuotient (t:Eisˣ) (h:Eis)
    (hfreq:(3:Eis)∣h-onceCuspScale t) (l:Fin 3) : Eis :=
  Classical.choose (onceCusp_q_dvd_frequency t l h hfreq)
def onceCuspRayUnit (u t:Eisˣ) (l:Fin 3) : Eisˣ := u⁻¹^2*t*ramifiedOmegaUnit^l.val
def onceCuspRayIndex (u t:Eisˣ) (l:Fin 3) : Fin 3 :=
  Classical.choose (unit_eq_sign_omega (onceCuspRayUnit u t l))
def onceCuspGaussSeries (u t:Eisˣ) (h:Eis) (hfreq:(3:Eis)∣h-onceCuspScale t) (s:ℂ) : ℂ :=
  ∑l:Fin 3,if (3:Eis)∣onceCuspFrequencyQuotient t h hfreq l+
    ramifiedAffineParameter (onceCuspRayIndex u t l).val 1 then
      (3:ℂ)*(3:ℂ)^(-s)*ShortDraftTrace.breveE (ninthCuspFrequency h/eisEmbedding (onceCuspScale t*omega^l.val))*
        unramifiedCubicGaussSeries s
          (3*((↑u⁻¹:Eis)^2*(onceCuspScale t*omega^l.val))^2*onceCuspFrequencyQuotient t h hfreq l) else 0
end
section
open Filter MeasureTheory
open scoped BigOperators Classical Topology MatrixGroups Manifold ContDiff
open Finset AddChar MulChar EisensteinEmbedding
lemma hyperbolicAction_contMDiff (g : SL(2,ℂ)) :
    ContMDiff 𝓘(ℝ,SpatialCoordinates) 𝓘(ℝ,SpatialCoordinates) ∞
      (fun w : HyperbolicSpace=>g•w) := by
  intro w
  rw [contMDiffAt_iff]
  refine ⟨(continuous_hyperbolic_action g).continuousAt,?_⟩
  have hp : hyperbolicSpatialCoordinates w∈hyperbolicSpatialChart.target :=
    hyperbolicSpatialChart.map_source (Set.mem_univ _)
  have he : (fun p : SpatialCoordinates=>hyperbolicSpatialCoordinates
      (g•hyperbolicSpatialChart.symm p))=ᶠ[𝓝 (hyperbolicSpatialCoordinates w)]mobiusSpatial g := by
    filter_upwards [hyperbolicSpatialChart.open_target.mem_nhds hp] with p hpt
    rw [mobiusSpatial_coordinates_global]
    exact congrArg (mobiusSpatial g) (hyperbolicSpatialChart.right_inv hpt)
  have hd := ((mobiusSpatial_contDiffAt g _ (hyperbolicSpatialCoordinates_positive w)).congr_of_eventuallyEq he).contDiffWithinAt (s:=Set.univ)
  simpa only [extChartAt_coe,extChartAt_coe_symm,modelWithCornersSelf_coe,
    modelWithCornersSelf_coe_symm,Function.id_comp,Function.comp_id,Set.preimage_id_eq,Set.range_id,
    hyperbolicSpatial_chartAt,hyperbolicSpatialChart_apply,Function.comp_def,id_eq] using hd
lemma kernel_contMDiff_of_lift (f : KernelQuotient→ℂ)
    (hf : ContMDiff 𝓘(ℝ,SpatialCoordinates) 𝓘(ℝ,ℂ) ∞
      (fun w : HyperbolicSpace=>f (integralOrbitProjection globalKubotaKernel w))) :
    ContMDiff 𝓘(ℝ,SpatialCoordinates) 𝓘(ℝ,ℂ) ∞ f := by
  intro q
  have hq : q∈(kernelQuotientChart q).source := mem_chart_source SpatialCoordinates q
  have hp : kernelQuotientChart q q∈hyperbolicSpatialChart.target :=
    ((kernelQuotientChart q).map_source hq).1
  have hs : ContMDiffOn 𝓘(ℝ,SpatialCoordinates) 𝓘(ℝ,SpatialCoordinates) ∞
      hyperbolicSpatialChart.symm hyperbolicSpatialChart.target := by
    simpa only [hyperbolicSpatial_chartAt] using
      (contMDiffOn_chart_symm (I:=𝓘(ℝ,SpatialCoordinates)) (n:=∞) (x:=q.out))
  have hd := (hf (hyperbolicSpatialChart.symm (kernelQuotientChart q q))).comp _
    (hs.contMDiffAt (hyperbolicSpatialChart.open_target.mem_nhds hp))
  have he : (fun p=>f ((kernelQuotientChart q).symm p))=
      (fun p=>f (integralOrbitProjection globalKubotaKernel (hyperbolicSpatialChart.symm p))) := by
    funext p
    rw [kernelQuotientChart_symm]
  have hdc : ContDiffAt ℝ ∞ (fun p=>f ((kernelQuotientChart q).symm p))
      (kernelQuotientChart q q) := by
    rw [he]
    exact hd.contDiffAt
  have hc : ContinuousAt f q := by
    have hc := hdc.continuousAt.comp
      ((kernelQuotientChart q).continuousOn.continuousAt
        ((kernelQuotientChart q).open_source.mem_nhds hq))
    apply hc.congr
    filter_upwards [(kernelQuotientChart q).open_source.mem_nhds hq] with r hr
    exact congrArg f ((kernelQuotientChart q).left_inv hr)
  rw [contMDiffAt_iff]
  refine ⟨hc,?_⟩
  have hh := hdc.contDiffWithinAt (s:=Set.univ)
  simpa only [extChartAt_coe,extChartAt_coe_symm,modelWithCornersSelf_coe,
    modelWithCornersSelf_coe_symm,Function.id_comp,Function.comp_id,Set.range_id,
    kernelSpatial_chartAt,chartAt_self_eq,OpenPartialHomeomorph.refl_apply,Function.comp_def,id_eq] using hh
lemma kernelSource_comp_contMDiff (M : CubicKubota.levelTwo) (f : KernelQuotient→ℂ)
    (hf : ContMDiff 𝓘(ℝ,SpatialCoordinates) 𝓘(ℝ,ℂ) ∞ f) :
    ContMDiff 𝓘(ℝ,SpatialCoordinates) 𝓘(ℝ,ℂ) ∞ (fun q=>f (kernelSourceAction M q)) := by
  apply kernel_contMDiff_of_lift
  exact (hf.comp kernelProjection_contMDiff).comp (hyperbolicAction_contMDiff (sourceComplexMatrix M))
def kernelSourceTest (M : CubicKubota.levelTwo) (f : kernelSmoothTests) : kernelSmoothTests :=
  ⟨fun q=>f.1 (kernelSourceAction M q),kernelSource_comp_contMDiff M f.1 f.2.1,
    f.2.2.comp_homeomorph (kernelSourceHomeomorph M)⟩
def kernelSourceTestLinear (M : CubicKubota.levelTwo) : kernelSmoothTests→ₗ[ℂ]kernelSmoothTests where
  toFun := kernelSourceTest M
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
lemma kernelSourceTest_field (M : CubicKubota.levelTwo) (f : kernelSmoothTests) :
    kernelTestField (kernelSourceTest M f)=kernelTestField f ∘ euclideanAction (sourceComplexMatrix M) := by
  funext p
  change f.1 (integralOrbitProjection globalKubotaKernel
      (sourceComplexMatrix M•euclideanToHyperbolic p))=
    f.1 (integralOrbitProjection globalKubotaKernel
      (euclideanToHyperbolic (euclideanAction (sourceComplexMatrix M) p)))
  rw [euclideanAction,euclideanToHyperbolic_coordinates]
lemma kernelSourceTest_energyDensity (M : CubicKubota.levelTwo) (f : kernelSmoothTests)
    (w : HyperbolicSpace) :
    kernelTestEnergyDensity (kernelSourceTest M f) w=
      kernelTestEnergyDensity f (sourceComplexMatrix M•w) := by
  have hp := hyperbolicHeight_pos w
  have he : hyperbolicEuclideanCoordinates (sourceComplexMatrix M•w)=
      euclideanAction (sourceComplexMatrix M) (hyperbolicEuclideanCoordinates w) := by
    rw [euclideanAction,euclideanToHyperbolic_coordinates]
  have hR := hyperbolic_cotangent_energy_comp (sourceComplexMatrix M)
    (fun p : EuclideanSpatial=>(kernelTestField f p).re) (hyperbolicEuclideanCoordinates w) hp
    ((kernelTestField_re_contDiffAt f _ (euclideanAction_positive _ _)).differentiableAt (by simp))
  have hI := hyperbolic_cotangent_energy_comp (sourceComplexMatrix M)
    (fun p : EuclideanSpatial=>(kernelTestField f p).im) (hyperbolicEuclideanCoordinates w) hp
    ((kernelTestField_im_contDiffAt f _ (euclideanAction_positive _ _)).differentiableAt (by simp))
  unfold kernelTestEnergyDensity euclideanScalarDirichletDensity
  rw [kernelSourceTest_field,he]
  exact congrArg₂ (fun a b : ℝ=>a+b) hR hI
lemma kernelSourceTest_quotientDensity (M : CubicKubota.levelTwo) (f : kernelSmoothTests)
    (q : KernelQuotient) :
    kernelQuotientEnergyDensity (kernelSourceTest M f) q=
      kernelQuotientEnergyDensity f (kernelSourceAction M q) := by
  induction q using Quotient.inductionOn with
  | _ w => exact kernelSourceTest_energyDensity M f w
lemma kernelSourceTest_energy (M : CubicKubota.levelTwo) (f : kernelSmoothTests) :
    kernelDirichletEnergy (kernelSourceTest M f)=kernelDirichletEnergy f := by
  unfold kernelDirichletEnergy
  simp_rw [kernelSourceTest_quotientDensity]
  exact (kernelSourceAction_measurePreserving M).integral_comp
    (kernelSourceHomeomorph M).measurableEmbedding _
lemma kernelSourceTest_mass (M : CubicKubota.levelTwo) (f : kernelSmoothTests) :
    kernelSmoothTestsToL2 (kernelSourceTest M f)=kernelSourcePullback M (kernelSmoothTestsToL2 f) := by
  apply Lp.ext
  have hbase := (kernelSourceAction_measurePreserving M).quasiMeasurePreserving.ae_eq_comp
    (kernelSmoothTests_memLp f).coeFn_toLp
  filter_upwards [(kernelSmoothTests_memLp (kernelSourceTest M f)).coeFn_toLp,
    kernelSourcePullback_ae_eq M (kernelSmoothTestsToL2 f),hbase] with q hnew hpull hbase
  exact hnew.trans (hpull.trans hbase).symm
lemma kernelSourceTest_graph_norm (M : CubicKubota.levelTwo) (f : kernelSmoothTests) :
    ‖kernelEnergyGraphCore (kernelSourceTest M f)‖=‖kernelEnergyGraphCore f‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [kernelEnergyGraphCore_norm_sq,kernelEnergyGraphCore_norm_sq,
    kernelSourceTest_energy,kernelSourceTest_mass,LinearIsometry.norm_map]
def kernelSourceEnergyPullback (M : CubicKubota.levelTwo) : KernelEnergyGraph→ₗᵢ[ℂ]KernelEnergyGraph :=
  { (kernelEnergyGraphCore.comp (kernelSourceTestLinear M)).extendOfNorm
      kernelEnergyGraphCore with
    norm_map' := by
      intro u
      refine kernelEnergyGraphCore_dense.induction_on (p := fun u => ‖(kernelEnergyGraphCore.comp (kernelSourceTestLinear M)).extendOfNorm kernelEnergyGraphCore u‖ = ‖u‖) u ?_ ?_
      · exact isClosed_eq (by fun_prop) (by fun_prop)
      · intro f
        rw [LinearMap.extendOfNorm_eq kernelEnergyGraphCore_dense
          ⟨1, fun f => by change ‖kernelEnergyGraphCore (kernelSourceTest M f)‖ ≤ 1 * ‖kernelEnergyGraphCore f‖; rw [kernelSourceTest_graph_norm, one_mul]⟩]
        exact kernelSourceTest_graph_norm M f }
end
open Filter MeasureTheory
open scoped BigOperators Classical Topology MatrixGroups InnerProductSpace
open Finset AddChar MulChar EisensteinEmbedding
end CubicEisenstein
section
open scoped Classical MatrixGroups BigOperators
namespace CubicKubota
open ActualEisensteinCubic ConcreteTraceCRT CubicEisenstein CubicJacobiGlobal
local notation "Eis" => ActualEisensteinCubic.O
def cubeCuspHeightWeight (p:Eis) (j:Fin 4) : ℂ :=
  (((Ideal.absNorm (Ideal.span {p}):ℝ)^((2*(j.val:ℝ)-3)/3)):ℝ)
end CubicKubota
namespace CubicEisenstein
section
open ActualEisensteinCubic ConcreteTraceCRT CubicJacobiGlobal CubicKubota
local notation "Eis" => ActualEisensteinCubic.O
def cubeDilationRoot (p:Eis) : ℂ :=
  Classical.choose (IsAlgClosed.exists_pow_nat_eq (eisEmbedding p^3) (by decide : 0<2))
lemma cubeDilationRoot_sq (p:Eis) : cubeDilationRoot p^2=eisEmbedding p^3 :=
  Classical.choose_spec (IsAlgClosed.exists_pow_nat_eq (eisEmbedding p^3) (by decide : 0<2))
lemma cubeDilationRoot_ne_zero (p:Eis) (hp:p≠0) : cubeDilationRoot p≠0 := by
  intro h
  have hs:=cubeDilationRoot_sq p
  rw [h,zero_pow (by decide)] at hs
  exact pow_ne_zero 3 (eisEmbedding_ne_zero hp) hs.symm
def cubeAverageMatrix (p:Eis) (hp:p≠0) (q:Eis) : SL(2,ℂ) :=
  complexDiagonal (cubeDilationRoot p)⁻¹ (inv_ne_zero (cubeDilationRoot_ne_zero p hp)) *
    complexTranslation (3*eisEmbedding q)
def cubeAverage (p:Eis) (hp:p≠0) (F:HyperbolicSpace→ℂ) (w:HyperbolicSpace) : ℂ :=
  (Ideal.absNorm (Ideal.span {p}):ℂ)⁻¹^3 *
    ∑' r:Eis⧸Ideal.span {p^3},
      F (cubeAverageMatrix p hp (GaussianShiftedPartition.representative (p^3) r) • w)
end
open ActualEisensteinCubic ConcreteTraceCRT CubicJacobiGlobal CubicKubota
local notation "Eis" => ActualEisensteinCubic.O
end CubicEisenstein
end
open Filter MeasureTheory
open scoped BigOperators Classical Topology MatrixGroups Pointwise
open Finset AddChar MulChar EisensteinEmbedding
namespace CubicEisenstein
local notation "O" => ActualEisensteinCubic.O
def integralCoverMap {H K : Subgroup (SL(2,ActualEisensteinCubic.O))} (hHK : H≤K) :
    IntegralOrbitQuotient H→IntegralOrbitQuotient K :=
  Quotient.map' id (by
    rintro w u ⟨M,hM⟩
    exact ⟨Subgroup.inclusion hHK M,hM⟩)
abbrev IntegralCoverCosets (H K : Subgroup (SL(2,ActualEisensteinCubic.O))) := K ⧸ H.subgroupOf K
def integralCoverRep (H K : Subgroup (SL(2,ActualEisensteinCubic.O))) (q : IntegralCoverCosets H K) : K := q.out
def integralCoverSheet (H K : Subgroup (SL(2,ActualEisensteinCubic.O))) (q : IntegralCoverCosets H K) : Set HyperbolicSpace :=
  (fun w=>integralCoverRep H K q • w) ⁻¹' hyperbolicFundamentalSet K
def integralCoverDomain (H K : Subgroup (SL(2,ActualEisensteinCubic.O))) : Set HyperbolicSpace :=
  ⋃q : IntegralCoverCosets H K,integralCoverSheet H K q
end CubicEisenstein
end
end OAI


