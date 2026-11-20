-- Prove2me | Definitions.Def_OAI_NumberTheory_DirichletL_Eisenstein_CorrespondenceAdjoint
-- name    : OAI_NumberTheory_DirichletL_Eisenstein_CorrespondenceAdjoint
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-19T07:36:03.59668+00:00
-- url     : https://prove2.me/theorems/2cb9b9f6-0cc1-4bcd-927c-88f83b8336b3
-- title:
--   Correspondence Adjoint
-- statement:
--   Definitions and structural lemmas for Correspondence Adjoint, from LW56e2 and the credited OpenAI and dependency authors's pinned QRH LW56e2 refinement development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/Eisenstein/CorrespondenceAdjoint.lean

import Definitions.Def_OAI_NumberTheory_DirichletL_Eisenstein_RamifiedSixBranches
import Theorems.Thm_OAI_ActualEisensteinCubic_principalSexticRow_mk
import Theorems.Thm_OAI_CanonicalCubeSeparation_cubeFrequencyFactor_norm
import Theorems.Thm_OAI_CanonicalCubeSeparation_radiusIter_succ
import Theorems.Thm_OAI_CanonicalCubeSeparation_radiusIter_zero
import Theorems.Thm_OAI_CanonicalCubeSeparation_sourceLogProfile_apply
import Theorems.Thm_OAI_CanonicalRowCompletion_cubeIndex_apply
import Theorems.Thm_OAI_CompletedHeight_completedT_normHeight_norm
import Theorems.Thm_OAI_CompletedHeight_shortCompletedSum_normHeight_norm
import Theorems.Thm_OAI_CubicEisenstein_breveE_norm
import Theorems.Thm_OAI_CubicEisenstein_continuous_upperCoordinates
import Theorems.Thm_OAI_CubicEisenstein_cubicBesselLowerConstant_pos
import Theorems.Thm_OAI_CubicEisenstein_cubicUnitGaussSum_one
import Theorems.Thm_OAI_CubicEisenstein_cuspCoordinateLift_positive
import Theorems.Thm_OAI_CubicEisenstein_cuspCoordinateLift_weighted_integrable_of_pos
import Theorems.Thm_OAI_CubicEisenstein_cuspFrequency_ne_zero
import Theorems.Thm_OAI_CubicEisenstein_cuspPeriodStrip_integral_coordinates_of_pos
import Theorems.Thm_OAI_CubicEisenstein_cusp_volume_ne_zero
import Theorems.Thm_OAI_CubicEisenstein_finiteCubicMultiplier_coe
import Theorems.Thm_OAI_CubicEisenstein_hyperbolicHeight_upperPoint
import Theorems.Thm_OAI_CubicEisenstein_hyperbolicSpatialChart_apply
import Theorems.Thm_OAI_CubicEisenstein_hyperbolicSpatialChart_source
import Theorems.Thm_OAI_CubicEisenstein_integralComplexMatrix_apply
import Theorems.Thm_OAI_CubicEisenstein_interval_ae_eq_of_boundedContinuous_height_tests
import Theorems.Thm_OAI_CubicEisenstein_kernelLocalLift_symm
import Theorems.Thm_OAI_CubicEisenstein_kernelQuotientChart_symm
import Theorems.Thm_OAI_CubicEisenstein_kernelTruncatedWeight_apply
import Theorems.Thm_OAI_CubicEisenstein_norm_mem_periodDomain
import Theorems.Thm_OAI_CubicEisenstein_periodDomain_finiteMeasure
import Theorems.Thm_OAI_CubicEisenstein_periodDomain_measurable
import Theorems.Thm_OAI_CubicEisenstein_quadraticHeightDenominator_continuous
import Theorems.Thm_OAI_CubicEisenstein_ramifiedSourceFunction_continuous
import Theorems.Thm_OAI_CubicEisenstein_ramifiedSource_height_continuous
import Theorems.Thm_OAI_CubicEisenstein_ramifiedSource_height_residue_integral
import Theorems.Thm_OAI_CubicEisenstein_ramifiedSource_scaled_fourier_active
import Theorems.Thm_OAI_CubicEisenstein_ramifiedSource_scaled_fourier_off_support
import Theorems.Thm_OAI_CubicEisenstein_ramifiedSource_zero_mode10
import Theorems.Thm_OAI_CubicEisenstein_ramifiedSource_zero_mode19
import Theorems.Thm_OAI_CubicEisenstein_schlafliBesselK_cubic_lower
import Theorems.Thm_OAI_CubicEisenstein_sourceFourierKernel_continuous_freq
import Theorems.Thm_OAI_CubicEisenstein_sourceFourierKernel_cubic_height
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
section
open Filter MeasureTheory
open scoped BigOperators Classical Topology MatrixGroups InnerProductSpace
local notation "O" => ActualEisensteinCubic.O
end
section
open Filter MeasureTheory
open scoped BigOperators Classical Topology MatrixGroups
section
lemma continuous_period_integral {X:Type*} [TopologicalSpace X]
    [FirstCountableTopology X] [LocallyCompactSpace X]
    (f:X→ℂ→ℂ) (hf:Continuous f.uncurry) :
    Continuous (fun x=>∫z in periodDomain,f x z) := by
  rw [continuous_iff_continuousAt]
  intro x0
  obtain ⟨U,hUc,hUn⟩:=exists_compact_mem_nhds x0
  let radius:ℝ:=∑i,‖periodBasis i‖
  obtain ⟨C,hC⟩:=(hUc.prod (isCompact_closedBall (0:ℂ) radius)).bddAbove_image hf.norm.continuousOn
  apply continuousAt_of_dominated
  · filter_upwards with x using (show Continuous (f x) from hf.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable
  · filter_upwards [hUn] with x hx
    filter_upwards [ae_restrict_mem periodDomain_measurable] with z hz
    apply hC
    exact ⟨(x,z),⟨hx,by simpa only [Metric.mem_closedBall,dist_zero_right,radius] using norm_mem_periodDomain z hz⟩,rfl⟩
  · let:=periodDomain_finiteMeasure
    exact integrable_const C
  · filter_upwards with z using (show Continuous (fun x=>f x z) from hf.comp (continuous_id.prodMk continuous_const)).continuousAt
def continuousCuspSlice (f:HyperbolicSpace→ℂ) (freq:ℂ) (v:ℝ) :ℂ:=
  (∫z in periodDomain,f (cuspCoordinateLift (v,z))*ShortDraftTrace.breveE (-freq*z))/(v:ℂ)^3
lemma continuousCuspSlice_integrable (f:HyperbolicSpace→ℂ) (hf:Continuous f)
    (freq:ℂ) (a b:ℝ) (ha:0<a) :
    IntegrableOn (continuousCuspSlice f freq) (Set.Icc a b) volume := by
  let g:HyperbolicSpace→ℂ:=fun w=>f w*arbitraryCuspWeightedPhase 1 freq w
  have hg:Continuous g:=hf.mul (arbitraryCuspWeightedPhase_continuous 1 freq)
  have hi:=cuspCoordinateLift_weighted_integrable_of_pos a b ha g hg
  rw [IntegrableOn,Measure.volume_eq_prod,←Measure.prod_restrict] at hi
  apply hi.integral_prod_left.congr
  filter_upwards [ae_restrict_mem measurableSet_Icc] with v hv
  have hp:0<v:=ha.trans_le hv.1
  rw [integral_div,continuousCuspSlice]
  apply congrArg (fun c:ℂ=>c/(v:ℂ)^3)
  apply integral_congr_ae
  exact Eventually.of_forall (fun z=>by
    dsimp only [g]
    rw [arbitraryCuspWeightedPhase,cuspCoordinateLift_positive v z hp,
      hyperbolicHeight_upperPoint,hyperbolicHorizontal_upperPoint]
    simp)
lemma continuousCuspSlice_continuousOn (f:HyperbolicSpace→ℂ) (hf:Continuous f)
    (freq:ℂ) (a b:ℝ) (ha:0<a) :
    ContinuousOn (continuousCuspSlice f freq) (Set.Icc a b) := by
  let coord:(ℝ × ℂ)→UpperCoordinates:=fun q=>⟨(q.2,max a q.1),ha.trans_le (le_max_left _ _)⟩
  have hc:Continuous coord:=by
    apply Continuous.subtype_mk
    exact continuous_snd.prodMk (continuous_const.max continuous_fst)
  have hup:Continuous (fun q:(ℝ × ℂ)=>f (upperPoint q.2 (max a q.1) (ha.trans_le (le_max_left _ _)))):=
    hf.comp (continuous_upperCoordinates.comp hc)
  have he:Continuous (fun q:(ℝ × ℂ)=>ShortDraftTrace.breveE (-freq*q.2)):=by
    change Continuous (fun q:(ℝ × ℂ)=>Complex.exp (2*Real.pi*Complex.I*((-freq*q.2)+starRingEnd ℂ (-freq*q.2))))
    fun_prop
  have hi:=continuous_period_integral (fun v z=>f (upperPoint z (max a v) (ha.trans_le (le_max_left _ _)))*
      ShortDraftTrace.breveE (-freq*z)) (hup.mul he)
  have hnum:ContinuousOn (fun v:ℝ=>∫z in periodDomain,f (cuspCoordinateLift (v,z))*
      ShortDraftTrace.breveE (-freq*z)) (Set.Icc a b):=by
    apply hi.continuousOn.congr
    intro v hv
    have hp:0<v:=ha.trans_le hv.1
    simp only [max_eq_right hv.1,cuspCoordinateLift_positive v _ hp]
  exact hnum.div (Complex.continuous_ofReal.pow 3).continuousOn
    (fun v hv=>pow_ne_zero 3 (Complex.ofReal_ne_zero.mpr (ha.trans_le hv.1).ne'))
lemma continuousCuspSlice_test (f:HyperbolicSpace→ℂ) (hf:Continuous f) (freq:ℂ)
    (a b:ℝ) (ha:0<a) (ρ:BoundedContinuousFunction ℝ ℂ) :
    (∫w in cuspPeriodStrip a b,f w*arbitraryCuspWeightedPhase ρ freq w∂hyperbolicVolume)=
      ∫v in Set.Icc a b,ρ v*continuousCuspSlice f freq v := by
  have hg:Continuous (fun w=>f w*arbitraryCuspWeightedPhase ρ freq w):=
    hf.mul (arbitraryCuspWeightedPhase_continuous ρ freq)
  rw [cuspPeriodStrip_integral_coordinates_of_pos a b ha _ hg.aestronglyMeasurable
    (cuspCoordinateLift_weighted_integrable_of_pos a b ha _ hg)]
  apply setIntegral_congr_fun measurableSet_Icc
  intro v hv
  have hp:0<v:=ha.trans_le hv.1
  dsimp only
  rw [continuousCuspSlice,←mul_div_assoc]
  congr 1
  rw [←integral_const_mul]
  apply integral_congr_ae
  exact Eventually.of_forall (fun z=>by
    dsimp only
    rw [arbitraryCuspWeightedPhase,cuspCoordinateLift_positive v z hp,
      hyperbolicHeight_upperPoint,hyperbolicHorizontal_upperPoint]
    ring)
theorem continuousCuspSlice_eq_of_tests (f:HyperbolicSpace→ℂ) (hf:Continuous f)
    (freq:ℂ) (g:ℝ→ℂ)
    (hg:∀a b:ℝ,0<a→ContinuousOn g (Set.Icc a b))
    (ht:∀a b:ℝ,∀_ha:0<a,∀ρ:BoundedContinuousFunction ℝ ℂ,
      (∫w in cuspPeriodStrip a b,f w*arbitraryCuspWeightedPhase ρ freq w∂hyperbolicVolume)=
        ∫v in Set.Icc a b,ρ v*g v) (v:ℝ) (hv:0<v) :
    continuousCuspSlice f freq v=g v := by
  have ha:0<v/2:=half_pos hv
  have hab:v/2≠2*v:=by linarith
  have he:continuousCuspSlice f freq=ᵐ[volume.restrict (Set.Icc (v/2) (2*v))]g:=by
    apply interval_ae_eq_of_boundedContinuous_height_tests (v/2) (2*v) _ _
      (continuousCuspSlice_integrable f hf freq _ _ ha) ((hg _ _ ha).integrableOn_Icc)
    intro ρ
    rw [←continuousCuspSlice_test f hf freq _ _ ha ρ]
    exact ht _ _ ha ρ
  exact Measure.eqOn_Icc_of_ae_eq volume hab he
    (continuousCuspSlice_continuousOn f hf freq _ _ ha) (hg _ _ ha)
      (by constructor <;>linarith)
local notation "Eis" => ActualEisensteinCubic.O
theorem ramifiedSource_fourier_all_heights (side:Bool) (h:Eis)
    (hf:(3:Eis)∣h-onceCuspScale (ramifiedCuspScaleUnit side))
    (v:ℝ) (hv:0<v) :
    (∫z in periodDomain,ramifiedSourceFunction (ramifiedCuspRoot side:Eis) (upperPoint z v hv)*
      ShortDraftTrace.breveE (-ninthCuspFrequency h*z))=
      ramifiedArithmeticResidue side h hf*(v:ℂ)^(2/3:ℂ)*
        sourceFourierKernel (4/3) (ninthCuspFrequency h*v) := by
  let R:=ramifiedArithmeticResidue side h hf
  let g:ℝ→ℂ:=fun v=>R*(v:ℂ)^(-(4/3:ℂ)-1)*
    sourceFourierKernel (4/3) (ninthCuspFrequency h*v)
  have hg:∀a b:ℝ,0<a→ContinuousOn g (Set.Icc a b):=by
    intro a b ha x hx
    have hp:0<x:=ha.trans_le hx.1
    exact ((continuousAt_const.mul
      (Complex.continuousAt_ofReal_cpow_const x (-(4/3:ℂ)-1) (Or.inr hp.ne'))).mul
        ((sourceFourierKernel_continuous_freq (4/3) (by norm_num)).continuousAt.comp
          ((Complex.continuous_ofReal.const_mul (ninthCuspFrequency h)).continuousAt))).continuousWithinAt
  have ht:∀a b:ℝ,∀ha:0<a,∀ρ:BoundedContinuousFunction ℝ ℂ,
      (∫w in cuspPeriodStrip a b,ramifiedSourceFunction (ramifiedCuspRoot side:Eis) w*
        arbitraryCuspWeightedPhase ρ (ninthCuspFrequency h) w∂hyperbolicVolume)=
          ∫x in Set.Icc a b,ρ x*g x:=by
    intro a b ha ρ
    rw [ramifiedSource_height_residue_integral side h hf a b ha ρ,
      arbitraryIntervalWhittaker,←integral_const_mul]
    apply integral_congr_ae
    exact Eventually.of_forall (fun x=>by dsimp only [g,R];ring)
  have he:=continuousCuspSlice_eq_of_tests
    (ramifiedSourceFunction (ramifiedCuspRoot side:Eis)) (ramifiedSourceFunction_continuous _)
    (ninthCuspFrequency h) g hg ht v hv
  have hvn:(v:ℂ)≠0:=Complex.ofReal_ne_zero.mpr hv.ne'
  have hp:(v:ℂ)^(-(4/3:ℂ)-1)=(v:ℂ)^(2/3:ℂ)/(v:ℂ)^3:=by
    rw [show -(4/3:ℂ)-1=(2/3:ℂ)-3 by ring,Complex.cpow_sub _ _ hvn]
    congr 1
    exact Complex.cpow_natCast _ 3
  dsimp only [continuousCuspSlice,g,R] at he
  simp only [cuspCoordinateLift_positive v _ hv,hp] at he
  apply (div_left_inj' (pow_ne_zero 3 hvn)).mp
  convert he using 1 ;ring
end
section
local notation "Eis" => ActualEisensteinCubic.O
lemma continuous_period_fourier_bound (f:ℂ→ℂ) (hf:Continuous f) :
    ∃C:ℝ,0≤C∧∀freq:ℂ,‖∫z in periodDomain,f z*ShortDraftTrace.breveE (-freq*z)‖≤C := by
  let radius:ℝ:=∑i,‖periodBasis i‖
  obtain ⟨B,hB⟩:=(isCompact_closedBall (0:ℂ) radius).bddAbove_image hf.norm.continuousOn
  refine ⟨max 0 B*(volume.restrict periodDomain).real Set.univ,mul_nonneg (le_max_left _ _) (measureReal_nonneg),?_⟩
  intro freq
  let:=periodDomain_finiteMeasure
  apply norm_integral_le_of_norm_le_const
  filter_upwards [ae_restrict_mem periodDomain_measurable] with z hz
  rw [norm_mul,breveE_norm,mul_one]
  apply le_trans _ (le_max_right _ _)
  apply hB
  exact ⟨z,by simpa only [Metric.mem_closedBall,dist_zero_right,radius] using norm_mem_periodDomain z hz,rfl⟩
theorem continuous_fourier_bessel_subexponential (f:ℝ→ℂ→ℂ) (c:Eis→ℂ)
    (hf:∀v:ℝ,0<v→Continuous (f v))
    (hfour:∀v:ℝ,∀_hv:0<v,∀h:Eis,h≠0→
      (∫z in periodDomain,f v z*ShortDraftTrace.breveE (-cuspFrequency h*z))=
        ((9*Real.sqrt 3/2:ℝ):ℂ)*c h*(v:ℂ)*
          schlafliBesselK (1/3) (4*Real.pi*‖cuspFrequency h‖*v))
    (ε:ℝ) (hε:0<ε) :
    ∃C:ℝ,0≤C∧∀h:Eis,h≠0→‖c h‖≤C*Real.exp (ε*‖cuspFrequency h‖) := by
  let v:ℝ:=ε/(9*Real.pi)
  have hv:0<v:=div_pos hε (by positivity)
  let area:ℂ:=((9*Real.sqrt 3/2:ℝ):ℂ)
  have harea:0<‖area‖:=norm_pos_iff.mpr cusp_volume_ne_zero
  obtain ⟨B,hB,hbound⟩:=continuous_period_fourier_bound (f v) (hf v hv)
  let D:ℝ:=‖area‖*v*cubicBesselLowerConstant
  have hD:0<D:=mul_pos (mul_pos harea hv) cubicBesselLowerConstant_pos
  refine ⟨B/D,div_nonneg hB hD.le,?_⟩
  intro h hh
  have hx:0<4*Real.pi*‖cuspFrequency h‖*v:=by
    have hr:=norm_pos_iff.mpr (cuspFrequency_ne_zero h hh)
    positivity
  have hl: cubicBesselLowerConstant*Real.exp (-(ε*‖cuspFrequency h‖))≤
      ‖schlafliBesselK (1/3) (4*Real.pi*‖cuspFrequency h‖*v)‖:=by
    have hb:=(schlafliBesselK_cubic_lower (4*Real.pi*‖cuspFrequency h‖*v) hx).trans (Complex.re_le_norm _)
    convert hb using 1
    congr 2
    dsimp [v]
    field_simp

  have hb:=hbound (cuspFrequency h)
  rw [hfour v hv h hh,norm_mul,norm_mul,norm_mul,Complex.norm_of_nonneg hv.le] at hb
  have hm:‖c h‖*(D*Real.exp (-(ε*‖cuspFrequency h‖)))≤B:=by
    calc
      _ = (‖area‖*‖c h‖*v)*(cubicBesselLowerConstant*Real.exp (-(ε*‖cuspFrequency h‖))) := by dsimp [D];ring
      _ ≤ (‖area‖*‖c h‖*v)*‖schlafliBesselK (1/3) (4*Real.pi*‖cuspFrequency h‖*v)‖ :=
        mul_le_mul_of_nonneg_left hl (by positivity)
      _ ≤ B := hb
  have hexp:0<Real.exp (-(ε*‖cuspFrequency h‖)):=Real.exp_pos _
  apply (le_div_iff₀ (mul_pos hD hexp)).mpr at hm
  calc
    _ ≤ B/(D*Real.exp (-(ε*‖cuspFrequency h‖))) := hm
    _ = (B/D)*Real.exp (ε*‖cuspFrequency h‖) := by rw [Real.exp_neg];field_simp
end
section
open ConcreteTraceCRT
local notation "Eis" => ActualEisensteinCubic.O
lemma ninthCuspFrequency_three (h:Eis) :
    3*ninthCuspFrequency h=cuspFrequency h := by
  unfold ninthCuspFrequency cuspFrequency
  ring
lemma sourceFourierKernel_cubic_amplitude (h:Eis) (hh:h≠0) (v:ℝ) (hv:0<v) :
    (v:ℂ)^(2/3:ℂ)*sourceFourierKernel (4/3) (cuspFrequency h*v)=
      cubicBesselNormalizer h*(v:ℂ)*schlafliBesselK (1/3) (4*Real.pi*‖cuspFrequency h‖*v) := by
  have hvn:(v:ℂ)≠0:=Complex.ofReal_ne_zero.mpr hv.ne'
  have hp:(v:ℂ)^(-(4/3:ℂ)-1)=(v:ℂ)^(2/3:ℂ)/(v:ℂ)^3:=by
    rw [show -(4/3:ℂ)-1=(2/3:ℂ)-3 by ring,Complex.cpow_sub _ _ hvn]
    congr 1
    exact Complex.cpow_natCast _ 3
  have he:=sourceFourierKernel_cubic_height h hh v hv
  rw [hp] at he
  apply (div_left_inj' (pow_ne_zero 3 hvn)).mp
  calc
    _ = ((v:ℂ)^(2/3:ℂ)/(v:ℂ)^3)*sourceFourierKernel (4/3) (cuspFrequency h*v) := by ring
    _ = _ := he
    _ = _ := by field_simp
lemma ramified_kernel_scaled_bessel (h:Eis) (hh:h≠0) (v:ℝ) (hv:0<v) :
    ((3*v:ℝ):ℂ)^(2/3:ℂ)*sourceFourierKernel (4/3) (ninthCuspFrequency h*(3*v:ℝ))=
      (3:ℂ)^(2/3:ℂ)*cubicBesselNormalizer h*(v:ℂ)*
        schlafliBesselK (1/3) (4*Real.pi*‖cuspFrequency h‖*v) := by
  have hfreq:ninthCuspFrequency h*((3*v:ℝ):ℂ)=cuspFrequency h*v:=by
    push_cast
    rw [←ninthCuspFrequency_three]
    ring
  have hp:((3*v:ℝ):ℂ)^(2/3:ℂ)=(3:ℂ)^(2/3:ℂ)*(v:ℂ)^(2/3:ℂ):=by
    simpa only [Complex.ofReal_mul,Complex.ofReal_ofNat] using
      Complex.mul_cpow_ofReal_nonneg (a:=3) (b:=v) (by norm_num) hv.le (2/3:ℂ)
  rw [hfreq,hp,mul_assoc,sourceFourierKernel_cubic_amplitude h hh v hv]
  ring
end
section
open ConcreteTraceCRT
local notation "Eis" => ActualEisensteinCubic.O
def ramifiedScaledRow (side:Bool) (v:ℝ) (z:ℂ) :ℂ:=
  ramifiedSourceFunction (ramifiedCuspRoot side:Eis) (cuspCoordinateLift (3*v,3*z))
def ramifiedBesselValue (side:Bool) (h:Eis) :ℂ:=
  if hf:(3:Eis)∣h-onceCuspScale (ramifiedCuspScaleUnit side) then
    (3:ℂ)^(2/3:ℂ)*cubicBesselNormalizer h*ramifiedArithmeticResidue side h hf/
      ((9*Real.sqrt 3/2:ℝ):ℂ)
  else 0
lemma ramifiedScaledRow_continuous (side:Bool) (v:ℝ) (hv:0<v) :
    Continuous (ramifiedScaledRow side v) := by
  have hp:0<3*v:=by positivity
  have he:ramifiedScaledRow side v=(fun z=>ramifiedSourceFunction (ramifiedCuspRoot side:Eis)
      (upperPoint (3*z) (3*v) hp)):=by
    funext z
    exact congrArg (ramifiedSourceFunction (ramifiedCuspRoot side:Eis)) (cuspCoordinateLift_positive (3*v) (3*z) hp)
  rw [he]
  exact (ramifiedSource_height_continuous side (3*v) hp).comp (continuous_const.mul continuous_id)
lemma ramifiedScaledRow_zero (side:Bool) (v:ℝ) (hv:0<v) :
    (∫z in periodDomain,ramifiedScaledRow side v z)=0 := by
  have hp:0<3*v:=by positivity
  simp only [ramifiedScaledRow,cuspCoordinateLift_positive (3*v) _ hp]
  cases side
  · simpa [ramifiedCuspRoot,ramifiedOmegaUnit_val] using ramifiedSource_zero_mode10 (3*v) hp
  · simpa [ramifiedCuspRoot,Units.val_pow_eq_pow_val,ramifiedOmegaUnit_val] using ramifiedSource_zero_mode19 (3*v) hp
lemma ramifiedScaledRow_fourier (side:Bool) (v:ℝ) (hv:0<v) (h:Eis) :
    (∫z in periodDomain,ramifiedScaledRow side v z*ShortDraftTrace.breveE (-cuspFrequency h*z))=
      ((9*Real.sqrt 3/2:ℝ):ℂ)*(if h=0 then 0 else ramifiedBesselValue side h*(v:ℂ)*
        schlafliBesselK (1/3) (4*Real.pi*‖cuspFrequency h‖*v)) := by
  by_cases hh:h=0
  · subst h
    simp only [cuspFrequency,map_zero,zero_div,neg_zero,zero_mul,AddChar.map_zero_eq_one,
      mul_one]
    simpa only [ite_true,mul_zero] using ramifiedScaledRow_zero side v hv
  have hp:0<3*v:=by positivity
  rw [if_neg hh]
  simp only [ramifiedScaledRow,cuspCoordinateLift_positive (3*v) _ hp]
  by_cases hf:(3:Eis)∣h-onceCuspScale (ramifiedCuspScaleUnit side)
  · rw [ramifiedSource_scaled_fourier_active side h hf (3*v) hp,
      ramifiedSource_fourier_all_heights side h hf (3*v) hp,
      ramifiedBesselValue,dif_pos hf,mul_assoc,ramified_kernel_scaled_bessel h hh v hv]
    field_simp [cusp_volume_ne_zero]

  · rw [ramifiedSource_scaled_fourier_off_support side h hf (3*v) hp,
      ramifiedBesselValue,dif_neg hf]
    ring
lemma ramifiedBesselValue_subexponential (side:Bool) (ε:ℝ) (hε:0<ε) :
    ∃C:ℝ,0≤C∧∀h:Eis,h≠0→‖ramifiedBesselValue side h‖≤C*Real.exp (ε*‖cuspFrequency h‖) := by
  apply continuous_fourier_bessel_subexponential (ramifiedScaledRow side) (ramifiedBesselValue side)
    (ramifiedScaledRow_continuous side) _ ε hε
  intro v hv h hh
  simpa only [if_neg hh,mul_assoc] using ramifiedScaledRow_fourier side v hv h
def ramifiedBesselCoefficients (side:Bool) :SubexponentialBesselCoefficients where
  value:=ramifiedBesselValue side
  growth:=ramifiedBesselValue_subexponential side
end
local notation "Eis" => ActualEisensteinCubic.O
def ramifiedCuspBesselTerm (side:Bool) (h:Eis) (v:ℝ) (z:ℂ) :ℂ:=
  (if h=0 then 0 else ramifiedBesselValue side h*((v/3:ℝ):ℂ)*
    schlafliBesselK (1/3) (4*Real.pi*‖cuspFrequency h‖*(v/3)))*
      ShortDraftTrace.breveE (ninthCuspFrequency h*z)
end
open Filter MeasureTheory
open scoped BigOperators Classical Topology MatrixGroups Pointwise Manifold ContDiff ENNReal InnerProductSpace
open Finset AddChar MulChar EisensteinEmbedding
def coverDirichletPair (F G : EuclideanSpatial→ℂ) (p : EuclideanSpatial) : ℂ :=
  inner ℂ (coverGradientAt F p) (coverGradientAt G p)
end CubicEisenstein
end
end OAI


