-- Prove2me | Definitions.Def_OAI_NumberTheory_DirichletL_QuadraticSieve_SelectedExponents
-- name    : OAI_NumberTheory_DirichletL_QuadraticSieve_SelectedExponents
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-09T06:17:22.8748+00:00
-- url     : https://prove2.me/theorems/6d52de14-032c-451b-8e3a-69a62c606ec1
-- title:
--   Selected Exponents
-- statement:
--   Definitions and structural lemmas for Selected Exponents, from LW56e2 and the credited OpenAI and dependency authors's pinned QRH LW56e2 refinement development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/QuadraticSieve/SelectedExponents.lean

import Definitions.Def_OAI_NumberTheory_DirichletL_QuadraticSieve_AnnularLifting
import Definitions.Def_OAI_NumberTheory_DirichletL_QuadraticSieve_PoissonConstants
import Theorems.Thm_OAI_ActualEisensteinCubic_principalSexticRow_mk
import Theorems.Thm_OAI_CubicEisenstein_complexBottomRow_ne_zero
import Theorems.Thm_OAI_CubicEisenstein_continuous_complexSL_coe
import Theorems.Thm_OAI_CubicEisenstein_continuous_hyperbolic_action
import Theorems.Thm_OAI_CubicEisenstein_continuous_upperCoordinates
import Theorems.Thm_OAI_CubicEisenstein_cusp_height_volume
import Theorems.Thm_OAI_CubicEisenstein_euclideanToHyperbolic_measurable
import Theorems.Thm_OAI_CubicEisenstein_euclideanToHyperbolic_positive
import Theorems.Thm_OAI_CubicEisenstein_finiteCubicMultiplier_coe
import Theorems.Thm_OAI_CubicEisenstein_finiteIndex_ford_cover
import Theorems.Thm_OAI_CubicEisenstein_globalKubotaKernel_finiteIndex
import Theorems.Thm_OAI_CubicEisenstein_globalKubotaKernel_le_levelThree
import Theorems.Thm_OAI_CubicEisenstein_hyperbolicEuclideanVolume_ae_positive
import Theorems.Thm_OAI_CubicEisenstein_hyperbolicFundamentalSet_isFundamentalDomain
import Theorems.Thm_OAI_CubicEisenstein_hyperbolicHeight_pos
import Theorems.Thm_OAI_CubicEisenstein_hyperbolicHeight_upperPoint
import Theorems.Thm_OAI_CubicEisenstein_hyperbolicVolume_invariant
import Theorems.Thm_OAI_CubicEisenstein_integralComplexMatrix_apply
import Theorems.Thm_OAI_CubicEisenstein_matrixCross_upperSection
import Theorems.Thm_OAI_CubicEisenstein_measurable_integralOrbitProjection
import Theorems.Thm_OAI_CubicEisenstein_quadraticHeightDenominator_continuous
import Theorems.Thm_OAI_CubicEisenstein_rowEnergy_pos
import Theorems.Thm_OAI_CubicEisenstein_spatialTriple_one
import Theorems.Thm_OAI_CubicEisenstein_spatialTriple_two
import Theorems.Thm_OAI_CubicEisenstein_spatialTriple_zero
import Theorems.Thm_OAI_CubicEisenstein_upperPoint_surjective
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
import Theorems.Thm_OAI_SecondPassArithmetic_secondSupportTuple_newLabel
import Theorems.Thm_OAI_SecondPassArithmetic_secondSupportTuple_newRow
import Theorems.Thm_OAI_SecondPassIntegration_conjugateProfile_apply
attribute [local fun_prop] OAI.CubicEisenstein.quadraticHeightDenominator_continuous
attribute [local simp] OAI.ActualEisensteinCubic.principalSexticRow_mk
attribute [local simp] OAI.CubicEisenstein.finiteCubicMultiplier_coe
attribute [local simp] OAI.CubicEisenstein.integralComplexMatrix_apply
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
open scoped BigOperators Classical SchwartzMap
namespace CanonicalQuadraticSieve
open ActualEisensteinCubic IdealCoprimeSieveOperator
end CanonicalQuadraticSieve
open Filter MeasureTheory
open scoped BigOperators Classical Topology MatrixGroups Matrix Pointwise
namespace CubicEisenstein
lemma hyperbolicHeight_continuous : Continuous hyperbolicHeight := by
  apply Continuous.quotient_lift
  have he (i j : Fin 2) : Continuous (fun g : SL(2,ℂ) => g i j) :=
    (continuous_apply j).comp ((continuous_apply i).comp continuous_complexSL_coe)
  apply Continuous.inv₀
  · exact ((he 1 0).norm.pow 2).add ((he 1 1).norm.pow 2)
  · intro g
    exact (rowEnergy_pos _ (complexBottomRow_ne_zero g)).ne'
lemma matrixCross_eq_gram (g : SL(2,ℂ)) : matrixCross g=matrixGram g 0 1 := by
  simp only [matrixCross,matrixGram,Matrix.mul_apply,Fin.sum_univ_two,Matrix.star_apply]
lemma hyperbolicGram_upperPoint (z : ℂ) (v : ℝ) (hv : 0<v) :
    hyperbolicGram (upperPoint z v hv) 0 1=z/(v:ℂ) := by
  change matrixGram (upperSection z v hv) 0 1=_
  rw [←matrixCross_eq_gram]
  have hh := matrixCross_upperSection (1:SL(2,ℂ)) z v hv
  simpa [Matrix.one_apply] using hh
def hyperbolicHorizontal (w : HyperbolicSpace) : ℂ :=
  hyperbolicGram w 0 1*(hyperbolicHeight w:ℂ)
lemma hyperbolicHorizontal_continuous : Continuous hyperbolicHorizontal := by
  unfold hyperbolicHorizontal
  exact ((continuous_apply 1).comp ((continuous_apply 0).comp hyperbolicGram_continuous)).mul
    (Complex.continuous_ofReal.comp hyperbolicHeight_continuous)
@[simp] lemma hyperbolicHorizontal_upperPoint (z : ℂ) (v : ℝ) (hv : 0<v) :
    hyperbolicHorizontal (upperPoint z v hv)=z := by
  simp only [hyperbolicHorizontal,hyperbolicGram_upperPoint,hyperbolicHeight_upperPoint]
  exact div_mul_cancel₀ z (Complex.ofReal_ne_zero.mpr hv.ne')
def hyperbolicCoordinates (w : HyperbolicSpace) : UpperCoordinates :=
  ⟨(hyperbolicHorizontal w,hyperbolicHeight w),hyperbolicHeight_pos w⟩
lemma hyperbolicCoordinates_continuous : Continuous hyperbolicCoordinates :=
  (hyperbolicHorizontal_continuous.prodMk hyperbolicHeight_continuous).subtype_mk _
lemma upperCoordinates_left_inverse : Function.LeftInverse hyperbolicCoordinates
    (fun p : UpperCoordinates => upperPoint p.1.1 p.1.2 p.2) := by
  intro p
  apply Subtype.ext
  exact Prod.ext (hyperbolicHorizontal_upperPoint _ _ _) (hyperbolicHeight_upperPoint _ _ _)
lemma upperCoordinates_right_inverse : Function.RightInverse hyperbolicCoordinates
    (fun p : UpperCoordinates => upperPoint p.1.1 p.1.2 p.2) := by
  intro w
  obtain ⟨z,v,hv,rfl⟩ := upperPoint_surjective w
  exact congrArg (fun p : UpperCoordinates => upperPoint p.1.1 p.1.2 p.2)
    (upperCoordinates_left_inverse ⟨(z,v),hv⟩)
def upperCoordinatesHomeomorph : UpperCoordinates ≃ₜ HyperbolicSpace where
  toFun p := upperPoint p.1.1 p.1.2 p.2
  invFun := hyperbolicCoordinates
  left_inv := upperCoordinates_left_inverse
  right_inv := upperCoordinates_right_inverse
  continuous_toFun := continuous_upperCoordinates
  continuous_invFun := hyperbolicCoordinates_continuous
lemma fundamentalSet_measure_le_cover (H : Subgroup (SL(2,ActualEisensteinCubic.O)))
    (hH : H≤CubicKubota.levelThree) (B : Set HyperbolicSpace)
    (hB : ∀w,∃M:H,M • w∈B) :
    hyperbolicVolume (hyperbolicFundamentalSet H)≤hyperbolicVolume B := by
  rw [(hyperbolicFundamentalSet_isFundamentalDomain H hH).measure_eq_tsum B]
  apply le_trans (measure_mono ?_) (measure_iUnion_le _)
  intro w hw
  obtain ⟨M,hM⟩ := hB w
  apply Set.mem_iUnion.mpr
  refine ⟨M⁻¹,?_,hw⟩
  exact ⟨M • w,hM,inv_smul_smul M w⟩
open Filter MeasureTheory
open scoped BigOperators Classical Topology MatrixGroups Matrix Pointwise ENNReal
def spatialHeightSplit : EuclideanSpatial ≃ᵐ ℝ × (Fin 2 → ℝ) :=
  (MeasurableEquiv.toLp 2 (Fin 3 → ℝ)).symm.trans
    (MeasurableEquiv.piFinSuccAbove (fun _ : Fin 3 => ℝ) 2)
lemma spatialHeightSplit_preserves_volume : MeasurePreserving spatialHeightSplit volume volume :=
  (volume_preserving_piFinSuccAbove (fun _ : Fin 3 => ℝ) 2).comp
    (EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp (Fin 3))
def horizontalUnitBox : Set (Fin 2 → ℝ) := Set.pi Set.univ (fun _ => Set.Icc (-1) 1)
lemma horizontalUnitBox_measurable : MeasurableSet horizontalUnitBox :=
  MeasurableSet.pi (Set.to_countable _) (fun _ _ => measurableSet_Icc)
lemma horizontalUnitBox_volume : volume horizontalUnitBox=4 := by
  rw [horizontalUnitBox,volume_pi_pi]
  norm_num
def euclideanCuspBox (a : ℝ) : Set EuclideanSpatial :=
  spatialHeightSplit ⁻¹' (Set.Ioi a ×ˢ horizontalUnitBox)
lemma euclideanCuspBox_measurable (a : ℝ) : MeasurableSet (euclideanCuspBox a) :=
  spatialHeightSplit.measurable (measurableSet_Ioi.prod horizontalUnitBox_measurable)
lemma euclideanCuspBox_positive (a : ℝ) (ha : 0≤a) : euclideanCuspBox a ⊆ euclideanUpperHalf := by
  intro p hp
  exact ha.trans_lt hp.1
theorem euclideanCuspBox_volume (a : ℝ) (ha : 0<a) :
    hyperbolicEuclideanVolume (euclideanCuspBox a)=4*ENNReal.ofReal (1/(2*a^2)) := by
  unfold hyperbolicEuclideanVolume
  rw [withDensity_apply _ (euclideanCuspBox_measurable a),
    Measure.restrict_restrict (euclideanCuspBox_measurable a),
    Set.inter_eq_left.mpr (euclideanCuspBox_positive a ha.le)]
  change (∫⁻p in spatialHeightSplit ⁻¹' (Set.Ioi a ×ˢ horizontalUnitBox),
    ENNReal.ofReal (((spatialHeightSplit p).1^3)⁻¹))=_
  rw [spatialHeightSplit_preserves_volume.setLIntegral_comp_preimage
    (f := fun q : ℝ × (Fin 2 → ℝ) => ENNReal.ofReal ((q.1^3)⁻¹))
    (measurableSet_Ioi.prod horizontalUnitBox_measurable) (by fun_prop)]
  change (∫⁻q : ℝ × (Fin 2 → ℝ) in Set.Ioi a ×ˢ horizontalUnitBox,
    ENNReal.ofReal ((q.1^3)⁻¹) ∂((volume : Measure ℝ).prod volume))=_
  rw [setLIntegral_prod _ (by fun_prop)]
  simp only [lintegral_const,Measure.restrict_apply MeasurableSet.univ,Set.univ_inter,
    horizontalUnitBox_volume]
  rw [lintegral_mul_const _ (by fun_prop),cusp_height_volume a ha]
  exact mul_comm _ _
local notation "O" => ActualEisensteinCubic.O
instance fullSLMeasurableAction : MeasurableConstSMul (SL(2,ℂ)) HyperbolicSpace :=
  ⟨fun g => (continuous_hyperbolic_action g).measurable⟩
instance fullSLVolumeInvariant : SMulInvariantMeasure (SL(2,ℂ)) HyperbolicSpace hyperbolicVolume where
  measure_preimage_smul g s hs := by
    have he := congrArg (fun ν : Measure HyperbolicSpace => ν s) (hyperbolicVolume_invariant g)
    simpa only [Measure.map_apply (continuous_hyperbolic_action g).measurable hs] using he
def hyperbolicCuspBox (a : ℝ) : Set HyperbolicSpace :=
  {w | ‖hyperbolicHorizontal w‖≤1 ∧ a<hyperbolicHeight w}
lemma hyperbolicCuspBox_measurable (a : ℝ) : MeasurableSet (hyperbolicCuspBox a) :=
  (isClosed_le hyperbolicHorizontal_continuous.norm continuous_const).measurableSet.inter
    (isOpen_lt continuous_const hyperbolicHeight_continuous).measurableSet
lemma hyperbolicCuspBox_volume_le (a : ℝ) (ha : 0<a) :
    hyperbolicVolume (hyperbolicCuspBox a)≤4*ENNReal.ofReal (1/(2*a^2)) := by
  rw [hyperbolicVolume,Measure.map_apply euclideanToHyperbolic_measurable
    (hyperbolicCuspBox_measurable a),←euclideanCuspBox_volume a ha]
  apply measure_mono_ae
  filter_upwards [hyperbolicEuclideanVolume_ae_positive] with p hp hB
  change euclideanToHyperbolic p ∈ hyperbolicCuspBox a at hB
  rw [euclideanToHyperbolic_positive p hp] at hB
  change ‖hyperbolicHorizontal (upperPoint _ _ hp)‖≤1 ∧ a<hyperbolicHeight (upperPoint _ _ hp) at hB
  rw [hyperbolicHorizontal_upperPoint,hyperbolicHeight_upperPoint] at hB
  refine ⟨hB.2,?_⟩
  intro j hj
  fin_cases j
  · change -1≤p 0 ∧ p 0≤1
    have hh := (Complex.abs_re_le_norm ((p 0:ℂ)+Complex.I*(p 1:ℂ))).trans hB.1
    simpa using abs_le.mp hh
  · change -1≤p 1 ∧ p 1≤1
    have hh := (Complex.abs_im_le_norm ((p 0:ℂ)+Complex.I*(p 1:ℂ))).trans hB.1
    simpa using abs_le.mp hh
lemma hyperbolicCuspBox_volume_lt_top (a : ℝ) (ha : 0<a) :
    hyperbolicVolume (hyperbolicCuspBox a)<⊤ :=
  (hyperbolicCuspBox_volume_le a ha).trans_lt (ENNReal.mul_lt_top (by norm_num) ENNReal.ofReal_lt_top)
theorem hyperbolicFundamentalSet_volume_lt_top (H : Subgroup (SL(2,O)))
    (hH : H≤CubicKubota.levelThree) [H.FiniteIndex] :
    hyperbolicVolume (hyperbolicFundamentalSet H)<⊤ := by
  obtain ⟨S,hS⟩ := finiteIndex_ford_cover H
  let a : ℝ := Real.sqrt (2/3)/2
  have ha : 0<a := by dsimp [a]; positivity
  let B : Set HyperbolicSpace := ⋃r∈S,integralComplexMatrix r⁻¹ • hyperbolicCuspBox a
  have hcover : ∀w,∃M:H,M • w∈B := by
    intro w
    obtain ⟨M,r,hr,z,v,hv,hM,hz,hfloor⟩ := hS w
    refine ⟨M,?_⟩
    rw [integralSubgroup_smul,hM]
    apply Set.mem_iUnion.mpr
    refine ⟨r,Set.mem_iUnion.mpr ⟨hr,?_⟩⟩
    apply Set.mem_smul_set.mpr
    refine ⟨upperPoint z v hv,?_,rfl⟩
    change ‖hyperbolicHorizontal (upperPoint z v hv)‖≤1 ∧ a<hyperbolicHeight (upperPoint z v hv)
    rw [hyperbolicHorizontal_upperPoint,hyperbolicHeight_upperPoint]
    refine ⟨?_,?_⟩
    · rw [Complex.normSq_eq_norm_sq] at hz
      nlinarith [norm_nonneg z]
    · dsimp [a] at *
      linarith
  apply (fundamentalSet_measure_le_cover H hH B hcover).trans_lt
  apply (measure_biUnion_finset_le S (fun r => integralComplexMatrix r⁻¹ • hyperbolicCuspBox a)).trans_lt
  apply ENNReal.sum_lt_top.mpr
  intro r hr
  rw [measure_smul]
  exact hyperbolicCuspBox_volume_lt_top a ha
lemma integralQuotientVolume_univ (H : Subgroup (SL(2,O))) :
    integralQuotientVolume H Set.univ=hyperbolicVolume (hyperbolicFundamentalSet H) := by
  rw [integralQuotientVolume,Measure.map_apply (measurable_integralOrbitProjection H) MeasurableSet.univ]
  simp
theorem integralQuotientVolume_finite (H : Subgroup (SL(2,O)))
    (hH : H≤CubicKubota.levelThree) [H.FiniteIndex] : IsFiniteMeasure (integralQuotientVolume H) :=
  ⟨by rw [integralQuotientVolume_univ]; exact hyperbolicFundamentalSet_volume_lt_top H hH⟩
instance kernelQuotientVolume_finite : IsFiniteMeasure (integralQuotientVolume globalKubotaKernel) := by
  let : globalKubotaKernel.FiniteIndex := globalKubotaKernel_finiteIndex
  exact integralQuotientVolume_finite globalKubotaKernel globalKubotaKernel_le_levelThree
end CubicEisenstein
namespace CanonicalQuadraticSieve
section
open ActualEisensteinCubic CompletedGauss
end
open ActualEisensteinCubic IdealCoprimeSieveOperator DivisorBlockCauchy
def fixedBadNorm : ℝ := Ideal.absNorm (∏P∈fixedBadPrimes,P)
def fixedCutoffBase : ℝ := max 4 fixedBadNorm
end CanonicalQuadraticSieve
end
end OAI


