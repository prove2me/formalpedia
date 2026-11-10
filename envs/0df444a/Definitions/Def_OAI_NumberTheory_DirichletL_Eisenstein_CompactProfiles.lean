-- Prove2me | Definitions.Def_OAI_NumberTheory_DirichletL_Eisenstein_CompactProfiles
-- name    : OAI_NumberTheory_DirichletL_Eisenstein_CompactProfiles
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-09T06:20:10.583435+00:00
-- url     : https://prove2.me/theorems/326de7ba-2d83-445c-884c-b307c3abd13a
-- title:
--   Compact Profiles
-- statement:
--   Definitions and structural lemmas for Compact Profiles, from LW56e2 and the credited OpenAI and dependency authors's pinned QRH LW56e2 refinement development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/Eisenstein/CompactProfiles.lean

import Definitions.Def_OAI_NumberTheory_DirichletL_QuadraticSieve_SelectedExponents
import Theorems.Thm_OAI_ActualEisensteinCubic_principalSexticRow_mk
import Theorems.Thm_OAI_CubicEisenstein_continuous_hyperbolic_action
import Theorems.Thm_OAI_CubicEisenstein_cosetHeight_cosetOf
import Theorems.Thm_OAI_CubicEisenstein_cuspCutoffCorrection_automorphy
import Theorems.Thm_OAI_CubicEisenstein_cuspCutoffCorrection_eq
import Theorems.Thm_OAI_CubicEisenstein_cuspCutoffTerm_summable
import Theorems.Thm_OAI_CubicEisenstein_cuspSeedDefectProfile_continuous
import Theorems.Thm_OAI_CubicEisenstein_cuspSeedDefectProfile_hasCompactSupport
import Theorems.Thm_OAI_CubicEisenstein_cuspTransition_contDiff
import Theorems.Thm_OAI_CubicEisenstein_finiteCubicMultiplier_coe
import Theorems.Thm_OAI_CubicEisenstein_globalKubotaKernel_mem
import Theorems.Thm_OAI_CubicEisenstein_integralComplexMatrix_apply
import Theorems.Thm_OAI_CubicEisenstein_norm_cosetCharacter
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
import Theorems.Thm_OAI_JointLogSeparation_halfNormalization_twist
import Theorems.Thm_OAI_LocalLogFourier_positiveLogProfile_apply
import Theorems.Thm_OAI_QuadraticGaussRay_residueQuotientFour_mk
import Theorems.Thm_OAI_QuadraticInitialBound_annularSieveCutoff_apply
import Theorems.Thm_OAI_QuadraticInitialBound_annularSieveCutoff_zero
import Theorems.Thm_OAI_QuadraticInitialBound_sieveCutoff_apply
import Theorems.Thm_OAI_SecondPassArithmetic_secondSupportTuple_newLabel
import Theorems.Thm_OAI_SecondPassArithmetic_secondSupportTuple_newRow
import Theorems.Thm_OAI_SecondPassIntegration_conjugateProfile_apply
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
namespace CubicEisenstein
section
open Filter MeasureTheory
open scoped BigOperators Classical Topology MatrixGroups Matrix Pointwise ENNReal
lemma cosetHeight_continuous (r : CuspCosets) : Continuous (cosetHeight r) := by
  induction r using Quotient.inductionOn with
  | _ M =>
    have heq : cosetHeight (cosetOf M)=(fun w => hyperbolicHeight (complexMatrix M • w)) :=
      funext (cosetHeight_cosetOf M)
    change Continuous (cosetHeight (cosetOf M))
    rw [heq]
    exact hyperbolicHeight_continuous.comp (continuous_hyperbolic_action _)
lemma cuspCutoffCorrection_measurable (Y : ℝ) (F : ℝ → ℂ) (hF : Measurable F) :
    Measurable (cuspCutoffCorrection Y F) := by
  unfold cuspCutoffCorrection
  apply Measurable.tsum
  intro r
  apply Measurable.ite
  · exact (isOpen_lt continuous_const (cosetHeight_continuous r)).measurableSet
  · exact measurable_const.mul (hF.comp (cosetHeight_continuous r).measurable)
  · exact measurable_const
lemma cuspCutoffCorrection_norm_le (F : ℝ → ℂ) (C : ℝ) (hC : 0≤C)
    (hF : ∀v,‖F v‖≤C) (w : HyperbolicSpace) : ‖cuspCutoffCorrection 1 F w‖≤C := by
  by_cases hh : ∃r : CuspCosets,1<cosetHeight r w
  · obtain ⟨r,hr⟩ := hh
    rw [cuspCutoffCorrection_eq 1 le_rfl F w r hr,norm_mul,norm_inv,
      norm_cosetCharacter,inv_one,one_mul]
    exact hF _
  · have hz : cuspCutoffCorrection 1 F w=0 := by
      unfold cuspCutoffCorrection
      have hz : (fun r => cuspCutoffTerm 1 F r w)=(fun _ : CuspCosets => (0:ℂ)) := by
        funext r
        simp [cuspCutoffTerm,show ¬1<cosetHeight r w from fun h => hh ⟨r,h⟩]
      rw [hz,tsum_zero]
    rw [hz,norm_zero]
    exact hC
lemma smoothCuspSeedDefect_measurable (a b : ℝ) (s : ℂ) (ha : 0<a) (hab : a<b) :
    Measurable (smoothCuspSeedDefect a b s) :=
  cuspCutoffCorrection_measurable 1 _ (cuspSeedDefectProfile_continuous a b s ha hab).measurable
lemma smoothCuspSeedDefect_bounded (a b : ℝ) (s : ℂ) (ha : 0<a) (hab : a<b) :
    ∃C : ℝ, 0≤C ∧ ∀w,‖smoothCuspSeedDefect a b s w‖≤C := by
  obtain ⟨C,hC⟩ := (cuspSeedDefectProfile_hasCompactSupport a b s hab).exists_bound_of_continuous
    (cuspSeedDefectProfile_continuous a b s ha hab)
  refine ⟨max C 0,le_max_right _ _,fun w => ?_⟩
  exact cuspCutoffCorrection_norm_le _ _ (le_max_right _ _) (fun v => (hC v).trans (le_max_left _ _)) w
lemma kernelQuotientDefect_measurable (a b : ℝ) (s : ℂ) (ha : 0<a) (hab : a<b) :
    Measurable (kernelQuotientDefect a b s) :=
  measurable_from_quotient.mpr (smoothCuspSeedDefect_measurable a b s ha hab)
theorem kernelQuotientDefect_memLp (a b : ℝ) (s : ℂ) (ha : 0<a) (hab : a<b) :
    MemLp (kernelQuotientDefect a b s) 2 (integralQuotientVolume globalKubotaKernel) := by
  obtain ⟨C,hC,hbound⟩ := smoothCuspSeedDefect_bounded a b s ha hab
  apply MemLp.of_bound (kernelQuotientDefect_measurable a b s ha hab).aestronglyMeasurable C
  apply Filter.Eventually.of_forall
  intro q
  induction q using Quotient.inductionOn with
  | _ w => exact hbound w
def kernelL2Defect (a b : ℝ) (ha : 0<a) (hab : a<b) (s : ℂ) : KernelQuotientL2 :=
  (kernelQuotientDefect_memLp a b s ha hab).toLp (kernelQuotientDefect a b s)
end
open Filter MeasureTheory
open scoped BigOperators Classical Topology MatrixGroups Pointwise ENNReal
lemma cuspCutoffCorrection_add (F G : ℝ → ℂ) (w : HyperbolicSpace) :
    cuspCutoffCorrection 1 (F+G) w=cuspCutoffCorrection 1 F w+cuspCutoffCorrection 1 G w := by
  unfold cuspCutoffCorrection
  rw [←(cuspCutoffTerm_summable 1 le_rfl F w).tsum_add (cuspCutoffTerm_summable 1 le_rfl G w)]
  apply tsum_congr
  intro r
  simp only [cuspCutoffTerm,Pi.add_apply]
  split_ifs <;> simp [mul_add]
lemma cuspCutoffCorrection_smul (c : ℂ) (F : ℝ → ℂ) (w : HyperbolicSpace) :
    cuspCutoffCorrection 1 (c • F) w=c • cuspCutoffCorrection 1 F w := by
  unfold cuspCutoffCorrection
  rw [smul_eq_mul,←tsum_mul_left]
  apply tsum_congr
  intro r
  simp only [cuspCutoffTerm,Pi.smul_apply,smul_eq_mul]
  split_ifs <;> ring
def compactHeightProfile (a b : ℝ) (hab : a≤b) (F : C(Set.Icc a b,ℂ)) : ℝ → ℂ :=
  (Set.Icc a b).indicator (fun v => F (Set.projIcc a b hab v))
lemma compactHeightProfile_measurable (a b : ℝ) (hab : a≤b) (F : C(Set.Icc a b,ℂ)) :
    Measurable (compactHeightProfile a b hab F) :=
  (F.continuous.comp continuous_projIcc).measurable.indicator measurableSet_Icc
lemma compactHeightProfile_norm_le (a b : ℝ) (hab : a≤b) (F : C(Set.Icc a b,ℂ)) (v : ℝ) :
    ‖compactHeightProfile a b hab F v‖≤‖F‖ := by
  unfold compactHeightProfile
  by_cases hv : v∈Set.Icc a b
  · rw [Set.indicator_of_mem hv]
    exact F.norm_coe_le_norm _
  · rw [Set.indicator_of_notMem hv,norm_zero]
    exact norm_nonneg _
lemma compactHeightProfile_add (a b : ℝ) (hab : a≤b) (F G : C(Set.Icc a b,ℂ)) :
    compactHeightProfile a b hab (F+G)=compactHeightProfile a b hab F+compactHeightProfile a b hab G := by
  funext v
  simp [compactHeightProfile,Set.indicator_add]
lemma compactHeightProfile_smul (a b : ℝ) (hab : a≤b) (c : ℂ) (F : C(Set.Icc a b,ℂ)) :
    compactHeightProfile a b hab (c • F)=c • compactHeightProfile a b hab F := by
  funext v
  by_cases hv : v∈Set.Icc a b <;> simp [compactHeightProfile,hv]
def kernelCompactProfile (a b : ℝ) (hab : a≤b) (F : C(Set.Icc a b,ℂ)) :
    IntegralOrbitQuotient globalKubotaKernel → ℂ :=
  Quotient.lift (cuspCutoffCorrection 1 (compactHeightProfile a b hab F)) (by
    rintro w u ⟨M,hM⟩
    rw [←hM]
    obtain ⟨hM,hchar⟩ := (globalKubotaKernel_mem (M:SL(2,ActualEisensteinCubic.O))).mp M.property
    have he := cuspCutoffCorrection_automorphy 1 le_rfl (compactHeightProfile a b hab F)
      (⟨(M:SL(2,ActualEisensteinCubic.O)),hM⟩ : CubicKubota.levelThree) w
    rw [hchar,one_mul] at he
    exact he.symm)
lemma kernelCompactProfile_measurable (a b : ℝ) (hab : a≤b) (F : C(Set.Icc a b,ℂ)) :
    Measurable (kernelCompactProfile a b hab F) :=
  measurable_from_quotient.mpr (cuspCutoffCorrection_measurable 1 _
    (compactHeightProfile_measurable a b hab F))
lemma kernelCompactProfile_norm_le (a b : ℝ) (hab : a≤b) (F : C(Set.Icc a b,ℂ))
    (q : IntegralOrbitQuotient globalKubotaKernel) : ‖kernelCompactProfile a b hab F q‖≤‖F‖ := by
  induction q using Quotient.inductionOn with
  | _ w =>
    exact cuspCutoffCorrection_norm_le _ _ (norm_nonneg F)
      (compactHeightProfile_norm_le a b hab F) w
lemma kernelCompactProfile_memLp (a b : ℝ) (hab : a≤b) (F : C(Set.Icc a b,ℂ)) :
    MemLp (kernelCompactProfile a b hab F) 2 (integralQuotientVolume globalKubotaKernel) :=
  MemLp.of_bound (kernelCompactProfile_measurable a b hab F).aestronglyMeasurable ‖F‖
    (Filter.Eventually.of_forall (kernelCompactProfile_norm_le a b hab F))
lemma kernelCompactProfile_add (a b : ℝ) (hab : a≤b) (F G : C(Set.Icc a b,ℂ)) :
    kernelCompactProfile a b hab (F+G)=kernelCompactProfile a b hab F+kernelCompactProfile a b hab G := by
  funext q
  induction q using Quotient.inductionOn with
  | _ w =>
    change cuspCutoffCorrection 1 _ w=_
    rw [compactHeightProfile_add,cuspCutoffCorrection_add]
    rfl
lemma kernelCompactProfile_smul (a b : ℝ) (hab : a≤b) (c : ℂ) (F : C(Set.Icc a b,ℂ)) :
    kernelCompactProfile a b hab (c • F)=c • kernelCompactProfile a b hab F := by
  funext q
  induction q using Quotient.inductionOn with
  | _ w =>
    change cuspCutoffCorrection 1 _ w=_
    rw [compactHeightProfile_smul,cuspCutoffCorrection_smul]
    rfl
def compactProfileL2Linear (a b : ℝ) (hab : a≤b) : C(Set.Icc a b,ℂ) →ₗ[ℂ] KernelQuotientL2 where
  toFun F := (kernelCompactProfile_memLp a b hab F).toLp (kernelCompactProfile a b hab F)
  map_add' F G := by
    apply Lp.ext
    grw [MemLp.coeFn_toLp,Lp.coeFn_add,MemLp.coeFn_toLp,MemLp.coeFn_toLp]
    rw [kernelCompactProfile_add]
  map_smul' c F := by
    apply Lp.ext
    grw [MemLp.coeFn_toLp,Lp.coeFn_smul,MemLp.coeFn_toLp]
    rw [kernelCompactProfile_smul]
    exact Filter.Eventually.of_forall (fun _ => rfl)
lemma compactProfileL2Linear_bound (a b : ℝ) (hab : a≤b) (F : C(Set.Icc a b,ℂ)) :
    ‖compactProfileL2Linear a b hab F‖≤
      (measureUnivNNReal (integralQuotientVolume globalKubotaKernel) : ℝ)^((2:ℝ)⁻¹)*‖F‖ := by
  apply Lp.norm_le_of_ae_bound (norm_nonneg F)
  filter_upwards [MemLp.coeFn_toLp (kernelCompactProfile_memLp a b hab F)] with q hq
  change ‖((kernelCompactProfile_memLp a b hab F).toLp (kernelCompactProfile a b hab F)) q‖≤‖F‖
  rw [hq]
  exact kernelCompactProfile_norm_le a b hab F q
def compactProfileL2 (a b : ℝ) (hab : a≤b) : C(Set.Icc a b,ℂ) →L[ℂ] KernelQuotientL2 :=
  (compactProfileL2Linear a b hab).mkContinuous
    ((measureUnivNNReal (integralQuotientVolume globalKubotaKernel) : ℝ)^((2:ℝ)⁻¹))
    (compactProfileL2Linear_bound a b hab)
def compactLogProfile (a b : ℝ) (ha : 0<a) : C(Set.Icc a b,ℂ) :=
  ⟨fun v => (Real.log (v:ℝ):ℂ),Complex.continuous_ofReal.comp
    (continuous_subtype_val.log (fun v => (ha.trans_le v.2.1).ne'))⟩
def compactDefectSecond (a b : ℝ) : C(Set.Icc a b,ℂ) where
  toFun v := (v:ℂ)^2*((deriv (deriv (cuspTransition a b)) (v:ℝ):ℝ):ℂ)
  continuous_toFun := by
    have hd := (contDiff_infty_iff_deriv.mp (cuspTransition_contDiff a b)).2
    have hdd := (contDiff_infty_iff_deriv.mp hd).2
    exact (Complex.continuous_ofReal.comp continuous_subtype_val).pow 2 |>.mul
      (Complex.continuous_ofReal.comp (hdd.continuous.comp continuous_subtype_val))
def compactDefectFirst (a b : ℝ) : C(Set.Icc a b,ℂ) where
  toFun v := (v:ℂ)*((deriv (cuspTransition a b) (v:ℝ):ℝ):ℂ)
  continuous_toFun := by
    have hd := (contDiff_infty_iff_deriv.mp (cuspTransition_contDiff a b)).2
    exact (Complex.continuous_ofReal.comp continuous_subtype_val).mul
      (Complex.continuous_ofReal.comp (hd.continuous.comp continuous_subtype_val))
def compactDefectProfile (a b : ℝ) (ha : 0<a) (s : ℂ) : C(Set.Icc a b,ℂ) :=
  NormedSpace.exp (s • compactLogProfile a b ha)*
    (compactDefectSecond a b+(2*s-1) • compactDefectFirst a b)
end CubicEisenstein
open scoped BigOperators Classical SchwartzMap ContDiff
namespace SecondPassIntegration
open ActualEisensteinCubic JointLogSeparation FirstPassCubeLabels SecondPassArithmetic
end SecondPassIntegration
namespace SecondPassArithmetic
section
open ActualEisensteinCubic
open FirstPassCubeLabels (primeProductNorm normalizedColumn columnLog b0Label)
open JointLogSeparation (halfNormalizationCLM)
open SecondPassFiber (newRow)
section
variable {ι : Type*} [DecidableEq ι]
  (p : ι → OAI.SecondPassArithmetic.O) (hp : ∀ i,p i ≠ 0) [∀ i,(Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i,lambda ∉ Ideal.span {p i})
def globalSecondLiteralTerm (F : Finset ι) (Ψ : O →* ℂ) (m : O) (ray : SecondRayIndex)
    (g₁ g₂ W : 𝓢(ℝ,ℂ)) (ell Y : ℝ) (side : Bool) (x : GlobalSecondData ι) : ℂ :=
  let X := globalFirstColumnScale p ell x side/primeProductNorm p x.firstCommon
  let m' := m*b0Label p x.cube.support (fun i => x.cube.leftExponent i+x.cube.rightExponent i) x.cube.leftBit x.cube.rightBit
  let c := secondBaseLabel p x.cube.support x.common x.cube.leftExponent x.cube.rightExponent x.cube.leftBit x.cube.rightBit
  let d := primeSubsetGenerator (fun i => Ideal.span {p i}) x.firstDivisor
  (primeProductNorm p x.firstCommon : ℂ)⁻¹ *
    secondExpansionSource p hp hcop hg (globalSecondRawPool F x) Ψ m' c d ray {x.source}
      (fun A => normalizedColumn p (fun S => g₁ (columnLog p X S)) A)
      (fun A => normalizedColumn p (fun S => g₂ (columnLog p X S)) A) W Y
end
end
open ActualEisensteinCubic
open FirstPassCubeLabels (primeProductNorm normalizedColumn columnLog b0Label)
open JointLogSeparation (halfNormalizationCLM frequencyTwist frequencyTwist_apply halfNormalization_twist)
open SecondPassFiber (newRow)
end SecondPassArithmetic
end
end OAI


