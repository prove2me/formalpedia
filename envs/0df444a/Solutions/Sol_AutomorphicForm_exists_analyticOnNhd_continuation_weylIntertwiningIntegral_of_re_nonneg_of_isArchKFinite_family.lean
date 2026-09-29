-- Prove2me | solution 1 for AutomorphicForm.exists_analyticOnNhd_continuation_weylIntertwiningIntegral_of_re_nonneg_of_isArchKFinite_family
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.961684+00:00
-- url     : https://prove2.me/submissions/742acd89-c6f5-5bd1-ae75-d1425b643a61

import Theorems.Thm_AutomorphicForm_exists_flat_isInducedSection_sum_eq_of_differentiable_family
import Theorems.Thm_AutomorphicForm_exists_sum_mul_godementSection_eq_partialEulerProduct_mul_of_flat_family
import Theorems.Thm_AutomorphicForm_exists_entire_eq_godementEisenstein_fe_norm_le_of_mem_schwartzBruhat2
import Theorems.Thm_AutomorphicForm_constantTerm_bruhatEisenstein_eq_section_add_weylIntertwiningIntegral
import Theorems.Thm_AutomorphicForm_weylIntertwiningIntegrand_integrable_of_re_gt_half
import Theorems.Thm_AutomorphicForm_isInducedSection_godementSection_of_forall_coe_eq_ideleNorm
import Theorems.Thm_AutomorphicForm_integrable_and_differentiableAt_and_continuous_godementSection_of_mem_schwartzBruhat2
import Theorems.Thm_NumberField_TateGlobal_exists_analyticOnNhd_mul_partialEulerProduct_eq_one_of_isUnitaryChar_of_isIdeleClassChar
import Theorems.Thm_NumberField_AdeleRing_distribHaarChar_algebraMap
import Theorems.Thm_Complex_differentiableOn_integral_of_continuousOn_of_forall_differentiableOn
import Theorems.Thm_AutomorphicForm_continuous_unipotentGL2
import Definitions.Def_AutomorphicForm_InducedSection
import Definitions.Def_AutomorphicForm_EtaFamily
import Definitions.Def_AutomorphicForm_WeylIntertwining
import Definitions.Def_AutomorphicForm_SmoothAutomorphicFnAt
import Definitions.Def_AutomorphicForm_ArchKFinite
import Definitions.Def_AutomorphicForm_GodementSection
import Definitions.Def_AutomorphicForm_ConstantTerm
import Definitions.Def_NumberField_AdelicHaar
import Definitions.Def_NumberField_AdelicBox
import Definitions.Def_NumberField_NormPowChar
import Definitions.Def_NumberField_AdelicTraceFin
import Mathlib.MeasureTheory.Measure.Haar.DistribChar
import Mathlib.Analysis.Analytic.Constructions
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Topology.UrysohnsLemma
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_exists_analyticOnNhd_continuation_weylIntertwiningIntegral_of_re_nonneg_of_isArchKFinite_family
p2m_attr_erase "instance" "instCountableOfNumberField_definitions HeckePair.instSMulCommClassSubtypeForallMemSubmoduleHeckeAlgebra HeckePair.instAlgebraSubtypeForallMemSubmoduleHeckeAlgebra HeckePair.instOneSubtypeForallMemSubmoduleHeckeAlgebra HeckePair.instIsScalarTowerSubtypeForallMemSubmoduleHeckeAlgebra HeckePair.instRingSubtypeForallMemSubmoduleHeckeAlgebra HeckePair.instMulSubtypeForallMemSubmoduleHeckeAlgebra FixedPoints.instMulActionElemFixedPointsOfSMulCommClass_definitions FixedPoints.module FixedPoints.instSMulElemFixedPointsOfSMulCommClass_definitions FixedPoints.instAddCommMonoidElemFixedPoints_definitions AutomorphicForm.compactSpace_maximalCompactAway AutomorphicForm.compactSpace_adelicMaximalCompact AutomorphicForm.isProbabilityMeasure_maximalCompactHaar AutomorphicForm.isHaarMeasure_maximalCompactHaar AutomorphicForm.compactSpace_maximalCompactAt AutomorphicForm.isProbabilityMeasure_maximalCompactAwayHaar AutomorphicForm.isHaarMeasure_maximalCompactAwayHaar AutomorphicForm.isProbabilityMeasure_maximalCompactAtHaar AutomorphicForm.isHaarMeasure_maximalCompactAtHaar instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions Submodule.instIsTopologicalModuleSubtypeMem Pi.instTopologicalModule IsTopologicalModule.toContinuousSMul IsTopologicalModule.toContinuousAdd instMeasurableSpaceRestrictedProduct_definitions instBorelSpaceRestrictedProduct_definitions"
p2m_attr_erase "instance" "MeasureTheory.instMeasurableNegSubtypeMemAddSubgroup_definitions MeasureTheory.instMeasurableMulSubtypeMemSubgroup_definitions MeasureTheory.instMeasurableMul₂SubtypeMemSubgroup_definitions MeasureTheory.instMeasurableMul₂SubtypeMemAddSubgroup_definitions MeasureTheory.instMeasurableAddSubtypeMemAddSubgroup_definitions MeasureTheory.instMeasurableInvSubtypeMemSubgroup_definitions"
p2m_attr_erase "simp" "AutomorphicForm.SiegelCoordinates.upperUnit_apply_zero_zero AutomorphicForm.SiegelCoordinates.upperUnit_apply_one_zero AutomorphicForm.SiegelCoordinates.upperUnit_apply_one_one AutomorphicForm.SiegelCoordinates.upperUnit_apply_zero_one AutomorphicForm.fnTwist_zero AutomorphicForm.fnTwist_apply LocalGL2.coe_localRepSome LocalGL2.coe_diagPi LocalGL2.coe_localRepInf LocalGL2.coe_localRepSome_inv LocalGL2.coe_unipotentInt LocalGL2.coe_weylInt LocalGL2.coe_diagPi_inv LocalGL2.transposeGL_val LocalGL2.transposeGL_one HeckePair.convTerm_mk HeckePair.coe_apply_add HeckePair.coe_apply_smul FixedPoints.coe_zero FixedPoints.coe_smul FixedPoints.coe_add LocalGL2.swapUnit_val LanglandsTunnell.TateLocal.charExt_coe_units LanglandsTunnell.TateLocal.modulus_one LanglandsTunnell.TateLocal.modulus_zero LanglandsTunnell.TateLocal.modulus_coe_units LanglandsTunnell.TateLocal.charExt_zero LanglandsTunnell.TateLocal.conductorExponentAt_one LanglandsTunnell.RankinSelberg.rs22GlobalIntegral_zero_left LanglandsTunnell.RankinSelberg.rs22LocalIntegral_zero_left LanglandsTunnell.RankinSelberg.rs22GlobalIntegral_zero_right M4aHerbrand.IdeleGaloisDescent.mk.sizeOf_spec M4aHerbrand.IdeleGaloisDescent.mk.injEq AutomorphicForm.rightTranslationEmbed_smul_apply AutomorphicForm.CuspidalityNotion.mk.injEq AutomorphicForm.HeckeEigensystem.twist_b AutomorphicForm.satakePow_zero AutomorphicForm.HeckeEigensystem.twist_a AutomorphicForm.HeckeEigensystem.mk.injEq AutomorphicForm.HeckeEigensystem.mk.sizeOf_spec"
p2m_attr_erase "simp" "AutomorphicForm.DescentPackage.mk.injEq AutomorphicForm.DescentPackage.mk.sizeOf_spec AutomorphicForm.CuspidalityNotion.mk.sizeOf_spec AutomorphicForm.satakePow_one ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff"
p2m_attr_erase "simp" "RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply ContinuousAddEquiv.preimage_mulLeft_smul IsModuleTopology.continuousLinearEquiv_apply AlgEquiv.extendScalars_symm_apply IsModuleTopology.Module.Basis.equivFun_homeo_symm_apply IsModuleTopology.Module.Basis.equivFun_homeo_apply IsModuleTopology.continuousAlgEquivOfIsBiscalar_apply AlgEquiv.extendScalars_apply IsModuleTopology.continuousLinearEquiv_symm_apply AutomorphicForm.classSq_apply AutomorphicForm.classRepEmbedding_one AutomorphicForm.finIdeleExponentAt_one AutomorphicForm.classRepFinIdele_one AutomorphicForm.productionPinsGeneralOf_D AutomorphicForm.productionPinsGeneral_D AutomorphicForm.productionPinsGeneralOf_μ AutomorphicForm.productionPinsGeneralOf_U AutomorphicForm.productionPinsCompact_ν AutomorphicForm.productionPinsCompact_U AutomorphicForm.productionPinsCompact_D AutomorphicForm.productionPinsCompact_nS AutomorphicForm.productionPinsCompact_gen AutomorphicForm.productionPinsCompact_Z AutomorphicForm.productionPinsCompact_mS AutomorphicForm.productionPinsCompact_μ AutomorphicForm.productionPins_nS AutomorphicForm.productionPins_mS AutomorphicForm.productionPins_ν AutomorphicForm.productionPins_Z AutomorphicForm.productionPins_U AutomorphicForm.productionPins_μ AutomorphicForm.productionPins_gen AutomorphicForm.productionPins_D AutomorphicForm.HeckeEigensystem.ofRawCentral_toRawCentral AutomorphicForm.HeckeEigensystem.toRawCentral_ofRawCentral AutomorphicForm.HeckeEigensystem.ofRawCentral_a AutomorphicForm.HeckeEigensystem.ofRawCentral_b AutomorphicForm.HeckeEigensystem.toRawCentral_level AutomorphicForm.HeckeEigensystem.toRawCentral_a"
p2m_attr_erase "simp" "AutomorphicForm.HeckeEigensystem.ofRawCentral_level AutomorphicForm.HeckeEigensystem.toRawCentral_b AutomorphicForm.SmoothCuspRealizationAt.mk.injEq AutomorphicForm.degenerateEigensystem_a AutomorphicForm.SmoothCuspRealizationAt.mk.sizeOf_spec AutomorphicForm.degenerateEigensystem_b AutomorphicForm.HeckeEigensystem.map_b AutomorphicForm.HeckeEigensystem.map_a AutomorphicForm.HeckeEigensystem.map_level LanglandsTunnell.ArchPlace.complexTestFun_zero_apply LanglandsTunnell.ArchPlace.norm_anglePhase LanglandsTunnell.ArchPlace.realTestFun_zero_apply NumberField.AdeleRing.val_finiteUnitsComponent IsDedekindDomain.FiniteAdeleRing.val_unitsComponent NumberField.AdeleRing.val_finitePartUnits NumberField.AdeleRing.val_infiniteUnitsComponent"

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Topology Set
open NumberField NumberField.AdelicHaar NumberField.AdelicBox NumberField.AdelicFourier NumberField.AdelicLevel
open NumberField.TateGlobal IsDedekindDomain
open AutomorphicForm AutomorphicForm.WindowedSiegel
open scoped NNReal ENNReal

namespace R4Mcont

attribute [local instance] NumberField.AdelicHaar.adeleBorel NumberField.AdelicHaar.borelSpace_adeleBorel
attribute [local instance] NumberField.AdelicHaar.isAddHaarMeasure_adelicAddHaar

section ConstantTerm

variable (F : Type) [Field F] [NumberField F]

scoped instance isProbabilityMeasure_cond_adelicBox' :
    IsProbabilityMeasure (ProbabilityTheory.cond (adelicAddHaar (𝓞 F) F) (adelicBox F)) :=
  isProbabilityMeasure_cond_adelicBox F

variable {F}

theorem analyticOnNhd_constantTerm {O : Set ℂ} (hO : IsOpen O) {Ec : ℂ → AdelicGL2 (𝓞 F) F → ℂ}
    (hEa : ∀ g : AdelicGL2 (𝓞 F) F, AnalyticOnNhd ℂ (fun s => Ec s g) O)
    (hEjc : ContinuousOn (fun p : ℂ × AdelicGL2 (𝓞 F) F => Ec p.1 p.2) (O ×ˢ Set.univ))
    (h : AdelicGL2 (𝓞 F) F) :
    AnalyticOnNhd ℂ (fun s => constantTerm (ProbabilityTheory.cond (adelicAddHaar (𝓞 F) F) (adelicBox F))
      (fun t => unipotentGL2 t) (Ec s) h) O := by
  obtain ⟨Cb, hCb, hboxCb⟩ := exists_isCompact_adelicBox_subset F
  obtain ⟨χ, hχ1, -, hχc, hχ01⟩ :=
    exists_continuous_one_zero_of_isCompact hCb isClosed_empty (Set.disjoint_empty _)
  set ν₀ : Measure (AdeleRing (𝓞 F) F) := ProbabilityTheory.cond (adelicAddHaar (𝓞 F) F) (adelicBox F) with hν₀
  set G : ℂ → AdeleRing (𝓞 F) F → ℂ := fun z t => ((χ t : ℝ) : ℂ) * Ec z (unipotentGL2 t * h) with hG
  have hmap : ContinuousOn (fun p : ℂ × AdeleRing (𝓞 F) F => ((p.1, unipotentGL2 p.2 * h) : ℂ × AdelicGL2 (𝓞 F) F))
      (O ×ˢ Set.univ) :=
    (continuous_fst.prodMk ((AutomorphicForm.continuous_unipotentGL2.comp continuous_snd).mul
      continuous_const)).continuousOn
  have hmaps : Set.MapsTo (fun p : ℂ × AdeleRing (𝓞 F) F => ((p.1, unipotentGL2 p.2 * h) : ℂ × AdelicGL2 (𝓞 F) F))
      (O ×ˢ Set.univ) (O ×ˢ Set.univ) := fun p hp => ⟨hp.1, Set.mem_univ _⟩
  have hEc2 : ContinuousOn (fun p : ℂ × AdeleRing (𝓞 F) F => Ec p.1 (unipotentGL2 p.2 * h)) (O ×ˢ Set.univ) :=
    hEjc.comp hmap hmaps
  have hGc : ContinuousOn (Function.uncurry G) (O ×ˢ Set.univ) := by
    have hχc' : Continuous fun p : ℂ × AdeleRing (𝓞 F) F => ((χ p.2 : ℝ) : ℂ) :=
      Complex.continuous_ofReal.comp (χ.continuous.comp continuous_snd)
    exact hχc'.continuousOn.mul hEc2
  have hGS : ∀ z ∈ O, ∀ a ∉ tsupport χ, G z a = 0 := by
    intro z hz a ha
    simp only [hG, image_eq_zero_of_notMem_tsupport ha, Complex.ofReal_zero, zero_mul]
  have hGhol : ∀ a : AdeleRing (𝓞 F) F, DifferentiableOn ℂ (fun z => G z a) O := fun a =>
    (differentiableOn_const _).mul (hEa _).differentiableOn
  have hd : DifferentiableOn ℂ (fun z => ∫ a, G z a ∂ν₀) O :=
    Complex.differentiableOn_integral_of_continuousOn_of_forall_differentiableOn ν₀ hO hχc.isCompact G hGc hGS hGhol
  have heq : ∀ z ∈ O, ∫ a, G z a ∂ν₀ = constantTerm ν₀ (fun t => unipotentGL2 t) (Ec z) h := by
    intro z hz
    unfold constantTerm constantTermIntegrand
    refine integral_congr_ae ?_
    have hae : ∀ᵐ t ∂ν₀, t ∈ adelicBox F := ProbabilityTheory.ae_cond_mem (measurableSet_adelicBox F)
    filter_upwards [hae] with t ht
    have h1 : χ t = 1 := hχ1 (hboxCb ht)
    simp only [hG, h1, Complex.ofReal_one, one_mul]
  have hd' : DifferentiableOn ℂ (fun z => constantTerm ν₀ (fun t => unipotentGL2 t) (Ec z) h) O :=
    hd.congr fun z hz => (heq z hz).symm
  exact hd'.analyticOnNhd hO

theorem continuousOn_integral_of_continuousOn_of_ae_mem_isCompact
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] [MeasurableSpace Y] [OpensMeasurableSpace Y]
    (μ : Measure Y) [IsProbabilityMeasure μ] {C : Set Y} (hC : IsCompact C) (hμC : ∀ᵐ y ∂μ, y ∈ C)
    {U : Set X} (f : X → Y → ℂ) (hf : ContinuousOn (Function.uncurry f) (U ×ˢ Set.univ)) :
    ContinuousOn (fun x => ∫ y, f x y ∂μ) U := by
  have hint : ∀ x ∈ U, Integrable (f x) μ := by
    intro x hx
    have hfx : Continuous (f x) :=
      hf.comp_continuous (continuous_const.prodMk continuous_id) (fun y => ⟨hx, Set.mem_univ _⟩)
    obtain ⟨M, hM⟩ := hC.exists_bound_of_continuousOn hfx.continuousOn
    refine Integrable.mono' (integrable_const M) hfx.aestronglyMeasurable ?_
    filter_upwards [hμC] with y hy
    exact hM y hy
  intro x₀ hx₀
  rw [ContinuousWithinAt, Metric.tendsto_nhds]
  intro ε hε
  have hu : {p : ℂ × ℂ | dist p.1 p.2 < ε / 2} ∈ uniformity ℂ := Metric.dist_mem_uniformity (half_pos hε)
  obtain ⟨v, hv, hvC⟩ := hC.mem_uniformity_of_prod
    (hf.mono (Set.prod_mono Subset.rfl (Set.subset_univ C))) hx₀ hu
  have hvU : ∀ᶠ x in 𝓝[U] x₀, x ∈ U := self_mem_nhdsWithin
  filter_upwards [hv, hvU] with x hx hxU
  rw [dist_eq_norm, ← integral_sub (hint x hxU) (hint x₀ hx₀)]
  have hbound : ∀ᵐ y ∂μ, ‖f x y - f x₀ y‖ ≤ ε / 2 := by
    filter_upwards [hμC] with y hy
    have h1 : dist (f x y) (f x₀ y) < ε / 2 := hvC x hx y hy
    rw [dist_eq_norm] at h1
    exact h1.le
  calc ‖∫ y, (f x y - f x₀ y) ∂μ‖
      ≤ ε / 2 * μ.real Set.univ := norm_integral_le_of_norm_le_const hbound
    _ = ε / 2 := by rw [probReal_univ, mul_one]
    _ < ε := half_lt_self hε

theorem continuousOn_constantTerm {O : Set ℂ} {Ec : ℂ → AdelicGL2 (𝓞 F) F → ℂ}
    (hEjc : ContinuousOn (fun p : ℂ × AdelicGL2 (𝓞 F) F => Ec p.1 p.2) (O ×ˢ Set.univ)) :
    ContinuousOn (fun p : ℂ × AdelicGL2 (𝓞 F) F =>
      constantTerm (ProbabilityTheory.cond (adelicAddHaar (𝓞 F) F) (adelicBox F))
        (fun t => unipotentGL2 t) (Ec p.1) p.2) (O ×ˢ Set.univ) := by
  obtain ⟨Cb, hCb, hboxCb⟩ := exists_isCompact_adelicBox_subset F
  have hae : ∀ᵐ t ∂(ProbabilityTheory.cond (adelicAddHaar (𝓞 F) F) (adelicBox F)), t ∈ Cb := by
    filter_upwards [ProbabilityTheory.ae_cond_mem (μ := adelicAddHaar (𝓞 F) F) (measurableSet_adelicBox F)]
      with t ht
    exact hboxCb ht
  have hmap : Continuous (fun q : (ℂ × AdelicGL2 (𝓞 F) F) × AdeleRing (𝓞 F) F =>
      ((q.1.1, unipotentGL2 q.2 * q.1.2) : ℂ × AdelicGL2 (𝓞 F) F)) :=
    (continuous_fst.comp continuous_fst).prodMk
      ((AutomorphicForm.continuous_unipotentGL2.comp continuous_snd).mul (continuous_snd.comp continuous_fst))
  have hf : ContinuousOn (Function.uncurry fun (p : ℂ × AdelicGL2 (𝓞 F) F) (t : AdeleRing (𝓞 F) F) =>
      Ec p.1 (unipotentGL2 t * p.2)) ((O ×ˢ (Set.univ : Set (AdelicGL2 (𝓞 F) F))) ×ˢ Set.univ) := by
    refine hEjc.comp hmap.continuousOn ?_
    intro q hq
    exact ⟨hq.1.1, Set.mem_univ _⟩
  unfold constantTerm constantTermIntegrand
  exact continuousOn_integral_of_continuousOn_of_ae_mem_isCompact _ hCb hae _ hf

theorem constantTerm_const_mul {Q G : Type*} [Group G] [MeasurableSpace Q] (m : Measure Q) (u : Q → G)
    (a : ℂ) (f : G → ℂ) (g : G) :
    constantTerm m u (fun x => a * f x) g = a * constantTerm m u f g := by
  unfold constantTerm constantTermIntegrand
  exact integral_const_mul a _

end ConstantTerm

section Glue

variable {F : Type} [Field F] [NumberField F]

theorem continuous_units_of_continuous_val (χ : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ)
    (h : Continuous fun x => ((χ x : ℂˣ) : ℂ)) : Continuous χ := by
  rw [Units.continuous_iff]
  refine ⟨h, ?_⟩
  simp_rw [Units.val_inv_eq_inv_val]
  exact h.inv₀ fun x => (χ x).ne_zero

theorem continuous_mul_inv (μ ν : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ)
    (hμk : Continuous fun x => ((μ x : ℂˣ) : ℂ)) (hνk : Continuous fun x => ((ν x : ℂˣ) : ℂ)) :
    Continuous (μ * ν⁻¹) := by
  have h1 := continuous_units_of_continuous_val μ hμk
  have h2 := continuous_units_of_continuous_val ν hνk
  show Continuous fun x => (μ * ν⁻¹) x
  simp only [MonoidHom.mul_apply, MonoidHom.inv_apply]
  exact h1.mul h2.inv

theorem isUnitaryChar_mul_inv (μ ν : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ)
    (hμ : IsUnitaryChar (𝓞 F) F μ) (hν : IsUnitaryChar (𝓞 F) F ν) : IsUnitaryChar (𝓞 F) F (μ * ν⁻¹) := by
  intro x
  rw [MonoidHom.mul_apply, MonoidHom.inv_apply, Units.val_mul, norm_mul, Units.val_inv_eq_inv_val, norm_inv,
    hμ x, hν x, inv_one, mul_one]

theorem isIdeleClassChar_mul_inv (μ ν : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ)
    (hμ : IsIdeleClassChar (𝓞 F) F μ) (hν : IsIdeleClassChar (𝓞 F) F ν) : IsIdeleClassChar (𝓞 F) F (μ * ν⁻¹) := by
  intro u
  rw [MonoidHom.mul_apply, MonoidHom.inv_apply, hμ u, hν u, inv_one, mul_one]

end Glue

section Flat

variable (F : Type) [Field F] [NumberField F]

theorem flat_case
    [MeasurableSpace (AdeleRing (𝓞 F) F)ˣ] [BorelSpace (AdeleRing (𝓞 F) F)ˣ]
    (ν₀ : Measure (AdeleRing (𝓞 F) F)ˣ) [ν₀.IsHaarMeasure] :
    let α : (AdeleRing (𝓞 F) F)ˣ →* ℝˣ :=
      ((NNReal.toRealHom : ℝ≥0 →+* ℝ).toMonoidHom.comp
        (distribHaarChar (AdeleRing (𝓞 F) F))).toHomUnits
    ∀ (hα : ∀ x, 0 < ((α x : ℝˣ) : ℝ))
      (μ ν : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ)
      (_hμ : IsUnitaryChar (𝓞 F) F μ) (_hν : IsUnitaryChar (𝓞 F) F ν)
      (_hμic : IsIdeleClassChar (𝓞 F) F μ) (_hνic : IsIdeleClassChar (𝓞 F) F ν)
      (_hμk : Continuous fun x : (AdeleRing (𝓞 F) F)ˣ => ((μ x : ℂˣ) : ℂ))
      (_hνk : Continuous fun x : (AdeleRing (𝓞 F) F)ˣ => ((ν x : ℂˣ) : ℂ))
      (c : ℂ) (q : ℂ → ℂ) (_hq : Differentiable ℂ q)
      (_hqz : ∀ s : ℂ, 0 ≤ s.re → s ≠ c → q s ≠ 0) (_hc : c.re = 1 / 2)
      (_hGE : ∀ Φ ∈ schwartzBruhat2 F, ∃ H : ℂ → AdelicGL2 (𝓞 F) F → ℂ,
        (∀ g, Differentiable ℂ fun s => H s g) ∧
        Continuous (fun p : ℂ × AdelicGL2 (𝓞 F) F => H p.1 p.2) ∧
        ∀ s : ℂ, 1 / 2 < s.re → ∀ g : AdelicGL2 (𝓞 F) F,
          H s g = q s * (godementSection F ν₀ μ ν α hα Φ s g
            + ∑' ξ : F, godementSection F ν₀ μ ν α hα Φ s
                (adelicWeyl (𝓞 F) F * unipotentGL2 (algebraMap F (AdeleRing (𝓞 F) F) ξ) * g)))
      (ψ : ℂ → AdelicGL2 (𝓞 F) F → ℂ)
      (_hψ : ∀ s, IsInducedSection (𝓞 F) F (etaFst μ α hα s) (etaSnd ν α hα s) (ψ s))
      (_hψK : ∀ s, IsArchKFinite F (ψ s))
      (_hψf : ∀ s, IsKfSmooth F (ψ s))
      (_hψjc : Continuous (fun p : ℂ × AdelicGL2 (𝓞 F) F => ψ p.1 p.2))
      (_hψhol : ∀ g, Differentiable ℂ (fun s => ψ s g))
      (_hψflat : ∀ (s s' : ℂ) (k : AdelicGL2 (𝓞 F) F),
          glFin (𝓞 F) F k ∈ finiteIntegralGL2 (𝓞 F) F →
          (∀ w : InfinitePlace F, IsRowIsometry (archComponent F w (glArch (𝓞 F) F k))) →
          ψ s k = ψ s' k),
    ∃ (U : Set ℂ) (Nc : ℂ → AdelicGL2 (𝓞 F) F → ℂ),
      IsOpen U ∧ {s : ℂ | 0 ≤ s.re} \ {c} ⊆ U ∧
      (∀ g : AdelicGL2 (𝓞 F) F, AnalyticOnNhd ℂ (fun s => Nc s g) U) ∧
      ContinuousOn (fun p : ℂ × AdelicGL2 (𝓞 F) F => Nc p.1 p.2) (U ×ˢ Set.univ) ∧
      (∀ s : ℂ, 1 / 2 < s.re → ∀ g : AdelicGL2 (𝓞 F) F,
        Nc s g = weylIntertwiningIntegral (𝓞 F) F (adelicAddHaar (𝓞 F) F) (ψ s) g) := by
  intro α hα μ ν hμ hν hμic hνic hμk hνk c q hq hqz hc hGE ψ hψ hψK hψf hψjc hψhol hψflat

  obtain ⟨n, Φ, B, S, ϖ, hΦ, hB, hϖ, hG1⟩ :=
    AutomorphicForm.exists_sum_mul_godementSection_eq_partialEulerProduct_mul_of_flat_family
      F ν₀ hα μ ν hμ hν hμk hνk ψ hψ hψK hψf hψjc hψhol hψflat

  have hχc : Continuous (μ * ν⁻¹) := continuous_mul_inv μ ν hμk hνk
  have hχu : IsUnitaryChar (𝓞 F) F (μ * ν⁻¹) := isUnitaryChar_mul_inv μ ν hμ hν
  have hχF : IsIdeleClassChar (𝓞 F) F (μ * ν⁻¹) := isIdeleClassChar_mul_inv μ ν hμic hνic
  obtain ⟨W, P, hW, hWsub, hPa, hPL⟩ :=
    NumberField.TateGlobal.exists_analyticOnNhd_mul_partialEulerProduct_eq_one_of_isUnitaryChar_of_isIdeleClassChar
      F S ϖ hϖ (μ * ν⁻¹) hχc hχu hχF

  choose H hHd hHc hHE using fun i : Fin n => hGE (Φ i) (hΦ i)

  set f : Fin n → ℂ → AdelicGL2 (𝓞 F) F → ℂ := fun i s g => godementSection F ν₀ μ ν α hα (Φ i) s g with hf_def
  have hαN : ∀ x, ((α x : ℝˣ) : ℝ) = ideleNorm F x := fun x => rfl
  have hfind : ∀ i s, IsInducedSection (𝓞 F) F (etaFst μ α hα s) (etaSnd ν α hα s) (f i s) := fun i s =>
    AutomorphicForm.isInducedSection_godementSection_of_forall_coe_eq_ideleNorm F ν₀ μ ν α hα hαN (Φ i) s
  have hfcont : ∀ i s, 0 < s.re → Continuous (f i s) := fun i s hs =>
    (AutomorphicForm.integrable_and_differentiableAt_and_continuous_godementSection_of_mem_schwartzBruhat2
      F ν₀ μ ν hμ hν hμk hνk α hα hαN (Φ i) (hΦ i)).2.2.2 s hs

  set vol : ℂ := ((((adelicAddHaar (𝓞 F) F) (adelicBox F)).toReal : ℝ) : ℂ) with hvol_def
  have hvol : vol ≠ 0 := by
    rw [hvol_def, Complex.ofReal_ne_zero]
    exact (ENNReal.toReal_pos (adelicAddHaar_adelicBox_pos F).ne' (adelicAddHaar_adelicBox_lt_top F).ne).ne'

  set CT : Fin n → ℂ → AdelicGL2 (𝓞 F) F → ℂ := fun i s g =>
    constantTerm (ProbabilityTheory.cond (adelicAddHaar (𝓞 F) F) (adelicBox F)) (fun t => unipotentGL2 t) (H i s) g
    with hCT_def
  have hCTa : ∀ i g, AnalyticOnNhd ℂ (fun s => CT i s g) Set.univ := fun i g =>
    analyticOnNhd_constantTerm isOpen_univ
      (fun g' => ((hHd i g').differentiableOn (s := Set.univ)).analyticOnNhd isOpen_univ)
      (hHc i).continuousOn g
  have hCTc : ∀ i, ContinuousOn (fun p : ℂ × AdelicGL2 (𝓞 F) F => CT i p.1 p.2) (Set.univ ×ˢ Set.univ) := fun i =>
    continuousOn_constantTerm (hHc i).continuousOn

  set U : Set ℂ := {s : ℂ | q s ≠ 0} ∩ (fun s : ℂ => 2 * s + 1) ⁻¹' W with hU_def
  have haff : Continuous fun s : ℂ => 2 * s + 1 := by fun_prop
  have haffa : AnalyticOnNhd ℂ (fun s : ℂ => 2 * s + 1) Set.univ :=
    (Differentiable.differentiableOn (by fun_prop)).analyticOnNhd isOpen_univ
  have hUo : IsOpen U := (isOpen_ne_fun hq.continuous continuous_const).inter (hW.preimage haff)
  refine ⟨U, fun s g => vol * P (2 * s + 1) * (q s)⁻¹ * (∑ i, B i s * CT i s g) - vol * ψ s g,
    hUo, ?_, ?_, ?_, ?_⟩
  ·
    rintro s ⟨hs0, hsc⟩
    refine ⟨hqz s hs0 hsc, hWsub ?_⟩
    show 1 ≤ (2 * s + 1).re
    have : (0 : ℝ) ≤ s.re := hs0
    simp only [Complex.add_re, Complex.mul_re, Complex.re_ofNat, Complex.im_ofNat, Complex.one_re, zero_mul,
      sub_zero]
    linarith
  ·
    intro g
    have hP2 : AnalyticOnNhd ℂ (fun s => P (2 * s + 1)) U := by
      intro s hs
      exact AnalyticAt.comp (f := fun s : ℂ => 2 * s + 1) (x := s) (hPa (2 * s + 1) hs.2)
        (haffa s (Set.mem_univ s))
    have hqi : AnalyticOnNhd ℂ (fun s => (q s)⁻¹) U := fun s hs =>
      ((hq.differentiableOn (s := Set.univ)).analyticOnNhd isOpen_univ s (Set.mem_univ s)).inv hs.1
    have hsum : AnalyticOnNhd ℂ (fun s => ∑ i, B i s * CT i s g) U :=
      Finset.analyticOnNhd_fun_sum (s := U) (f := fun i s => B i s * CT i s g) Finset.univ
        (fun i _ => (((hB i).differentiableOn (s := Set.univ)).analyticOnNhd isOpen_univ).mono (Set.subset_univ U)
          |>.mul ((hCTa i g).mono (Set.subset_univ U)))
    have hψa : AnalyticOnNhd ℂ (fun s => ψ s g) U :=
      (((hψhol g).differentiableOn (s := Set.univ)).analyticOnNhd isOpen_univ).mono (Set.subset_univ U)
    exact (((analyticOnNhd_const.mul hP2).mul hqi).mul hsum).sub (analyticOnNhd_const.mul hψa)
  ·
    have hP2 : ContinuousOn (fun p : ℂ × AdelicGL2 (𝓞 F) F => P (2 * p.1 + 1)) (U ×ˢ Set.univ) := by
      have h1 : ContinuousOn (fun s : ℂ => P (2 * s + 1)) U :=
        hPa.continuousOn.comp haff.continuousOn (fun s hs => hs.2)
      exact h1.comp continuous_fst.continuousOn (fun p hp => hp.1)
    have hqi : ContinuousOn (fun p : ℂ × AdelicGL2 (𝓞 F) F => (q p.1)⁻¹) (U ×ˢ Set.univ) :=
      ContinuousOn.inv₀ ((hq.continuous.comp continuous_fst).continuousOn) (fun p hp => hp.1.1)
    have hsum : ContinuousOn (fun p : ℂ × AdelicGL2 (𝓞 F) F => ∑ i, B i p.1 * CT i p.1 p.2) (U ×ˢ Set.univ) := by
      refine continuousOn_finsetSum _ (fun i _ => ?_)
      exact ((hB i).continuous.comp continuous_fst).continuousOn.mul
        ((hCTc i).mono (Set.prod_mono (Set.subset_univ U) subset_rfl))
    have hψc : ContinuousOn (fun p : ℂ × AdelicGL2 (𝓞 F) F => ψ p.1 p.2) (U ×ˢ Set.univ) := hψjc.continuousOn
    exact (((continuousOn_const.mul hP2).mul hqi).mul hsum).sub (continuousOn_const.mul hψc)
  ·
    intro s hs g
    have hs0 : 0 < s.re := lt_trans (by norm_num) hs
    have hsc : s ≠ c := fun h => by rw [h, hc] at hs; exact lt_irrefl _ hs
    have hq0 : q s ≠ 0 := hqz s hs0.le hsc
    have hw : 1 < (2 * s + 1).re := by
      simp only [Complex.add_re, Complex.mul_re, Complex.re_ofNat, Complex.im_ofNat, Complex.one_re, zero_mul,
        sub_zero]
      linarith

    set L : ℂ := ∏' v : {v // v ∉ S},
        (1 - ((localChar (μ * ν⁻¹) v.1 (ϖ v.1) : ℂˣ) : ℂ)
          * ((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-(2 * s + 1)))⁻¹ with hL_def
    have hpl : P (2 * s + 1) * L = 1 := hPL (2 * s + 1) hw

    have h1 : ∀ y, ∑ i, B i s * f i s y = L * ψ s y := fun y => hG1 s hs0 y
    have hψpt : ∀ y, ψ s y = P (2 * s + 1) * ∑ i, B i s * f i s y := fun y => by
      rw [h1 y, ← mul_assoc, hpl, one_mul]

    set Mψ : ℂ := weylIntertwiningIntegral (𝓞 F) F (adelicAddHaar (𝓞 F) F) (ψ s) g with hMψ_def
    set Mf : Fin n → ℂ := fun i => weylIntertwiningIntegral (𝓞 F) F (adelicAddHaar (𝓞 F) F) (f i s) g with hMf_def
    have hint : ∀ i, Integrable (fun x : AdeleRing (𝓞 F) F =>
        f i s ((adelicWeyl (𝓞 F) F)⁻¹ * unipotentGL2 x * g)) (adelicAddHaar (𝓞 F) F) := fun i =>
      AutomorphicForm.weylIntertwiningIntegrand_integrable_of_re_gt_half F hα μ ν hμ hν s hs (f i s) (hfind i s)
        (hfcont i s hs0) g
    have h2 : Mψ = P (2 * s + 1) * ∑ i, B i s * Mf i := by
      have e1 : Mψ = ∫ x, P (2 * s + 1) * ∑ i, B i s * f i s ((adelicWeyl (𝓞 F) F)⁻¹ * unipotentGL2 x * g)
          ∂(adelicAddHaar (𝓞 F) F) := by
        rw [hMψ_def]
        unfold weylIntertwiningIntegral
        exact integral_congr_ae (Eventually.of_forall fun x => hψpt _)
      have e2 : ∀ i, Mf i = ∫ x, f i s ((adelicWeyl (𝓞 F) F)⁻¹ * unipotentGL2 x * g) ∂(adelicAddHaar (𝓞 F) F) :=
        fun i => rfl
      rw [e1, integral_const_mul]
      congr 1
      rw [integral_finsetSum _ (fun i _ => (hint i).const_mul (B i s))]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [integral_const_mul, e2 i]

    have h3 : ∀ i, CT i s g = q s * (f i s g + vol⁻¹ * Mf i) := by
      intro i
      have hct := AutomorphicForm.constantTerm_bruhatEisenstein_eq_section_add_weylIntertwiningIntegral
        F hα μ ν hμ hν s hs (f i s) (hfind i s) (hfcont i s hs0) g
      dsimp only at hct
      have hHfun : H i s = fun g' => q s * (f i s g' + ∑' ξ : F, f i s
          (adelicWeyl (𝓞 F) F * unipotentGL2 (algebraMap F (AdeleRing (𝓞 F) F) ξ) * g')) := by
        funext g'
        exact hHE i s hs g'
      rw [hCT_def]
      dsimp only
      rw [hHfun, constantTerm_const_mul, hct]
    have hsum : ∑ i, B i s * CT i s g = q s * (L * ψ s g) + q s * vol⁻¹ * (P (2 * s + 1))⁻¹ * Mψ := by
      have hP0 : P (2 * s + 1) ≠ 0 := left_ne_zero_of_mul_eq_one hpl
      simp_rw [h3]
      calc ∑ i, B i s * (q s * (f i s g + vol⁻¹ * Mf i))
          = q s * (∑ i, B i s * f i s g) + q s * vol⁻¹ * (∑ i, B i s * Mf i) := by
            rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
            refine Finset.sum_congr rfl (fun i _ => ?_)
            ring
        _ = q s * (L * ψ s g) + q s * vol⁻¹ * (P (2 * s + 1))⁻¹ * Mψ := by
            rw [h1 g, h2, mul_assoc (q s * vol⁻¹) (P (2 * s + 1))⁻¹, ← mul_assoc (P (2 * s + 1))⁻¹,
              inv_mul_cancel₀ hP0, one_mul]
    show vol * P (2 * s + 1) * (q s)⁻¹ * (∑ i, B i s * CT i s g) - vol * ψ s g = Mψ
    rw [hsum]
    have hP0 : P (2 * s + 1) ≠ 0 := left_ne_zero_of_mul_eq_one hpl
    calc vol * P (2 * s + 1) * (q s)⁻¹ * (q s * (L * ψ s g) + q s * vol⁻¹ * (P (2 * s + 1))⁻¹ * Mψ) - vol * ψ s g
        = (P (2 * s + 1) * L) * (vol * ψ s g) * ((q s)⁻¹ * q s)
            + ((q s)⁻¹ * q s) * (vol * vol⁻¹) * (P (2 * s + 1) * (P (2 * s + 1))⁻¹) * Mψ - vol * ψ s g := by ring
      _ = Mψ := by rw [hpl, inv_mul_cancel₀ hq0, mul_inv_cancel₀ hvol, mul_inv_cancel₀ hP0]; ring

end Flat

section Polar

variable (F : Type) [Field F] [NumberField F]

theorem polar_data
    [MeasurableSpace (AdeleRing (𝓞 F) F)ˣ] [BorelSpace (AdeleRing (𝓞 F) F)ˣ]
    (ν₀ : Measure (AdeleRing (𝓞 F) F)ˣ) [ν₀.IsHaarMeasure] :
    let α : (AdeleRing (𝓞 F) F)ˣ →* ℝˣ :=
      ((NNReal.toRealHom : ℝ≥0 →+* ℝ).toMonoidHom.comp
        (distribHaarChar (AdeleRing (𝓞 F) F))).toHomUnits
    ∀ (hα : ∀ x, 0 < ((α x : ℝˣ) : ℝ))
      (μ ν : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ)
      (_hμ : IsUnitaryChar (𝓞 F) F μ) (_hν : IsUnitaryChar (𝓞 F) F ν)
      (_hμic : IsIdeleClassChar (𝓞 F) F μ) (_hνic : IsIdeleClassChar (𝓞 F) F ν)
      (_hμk : Continuous fun x : (AdeleRing (𝓞 F) F)ˣ => ((μ x : ℂˣ) : ℂ))
      (_hνk : Continuous fun x : (AdeleRing (𝓞 F) F)ˣ => ((ν x : ℂˣ) : ℂ)),
    ∃ (c : ℂ) (q : ℂ → ℂ), c.re = 1 / 2 ∧ Differentiable ℂ q ∧
      (∀ s : ℂ, 0 ≤ s.re → s ≠ c → q s ≠ 0) ∧
      ∀ Φ ∈ schwartzBruhat2 F, ∃ H : ℂ → AdelicGL2 (𝓞 F) F → ℂ,
        (∀ g, Differentiable ℂ fun s => H s g) ∧
        Continuous (fun p : ℂ × AdelicGL2 (𝓞 F) F => H p.1 p.2) ∧
        ∀ s : ℂ, 1 / 2 < s.re → ∀ g : AdelicGL2 (𝓞 F) F,
          H s g = q s * (godementSection F ν₀ μ ν α hα Φ s g
            + ∑' ξ : F, godementSection F ν₀ μ ν α hα Φ s
                (adelicWeyl (𝓞 F) F * unipotentGL2 (algebraMap F (AdeleRing (𝓞 F) F) ξ) * g)) := by
  intro α hα μ ν hμ hν hμic hνic hμk hνk

  set μ₁ : Measure (AdeleRing (𝓞 F) F) := ((adelicAddHaar (𝓞 F) F) (adelicBox F))⁻¹ • adelicAddHaar (𝓞 F) F
    with hμ₁_def
  haveI : μ₁.IsAddHaarMeasure :=
    Measure.IsAddHaarMeasure.smul (adelicAddHaar (𝓞 F) F)
      (ENNReal.inv_ne_zero.mpr (adelicAddHaar_adelicBox_lt_top F).ne)
      (ENNReal.inv_ne_top.mpr (adelicAddHaar_adelicBox_pos F).ne')
  have hμ₁ : μ₁ (adelicBox F) = 1 := by
    rw [hμ₁_def, Measure.smul_apply, smul_eq_mul]
    exact ENNReal.inv_mul_cancel (adelicAddHaar_adelicBox_pos F).ne' (adelicAddHaar_adelicBox_lt_top F).ne
  have hψ : IsGlobalAddChar F (NumberField.StandardAddChar.stdAddChar F) :=
    (NumberField.StandardAddChar.adelicTraceData F).isGlobalAddChar_psiK
  have hprin : IsPrincipalTrivial (R := 𝓞 F) (K := F) α := by
    intro u
    have h := NumberField.AdeleRing.distribHaarChar_algebraMap F u
    have e : ((α (Units.map (↑(algebraMap F (AdeleRing (𝓞 F) F))) u) : ℝˣ) : ℝ)
        = ((distribHaarChar (AdeleRing (𝓞 F) F)
            (Units.map (algebraMap F (AdeleRing (𝓞 F) F)).toMonoidHom u) : ℝ≥0) : ℝ) := rfl
    rw [← Units.val_eq_one, e, h, NNReal.coe_one]
  have hGE := AutomorphicForm.exists_entire_eq_godementEisenstein_fe_norm_le_of_mem_schwartzBruhat2
    F ν₀ μ₁ hμ₁ (NumberField.StandardAddChar.stdAddChar F) hψ hα hprin μ ν hμ hν hμic hνic hμk hνk
  by_cases hex : ∃ τ : ℝ, μ * ν⁻¹ = normPowChar F τ
  ·
    obtain ⟨τ, hτ⟩ := hex
    refine ⟨((1 : ℂ) - (τ : ℂ) * Complex.I) / 2,
      fun s => (s - ((1 : ℂ) - (τ : ℂ) * Complex.I) / 2) * (s + ((1 : ℂ) + (τ : ℂ) * Complex.I) / 2),
      ?_, by fun_prop, ?_, ?_⟩
    · simp
    · intro s hs0 hsc
      refine mul_ne_zero (sub_ne_zero.mpr hsc) ?_
      intro h
      have := congrArg Complex.re h
      simp only [Complex.add_re, Complex.div_re, Complex.one_re, Complex.mul_re, Complex.ofReal_re,
        Complex.I_re, mul_zero, Complex.ofReal_im, Complex.I_im, mul_one, sub_self, add_zero,
        Complex.re_ofNat, Complex.normSq_ofNat, Complex.add_im, Complex.one_im, Complex.mul_im, zero_add,
        Complex.im_ofNat, Complex.zero_re] at this
      linarith
    · intro Φ hΦ
      obtain ⟨H, H', hHd, -, hHc, -, hHE, -⟩ := (hGE Φ hΦ).2 τ hτ
      exact ⟨H, hHd, hHc, fun s hs g => hHE s hs g⟩
  ·
    push Not at hex
    refine ⟨1 / 2, fun _ => 1, by simp, by fun_prop, fun _ _ _ => one_ne_zero, ?_⟩
    intro Φ hΦ
    obtain ⟨H, H', hHd, -, hHc, -, hHE, -⟩ := (hGE Φ hΦ).1 hex
    exact ⟨H, hHd, hHc, fun s hs g => by rw [one_mul]; exact hHE s hs g⟩

end Polar

end R4Mcont
p2m_reactivate "P2MW.S_AutomorphicForm_exists_analyticOnNhd_continuation_weylIntertwiningIntegral_of_re_nonneg_of_isArchKFinite_family.R4Mcont"

end
p2m_reactivate "P2MW.S_AutomorphicForm_exists_analyticOnNhd_continuation_weylIntertwiningIntegral_of_re_nonneg_of_isArchKFinite_family.R4Mcont"

open MeasureTheory Filter Topology Set
open NumberField NumberField.AdelicHaar NumberField.AdelicBox NumberField.AdelicFourier NumberField.AdelicLevel
open NumberField.TateGlobal IsDedekindDomain
open AutomorphicForm AutomorphicForm.WindowedSiegel
open scoped NNReal ENNReal

theorem solution
    (F : Type) [Field F] [NumberField F] :
    let α : (AdeleRing (𝓞 F) F)ˣ →* ℝˣ :=
      ((NNReal.toRealHom : ℝ≥0 →+* ℝ).toMonoidHom.comp
        (distribHaarChar (AdeleRing (𝓞 F) F))).toHomUnits
    ∀ (hα : ∀ x, 0 < ((α x : ℝˣ) : ℝ))
      (μ ν : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ)
      (_hμ : IsUnitaryChar (𝓞 F) F μ) (_hν : IsUnitaryChar (𝓞 F) F ν)
      (_hμic : IsIdeleClassChar (𝓞 F) F μ) (_hνic : IsIdeleClassChar (𝓞 F) F ν)
      (_hμk : Continuous fun x : (AdeleRing (𝓞 F) F)ˣ => ((μ x : ℂˣ) : ℂ))
      (_hνk : Continuous fun x : (AdeleRing (𝓞 F) F)ˣ => ((ν x : ℂˣ) : ℂ))
      (φ : ℂ → AdelicGL2 (𝓞 F) F → ℂ)
      (_hφ : ∀ s, IsInducedSection (𝓞 F) F (etaFst μ α hα s) (etaSnd ν α hα s) (φ s))
      (_hφK : ∀ s, IsArchKFinite F (φ s))
      (_hφf : ∀ s, IsKfSmooth F (φ s))
      (_hφjc : Continuous (fun p : ℂ × AdelicGL2 (𝓞 F) F => φ p.1 p.2))
      (_hφhol : ∀ g, Differentiable ℂ (fun s => φ s g))
      (_hφKu : ∀ w : InfinitePlace F, ∃ W : Submodule ℂ (↥(archRowIsometrySubgroup F w) → ℂ),
        FiniteDimensional ℂ W ∧ ∀ (s : ℂ) (g : AdelicGL2 (𝓞 F) F),
          (fun k : ↥(archRowIsometrySubgroup F w) => φ s (g * (k : AdelicGL2 (𝓞 F) F))) ∈ W),
    letI := adeleBorel (𝓞 F) F
    ∃ (c : ℂ) (U : Set ℂ) (Nc : ℂ → AdelicGL2 (𝓞 F) F → ℂ),
      c.re = 1 / 2 ∧ IsOpen U ∧ {s : ℂ | 0 ≤ s.re} \ {c} ⊆ U ∧
      (∀ g : AdelicGL2 (𝓞 F) F, AnalyticOnNhd ℂ (fun s => Nc s g) U) ∧
      ContinuousOn (fun p : ℂ × AdelicGL2 (𝓞 F) F => Nc p.1 p.2) (U ×ˢ Set.univ) ∧
      (∀ s : ℂ, 1 / 2 < s.re → ∀ g : AdelicGL2 (𝓞 F) F,
        Nc s g = weylIntertwiningIntegral (𝓞 F) F (adelicAddHaar (𝓞 F) F) (φ s) g) := by
  intro α hα μ ν hμ hν hμic hνic hμk hνk φ hφ hφK hφf hφjc hφhol _hφKu
  letI : MeasurableSpace (AdeleRing (𝓞 F) F) := adeleBorel (𝓞 F) F
  haveI : BorelSpace (AdeleRing (𝓞 F) F) := borelSpace_adeleBorel _ _

  letI : MeasurableSpace (AdeleRing (𝓞 F) F)ˣ := borel _
  haveI : BorelSpace (AdeleRing (𝓞 F) F)ˣ := ⟨rfl⟩
  set ν₀ : Measure (AdeleRing (𝓞 F) F)ˣ := Measure.haar with hν₀

  obtain ⟨c, q, hc, hq, hqz, hGE⟩ := R4Mcont.polar_data F ν₀ hα μ ν hμ hν hμic hνic hμk hνk

  obtain ⟨n, cf, ψ, hcf, hψ, hψK, hψf, hψjc, hψhol, hψflat, hφeq⟩ :=
    AutomorphicForm.exists_flat_isInducedSection_sum_eq_of_differentiable_family
      F hα μ ν φ hφ hφK hφf hφjc hφhol

  have hflat : ∀ i : Fin n, ∃ (U : Set ℂ) (Nc : ℂ → AdelicGL2 (𝓞 F) F → ℂ),
      IsOpen U ∧ {s : ℂ | 0 ≤ s.re} \ {c} ⊆ U ∧
      (∀ g : AdelicGL2 (𝓞 F) F, AnalyticOnNhd ℂ (fun s => Nc s g) U) ∧
      ContinuousOn (fun p : ℂ × AdelicGL2 (𝓞 F) F => Nc p.1 p.2) (U ×ˢ Set.univ) ∧
      (∀ s : ℂ, 1 / 2 < s.re → ∀ g : AdelicGL2 (𝓞 F) F,
        Nc s g = weylIntertwiningIntegral (𝓞 F) F (adelicAddHaar (𝓞 F) F) (ψ i s) g) := fun i =>
    R4Mcont.flat_case F ν₀ hα μ ν hμ hν hμic hνic hμk hνk c q hq hqz hc hGE (ψ i) (hψ i) (hψK i) (hψf i)
      (hψjc i) (hψhol i) (hψflat i)
  choose U Nc hUo hUsub hNa hNc hNeq using hflat

  have hψc : ∀ i s, Continuous (ψ i s) := fun i s => (hψjc i).comp (Continuous.prodMk_right s)
  refine ⟨c, ⋂ i, U i, fun s g => ∑ i, cf i s * Nc i s g, hc, isOpen_iInter_of_finite hUo,
    fun s hs => Set.mem_iInter.mpr fun i => hUsub i hs, ?_, ?_, ?_⟩
  ·
    intro g
    exact Finset.analyticOnNhd_fun_sum (s := ⋂ i, U i) (f := fun i s => cf i s * Nc i s g) Finset.univ
      (fun i _ => (((hcf i).differentiableOn (s := Set.univ)).analyticOnNhd isOpen_univ).mono (Set.subset_univ _)
        |>.mul ((hNa i g).mono (Set.iInter_subset _ i)))
  ·
    refine continuousOn_finsetSum _ (fun i _ => ?_)
    exact ((hcf i).continuous.comp continuous_fst).continuousOn.mul
      ((hNc i).mono (Set.prod_mono (Set.iInter_subset _ i) subset_rfl))
  ·
    intro s hs g
    have hint : ∀ i, Integrable (fun x : AdeleRing (𝓞 F) F =>
        ψ i s ((adelicWeyl (𝓞 F) F)⁻¹ * unipotentGL2 x * g)) (adelicAddHaar (𝓞 F) F) := fun i =>
      AutomorphicForm.weylIntertwiningIntegrand_integrable_of_re_gt_half F hα μ ν hμ hν s hs (ψ i s) (hψ i s)
        (hψc i s) g
    show ∑ i, cf i s * Nc i s g = weylIntertwiningIntegral (𝓞 F) F (adelicAddHaar (𝓞 F) F) (φ s) g
    unfold weylIntertwiningIntegral
    simp_rw [hφeq s]
    rw [integral_finsetSum _ (fun i _ => (hint i).const_mul (cf i s))]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [integral_const_mul, hNeq i s hs g]
    rfl

end S_AutomorphicForm_exists_analyticOnNhd_continuation_weylIntertwiningIntegral_of_re_nonneg_of_isArchKFinite_family
end P2MW
export P2MW.S_AutomorphicForm_exists_analyticOnNhd_continuation_weylIntertwiningIntegral_of_re_nonneg_of_isArchKFinite_family (solution)
