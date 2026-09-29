-- Prove2me | solution 1 for AutomorphicForm.forall_isCompact_exists_forall_norm_axis_continuation_le_mul_adelicHeight_rpow_of_mem_canonicalTruncationDomain
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.340288+00:00
-- url     : https://prove2.me/submissions/13a6f871-22bb-585b-8933-d42db01bba8f

import Definitions.Def_AutomorphicForm_InducedSection
import Definitions.Def_AutomorphicForm_CanonicalTruncationDomain
import Definitions.Def_AutomorphicForm_CarrierPins
import Definitions.Def_NumberField_PrincipalLevel
import Definitions.Def_NumberField_AdelicHeight
import Definitions.Def_NumberField_AdelicBox
import Definitions.Def_AutomorphicForm_TruncationOperator
import Definitions.Def_AutomorphicForm_EtaFamily
import Definitions.Def_AutomorphicForm_WeylIntertwining
import Definitions.Def_AutomorphicForm_SlabProfile
import Definitions.Def_AutomorphicForm_AdelicMaximalCompact
import Definitions.Def_AutomorphicForm_ArchKFinite
import Definitions.Def_AutomorphicForm_SmoothAutomorphicFnAt
import Definitions.Def_NumberField_AdelicHaar
import Theorems.Thm_AutomorphicForm_norm_sub_constantTerm_le_mul_rpow_neg_of_axis_continuation_family
import Theorems.Thm_AutomorphicForm_analyticOnNhd_constantTerm_and_eq_add_of_axis_continuation_family
import Theorems.Thm_AutomorphicForm_exists_pos_forall_le_adelicHeight_and_adelicHeight_globalPoints_mul_le_inv_of_mem_canonicalTruncationDomain
import Theorems.Thm_AutomorphicForm_exists_mem_adelicBorel_mul_eq
import Theorems.Thm_AutomorphicForm_isInducedSection_adelicHeight_cpow
import Theorems.Thm_NumberField_AdelicHeight_adelicHeight_mul_of_mem_adelicMaximalCompact
import Theorems.Thm_AutomorphicForm_isInducedSection_and_continuous_weylIntertwiningIntegral_of_re_gt_half
import Theorems.Thm_NumberField_AdelicHeight_continuous_adelicHeight
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_forall_isCompact_exists_forall_norm_axis_continuation_le_mul_adelicHeight_rpow_of_mem_canonicalTruncationDomain
p2m_attr_erase "instance" "IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder_1 IsDedekindDomain.HeightOneSpectrum.instMulActionHomClassAlgHomTensorProductAdicCompletionForallValEqUnder_definitions IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraAdicCompletionValEqUnder IsDedekindDomain.HeightOneSpectrum.adicCompletion.instFiniteForallValEqUnderOfFiniteDimensional_definitions IsDedekindDomain.HeightOneSpectrum.instIsBiscalarSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersTensorProductCoeAlgHomTensorAdicCompletionIntegersTo IsDedekindDomain.HeightOneSpectrum.Extension.instContinuousSMulAdicCompletionValEqUnder IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsModuleTopology IsDedekindDomain.HeightOneSpectrum.Extension.instFiniteSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnderOfFiniteDimensional IsDedekindDomain.HeightOneSpectrum.adicCompletion.instFiniteValEqUnderOfFiniteDimensional_definitions instIsBiscalarTensorProductCoeAlgHomBaseChange_of_algebraMap IsDedekindDomain.HeightOneSpectrum.instIsScalarTowerSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsModuleTopologyPi IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions Submodule.instIsTopologicalModuleSubtypeMem Pi.instTopologicalModule IsTopologicalModule.toContinuousSMul IsTopologicalModule.toContinuousAdd instFunLike SemialgHomClass.toSemilinearMapClass instCoeTCSemialgHom SemialgHomClass.toRingHomClass SemialgHomClass.instSemialgHom instCountableOfNumberField_definitions instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions HeckePair.instSMulCommClassSubtypeForallMemSubmoduleHeckeAlgebra HeckePair.instAlgebraSubtypeForallMemSubmoduleHeckeAlgebra HeckePair.instOneSubtypeForallMemSubmoduleHeckeAlgebra HeckePair.instIsScalarTowerSubtypeForallMemSubmoduleHeckeAlgebra HeckePair.instRingSubtypeForallMemSubmoduleHeckeAlgebra"
p2m_attr_erase "instance" "HeckePair.instMulSubtypeForallMemSubmoduleHeckeAlgebra FixedPoints.instMulActionElemFixedPointsOfSMulCommClass_definitions FixedPoints.module FixedPoints.instSMulElemFixedPointsOfSMulCommClass_definitions FixedPoints.instAddCommMonoidElemFixedPoints_definitions RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions"
p2m_attr_erase "simp" "AutomorphicForm.whittakerCoefficient_zero AutomorphicForm.productionPins_nS AutomorphicForm.productionPins_mS AutomorphicForm.productionPins_ν AutomorphicForm.productionPins_Z AutomorphicForm.productionPins_U AutomorphicForm.productionPins_μ AutomorphicForm.productionPins_gen AutomorphicForm.productionPins_D LanglandsTunnell.TateLocal.charExt_coe_units LanglandsTunnell.TateLocal.modulus_one LanglandsTunnell.TateLocal.modulus_zero LanglandsTunnell.TateLocal.modulus_coe_units LanglandsTunnell.TateLocal.charExt_zero LanglandsTunnell.TateLocal.conductorExponentAt_one NumberField.StandardAddChar.ratArchLine_apply NumberField.StandardAddChar.AdelicTraceData.mk.sizeOf_spec NumberField.StandardAddChar.AdelicTraceData.mk.injEq NumberField.AdelicTrace.traceDiag_apply NumberField.AdelicTrace.diag_apply SemialgHom.baseChange_of_algebraMap_tmul_left SemialgHom.baseChangeRightOfAlgebraMap_apply Pi.semialgHomPi_apply Pi.semialgHom_apply Module.Basis.rightBaseChange_apply LinearEquiv.coe_mulLeft LinearEquiv.coe_mulRight WithVal.semialgebraMap_toFun_ofVal Module.Basis.rightBaseChange_repr IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers.tensorCoe_tmul IsDedekindDomain.HeightOneSpectrum.tensorAdicCompletionIntegersTo_tmul SemialgHom.baseChangeRightOfAlgebraMap_coe IsDedekindDomain.HeightOneSpectrum.adicCompletion.integerBaseChangeLinearEquiv_tmul_apply SemialgHom.baseChange_of_algebraMap_tmul_right IsLocalization.map_moduleTensorEquiv_symm_tmul IsLocalization.leftModuleTensorEquiv_apply IsLocalization.moduleLid_symm_apply IsLocalization.leftModuleTensorEquiv_symm_apply IsLocalization.map_moduleTensorEquiv_tmul IsModuleTopology.continuousLinearEquiv_apply"
p2m_attr_erase "simp" "AlgEquiv.extendScalars_symm_apply IsModuleTopology.Module.Basis.equivFun_homeo_symm_apply IsModuleTopology.Module.Basis.equivFun_homeo_apply IsModuleTopology.continuousAlgEquivOfIsBiscalar_apply AlgEquiv.extendScalars_apply IsModuleTopology.continuousLinearEquiv_symm_apply SemialgHom.restrictScalars_toFun SemialgHom.mk.sizeOf_spec SemialgHom.mk.injEq SemialgHom.coe_coe coe_mk TensorProduct.RightActions.smul_def TensorProduct.RightActions.Module.TensorProduct.comm_symm_apply_tmul TensorProduct.RightActions.LinearMap.baseChange_id TensorProduct.RightActions.algebraMap_eval TensorProduct.RightActions.Module.TensorProduct.comm_apply_tmul TensorProduct.RightActions.Algebra.TensorProduct.comm_symm_apply_tmul TensorProduct.RightActions.Algebra.TensorProduct.comm_apply_tmul EisensteinGeneral.Piece.FactorizationDatum.mk.sizeOf_spec EisensteinGeneral.Piece.FactorizationDatum.mk.injEq NumberField.AdeleRing.val_finiteUnitsComponent IsDedekindDomain.FiniteAdeleRing.val_unitsComponent NumberField.AdeleRing.val_finitePartUnits NumberField.AdeleRing.val_infiniteUnitsComponent LocalGL2.coe_localRepSome LocalGL2.coe_diagPi LocalGL2.coe_localRepInf LocalGL2.coe_localRepSome_inv LocalGL2.coe_unipotentInt LocalGL2.coe_weylInt LocalGL2.coe_diagPi_inv LocalGL2.transposeGL_val LocalGL2.transposeGL_one HeckePair.convTerm_mk HeckePair.coe_apply_add HeckePair.coe_apply_smul FixedPoints.coe_zero FixedPoints.coe_smul FixedPoints.coe_add LocalGL2.swapUnit_val"
p2m_attr_erase "simp" "M4aHerbrand.IdeleGaloisDescent.mk.sizeOf_spec M4aHerbrand.IdeleGaloisDescent.mk.injEq AutomorphicForm.fnTwist_zero AutomorphicForm.fnTwist_apply AutomorphicForm.classSq_apply AutomorphicForm.classRepEmbedding_one AutomorphicForm.finIdeleExponentAt_one AutomorphicForm.classRepFinIdele_one AutomorphicForm.productionPinsGeneralOf_D AutomorphicForm.productionPinsGeneral_D AutomorphicForm.productionPinsGeneralOf_μ AutomorphicForm.productionPinsGeneralOf_U AutomorphicForm.productionPinsCompact_ν AutomorphicForm.productionPinsCompact_U AutomorphicForm.productionPinsCompact_D AutomorphicForm.productionPinsCompact_nS AutomorphicForm.productionPinsCompact_gen AutomorphicForm.productionPinsCompact_Z AutomorphicForm.productionPinsCompact_mS AutomorphicForm.productionPinsCompact_μ AutomorphicForm.HeckeEigensystem.ofRawCentral_toRawCentral AutomorphicForm.HeckeEigensystem.toRawCentral_ofRawCentral AutomorphicForm.HeckeEigensystem.ofRawCentral_a AutomorphicForm.HeckeEigensystem.ofRawCentral_b AutomorphicForm.HeckeEigensystem.toRawCentral_level AutomorphicForm.HeckeEigensystem.toRawCentral_a AutomorphicForm.HeckeEigensystem.ofRawCentral_level AutomorphicForm.HeckeEigensystem.toRawCentral_b AutomorphicForm.SmoothCuspRealizationAt.mk.injEq AutomorphicForm.degenerateEigensystem_a AutomorphicForm.SmoothCuspRealizationAt.mk.sizeOf_spec AutomorphicForm.degenerateEigensystem_b AutomorphicForm.HeckeEigensystem.map_b AutomorphicForm.HeckeEigensystem.map_a AutomorphicForm.HeckeEigensystem.map_level AutomorphicForm.CuspidalityNotion.mk.injEq AutomorphicForm.HeckeEigensystem.twist_b AutomorphicForm.satakePow_zero AutomorphicForm.HeckeEigensystem.twist_a AutomorphicForm.HeckeEigensystem.mk.injEq"
p2m_attr_erase "simp" "AutomorphicForm.HeckeEigensystem.mk.sizeOf_spec AutomorphicForm.DescentPackage.mk.injEq AutomorphicForm.DescentPackage.mk.sizeOf_spec AutomorphicForm.CuspidalityNotion.mk.sizeOf_spec AutomorphicForm.satakePow_one ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg"
p2m_attr_erase "simp" "RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply"

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicHaar
open IsDedekindDomain
open scoped ComplexConjugate NNReal

attribute [local instance] NumberField.AdelicHaar.glBorel

open AutomorphicForm AutomorphicForm.WindowedSiegel NumberField.AdelicHeight

namespace HoloG2

theorem rpow_le_max_mul_rpow {h₀ H a A : ℝ} (hh₀ : 0 < h₀) (hH : h₀ ≤ H) (ha : |a| ≤ A) :
    H ^ a ≤ max 1 (h₀ ^ (-2 * A)) * H ^ A := by
  have hHpos : 0 < H := hh₀.trans_le hH
  have haA : a ≤ A := (le_abs_self a).trans ha
  have hAa : -A ≤ a := (neg_le_neg ha).trans (neg_abs_le a)
  have hsplit : H ^ a = H ^ (a - A) * H ^ A := by
    rw [← Real.rpow_add hHpos]; congr 1; ring
  rw [hsplit]
  refine mul_le_mul_of_nonneg_right ?_ (Real.rpow_nonneg hHpos.le A)
  by_cases h1 : 1 ≤ H
  · exact (Real.rpow_le_one_of_one_le_of_nonpos h1 (sub_nonpos.mpr haA)).trans (le_max_left _ _)
  · have hH1 : H ≤ 1 := le_of_lt (not_le.mp h1)
    calc H ^ (a - A) ≤ H ^ (-2 * A) :=
          Real.rpow_le_rpow_of_exponent_ge hHpos hH1 (by linarith)
      _ ≤ h₀ ^ (-2 * A) := Real.rpow_le_rpow_of_nonpos hh₀ hH (by linarith [(abs_nonneg a).trans ha])
      _ ≤ max 1 (h₀ ^ (-2 * A)) := le_max_right _ _

variable (F : Type) [Field F] [NumberField F]

theorem unif_section_bound
    (α : (AdeleRing (𝓞 F) F)ˣ →* ℝˣ) (hα : ∀ x, 0 < ((α x : ℝˣ) : ℝ))
    (hsph : ∀ s : ℂ, IsInducedSection (𝓞 F) F (etaFst 1 α hα s) (etaSnd 1 α hα s)
        (fun g : AdelicGL2 (𝓞 F) F => ((adelicHeight F g : ℝ) : ℂ) ^ (s + 1 / 2)))
    {μ ν : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ} (hμ : IsUnitaryChar (𝓞 F) F μ) (hν : IsUnitaryChar (𝓞 F) F ν)
    (C : Set ℂ) (hC : IsCompact C) (σ : ℂ → ℂ) (hσ : Continuous σ)
    (φ : ℂ → AdelicGL2 (𝓞 F) F → ℂ)
    (hφ : ∀ x ∈ C, IsInducedSection (𝓞 F) F (etaFst μ α hα (σ x)) (etaSnd ν α hα (σ x)) (φ x))
    (hφc : ContinuousOn (fun p : ℂ × AdelicGL2 (𝓞 F) F => φ p.1 p.2) (C ×ˢ Set.univ)) :
    ∃ S : ℝ, 0 ≤ S ∧ ∀ x ∈ C, ∀ g : AdelicGL2 (𝓞 F) F,
      ‖φ x g‖ ≤ S * adelicHeight F g ^ ((σ x).re + 1 / 2) := by

  set q : ℂ × AdelicGL2 (𝓞 F) F → ℝ := fun p => ‖φ p.1 p.2‖ / adelicHeight F p.2 ^ ((σ p.1).re + 1 / 2)
    with hq
  have hHpow_pos : ∀ (x : ℂ) (g : AdelicGL2 (𝓞 F) F), 0 < adelicHeight F g ^ ((σ x).re + 1 / 2) :=
    fun x g => Real.rpow_pos_of_pos (adelicHeight_pos g) _
  have hnorm_factor : ∀ (μ' ν' : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ), IsUnitaryChar (𝓞 F) F μ' →
      IsUnitaryChar (𝓞 F) F ν' → ∀ (s : ℂ) (a d : (AdeleRing (𝓞 F) F)ˣ),
      ‖((etaFst μ' α hα s a : ℂˣ) : ℂ) * ((etaSnd ν' α hα s d : ℂˣ) : ℂ)‖
        = ((α a : ℝˣ) : ℝ) ^ (s.re + 1 / 2) * ((α d : ℝˣ) : ℝ) ^ (-(s.re + 1 / 2)) := by
    intro μ' ν' hμ' hν' s a d
    rw [norm_mul, norm_etaFst_apply_of_unitary hμ']
    congr 1
    rw [etaSnd_apply, Units.val_mul, norm_mul, hν' d, one_mul, norm_cpowChar_apply]
    congr 1
    rw [Complex.neg_re, re_add_half]
  have hnorm_h : ∀ (t : ℝ) (g : AdelicGL2 (𝓞 F) F),
      ‖((adelicHeight F g : ℝ) : ℂ) ^ ((t : ℂ) + 1 / 2)‖ = adelicHeight F g ^ (t + 1 / 2) := by
    intro t g
    rw [Complex.norm_cpow_eq_rpow_re_of_pos (adelicHeight_pos g)]
    congr 1
    simp [Complex.add_re]

  have hq_borel : ∀ x ∈ C, ∀ (b : AdelicGL2 (𝓞 F) F) (hb : b ∈ adelicBorel (𝓞 F) F)
      (g : AdelicGL2 (𝓞 F) F), q (x, b * g) = q (x, g) := by
    intro x hx b hb g
    set t : ℝ := (σ x).re with ht
    have h1 : ‖φ x (b * g)‖ = ((α (borelDiagFst ⟨b, hb⟩) : ℝˣ) : ℝ) ^ (t + 1 / 2)
        * ((α (borelDiagSnd ⟨b, hb⟩) : ℝˣ) : ℝ) ^ (-(t + 1 / 2)) * ‖φ x g‖ := by
      rw [hφ x hx b hb g, norm_mul, hnorm_factor μ ν hμ hν (σ x)]
    have h1u : IsUnitaryChar (𝓞 F) F (1 : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ) := fun _ => by simp
    have h2 : adelicHeight F (b * g) ^ (t + 1 / 2)
        = ((α (borelDiagFst ⟨b, hb⟩) : ℝˣ) : ℝ) ^ (t + 1 / 2)
          * ((α (borelDiagSnd ⟨b, hb⟩) : ℝˣ) : ℝ) ^ (-(t + 1 / 2)) * adelicHeight F g ^ (t + 1 / 2) := by
      have e := hsph (t : ℂ) b hb g
      dsimp only at e
      rw [← hnorm_h, ← hnorm_h, e, norm_mul, hnorm_factor 1 1 h1u h1u (t : ℂ)]
      simp [Complex.ofReal_re]
    have hpos : 0 < ((α (borelDiagFst ⟨b, hb⟩) : ℝˣ) : ℝ) ^ (t + 1 / 2)
        * ((α (borelDiagSnd ⟨b, hb⟩) : ℝˣ) : ℝ) ^ (-(t + 1 / 2)) :=
      mul_pos (Real.rpow_pos_of_pos (hα _) _) (Real.rpow_pos_of_pos (hα _) _)
    simp only [hq]
    rw [h1, h2, mul_div_mul_left _ _ hpos.ne']

  have hq_cont : ContinuousOn q (C ×ˢ Set.univ) := by
    refine (continuous_norm.continuousOn.comp hφc (Set.mapsTo_univ _ _)).div ?_ fun p _ => (hHpow_pos p.1 p.2).ne'
    refine Continuous.continuousOn ?_
    refine ((NumberField.AdelicHeight.continuous_adelicHeight F).comp continuous_snd).rpow ?_ ?_
    · exact ((Complex.continuous_re.comp (hσ.comp continuous_fst)).add continuous_const)
    · exact fun p => Or.inl (adelicHeight_pos p.2).ne'

  have hKc : IsCompact (adelicMaximalCompact F : Set (AdelicGL2 (𝓞 F) F)) := isCompact_adelicMaximalCompact F
  obtain ⟨M, hM⟩ : ∃ M : ℝ, ∀ p ∈ C ×ˢ (adelicMaximalCompact F : Set (AdelicGL2 (𝓞 F) F)), q p ≤ M := by
    have hbdd := (hC.prod hKc).bddAbove_image
      (hq_cont.mono (Set.prod_mono subset_rfl (Set.subset_univ _)))
    obtain ⟨M, hM⟩ := hbdd
    exact ⟨M, fun p hp => hM ⟨p, hp, rfl⟩⟩
  refine ⟨max M 0, le_max_right _ _, fun x hx g => ?_⟩
  obtain ⟨b, k, hb, hk₁, hk₂, hg⟩ := AutomorphicForm.exists_mem_adelicBorel_mul_eq F g
  have hk : k ∈ adelicMaximalCompact F := mem_adelicMaximalCompact_iff.mpr ⟨hk₁, hk₂⟩
  have hqg : q (x, g) ≤ max M 0 := by
    rw [hg, hq_borel x hx b hb k]
    exact (hM (x, k) ⟨hx, hk⟩).trans (le_max_left _ _)
  have : ‖φ x g‖ = q (x, g) * adelicHeight F g ^ ((σ x).re + 1 / 2) := by
    simp only [hq]; rw [div_mul_cancel₀ _ (hHpow_pos x g).ne']
  rw [this]
  exact mul_le_mul_of_nonneg_right hqg (hHpow_pos x g).le

end HoloG2

theorem solution
    (F : Type) [Field F] [NumberField F] (α β : ℝ) (hα : 0 < α) (hαβ : α < β) :
    let αm : (AdeleRing (𝓞 F) F)ˣ →* ℝˣ :=
      ((NNReal.toRealHom : ℝ≥0 →+* ℝ).toMonoidHom.comp
        (distribHaarChar (AdeleRing (𝓞 F) F))).toHomUnits
    letI := adeleBorel (𝓞 F) F
    ∀ (hαm : ∀ x, 0 < ((αm x : ℝˣ) : ℝ))
      (μ ν : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ)
      (_hμ : AutomorphicForm.IsUnitaryChar (𝓞 F) F μ) (_hν : AutomorphicForm.IsUnitaryChar (𝓞 F) F ν)
      (_hμF : AutomorphicForm.IsIdeleClassChar (𝓞 F) F μ) (_hνF : AutomorphicForm.IsIdeleClassChar (𝓞 F) F ν)
      (_hμk : Continuous fun x : (AdeleRing (𝓞 F) F)ˣ => ((μ x : ℂˣ) : ℂ))
      (_hνk : Continuous fun x : (AdeleRing (𝓞 F) F)ˣ => ((ν x : ℂˣ) : ℂ))
      (φf : ℂ → AdelicGL2 (𝓞 F) F → ℂ)
      (_hφf : ∀ s, IsInducedSection (𝓞 F) F (etaFst μ αm hαm s) (etaSnd ν αm hαm s) (φf s))
      (_hφfK : ∀ s, IsArchKFinite F (φf s))
      (_hφff : ∀ s, IsKfSmooth F (φf s))
      (_hφfjc : Continuous (fun p : ℂ × AdelicGL2 (𝓞 F) F => φf p.1 p.2))
      (_hφfhol : ∀ g, Differentiable ℂ (fun s => φf s g))
      (_hφfKu : ∀ w : InfinitePlace F, ∃ W : Submodule ℂ (↥(archRowIsometrySubgroup F w) → ℂ),
        FiniteDimensional ℂ W ∧ ∀ (s : ℂ) (g : AdelicGL2 (𝓞 F) F),
          (fun k : ↥(archRowIsometrySubgroup F w) => φf s (g * (k : AdelicGL2 (𝓞 F) F))) ∈ W)
      (Oφ : Set ℂ) (Eφ Nφ : ℂ → AdelicGL2 (𝓞 F) F → ℂ)
      (_hEφ :
      IsOpen Oφ ∧ IsPreconnected Oφ ∧ {s : ℂ | s.re = 0} ⊆ Oφ ∧ {s : ℂ | 1 / 2 < s.re} ⊆ Oφ ∧
      (∀ g : AdelicGL2 (𝓞 F) F, AnalyticOnNhd ℂ (fun s => Eφ s g) Oφ) ∧
      (∀ g : AdelicGL2 (𝓞 F) F, AnalyticOnNhd ℂ (fun s => Nφ s g) Oφ) ∧
      ContinuousOn (fun p : ℂ × AdelicGL2 (𝓞 F) F => Eφ p.1 p.2) (Oφ ×ˢ Set.univ) ∧
      ContinuousOn (fun p : ℂ × AdelicGL2 (𝓞 F) F => Nφ p.1 p.2) (Oφ ×ˢ Set.univ) ∧
      (∀ s : ℂ, 1 / 2 < s.re → ∀ g : AdelicGL2 (𝓞 F) F,
        Eφ s g = φf s g + ∑' ξ : F, φf s (adelicWeyl (𝓞 F) F
          * unipotentGL2 (algebraMap F (AdeleRing (𝓞 F) F) ξ) * g)) ∧
      (∀ s : ℂ, 1 / 2 < s.re → ∀ g : AdelicGL2 (𝓞 F) F,
        Nφ s g = weylIntertwiningIntegral (𝓞 F) F (adelicAddHaar (𝓞 F) F) (φf s) g))
      (C : Set ℂ), IsCompact C → C ⊆ Oφ → ∃ (M A : ℝ), ∀ s ∈ C, ∀ (g : AdelicGL2 (𝓞 F) F),
        g ∈ AutomorphicForm.canonicalTruncationDomain F α β →
        ‖Eφ s g‖ ≤ M * (NumberField.AdelicHeight.adelicHeight F g) ^ A := by
  intro αm hαm μ ν hμ hν hμF hνF hμk hνk φf hφf hφfK hφff hφfjc hφfhol hφfKu Oφ Eφ Nφ hEφ C hC hCO
  letI : MeasurableSpace (AdeleRing (𝓞 F) F) := adeleBorel (𝓞 F) F
  obtain ⟨hO, hOc, hax, hhalf, hEa, hNa, hEjc, hNjc, hE, hN⟩ := hEφ
  have hE' : ∀ z : ℂ, 1 / 2 < z.re → ∀ g : AdelicGL2 (𝓞 F) F,
      Eφ z g = AutomorphicForm.pseudoEisenstein F (φf z) g := fun z hz g => by
    rw [hE z hz g, AutomorphicForm.pseudoEisenstein_apply]
  have hφc : ∀ z : ℂ, Continuous (φf z) := fun z =>
    hφfjc.comp (continuous_const.prodMk continuous_id)

  obtain ⟨h₀, hh₀, hfloor, -⟩ :=
    AutomorphicForm.exists_pos_forall_le_adelicHeight_and_adelicHeight_globalPoints_mul_le_inv_of_mem_canonicalTruncationDomain
      F α β hα hαβ

  have hKc : IsCompact (adelicMaximalCompact F : Set (AdelicGL2 (𝓞 F) F)) :=
    isCompact_adelicMaximalCompact (K := F)
  obtain ⟨M₀, hM₀⟩ :=
    AutomorphicForm.norm_sub_constantTerm_le_mul_rpow_neg_of_axis_continuation_family F hαm μ ν hμ hν hμF hνF
      φf hφf hφfK hφff hφfjc hφfhol hφfKu Oφ Eφ Nφ hO hOc hhalf hEa hNa hEjc hNjc hE' hN
      C (adelicMaximalCompact F : Set (AdelicGL2 (𝓞 F) F)) h₀ 0 hC hCO hKc hh₀

  have hCT := (AutomorphicForm.analyticOnNhd_constantTerm_and_eq_add_of_axis_continuation_family F hαm
    μ ν hμ hν hμF hνF φf hφf hφfK hφff hφfjc hφfhol hφfKu Oφ Eφ Nφ hO hOc hhalf hEa hNa hEjc hNjc
    hE' hN).2.2

  obtain ⟨-, h1u, hsph⟩ := AutomorphicForm.isInducedSection_adelicHeight_cpow F
  obtain ⟨S₁, hS₁0, hS₁⟩ := HoloG2.unif_section_bound F αm hαm (hsph hαm) hμ hν C hC id continuous_id φf
    (fun x _ => hφf x) hφfjc.continuousOn

  have h1 : (1 : ℂ) ∈ Oφ := hhalf (by simp only [Set.mem_setOf_eq, Complex.one_re]; norm_num)
  have hopen : IsOpen {z : ℂ | 1 / 2 < z.re} := isOpen_lt continuous_const Complex.continuous_re
  have h1mem : {z : ℂ | 1 / 2 < z.re} ∈ nhds (1 : ℂ) :=
    hopen.mem_nhds (by simp only [Set.mem_setOf_eq, Complex.one_re]; norm_num)
  have hcpow : ∀ (x : (AdeleRing (𝓞 F) F)ˣ) (w : ℂ),
      AnalyticOnNhd ℂ (fun z : ℂ => ((cpowChar αm hαm (-z + w) x : ℂˣ) : ℂ)) Oφ := by
    intro x w
    have hx0 : ((((αm x : ℝˣ) : ℝ) : ℂ)) ≠ 0 := Complex.ofReal_ne_zero.mpr (hαm x).ne'
    have hd : Differentiable ℂ (fun z : ℂ => ((((αm x : ℝˣ) : ℝ) : ℂ)) ^ (-z + w)) := fun z =>
      ((differentiableAt_id.neg).add_const w).const_cpow (Or.inl hx0)
    simpa only [cpowChar_apply_val] using hd.differentiableOn.analyticOnNhd hO
  have hNind : ∀ s ∈ Oφ, IsInducedSection (𝓞 F) F (etaFst ν αm hαm (-s)) (etaSnd μ αm hαm (-s)) (Nφ s) := by
    intro s hs b hb g
    have hu : AnalyticOnNhd ℂ (fun z => Nφ z (b * g)) Oφ := hNa _
    have hv : AnalyticOnNhd ℂ (fun z =>
        ((etaFst ν αm hαm (-z) (borelDiagFst (⟨b, hb⟩ : ↥(adelicBorel (𝓞 F) F))) : ℂˣ) : ℂ) *
        ((etaSnd μ αm hαm (-z) (borelDiagSnd (⟨b, hb⟩ : ↥(adelicBorel (𝓞 F) F))) : ℂˣ) : ℂ) *
        Nφ z g) Oφ := by
      have hA : AnalyticOnNhd ℂ (fun z =>
          ((etaFst ν αm hαm (-z) (borelDiagFst (⟨b, hb⟩ : ↥(adelicBorel (𝓞 F) F))) : ℂˣ) : ℂ)) Oφ := by
        have := (analyticOnNhd_const (v := ((ν (borelDiagFst (⟨b, hb⟩ : ↥(adelicBorel (𝓞 F) F))) : ℂˣ) : ℂ))).mul
          (hcpow (borelDiagFst (⟨b, hb⟩ : ↥(adelicBorel (𝓞 F) F))) (1 / 2))
        simpa only [etaFst_apply, Units.val_mul] using this
      have hB : AnalyticOnNhd ℂ (fun z =>
          ((etaSnd μ αm hαm (-z) (borelDiagSnd (⟨b, hb⟩ : ↥(adelicBorel (𝓞 F) F))) : ℂˣ) : ℂ)) Oφ := by
        have hx0 : ((((αm (borelDiagSnd (⟨b, hb⟩ : ↥(adelicBorel (𝓞 F) F))) : ℝˣ) : ℝ) : ℂ)) ≠ 0 :=
          Complex.ofReal_ne_zero.mpr (hαm _).ne'
        have hd : Differentiable ℂ (fun z : ℂ =>
            ((((αm (borelDiagSnd (⟨b, hb⟩ : ↥(adelicBorel (𝓞 F) F))) : ℝˣ) : ℝ) : ℂ)) ^ (-(-z + 1 / 2))) :=
          fun z => (((differentiableAt_id.neg).add_const (1 / 2 : ℂ)).neg).const_cpow (Or.inl hx0)
        have := (analyticOnNhd_const (v := ((μ (borelDiagSnd (⟨b, hb⟩ : ↥(adelicBorel (𝓞 F) F))) : ℂˣ) : ℂ))).mul
          (hd.differentiableOn.analyticOnNhd hO)
        simpa only [etaSnd_apply, Units.val_mul, cpowChar_apply_val] using this
      exact (hA.mul hB).mul (hNa g)
    have key : ∀ z : ℂ, 1 / 2 < z.re →
        Nφ z (b * g) =
          ((etaFst ν αm hαm (-z) (borelDiagFst (⟨b, hb⟩ : ↥(adelicBorel (𝓞 F) F))) : ℂˣ) : ℂ) *
          ((etaSnd μ αm hαm (-z) (borelDiagSnd (⟨b, hb⟩ : ↥(adelicBorel (𝓞 F) F))) : ℂˣ) : ℂ) *
          Nφ z g := by
      intro z hz
      have hI := (AutomorphicForm.isInducedSection_and_continuous_weylIntertwiningIntegral_of_re_gt_half F
        hαm μ ν hμ hν z hz (φf z) (hφf z) (hφc z)).1
      rw [hN z hz (b * g), hN z hz g]
      exact hI b hb g
    have hfg : (fun z => Nφ z (b * g)) =ᶠ[nhds (1 : ℂ)] (fun z =>
        ((etaFst ν αm hαm (-z) (borelDiagFst (⟨b, hb⟩ : ↥(adelicBorel (𝓞 F) F))) : ℂˣ) : ℂ) *
        ((etaSnd μ αm hαm (-z) (borelDiagSnd (⟨b, hb⟩ : ↥(adelicBorel (𝓞 F) F))) : ℂˣ) : ℂ) *
        Nφ z g) := Filter.eventuallyEq_of_mem h1mem (fun z hz => key z hz)
    exact (hu.eqOn_of_preconnected_of_eventuallyEq hv hOc h1 hfg) hs
  obtain ⟨S₂, hS₂0, hS₂⟩ := HoloG2.unif_section_bound F αm hαm (hsph hαm) hν hμ C hC (fun z => -z)
    continuous_neg Nφ (fun x hx => hNind x (hCO hx)) (hNjc.mono (Set.prod_mono hCO subset_rfl))

  obtain ⟨ρ, hρ⟩ := hC.isBounded.exists_norm_le
  set A : ℝ := max ρ 0 + 1 / 2 with hA
  have hA0 : 0 ≤ A := by positivity
  have hre : ∀ s ∈ C, |s.re| ≤ max ρ 0 := fun s hs =>
    ((Complex.abs_re_le_norm s).trans (hρ s hs)).trans (le_max_left _ _)
  have ha1 : ∀ s ∈ C, |s.re + 1 / 2| ≤ A := fun s hs => by
    have := hre s hs
    rw [abs_le] at this ⊢; constructor <;> linarith [this.1, this.2, le_max_right ρ 0]
  have ha2 : ∀ s ∈ C, |(-s).re + 1 / 2| ≤ A := fun s hs => by
    have := hre s hs
    rw [Complex.neg_re]
    rw [abs_le] at this ⊢; constructor <;> linarith [this.1, this.2, le_max_right ρ 0]
  have ha0 : |(0 : ℝ)| ≤ A := by rw [abs_zero]; exact hA0
  set κ : ℝ := max 1 (h₀ ^ (-2 * A)) with hκ
  have hκ0 : 0 ≤ κ := le_trans zero_le_one (le_max_left _ _)
  set c : ℂ := ((((adelicAddHaar (𝓞 F) F) (adelicBox F)).toReal : ℂ))⁻¹ with hc
  refine ⟨(max M₀ 0 + S₁ + ‖c‖ * S₂) * κ, A, ?_⟩
  intro s hs g hg
  have hsO : s ∈ Oφ := hCO hs
  have hH : h₀ ≤ adelicHeight F g := hfloor g hg
  have hHpos : 0 < adelicHeight F g := hh₀.trans_le hH

  obtain ⟨b, k, hb, hkf, hka, hgbk⟩ := AutomorphicForm.exists_mem_adelicBorel_mul_eq F g
  have hk : k ∈ adelicMaximalCompact F := mem_adelicMaximalCompact_iff.mpr ⟨hkf, hka⟩
  have hH1 : adelicHeight F (1 : AdelicGL2 (𝓞 F) F) = 1 := by
    rw [NumberField.AdelicHeight.adelicHeight_eq_archHeight_of_mem
      (by rw [map_one]; exact (finiteIntegralGL2 (𝓞 F) F).one_mem), map_one, archHeight_one]
  have hsph1 := hsph hαm ((1 : ℂ) / 2) b hb 1
  have h11 : ((1 : ℂ) / 2 + 1 / 2) = 1 := by norm_num
  simp only [mul_one, hH1, Complex.ofReal_one, h11, Complex.cpow_one,
    etaFst_apply, etaSnd_apply, cpowChar_apply_val, MonoidHom.one_apply,
    one_mul, Complex.cpow_neg_one] at hsph1
  have hHb : adelicHeight F b =
      ((αm (borelDiagFst (⟨b, hb⟩ : ↥(adelicBorel (𝓞 F) F))) : ℝˣ) : ℝ) /
        ((αm (borelDiagSnd (⟨b, hb⟩ : ↥(adelicBorel (𝓞 F) F))) : ℝˣ) : ℝ) := by
    rw [div_eq_mul_inv]
    exact_mod_cast hsph1
  have hHg : adelicHeight F g =
      ((αm (borelDiagFst (⟨b, hb⟩ : ↥(adelicBorel (𝓞 F) F))) : ℝˣ) : ℝ) /
        ((αm (borelDiagSnd (⟨b, hb⟩ : ↥(adelicBorel (𝓞 F) F))) : ℝˣ) : ℝ) := by
    rw [hgbk, NumberField.AdelicHeight.adelicHeight_mul_of_mem_adelicMaximalCompact F b k hk, hHb]
  have hcusp : ‖Eφ s g - AutomorphicForm.constantTerm (ProbabilityTheory.cond (adelicAddHaar (𝓞 F) F) (adelicBox F))
      (fun t => AutomorphicForm.unipotentGL2 t) (Eφ s) g‖ ≤ max M₀ 0 := by
    have key := hM₀ s hs ⟨b, hb⟩ k hk (by rw [← hHg]; exact hH)
    have hbk : ((⟨b, hb⟩ : ↥(adelicBorel (𝓞 F) F)) : AdelicGL2 (𝓞 F) F) * k = g := hgbk.symm
    rw [← hHg, hbk] at key
    simp only [Nat.cast_zero, neg_zero, Real.rpow_zero, mul_one] at key
    exact key.trans (le_max_left _ _)

  have hp0 : (1 : ℝ) ≤ κ * adelicHeight F g ^ A := by
    have := HoloG2.rpow_le_max_mul_rpow hh₀ hH ha0
    rwa [Real.rpow_zero] at this
  have hp1 : adelicHeight F g ^ (s.re + 1 / 2) ≤ κ * adelicHeight F g ^ A :=
    HoloG2.rpow_le_max_mul_rpow hh₀ hH (ha1 s hs)
  have hp2 : adelicHeight F g ^ ((-s).re + 1 / 2) ≤ κ * adelicHeight F g ^ A :=
    HoloG2.rpow_le_max_mul_rpow hh₀ hH (ha2 s hs)
  have hφb : ‖φf s g‖ ≤ S₁ * adelicHeight F g ^ (s.re + 1 / 2) := hS₁ s hs g
  have hNb : ‖Nφ s g‖ ≤ S₂ * adelicHeight F g ^ ((-s).re + 1 / 2) := hS₂ s hs g
  have hdecomp : Eφ s g = (Eφ s g - AutomorphicForm.constantTerm
      (ProbabilityTheory.cond (adelicAddHaar (𝓞 F) F) (adelicBox F))
      (fun t => AutomorphicForm.unipotentGL2 t) (Eφ s) g) + (φf s g + c * Nφ s g) := by
    rw [← hCT s hsO g]; ring
  rw [hdecomp]
  calc ‖(Eφ s g - AutomorphicForm.constantTerm
      (ProbabilityTheory.cond (adelicAddHaar (𝓞 F) F) (adelicBox F))
      (fun t => AutomorphicForm.unipotentGL2 t) (Eφ s) g) + (φf s g + c * Nφ s g)‖
      ≤ max M₀ 0 + (‖φf s g‖ + ‖c‖ * ‖Nφ s g‖) := by
        refine (norm_add_le _ _).trans (add_le_add hcusp ?_)
        refine (norm_add_le _ _).trans ?_
        rw [norm_mul]
    _ ≤ max M₀ 0 * (κ * adelicHeight F g ^ A) + (S₁ * (κ * adelicHeight F g ^ A) +
        ‖c‖ * (S₂ * (κ * adelicHeight F g ^ A))) := by
        have e0 : max M₀ 0 ≤ max M₀ 0 * (κ * adelicHeight F g ^ A) :=
          le_mul_of_one_le_right (le_max_right _ _) hp0
        have e1 : ‖φf s g‖ ≤ S₁ * (κ * adelicHeight F g ^ A) :=
          hφb.trans (mul_le_mul_of_nonneg_left hp1 hS₁0)
        have e2 : ‖c‖ * ‖Nφ s g‖ ≤ ‖c‖ * (S₂ * (κ * adelicHeight F g ^ A)) :=
          mul_le_mul_of_nonneg_left (hNb.trans (mul_le_mul_of_nonneg_left hp2 hS₂0)) (norm_nonneg _)
        linarith
    _ = (max M₀ 0 + S₁ + ‖c‖ * S₂) * κ * adelicHeight F g ^ A := by ring

end S_AutomorphicForm_forall_isCompact_exists_forall_norm_axis_continuation_le_mul_adelicHeight_rpow_of_mem_canonicalTruncationDomain
end P2MW
export P2MW.S_AutomorphicForm_forall_isCompact_exists_forall_norm_axis_continuation_le_mul_adelicHeight_rpow_of_mem_canonicalTruncationDomain (solution)
