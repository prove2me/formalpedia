-- Prove2me | solution 1 for AlgebraicGeometry.RelPicard.isNodeUnitModule_foldr_ofPoint_of_forall_eq_ord_of_hasValue
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:03.589526+00:00
-- url     : https://prove2.me/submissions/5345262b-f86f-5199-8919-88d00a751475

import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RepresentsRelSubPic
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroGroupCut
import Definitions.Def_AlgebraicGeometry_RelPicardPullback
import Definitions.Def_AlgebraicGeometry_ModulesRigidify
import Definitions.Def_AlgebraicGeometry_NeronModelEndomorphismExtension
import Definitions.Def_AlgebraicGeometry_TwoGluedCurvesNodeUnitModule
import Definitions.Def_AlgebraicGeometry_IdealSheafModule
import Definitions.Def_AlgebraicGeometry_RelEffCartierDiv
import Definitions.Def_AlgebraicGeometry_RelEffCartierDivOfPoint
import Definitions.Def_SheafOfModules_Monoidal
import Definitions.Def_AlgebraicCurve_CurveModel
import Definitions.Def_AlgebraicCurve_GluedPic0
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Definitions.Def_AlgebraicCurve_AdelicIndex
import Definitions.Def_AlgebraicGeometry_IdealSheafModuleMaps
import Definitions.Def_AlgebraicCurve_RelCartier
import Definitions.Def_AlgebraicGeometry_ModulesPullbackMonoidal
import Definitions.Def_AlgebraicGeometry_RelEffCartierDivSupportedIn
import Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_nonempty_module_tensor_invModule_iso
import Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_nonempty_mul_module_iso_tensor
import Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_nonempty_mul_invModule_iso_tensor
import Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_pow
import Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_comap_mul
import Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_isInvertible_module
import Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_isInvertible_invModule
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_tensor
import Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_isIso_pullbackModuleComparison
import Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_nonempty_pullback_invModule_iso
import Theorems.Thm_AlgebraicGeometry_RelEffCartierDiv_isInvertible_I_of_supportedIn
import Theorems.Thm_AlgebraicGeometry_isIso_morphismRestrict_and_smoothOfRelativeDimension_one_of_coe_eq_compl_range_of_isClosedImmersion
import Theorems.Thm_AlgebraicGeometry_TwoGluedCurves_IsNodeUnitModule_tensor
import Theorems.Thm_AlgebraicGeometry_exists_rationalPoint_enumeration_of_natCard_pullback_eq
import Definitions.Def_AlgebraicGeometry_ModulesSectionsTensor
import Definitions.Def_AlgebraicGeometry_ModulesPullbackLocalSection
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_isFrameOn
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsFrameOn_pullbackLocalSection
import Theorems.Thm_AlgebraicGeometry_TwoGluedCurves_injective_and_range_eq_nodeCondition_of_forall_exists_isFrameOn
import Theorems.Thm_AlgebraicGeometry_RelEffCartierDiv_comap_curveChange_ofPoint_comp_eq_and_isIso_pullbackModuleComparison_of_isIso_morphismRestrict
import Theorems.Thm_AlgebraicGeometry_RelEffCartierDiv_comap_curveChange_ofPoint_eq_top_and_isIso_pullbackModuleComparison_of_disjoint
import Theorems.Thm_AlgebraicGeometry_RelEffCartierDiv_isInvertible_I
import Theorems.Thm_AlgebraicGeometry_TwoGluedCurves_IsNodeUnitModule_smul_units
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_isIso_ev_app_and_isIso_curry_braiding_ev
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_isIso_ev_app_tensorUnit
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_tensor_inverse
import Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_comap_of_isOpenImmersion
import Definitions.Def_AlgebraicGeometry_ModulesSectionZeroScheme
import Definitions.Def_AlgebraicGeometry_ModulesIhomSections
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_pullbackTensorUnitObjIso_hom_app_pullbackLocalSection_unitSection
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_pullbackTensorObjIso_hom_app_pullbackLocalSection
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_tensorHom_app_tensorSections
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_leftUnitor_hom_app_tensorSections
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_rightUnitor_hom_app_tensorSections
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsFrameOn_tensorSections
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_isFrameOn_app_of_disjoint_support_zeroSchemeIdeal
import Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_zeroSchemeIdeal_invModuleSection
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_whiskerLeft_app_tensorSections
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_whiskerRight_app_tensorSections
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_pullbackUnitIso_hom_app_pullbackLocalSection_toUnitSection
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_ideal_zeroSchemeIdeal_eq_span_of_app_eq_smul
import Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_range_moduleIota_app_and_injective
import Theorems.Thm_AlgebraicGeometry_Scheme_Hom_isInvertible_ker_of_comp_eq_id
import Theorems.Thm_AlgebraicGeometry_Scheme_Hom_ord_eq_of_ker_pow_ideal_eq_span
import Definitions.Def_AlgebraicCurve_PlacesOf
import Definitions.Def_AlgebraicCurve_CechSectionsOfDivisor
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_exists_iso_app_eq_of_isFrameOn_of_eq_smul
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsFrameOn_of_iSup
import Definitions.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier
import Theorems.Thm_AlgebraicCurve_CurveModel_infinite_place
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_divisor_range_eq_lSpaceOn
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_RelPicard_isNodeUnitModule_foldr_ofPoint_of_forall_eq_ord_of_hasValue
p2m_attr_erase "instance" "AlgebraicGeometry.RelEffCartierDiv.isClosedImmersion_subschemeι_resProdMap AlgebraicGeometry.RelEffCartierDiv.isOpenImmersion_resProdMap AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupDivisor AlgebraicCurve.Pic0.instModuleZModTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instDistribMulActionTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instSMulTorsion AlgebraicCurve.SemilinearAut.instMulActionSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instSMulCommClassZModTorsion AlgebraicCurve.SemilinearAut.instMulSemiringActionSubtypeProdRingAutMemSubgroup instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions"
p2m_attr_erase "simp" "AlgebraicGeometry.RelEffCartierDiv.restrictAlong_extendAlong AlgebraicGeometry.RelEffCartierDiv.extendAlong_I AlgebraicGeometry.RelEffCartierDiv.resProdMap_snd AlgebraicGeometry.RelEffCartierDiv.restrictAlong_I AlgebraicGeometry.RelEffCartierDiv.extendAlong_restrictAlong AlgebraicGeometry.RelEffCartierDiv.resProdMap_fst_assoc AlgebraicGeometry.RelEffCartierDiv.resProdMap_snd_assoc AlgebraicGeometry.RelEffCartierDiv.resProdMap_fst AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk"
p2m_attr_erase "simp" "ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.SemilinearAut.toRingAut_inv AlgebraicCurve.SemilinearAut.smul_def AlgebraicCurve.SemilinearAut.smul_single AlgebraicCurve.SemilinearAut.smul_toValuationSubring AlgebraicCurve.SemilinearAut.baseAut_inv AlgebraicCurve.SemilinearAut.baseAut_ofAlgAut AlgebraicCurve.SemilinearAut.toRingAut_ofAlgAut AlgebraicCurve.SemilinearAut.torsionRep_apply AlgebraicCurve.SemilinearAut.toRingAut_one AlgebraicCurve.SemilinearAut.deg_smul AlgebraicCurve.SemilinearAut.degree_smul AlgebraicCurve.SemilinearAut.coe_degZeroSMulHom AlgebraicCurve.SemilinearAut.baseAut_mul AlgebraicCurve.SemilinearAut.coe_smulValuationSubringEquiv_apply AlgebraicCurve.SemilinearAut.baseAut_one AlgebraicCurve.SemilinearAut.ofAlgAut_smul AlgebraicCurve.SemilinearAut.coe_torsion_smul AlgebraicCurve.SemilinearAut.toRingAut_mul AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.jqNModC_one ModularCurve.qExpand_coeff_mul ModularCurve.qExpandₐ_apply ModularCurve.jqN_one ModularCurve.qExpand_single ModularCurve.dedekindPsi_one ModularCurve.ModularPolynomialData.mk.sizeOf_spec ModularCurve.evalAtJ_X ModularCurve.ModularPolynomialData.mk.injEq ModularCurve.constantCoeff_jNum ModularCurve.constantCoeff_eisenstein4 ModularCurve.qExpand_C ModularCurve.coeff_jq_neg_one ModularCurve.constantCoeff_jNumQ"
p2m_attr_erase "simp" "ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one"
set_option autoImplicit false

universe u v

p2m_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry NeronModelInfra GoodReductionJacobian AlgebraicGeometry.RelPicard AlgebraicGeometry.TwoGluedCurves AlgebraicCurve Opposite TopologicalSpace"

noncomputable section

namespace EPkgTwist

p2m_open "AlgebraicGeometry.Scheme.IdealSheafData"

variable {Y : Scheme.{u}}

def shuffle (A B C D : Y.Modules) : (A ⊗ B) ⊗ (C ⊗ D) ≅ (A ⊗ C) ⊗ (B ⊗ D) :=
  α_ A B (C ⊗ D) ≪≫ whiskerLeftIso A ((α_ B C D).symm ≪≫ whiskerRightIso (β_ B C) D ≪≫ α_ C B D) ≪≫
    (α_ A C (B ⊗ D)).symm

def shuffle' (A B C D : Y.Modules) : (A ⊗ B) ⊗ (C ⊗ D) ≅ (A ⊗ D) ⊗ (B ⊗ C) :=
  whiskerLeftIso (A ⊗ B) (β_ C D) ≪≫ shuffle A B D C

abbrev pf (J K : Y.IdealSheafData) : Y.Modules := J.invModule ⊗ K.module

theorem nonempty_module_top_iso : Nonempty ((⊤ : Y.IdealSheafData).module ≅ 𝟙_ Y.Modules) := by
  obtain ⟨⟨e⟩, -⟩ := (isInvertible_top (X := Y)).nonempty_module_tensor_invModule_iso
  obtain ⟨μ⟩ := (isInvertible_top (X := Y)).nonempty_mul_module_iso_tensor (isInvertible_top (X := Y))
  have hμ : (⊤ : Y.IdealSheafData).module ⊗ (⊤ : Y.IdealSheafData).module ≅ (⊤ : Y.IdealSheafData).module :=
    μ.symm ≪≫ eqToIso (congrArg Scheme.IdealSheafData.module (top_mul (⊤ : Y.IdealSheafData)))
  exact ⟨(ρ_ _).symm ≪≫ whiskerLeftIso _ e.symm ≪≫ (α_ _ _ _).symm ≪≫ whiskerRightIso hμ _ ≪≫ e⟩

theorem nonempty_invModule_top_iso : Nonempty ((⊤ : Y.IdealSheafData).invModule ≅ 𝟙_ Y.Modules) := by
  obtain ⟨-, ⟨e⟩⟩ := (isInvertible_top (X := Y)).nonempty_module_tensor_invModule_iso
  obtain ⟨m⟩ := nonempty_module_top_iso (Y := Y)
  exact ⟨(ρ_ _).symm ≪≫ whiskerLeftIso _ m.symm ≪≫ e⟩

theorem nonempty_pf_top_top_iso : Nonempty (pf (⊤ : Y.IdealSheafData) ⊤ ≅ 𝟙_ Y.Modules) :=
  ((isInvertible_top (X := Y)).nonempty_module_tensor_invModule_iso).2

theorem IsInvertible.listProd {ι : Type v} (f : ι → Y.IdealSheafData) :
    ∀ (l : List ι), (∀ i ∈ l, (f i).IsInvertible) → (l.map f).prod.IsInvertible
  | [], _ => by simpa using (isInvertible_top (X := Y))
  | (i :: l), h => by
      rw [List.map_cons, List.prod_cons]
      exact (h i (by simp)).mul (IsInvertible.listProd f l (fun j hj => h j (by simp [hj])))

theorem IsInvertible.finsetProd {ι : Type v} (f : ι → Y.IdealSheafData) (s : Finset ι)
    (h : ∀ i ∈ s, (f i).IsInvertible) : (∏ i ∈ s, f i).IsInvertible := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (isInvertible_top (X := Y))
  | insert a s ha ih =>
      rw [Finset.prod_insert ha]
      exact (h a (by simp)).mul (ih (fun i hi => h i (by simp [hi])))

theorem nonempty_pf_mul_iso {J J' K K' : Y.IdealSheafData} (hJ : J.IsInvertible) (hJ' : J'.IsInvertible)
    (hK : K.IsInvertible) (hK' : K'.IsInvertible) :
    Nonempty (pf (J * J') (K * K') ≅ pf J K ⊗ pf J' K') := by
  obtain ⟨a⟩ := hJ.nonempty_mul_invModule_iso_tensor hJ'
  obtain ⟨b⟩ := hK.nonempty_mul_module_iso_tensor hK'
  exact ⟨(a ⊗ᵢ b) ≪≫ shuffle _ _ _ _⟩

def contract {A B C D : Y.Modules} (e : B ⊗ D ≅ 𝟙_ Y.Modules) : (A ⊗ B) ⊗ (C ⊗ D) ≅ A ⊗ C :=
  shuffle A B C D ≪≫ whiskerLeftIso _ e ≪≫ ρ_ _

theorem nonempty_pf_congr {J J' K K' : Y.IdealSheafData} (hJ : J.IsInvertible) (hJ' : J'.IsInvertible)
    (hK : K.IsInvertible) (hK' : K'.IsInvertible) (h : J * K' = J' * K) :
    Nonempty (pf J K ≅ pf J' K') := by
  obtain ⟨a⟩ := hJ.nonempty_mul_invModule_iso_tensor hK'
  obtain ⟨a'⟩ := hJ'.nonempty_mul_invModule_iso_tensor hK
  obtain ⟨-, ⟨eK⟩⟩ := hK.nonempty_module_tensor_invModule_iso
  obtain ⟨-, ⟨eK'⟩⟩ := hK'.nonempty_module_tensor_invModule_iso

  have c : J.invModule ⊗ K'.invModule ≅ J'.invModule ⊗ K.invModule :=
    a.symm ≪≫ eqToIso (congrArg Scheme.IdealSheafData.invModule h) ≪≫ a'

  have l : (J.invModule ⊗ K'.invModule) ⊗ (K.module ⊗ K'.module) ≅ pf J K :=
    contract eK'
  have r : (J'.invModule ⊗ K.invModule) ⊗ (K.module ⊗ K'.module) ≅ pf J' K' :=
    whiskerLeftIso _ (β_ _ _) ≪≫ contract eK
  exact ⟨l.symm ≪≫ whiskerRightIso c _ ≪≫ r⟩

variable {V : Type v}

def twistL (P : V → Y.IdealSheafData) (D : V → ℤ) (l : List V) : Y.Modules :=
  l.foldr (fun v M => (P v ^ (D v).toNat).invModule ⊗ ((P v ^ (-(D v)).toNat).module ⊗ M)) (𝟙_ Y.Modules)

@[scoped simp] theorem twistL_nil (P : V → Y.IdealSheafData) (D : V → ℤ) : twistL P D [] = 𝟙_ Y.Modules := rfl

@[scoped simp] theorem twistL_cons (P : V → Y.IdealSheafData) (D : V → ℤ) (v : V) (l : List V) :
    twistL P D (v :: l) = (P v ^ (D v).toNat).invModule ⊗ ((P v ^ (-(D v)).toNat).module ⊗ twistL P D l) := rfl

theorem nonempty_twistL_iso_of_forall_eq (P P' : V → Y.IdealSheafData) (D : V → ℤ) :
    ∀ (l : List V), (∀ v ∈ l, P v = P' v) → Nonempty (twistL P D l ≅ twistL P' D l)
  | [], _ => ⟨(Iso.refl (𝟙_ Y.Modules) : twistL P D [] ≅ twistL P' D [])⟩
  | (v :: l), h => by
      obtain ⟨e⟩ := nonempty_twistL_iso_of_forall_eq P P' D l (fun w hw => h w (by simp [hw]))
      have hv : P v = P' v := h v (by simp)
      refine ⟨?_⟩
      change (P v ^ (D v).toNat).invModule ⊗ ((P v ^ (-(D v)).toNat).module ⊗ twistL P D l) ≅
        (P' v ^ (D v).toNat).invModule ⊗ ((P' v ^ (-(D v)).toNat).module ⊗ twistL P' D l)
      exact eqToIso (congrArg (fun I : Y.IdealSheafData => (I ^ (D v).toNat).invModule) hv) ⊗ᵢ
        (eqToIso (congrArg (fun I : Y.IdealSheafData => (I ^ (-(D v)).toNat).module) hv) ⊗ᵢ e)

abbrev Jp (P : V → Y.IdealSheafData) (D : V → ℤ) (l : List V) : Y.IdealSheafData :=
  (l.map fun v => P v ^ (D v).toNat).prod
abbrev Jn (P : V → Y.IdealSheafData) (D : V → ℤ) (l : List V) : Y.IdealSheafData :=
  (l.map fun v => P v ^ (-(D v)).toNat).prod

theorem isInvertible_Jp (P : V → Y.IdealSheafData) (D : V → ℤ) (l : List V) (h : ∀ v ∈ l, (P v).IsInvertible) :
    (Jp P D l).IsInvertible :=
  IsInvertible.listProd _ l (fun v hv => (h v hv).pow _)
theorem isInvertible_Jn (P : V → Y.IdealSheafData) (D : V → ℤ) (l : List V) (h : ∀ v ∈ l, (P v).IsInvertible) :
    (Jn P D l).IsInvertible :=
  IsInvertible.listProd _ l (fun v hv => (h v hv).pow _)

theorem nonempty_twistL_iso_pf (P : V → Y.IdealSheafData) (D : V → ℤ) :
    ∀ (l : List V), (∀ v ∈ l, (P v).IsInvertible) → Nonempty (twistL P D l ≅ pf (Jp P D l) (Jn P D l))
  | [], _ => ⟨(nonempty_pf_top_top_iso (Y := Y)).some.symm⟩
  | (v :: l), h => by
      have hv : (P v).IsInvertible := h v (by simp)
      have hl : ∀ w ∈ l, (P w).IsInvertible := fun w hw => h w (by simp [hw])
      obtain ⟨e⟩ := nonempty_twistL_iso_pf P D l hl
      obtain ⟨m⟩ := nonempty_pf_mul_iso (hv.pow (D v).toNat) (isInvertible_Jp P D l hl)
        (hv.pow (-(D v)).toNat) (isInvertible_Jn P D l hl)
      refine ⟨whiskerLeftIso _ (whiskerLeftIso _ e) ≪≫ (α_ _ _ _).symm ≪≫ m.symm ≪≫ eqToIso ?_⟩
      simp [Jp, Jn]

theorem isInvertible_twistL (P : V → Y.IdealSheafData) (D : V → ℤ) :
    ∀ (l : List V), (∀ v ∈ l, (P v).IsInvertible) → Scheme.Modules.IsInvertible (twistL P D l)
  | [], _ => Scheme.Modules.isInvertible_unit Y
  | (v :: l), h => by
      have hv : (P v).IsInvertible := h v (by simp)
      rw [twistL_cons]
      exact (hv.pow _).isInvertible_invModule.tensor
        ((hv.pow _).isInvertible_module.tensor (isInvertible_twistL P D l (fun w hw => h w (by simp [hw]))))

theorem nonempty_twistL_iso_unit_of_forall_eq_top (P : V → Y.IdealSheafData) (D : V → ℤ) :
    ∀ (l : List V), (∀ v ∈ l, P v = ⊤) → Nonempty (twistL P D l ≅ 𝟙_ Y.Modules)
  | [], _ => ⟨Iso.refl _⟩
  | (v :: l), h => by
      obtain ⟨e⟩ := nonempty_twistL_iso_unit_of_forall_eq_top P D l (fun w hw => h w (by simp [hw]))
      obtain ⟨a⟩ := nonempty_invModule_top_iso (Y := Y)
      obtain ⟨b⟩ := nonempty_module_top_iso (Y := Y)
      have hv : P v = ⊤ := h v (by simp)
      have ha : (P v ^ (D v).toNat).invModule ≅ 𝟙_ Y.Modules :=
        eqToIso (by rw [hv, ← one_eq_top, one_pow]) ≪≫ a
      have hb : (P v ^ (-(D v)).toNat).module ≅ 𝟙_ Y.Modules :=
        eqToIso (by rw [hv, ← one_eq_top, one_pow]) ≪≫ b
      exact ⟨(ha ⊗ᵢ (hb ⊗ᵢ e)) ≪≫ whiskerLeftIso _ (λ_ _) ≪≫ λ_ _⟩

theorem comap_pow {Y' : Scheme.{u}} (I : Y.IdealSheafData) (f : Y' ⟶ Y) :
    ∀ n : ℕ, (I ^ n).comap f = I.comap f ^ n
  | 0 => by rw [pow_zero, pow_zero, one_eq_top, one_eq_top, comap_top]
  | (n + 1) => by rw [pow_succ, pow_succ, comap_mul, comap_pow I f n]

theorem nonempty_pullback_twistL_iso {Y' : Scheme.{u}} (f : Y' ⟶ Y) (P : V → Y.IdealSheafData)
    (Q : V → Y'.IdealSheafData) (D : V → ℤ) :
    ∀ (l : List V), (∀ v ∈ l, (P v).IsInvertible ∧ (P v).comap f = Q v ∧ (Q v).IsInvertible) →
      Nonempty ((Scheme.Modules.pullback f).obj (twistL P D l) ≅ twistL Q D l)
  | [], _ => ⟨Scheme.Modules.pullbackTensorUnitObjIso f⟩
  | (v :: l), h => by
      obtain ⟨hP, hPQ, hQ⟩ := h v (by simp)
      obtain ⟨e⟩ := nonempty_pullback_twistL_iso f P Q D l (fun w hw => h w (by simp [hw]))
      have hc : ∀ n : ℕ, ((P v ^ n).comap f) = Q v ^ n := fun n => by rw [comap_pow, hPQ]
      have hc' : ∀ n : ℕ, ((P v ^ n).comap f).IsInvertible := fun n => by rw [hc]; exact hQ.pow n

      have em : (Scheme.Modules.pullback f).obj ((P v ^ (-(D v)).toNat).module) ≅ (Q v ^ (-(D v)).toNat).module := by
        haveI := (hP.pow (-(D v)).toNat).isIso_pullbackModuleComparison f (hc' _)
        exact asIso ((P v ^ (-(D v)).toNat).pullbackModuleComparison f) ≪≫
          eqToIso (congrArg Scheme.IdealSheafData.module (hc _))

      obtain ⟨ei0⟩ := (hP.pow (D v).toNat).nonempty_pullback_invModule_iso f (hc' _)
      have ei : (Scheme.Modules.pullback f).obj ((P v ^ (D v).toNat).invModule) ≅ (Q v ^ (D v).toNat).invModule :=
        ei0 ≪≫ eqToIso (congrArg Scheme.IdealSheafData.invModule (hc _))
      refine ⟨?_⟩
      change (Scheme.Modules.pullback f).obj ((P v ^ (D v).toNat).invModule ⊗ ((P v ^ (-(D v)).toNat).module ⊗ twistL P D l)) ≅
        (Q v ^ (D v).toNat).invModule ⊗ ((Q v ^ (-(D v)).toNat).module ⊗ twistL Q D l)
      exact Scheme.Modules.pullbackTensorObjIso f _ _ ≪≫
        (ei ⊗ᵢ (Scheme.Modules.pullbackTensorObjIso f _ _ ≪≫ (em ⊗ᵢ e)))

open Classical in
theorem Jp_toList_eq (P : V → Y.IdealSheafData) (D : V →₀ ℤ) (s : Finset V) (hs : D.support ⊆ s) :
    Jp P D D.support.toList = ∏ v ∈ s, P v ^ (D v).toNat := by
  rw [Jp, Finset.prod_map_toList]
  refine Finset.prod_subset hs (fun v _ hv => ?_)
  rw [Finsupp.notMem_support_iff.mp hv]; simp

open Classical in
theorem Jn_toList_eq (P : V → Y.IdealSheafData) (D : V →₀ ℤ) (s : Finset V) (hs : D.support ⊆ s) :
    Jn P D D.support.toList = ∏ v ∈ s, P v ^ (-(D v)).toNat := by
  rw [Jn, Finset.prod_map_toList]
  refine Finset.prod_subset hs (fun v _ hv => ?_)
  rw [Finsupp.notMem_support_iff.mp hv]; simp

abbrev twist (P : V → Y.IdealSheafData) (D : V →₀ ℤ) : Y.Modules := twistL P D D.support.toList

open Classical in
theorem nonempty_twist_add_iso (P : V → Y.IdealSheafData) (D D' : V →₀ ℤ)
    (h : ∀ v ∈ D.support ∪ D'.support, (P v).IsInvertible) :
    Nonempty (twist P (D + D') ≅ twist P D ⊗ twist P D') := by
  set s := D.support ∪ D'.support with hs_def
  have hD : D.support ⊆ s := Finset.subset_union_left
  have hD' : D'.support ⊆ s := Finset.subset_union_right
  have hDD' : (D + D').support ⊆ s := Finsupp.support_add
  have hinv : ∀ (E : V →₀ ℤ), E.support ⊆ s → ∀ v ∈ E.support.toList, (P v).IsInvertible :=
    fun E hE v hv => h v (hE (Finset.mem_toList.mp hv))
  have hPs : ∀ (g : V → ℕ), (∏ v ∈ s, P v ^ g v).IsInvertible :=
    fun g => IsInvertible.finsetProd _ s (fun v hv => (h v hv).pow _)
  obtain ⟨e⟩ := nonempty_twistL_iso_pf P (⇑(D + D')) (D + D').support.toList (hinv _ hDD')
  obtain ⟨e₁⟩ := nonempty_twistL_iso_pf P D D.support.toList (hinv _ hD)
  obtain ⟨e₂⟩ := nonempty_twistL_iso_pf P D' D'.support.toList (hinv _ hD')
  rw [Jp_toList_eq P _ s hDD', Jn_toList_eq P _ s hDD'] at e
  rw [Jp_toList_eq P _ s hD, Jn_toList_eq P _ s hD] at e₁
  rw [Jp_toList_eq P _ s hD', Jn_toList_eq P _ s hD'] at e₂

  have key : (∏ v ∈ s, P v ^ ((D + D') v).toNat) * ((∏ v ∈ s, P v ^ (-(D v)).toNat) * ∏ v ∈ s, P v ^ (-(D' v)).toNat) =
      ((∏ v ∈ s, P v ^ (D v).toNat) * ∏ v ∈ s, P v ^ (D' v).toNat) * ∏ v ∈ s, P v ^ (-((D + D') v)).toNat := by
    simp only [← Finset.prod_mul_distrib, ← pow_add]
    refine Finset.prod_congr rfl (fun v _ => ?_)
    congr 1
    simp only [Finsupp.coe_add, Pi.add_apply]
    omega
  obtain ⟨c⟩ := nonempty_pf_congr (hPs _) ((hPs _).mul (hPs _)) (hPs _) ((hPs _).mul (hPs _)) key
  obtain ⟨m⟩ := nonempty_pf_mul_iso (hPs fun v => (D v).toNat) (hPs fun v => (D' v).toNat)
    (hPs fun v => (-(D v)).toNat) (hPs fun v => (-(D' v)).toNat)
  exact ⟨e ≪≫ c ≪≫ m ≪≫ (e₁.symm ⊗ᵢ e₂.symm)⟩

theorem twist_zero (P : V → Y.IdealSheafData) : twist P (0 : V →₀ ℤ) = 𝟙_ Y.Modules := by
  simp [twist, twistL]

theorem isInvertible_twist (P : V → Y.IdealSheafData) (D : V →₀ ℤ) (h : ∀ v ∈ D.support, (P v).IsInvertible) :
    Scheme.Modules.IsInvertible (twist P D) :=
  isInvertible_twistL P D _ (fun v hv => h v (Finset.mem_toList.mp hv))

open Classical in
theorem nonempty_twist_single_sub_single_iso (P : V → Y.IdealSheafData) (u w : V)
    (hu : (P u).IsInvertible) (hw : (P w).IsInvertible) :
    Nonempty (twist P (Finsupp.single u 1 - Finsupp.single w 1) ≅ (P u).invModule ⊗ (P w).module) := by
  set D : V →₀ ℤ := Finsupp.single u 1 - Finsupp.single w 1 with hD
  have hsupp : D.support ⊆ {u, w} := by
    intro v hv
    have h := Finsupp.support_sub hv
    simp only [Finset.mem_union] at h
    rcases h with h | h
    · have := Finsupp.support_single_subset h; simp_all
    · have := Finsupp.support_single_subset h; simp_all
  have hinv : ∀ v ∈ D.support.toList, (P v).IsInvertible := by
    intro v hv
    have := hsupp (Finset.mem_toList.mp hv)
    simp only [Finset.mem_insert, Finset.mem_singleton] at this
    rcases this with rfl | rfl <;> assumption
  have hPs : ∀ (g : V → ℕ), (∏ v ∈ ({u, w} : Finset V), P v ^ g v).IsInvertible := by
    intro g
    refine IsInvertible.finsetProd _ _ (fun v hv => ?_)
    simp only [Finset.mem_insert, Finset.mem_singleton] at hv
    rcases hv with rfl | rfl <;> exact IsInvertible.pow ‹_› _
  obtain ⟨e⟩ := nonempty_twistL_iso_pf P (⇑D) D.support.toList hinv
  rw [Jp_toList_eq P D {u, w} hsupp, Jn_toList_eq P D {u, w} hsupp] at e

  have key : (∏ v ∈ ({u, w} : Finset V), P v ^ (D v).toNat) * P w = P u * ∏ v ∈ ({u, w} : Finset V), P v ^ (-(D v)).toNat := by
    by_cases huw : u = w
    · subst huw
      simp [hD]
    · rw [Finset.prod_pair huw, Finset.prod_pair huw]
      simp [hD, Finsupp.single_apply, huw, Ne.symm huw]
  obtain ⟨c⟩ := nonempty_pf_congr (hPs _) hu (hPs _) hw key
  exact ⟨e ≪≫ c⟩

end EPkgTwist
p2m_reactivate "P2MW.S_AlgebraicGeometry_RelPicard_isNodeUnitModule_foldr_ofPoint_of_forall_eq_ord_of_hasValue.EPkgTwist"

namespace EPkgTwist

p2m_open "AlgebraicGeometry.Scheme.IdealSheafData CategoryTheory.MonoidalClosed"

variable {Y : Scheme.{u}}

theorem unitToPushforwardUnit_subschemeι_top_eq_zero :
    (⊤ : Y.IdealSheafData).subschemeι.unitToPushforwardUnit = 0 := by
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro U
  have hU : (TopologicalSpace.Opens.map (⊤ : Y.IdealSheafData).subschemeι.base).obj U.unop = ⊥ :=
    SetLike.ext' (Set.eq_empty_of_isEmpty _)
  haveI : Subsingleton Γ((⊤ : Y.IdealSheafData).subscheme, (TopologicalSpace.Opens.map (⊤ : Y.IdealSheafData).subschemeι.base).obj U.unop) :=
    CommRingCat.subsingleton_of_isTerminal ((⊤ : Y.IdealSheafData).subscheme.sheaf.isTerminalOfEqEmpty hU)
  ext
  exact Subsingleton.elim (α := Γ((⊤ : Y.IdealSheafData).subscheme, (TopologicalSpace.Opens.map (⊤ : Y.IdealSheafData).subschemeι.base).obj U.unop)) _ _

def moduleTopInv : (SheafOfModules.unit Y.ringCatSheaf : SheafOfModules Y.ringCatSheaf) ⟶
    kernel (⊤ : Y.IdealSheafData).subschemeι.unitToPushforwardUnit :=
  kernel.lift _ (𝟙 _) (by rw [unitToPushforwardUnit_subschemeι_top_eq_zero, comp_zero])

theorem moduleι_moduleTopInv :
    ((⊤ : Y.IdealSheafData).moduleι ≫ moduleTopInv : (kernel (⊤ : Y.IdealSheafData).subschemeι.unitToPushforwardUnit : SheafOfModules Y.ringCatSheaf) ⟶ _) = 𝟙 _ := by
  rw [← cancel_mono (kernel.ι ((⊤ : Y.IdealSheafData).subschemeι.unitToPushforwardUnit)), Category.assoc]
  change _ ≫ kernel.lift _ _ _ ≫ kernel.ι _ = _
  rw [kernel.lift_ι, Category.id_comp]
  exact (Category.comp_id _).symm

theorem moduleTopInv_moduleι :
    (moduleTopInv ≫ (⊤ : Y.IdealSheafData).moduleι : (SheafOfModules.unit Y.ringCatSheaf : SheafOfModules Y.ringCatSheaf) ⟶ _) = 𝟙 _ :=
  kernel.lift_ι _ _ _

def moduleTopIso : (⊤ : Y.IdealSheafData).module ≅ 𝟙_ Y.Modules where
  hom := (⊤ : Y.IdealSheafData).moduleι
  inv := moduleTopInv
  hom_inv_id := moduleι_moduleTopInv
  inv_hom_id := moduleTopInv_moduleι

theorem moduleTopIso_hom : (moduleTopIso (Y := Y)).hom = (⊤ : Y.IdealSheafData).moduleι := rfl

def preIso {A B : Y.Modules} (e : A ≅ B) : ihom B ≅ ihom A where
  hom := MonoidalClosed.pre e.hom
  inv := MonoidalClosed.pre e.inv
  hom_inv_id := by rw [← MonoidalClosed.pre_map, Iso.inv_hom_id, MonoidalClosed.pre_id]
  inv_hom_id := by rw [← MonoidalClosed.pre_map, Iso.hom_inv_id, MonoidalClosed.pre_id]

def invModuleTopIso : (⊤ : Y.IdealSheafData).invModule ≅ 𝟙_ Y.Modules :=
  (preIso (moduleTopIso (Y := Y)).symm).app (𝟙_ Y.Modules) ≪≫ MonoidalClosed.unitIsoSelf (𝟙_ Y.Modules)

theorem top_pow (n : ℕ) : (⊤ : Y.IdealSheafData) ^ n = ⊤ := by
  rw [← one_eq_top, one_pow]

variable {V : Type v}

def twistLTopIso (D : V → ℤ) : (l : List V) → (twistL (fun _ => (⊤ : Y.IdealSheafData)) D l ≅ 𝟙_ Y.Modules)
  | [] => Iso.refl _
  | (v :: l) =>
      ((eqToIso (congrArg Scheme.IdealSheafData.invModule (top_pow (Y := Y) (D v).toNat)) ≪≫ invModuleTopIso) ⊗ᵢ
        ((eqToIso (congrArg Scheme.IdealSheafData.module (top_pow (Y := Y) (-(D v)).toNat)) ≪≫ moduleTopIso) ⊗ᵢ
          twistLTopIso D l)) ≪≫
      whiskerLeftIso _ (λ_ _) ≪≫ λ_ _

variable {Y' : Scheme.{u}} (f : Y' ⟶ Y)

def dualComparison {A : Y.Modules} {B : Y'.Modules} (c : B ⟶ (Scheme.Modules.pullback f).obj A) :
    (Scheme.Modules.pullback f).obj (Scheme.Modules.dual A) ⟶ Scheme.Modules.dual B :=
  MonoidalClosed.curry
    (c ▷ _ ≫ (Functor.Monoidal.μIso (Scheme.Modules.pullback f) A (Scheme.Modules.dual A)).hom ≫
      (Scheme.Modules.pullback f).map ((ihom.ev A).app (𝟙_ Y.Modules)) ≫ (Scheme.Modules.pullbackTensorUnitObjIso f).hom)

theorem whiskerLeft_dualComparison_ev {A : Y.Modules} {B : Y'.Modules} (c : B ⟶ (Scheme.Modules.pullback f).obj A) :
    B ◁ dualComparison f c ≫ (ihom.ev B).app (𝟙_ _) =
      c ▷ _ ≫ (Functor.Monoidal.μIso (Scheme.Modules.pullback f) A (Scheme.Modules.dual A)).hom ≫
        (Scheme.Modules.pullback f).map ((ihom.ev A).app (𝟙_ Y.Modules)) ≫ (Scheme.Modules.pullbackTensorUnitObjIso f).hom := by
  rw [dualComparison, ← MonoidalClosed.uncurry_eq, MonoidalClosed.uncurry_curry]

end EPkgTwist
p2m_reactivate "P2MW.S_AlgebraicGeometry_RelPicard_isNodeUnitModule_foldr_ofPoint_of_forall_eq_ord_of_hasValue.EPkgTwist"

namespace EPkgTwist

p2m_open "AlgebraicGeometry.Scheme.IdealSheafData CategoryTheory.MonoidalClosed"

section Reflect

variable {C : Type*} [Category C] [MonoidalCategory C]

theorem isIso_of_isIso_whiskerLeft {B B' Y Z : C} (e : B' ⊗ B ≅ 𝟙_ C) (g : Y ⟶ Z) [IsIso (B ◁ g)] : IsIso g := by
  have h1 : IsIso ((B' ⊗ B) ◁ g) := by
    rw [MonoidalCategory.tensor_whiskerLeft]; infer_instance
  have h2 : IsIso (𝟙_ C ◁ g) := by
    have : 𝟙_ C ◁ g = e.inv ▷ Y ≫ (B' ⊗ B) ◁ g ≫ e.hom ▷ Z := by
      rw [MonoidalCategory.whisker_exchange, ← Category.assoc, ← MonoidalCategory.comp_whiskerRight,
        Iso.inv_hom_id, MonoidalCategory.id_whiskerRight, Category.id_comp]
    rw [this]; infer_instance
  have h3 : g = (λ_ Y).inv ≫ 𝟙_ C ◁ g ≫ (λ_ Z).hom := by
    rw [MonoidalCategory.id_whiskerLeft, Category.assoc, Category.assoc, Iso.inv_hom_id, Category.comp_id,
      Iso.inv_hom_id_assoc]
  rw [h3]; infer_instance

end Reflect
p2m_reactivate "P2MW.S_AlgebraicGeometry_RelPicard_isNodeUnitModule_foldr_ofPoint_of_forall_eq_ord_of_hasValue.EPkgTwist"

variable {Y Y' : Scheme.{u}} (f : Y' ⟶ Y)

theorem isIso_dualComparison {A : Y.Modules} {B : Y'.Modules} (hA : Scheme.Modules.IsInvertible A)
    (hB : Scheme.Modules.IsInvertible B) (c : B ⟶ (Scheme.Modules.pullback f).obj A) (hc : IsIso c) :
    IsIso (dualComparison f c) := by

  have hevA : IsIso ((ihom.ev A).app (𝟙_ Y.Modules)) := (hA.isIso_ev_app_and_isIso_curry_braiding_ev).1 _
  let evA : A ⊗ Scheme.Modules.dual A ≅ 𝟙_ Y.Modules := @asIso _ _ _ _ ((ihom.ev A).app (𝟙_ Y.Modules)) hevA
  let u : B ⊗ (Scheme.Modules.pullback f).obj (Scheme.Modules.dual A) ≅ 𝟙_ Y'.Modules :=
    whiskerRightIso (@asIso _ _ _ _ c hc) _ ≪≫ Functor.Monoidal.μIso (Scheme.Modules.pullback f) A (Scheme.Modules.dual A) ≪≫
      (Scheme.Modules.pullback f).mapIso evA ≪≫ Scheme.Modules.pullbackTensorUnitObjIso f
  have hu : u.hom = c ▷ _ ≫ (Functor.Monoidal.μIso (Scheme.Modules.pullback f) A (Scheme.Modules.dual A)).hom ≫
      (Scheme.Modules.pullback f).map ((ihom.ev A).app (𝟙_ Y.Modules)) ≫ (Scheme.Modules.pullbackTensorUnitObjIso f).hom := rfl

  have hevB : IsIso ((ihom.ev B).app (𝟙_ Y'.Modules)) := hB.isIso_ev_app_tensorUnit
  let evB : B ⊗ Scheme.Modules.dual B ≅ 𝟙_ Y'.Modules := @asIso _ _ _ _ ((ihom.ev B).app (𝟙_ Y'.Modules)) hevB
  have hk : B ◁ (dualComparison f c) = u.hom ≫ evB.inv := by
    rw [Iso.eq_comp_inv, hu]
    exact whiskerLeft_dualComparison_ev f c
  haveI hk' : IsIso (B ◁ (dualComparison f c)) := by rw [hk]; infer_instance
  obtain ⟨B', -, ⟨e⟩⟩ := hB.exists_tensor_inverse
  exact isIso_of_isIso_whiskerLeft ((β_ _ _) ≪≫ e) _

def moduleComparisonIso (I : Y.IdealSheafData) (hI : I.IsInvertible) (hI' : (I.comap f).IsInvertible) :
    (Scheme.Modules.pullback f).obj I.module ≅ (I.comap f).module :=
  haveI := hI.isIso_pullbackModuleComparison f hI'
  asIso (I.pullbackModuleComparison f)

@[scoped simp] theorem moduleComparisonIso_hom (I : Y.IdealSheafData) (hI : I.IsInvertible) (hI' : (I.comap f).IsInvertible) :
    (moduleComparisonIso f I hI hI').hom = I.pullbackModuleComparison f := rfl

def invModuleComparisonIso (I : Y.IdealSheafData) (hI : I.IsInvertible) (hI' : (I.comap f).IsInvertible) :
    (Scheme.Modules.pullback f).obj I.invModule ≅ (I.comap f).invModule :=
  @asIso _ _ _ _ (dualComparison f (moduleComparisonIso f I hI hI').inv)
    (isIso_dualComparison f hI.isInvertible_module hI'.isInvertible_module (moduleComparisonIso f I hI hI').inv inferInstance)

@[scoped simp] theorem invModuleComparisonIso_hom (I : Y.IdealSheafData) (hI : I.IsInvertible) (hI' : (I.comap f).IsInvertible) :
    (invModuleComparisonIso f I hI hI').hom = dualComparison f (moduleComparisonIso f I hI hI').inv := rfl

variable {V : Type v}

def twistLComparisonIso (P : V → Y.IdealSheafData) (Q : V → Y'.IdealSheafData) (D : V → ℤ) :
    (l : List V) → (∀ v ∈ l, (P v).IsInvertible ∧ (P v).comap f = Q v ∧ (Q v).IsInvertible) →
      ((Scheme.Modules.pullback f).obj (twistL P D l) ≅ twistL Q D l)
  | [], _ => Scheme.Modules.pullbackTensorUnitObjIso f
  | (v :: l), h =>
      have hP : (P v).IsInvertible := (h v (List.mem_cons_self)).1
      have hcv : ∀ n : ℕ, (P v ^ n).comap f = Q v ^ n := fun n => by rw [comap_pow, (h v (List.mem_cons_self)).2.1]
      have hPc : ∀ n : ℕ, ((P v ^ n).comap f).IsInvertible := fun n => by rw [hcv]; exact (h v (List.mem_cons_self)).2.2.pow n
      Scheme.Modules.pullbackTensorObjIso f _ _ ≪≫
        ((invModuleComparisonIso f (P v ^ (D v).toNat) (hP.pow _) (hPc _) ≪≫
            eqToIso (congrArg Scheme.IdealSheafData.invModule (hcv _))) ⊗ᵢ
          (Scheme.Modules.pullbackTensorObjIso f _ _ ≪≫
            ((moduleComparisonIso f (P v ^ (-(D v)).toNat) (hP.pow _) (hPc _) ≪≫
                eqToIso (congrArg Scheme.IdealSheafData.module (hcv _))) ⊗ᵢ
              twistLComparisonIso P Q D l (fun w hw => h w (List.mem_cons_of_mem v hw)))))

end EPkgTwist
p2m_reactivate "P2MW.S_AlgebraicGeometry_RelPicard_isNodeUnitModule_foldr_ofPoint_of_forall_eq_ord_of_hasValue.EPkgTwist"

namespace EPkgTwist

p2m_open "AlgebraicGeometry.Scheme.IdealSheafData AlgebraicGeometry.Scheme.Modules TopologicalSpace"

variable {Y : Scheme.{u}}

def oneInv (I : Y.IdealSheafData) (W : Y.Opens) : Γ(I.invModule, W) :=
  I.invModuleSection.app W (unitSection W)

theorem oneInv_def (I : Y.IdealSheafData) (W : Y.Opens) : oneInv I W = I.invModuleSection.app W (unitSection W) := rfl

theorem map_oneInv (I : Y.IdealSheafData) {W W' : Y.Opens} (i : W' ⟶ W) :
    I.invModule.presheaf.map i.op (oneInv I W) = oneInv I W' := by
  have h := (I.invModuleSection.mapPresheaf).naturality i.op
  have h' := congrFun (congrArg (fun f => (ConcreteCategory.hom f : Γ(𝟙_ Y.Modules, W) → Γ(I.invModule, W'))) h) (unitSection W)
  simp only [CategoryTheory.comp_apply] at h'
  rw [oneInv, oneInv, ← map_unitSection i]
  exact h'.symm

section OneMod

variable (I : Y.IdealSheafData) (W : Y.Opens)

abbrev evW : SheafOfModules Y.ringCatSheaf ⥤ ModuleCat (Y.ringCatSheaf.val.obj (Opposite.op W)) :=
  SheafOfModules.evaluation Y.ringCatSheaf (Opposite.op W)

scoped instance : (evW (Y := Y) W).PreservesZeroMorphisms := ⟨fun _ _ => rfl⟩

theorem preimage_subschemeι_eq_bot (hW : I.comap W.ι = ⊤) : (Opens.map I.subschemeι.base).obj W = ⊥ := by
  have hs : (I.comap W.ι).support = ⊥ := (support_eq_bot_iff _).mpr hW
  rw [support_comap] at hs
  apply SetLike.ext'
  simp only [Opens.map_coe, Opens.coe_bot]
  refine Set.eq_empty_iff_forall_notMem.mpr (fun z hz => ?_)
  have hzI : I.subschemeι.base z ∈ (I.support : Set Y) := by
    rw [← range_subschemeι]; exact ⟨z, rfl⟩
  have hmem : (⟨I.subschemeι.base z, hz⟩ : W) ∈ ((⊥ : TopologicalSpace.Closeds W) : Set W) := by
    rw [← hs]; exact hzI
  exact hmem

theorem evW_map_unitToPushforwardUnit_eq_zero (hW : I.comap W.ι = ⊤) :
    (evW W).map I.subschemeι.unitToPushforwardUnit = 0 := by
  have hU := preimage_subschemeι_eq_bot I W hW
  haveI : Subsingleton Γ(I.subscheme, (Opens.map I.subschemeι.base).obj W) :=
    CommRingCat.subsingleton_of_isTerminal (I.subscheme.sheaf.isTerminalOfEqEmpty hU)
  ext
  exact Subsingleton.elim (α := Γ(I.subscheme, (Opens.map I.subschemeι.base).obj W)) _ _

def moduleSectionsIso :
    (evW W).obj (kernel I.subschemeι.unitToPushforwardUnit) ≅
      ModuleCat.of _ (LinearMap.ker ((evW W).map I.subschemeι.unitToPushforwardUnit).hom) :=
  PreservesKernel.iso (evW W) I.subschemeι.unitToPushforwardUnit ≪≫ ModuleCat.kernelIsoKer _

theorem moduleSectionsIso_inv_ι :
    (moduleSectionsIso I W).inv ≫ (evW W).map (kernel.ι I.subschemeι.unitToPushforwardUnit) =
      ModuleCat.ofHom (LinearMap.ker ((evW W).map I.subschemeι.unitToPushforwardUnit).hom).subtype := by
  rw [moduleSectionsIso, Iso.trans_inv, Category.assoc, PreservesKernel.iso_inv_ι, ModuleCat.kernelIsoKer_inv_kernel_ι]

theorem map_kernelι_eq :
    (evW W).map (kernel.ι I.subschemeι.unitToPushforwardUnit) =
      (moduleSectionsIso I W).hom ≫ ModuleCat.ofHom (LinearMap.ker ((evW W).map I.subschemeι.unitToPushforwardUnit).hom).subtype := by
  rw [← moduleSectionsIso_inv_ι, Iso.hom_inv_id_assoc]

theorem moduleι_app_eq (m : Γ(I.module, W)) :
    I.moduleι.app W m = ((evW W).map (kernel.ι I.subschemeι.unitToPushforwardUnit)).hom m := rfl

theorem moduleι_app_injective : Function.Injective (I.moduleι.app W) := by
  intro m m' h
  rw [moduleι_app_eq, moduleι_app_eq, map_kernelι_eq] at h
  have h' : (moduleSectionsIso I W).hom.hom m = (moduleSectionsIso I W).hom.hom m' := Subtype.ext h
  have h'' := congrArg ((moduleSectionsIso I W).inv.hom) h'
  have e1 : (moduleSectionsIso I W).inv.hom ((moduleSectionsIso I W).hom.hom m) = m :=
    congrFun (congrArg (fun φ => (ModuleCat.Hom.hom φ : _ → _)) (moduleSectionsIso I W).hom_inv_id) m
  have e2 : (moduleSectionsIso I W).inv.hom ((moduleSectionsIso I W).hom.hom m') = m' :=
    congrFun (congrArg (fun φ => (ModuleCat.Hom.hom φ : _ → _)) (moduleSectionsIso I W).hom_inv_id) m'
  rw [e1, e2] at h''
  exact h''

theorem existsUnique_oneMod (hW : I.comap W.ι = ⊤) :
    ∃! m : Γ(I.module, W), I.moduleι.app W m = unitSection W := by
  have h0 := evW_map_unitToPushforwardUnit_eq_zero I W hW
  let one : LinearMap.ker ((evW W).map I.subschemeι.unitToPushforwardUnit).hom :=
    ⟨(1 : Γ(Y, W)), by rw [LinearMap.mem_ker, h0]; rfl⟩
  have key : I.moduleι.app W ((moduleSectionsIso I W).inv.hom one) = unitSection W := by
    rw [moduleι_app_eq]
    exact congrArg (fun φ => (ConcreteCategory.hom φ) one) (moduleSectionsIso_inv_ι I W)
  exact ⟨(moduleSectionsIso I W).inv.hom one, key, fun m hm => moduleι_app_injective I W (hm.trans key.symm)⟩

variable {I W}

def oneMod (hW : I.comap W.ι = ⊤) : Γ(I.module, W) := (existsUnique_oneMod I W hW).exists.choose

@[scoped simp] theorem moduleι_oneMod (hW : I.comap W.ι = ⊤) : I.moduleι.app W (oneMod hW) = unitSection W :=
  (existsUnique_oneMod I W hW).exists.choose_spec

theorem eq_oneMod_of_moduleι_eq (hW : I.comap W.ι = ⊤) {m : Γ(I.module, W)} (h : I.moduleι.app W m = unitSection W) :
    m = oneMod hW :=
  (existsUnique_oneMod I W hW).unique h (moduleι_oneMod hW)

theorem comap_ι_eq_top_of_le (hW : I.comap W.ι = ⊤) {W' : Y.Opens} (h : W' ≤ W) : I.comap W'.ι = ⊤ := by
  have : W'.ι = Y.homOfLE h ≫ W.ι := (Y.homOfLE_ι h).symm
  rw [this, Scheme.IdealSheafData.comap_comp, hW, Scheme.IdealSheafData.comap_top]

theorem map_oneMod (hW : I.comap W.ι = ⊤) {W' : Y.Opens} (i : W' ⟶ W) (hW' : I.comap W'.ι = ⊤) :
    I.module.presheaf.map i.op (oneMod hW) = oneMod hW' := by
  apply eq_oneMod_of_moduleι_eq
  have hn := (I.moduleι.mapPresheaf).naturality i.op
  have hn' := congrFun (congrArg (fun f => (ConcreteCategory.hom f : Γ(I.module, W) → Γ(𝟙_ Y.Modules, W'))) hn) (oneMod hW)
  simp only [CategoryTheory.comp_apply] at hn'
  change (I.moduleι.mapPresheaf.app (Opposite.op W')) (I.module.presheaf.map i.op (oneMod hW)) = unitSection W'
  rw [hn']
  change (𝟙_ Y.Modules).presheaf.map i.op (I.moduleι.app W (oneMod hW)) = _
  rw [moduleι_oneMod, map_unitSection]

end OneMod
p2m_reactivate "P2MW.S_AlgebraicGeometry_RelPicard_isNodeUnitModule_foldr_ofPoint_of_forall_eq_ord_of_hasValue.EPkgTwist"

end EPkgTwist
p2m_reactivate "P2MW.S_AlgebraicGeometry_RelPicard_isNodeUnitModule_foldr_ofPoint_of_forall_eq_ord_of_hasValue.EPkgTwist"

namespace EPkgTwist

p2m_open "AlgebraicGeometry.Scheme.IdealSheafData AlgebraicGeometry.Scheme.Modules TopologicalSpace"

variable {Y : Scheme.{u}}

theorem isFrameOn_oneMod {I : Y.IdealSheafData} {W : Y.Opens} (hW : I.comap W.ι = ⊤) : IsFrameOn (oneMod hW) W := by
  intro W' hW'W _
  have hW' := comap_ι_eq_top_of_le hW hW'W
  have hres : I.module.presheaf.map (homOfLE hW'W).op (oneMod hW) = oneMod hW' := map_oneMod hW (homOfLE hW'W) hW'
  simp only [hres]
  constructor
  · intro g g' h
    have h' := congrArg (I.moduleι.app W') h
    simp only [Scheme.Modules.Hom.app_smul, moduleι_oneMod, smul_unitSection] at h'
    exact h'
  · intro m
    refine ⟨ofUnitSection W' (I.moduleι.app W' m), moduleι_app_injective I W' ?_⟩
    rw [Scheme.Modules.Hom.app_smul, moduleι_oneMod, smul_unitSection]
    rfl

theorem support_inter_eq_empty_of_comap_ι_eq_top {I : Y.IdealSheafData} {W : Y.Opens} (hW : I.comap W.ι = ⊤) :
    Disjoint (W : Set Y) (I.support : Set Y) := by
  have hs : (I.comap W.ι).support = ⊥ := (support_eq_bot_iff _).mpr hW
  rw [support_comap] at hs
  rw [Set.disjoint_left]
  intro y hyW hyI
  have hmem : (⟨y, hyW⟩ : W) ∈ ((⊥ : TopologicalSpace.Closeds W) : Set W) := by
    rw [← hs]; exact hyI
  exact hmem

theorem isFrameOn_oneInv {I : Y.IdealSheafData} (hI : I.IsInvertible) {W : Y.Opens} (hW : I.comap W.ι = ⊤) :
    IsFrameOn (oneInv I W) W := by
  have h := hI.isInvertible_invModule.isFrameOn_app_of_disjoint_support_zeroSchemeIdeal I.invModuleSection W
    (by rw [hI.zeroSchemeIdeal_invModuleSection]; exact support_inter_eq_empty_of_comap_ι_eq_top hW)
  have := h.map (homOfLE (le_top : W ≤ ⊤))
  rw [show I.invModule.presheaf.map (homOfLE (le_top : W ≤ ⊤)).op (I.invModuleSection.app ⊤ (toUnitSection ⊤ 1)) = oneInv I W from
    map_oneInv I (homOfLE (le_top : W ≤ ⊤))] at this
  exact this

variable {V : Type v}

theorem comap_pow_eq_top {I : Y.IdealSheafData} {W : Y.Opens} (hW : I.comap W.ι = ⊤) (n : ℕ) : (I ^ n).comap W.ι = ⊤ := by
  rw [comap_pow, hW, top_pow]

def eCan (P : V → Y.IdealSheafData) (D : V → ℤ) :
    (l : List V) → (W : Y.Opens) → (∀ v ∈ l, (P v).comap W.ι = ⊤) → Γ(twistL P D l, W)
  | [], W, _ => unitSection W
  | (v :: l), W, h =>
      tensorSections (oneInv (P v ^ (D v).toNat) W)
        (tensorSections (oneMod (comap_pow_eq_top (h v List.mem_cons_self) (-(D v)).toNat))
          (eCan P D l W (fun w hw => h w (List.mem_cons_of_mem v hw))))

theorem eCan_nil (P : V → Y.IdealSheafData) (D : V → ℤ) (W : Y.Opens) (h : ∀ v ∈ ([] : List V), (P v).comap W.ι = ⊤) :
    eCan P D [] W h = unitSection W := rfl

theorem eCan_cons (P : V → Y.IdealSheafData) (D : V → ℤ) (v : V) (l : List V) (W : Y.Opens)
    (h : ∀ w ∈ v :: l, (P w).comap W.ι = ⊤) :
    eCan P D (v :: l) W h = tensorSections (oneInv (P v ^ (D v).toNat) W)
        (tensorSections (oneMod (comap_pow_eq_top (h v List.mem_cons_self) (-(D v)).toNat))
          (eCan P D l W (fun w hw => h w (List.mem_cons_of_mem v hw)))) := rfl

theorem map_eCan (P : V → Y.IdealSheafData) (D : V → ℤ) :
    ∀ (l : List V) {W W' : Y.Opens} (i : W' ⟶ W) (h : ∀ v ∈ l, (P v).comap W.ι = ⊤) (h' : ∀ v ∈ l, (P v).comap W'.ι = ⊤),
      (twistL P D l).presheaf.map i.op (eCan P D l W h) = eCan P D l W' h'
  | [], W, W', i, _, _ => map_unitSection i
  | (v :: l), W, W', i, h, h' => by
      rw [eCan_cons, eCan_cons]
      change ((P v ^ (D v).toNat).invModule ⊗ ((P v ^ (-(D v)).toNat).module ⊗ twistL P D l)).presheaf.map i.op _ = _
      rw [map_tensorSections, map_oneInv]
      congr 1
      change ((P v ^ (-(D v)).toNat).module ⊗ twistL P D l).presheaf.map i.op _ = _
      rw [map_tensorSections, map_oneMod _ i, map_eCan P D l i]

theorem isFrameOn_eCan (P : V → Y.IdealSheafData) (D : V → ℤ) :
    ∀ (l : List V) (W : Y.Opens) (h : ∀ v ∈ l, (P v).comap W.ι = ⊤), (∀ v ∈ l, (P v).IsInvertible) →
      IsFrameOn (eCan P D l W h) W
  | [], W, _, _ => isFrameOn_unitSection W
  | (v :: l), W, h, hinv => by
      rw [eCan_cons]
      exact (isFrameOn_oneInv ((hinv v List.mem_cons_self).pow _) (comap_pow_eq_top (h v List.mem_cons_self) _)).tensorSections
        ((isFrameOn_oneMod _).tensorSections
          (isFrameOn_eCan P D l W _ (fun w hw => hinv w (List.mem_cons_of_mem v hw))))

theorem eqToHom_invModule_app_oneInv {I J : Y.IdealSheafData} (e : I = J) (W : Y.Opens) :
    (eqToHom (congrArg Scheme.IdealSheafData.invModule e)).app W (oneInv I W) = oneInv J W := by
  subst e; rfl

theorem eqToHom_module_app_oneMod {I J : Y.IdealSheafData} (e : I = J) {W : Y.Opens} (hI : I.comap W.ι = ⊤) (hJ : J.comap W.ι = ⊤) :
    (eqToHom (congrArg Scheme.IdealSheafData.module e)).app W (oneMod hI) = oneMod hJ := by
  subst e; rfl

theorem invModuleTopIso_hom_app_oneInv (W : Y.Opens) :
    (invModuleTopIso (Y := Y)).hom.app W (oneInv ⊤ W) = unitSection W := by
  rw [invModuleTopIso, Iso.trans_hom, Scheme.Modules.Hom.comp_app, CategoryTheory.comp_apply]
  change (MonoidalClosed.unitIsoSelf (𝟙_ Y.Modules)).hom.app W
    ((MonoidalClosed.pre (moduleTopIso (Y := Y)).inv).app (𝟙_ Y.Modules) |>.app W (oneInv ⊤ W)) = _
  rw [unitIsoSelf_hom_app, ihomEval_pre_app, oneInv_def, Scheme.IdealSheafData.invModuleSection, MonoidalClosed.curry']
  erw [ihomEval_curry_app]
  rw [Scheme.Modules.Hom.comp_app, CategoryTheory.comp_apply]
  erw [rightUnitor_hom_app_tensorSections]
  erw [Scheme.Modules.Hom.app_smul]
  have h1 : (⊤ : Y.IdealSheafData).moduleι.app W ((moduleTopIso (Y := Y)).inv.app W (unitSection W)) = unitSection W := by
    rw [← moduleTopIso_hom, ← CategoryTheory.comp_apply, ← Scheme.Modules.Hom.comp_app, Iso.inv_hom_id, Scheme.Modules.Hom.id_app,
      CategoryTheory.id_apply]
  erw [h1]
  exact smul_unitSection _

theorem moduleTopIso_hom_app_oneMod {W : Y.Opens} (h : (⊤ : Y.IdealSheafData).comap W.ι = ⊤) :
    (moduleTopIso (Y := Y)).hom.app W (oneMod h) = unitSection W :=
  moduleι_oneMod h

theorem twistLTopIso_cons_hom_app (D : V → ℤ) (v : V) (l : List V) (W : Y.Opens)
    (a : Γ(((⊤ : Y.IdealSheafData) ^ (D v).toNat).invModule, W)) (b : Γ(((⊤ : Y.IdealSheafData) ^ (-(D v)).toNat).module, W))
    (c : Γ(twistL (fun _ => (⊤ : Y.IdealSheafData)) D l, W)) :
    (twistLTopIso (Y := Y) D (v :: l)).hom.app W (tensorSections a (tensorSections b c)) =
      ofUnitSection W (((eqToIso (congrArg Scheme.IdealSheafData.invModule (top_pow (Y := Y) (D v).toNat)) ≪≫ invModuleTopIso).hom.app W a)) •
        (ofUnitSection W (((eqToIso (congrArg Scheme.IdealSheafData.module (top_pow (Y := Y) (-(D v)).toNat)) ≪≫ moduleTopIso).hom.app W b)) •
          (twistLTopIso (Y := Y) D l).hom.app W c) := by
  show (((eqToIso (congrArg Scheme.IdealSheafData.invModule (top_pow (Y := Y) (D v).toNat)) ≪≫ invModuleTopIso) ⊗ᵢ
        ((eqToIso (congrArg Scheme.IdealSheafData.module (top_pow (Y := Y) (-(D v)).toNat)) ≪≫ moduleTopIso) ⊗ᵢ
          twistLTopIso D l)) ≪≫ whiskerLeftIso _ (λ_ _) ≪≫ λ_ _).hom.app W (tensorSections a (tensorSections b c)) = _
  rw [Iso.trans_hom, Iso.trans_hom, Scheme.Modules.Hom.comp_app, Scheme.Modules.Hom.comp_app, CategoryTheory.comp_apply,
    CategoryTheory.comp_apply, tensorIso_hom, tensorIso_hom, tensorHom_app_tensorSections, tensorHom_app_tensorSections,
    whiskerLeftIso_hom, whiskerLeft_app_tensorSections, leftUnitor_hom_app_tensorSections, leftUnitor_hom_app_tensorSections]
  rw [Scheme.Modules.ofUnitSection, Scheme.Modules.ofUnitSection]

theorem twistLTopIso_hom_app_eCan (D : V → ℤ) :
    ∀ (l : List V) (W : Y.Opens) (h : ∀ v ∈ l, ((fun _ => (⊤ : Y.IdealSheafData)) v).comap W.ι = ⊤),
      (twistLTopIso (Y := Y) D l).hom.app W (eCan (fun _ => (⊤ : Y.IdealSheafData)) D l W h) = unitSection W
  | [], W, _ => rfl
  | (v :: l), W, h => by
      rw [eCan_cons]
      refine (twistLTopIso_cons_hom_app D v l W _ _ _).trans ?_
      rw [twistLTopIso_hom_app_eCan D l W, Iso.trans_hom, Iso.trans_hom,
        Scheme.Modules.Hom.comp_app, Scheme.Modules.Hom.comp_app, CategoryTheory.comp_apply, CategoryTheory.comp_apply,
        eqToIso.hom, eqToIso.hom, eqToHom_invModule_app_oneInv (top_pow _), invModuleTopIso_hom_app_oneInv,
        eqToHom_module_app_oneMod (top_pow _) _ (by rw [Scheme.IdealSheafData.comap_top]), moduleTopIso_hom_app_oneMod]
      rw [show ofUnitSection W (unitSection W) = (1 : Γ(Y, W)) from rfl, one_smul, one_smul]

end EPkgTwist
p2m_reactivate "P2MW.S_AlgebraicGeometry_RelPicard_isNodeUnitModule_foldr_ofPoint_of_forall_eq_ord_of_hasValue.EPkgTwist"

end
p2m_reactivate "P2MW.S_AlgebraicGeometry_RelPicard_isNodeUnitModule_foldr_ofPoint_of_forall_eq_ord_of_hasValue.EPkgTwist"

noncomputable section

namespace EPrincI

open IsLocalRing

variable {k : Type u} [Field k] {F F' : Type u} [Field F] [Field F'] [Algebra k F] [Algebra k F']

def vsMapEquiv (τ : F ≃+* F') (A : ValuationSubring F) : ValuationSubring F' :=
  A.comap τ.symm.toRingHom

theorem mem_vsMapEquiv_iff (τ : F ≃+* F') (A : ValuationSubring F) (x : F') :
    x ∈ vsMapEquiv τ A ↔ τ.symm x ∈ A := Iff.rfl

def vsRingEquiv (τ : F ≃+* F') (A : ValuationSubring F) : A ≃+* vsMapEquiv τ A where
  toFun x := ⟨τ x, by rw [mem_vsMapEquiv_iff, RingEquiv.symm_apply_apply]; exact x.2⟩
  invFun y := ⟨τ.symm y, (mem_vsMapEquiv_iff τ A y).mp y.2⟩
  left_inv x := by ext; simp
  right_inv y := by ext; simp
  map_mul' x y := by ext; simp
  map_add' x y := by ext; simp

@[scoped simp]
theorem coe_vsRingEquiv_apply (τ : F ≃+* F') (A : ValuationSubring F) (x : A) :
    ((vsRingEquiv τ A x : vsMapEquiv τ A) : F') = τ x := rfl

theorem vsMapEquiv_ne_top (τ : F ≃+* F') {A : ValuationSubring F} (hA : A ≠ ⊤) :
    vsMapEquiv τ A ≠ ⊤ := by
  intro h
  apply hA
  refine SetLike.ext fun x => ⟨fun _ => ValuationSubring.mem_top x, fun _ => ?_⟩
  have hx : τ x ∈ vsMapEquiv τ A := h ▸ ValuationSubring.mem_top (τ x)
  rwa [mem_vsMapEquiv_iff, RingEquiv.symm_apply_apply] at hx

namespace Place

private def _root_.EPrincI.Place.mapEquiv (τ : F ≃+* F') (hτ : ∀ a : k, τ (algebraMap k F a) = algebraMap k F' a)
    (v : AlgebraicCurve.Place k F) : AlgebraicCurve.Place k F' where
  toValuationSubring := vsMapEquiv τ v.toValuationSubring
  algebraMap_mem' a := by
    rw [mem_vsMapEquiv_iff, ← hτ, RingEquiv.symm_apply_apply]
    exact v.algebraMap_mem' a
  ne_top' := vsMapEquiv_ne_top τ v.ne_top'
  isPrincipalIdealRing' :=
    IsPrincipalIdealRing.of_surjective (vsRingEquiv τ v.toValuationSubring : _ ≃+* _)
      (vsRingEquiv τ v.toValuationSubring).surjective

end Place
p2m_export "EPrincI" "Place.mapEquiv"
theorem Place.mem_mapEquiv_iff (τ : F ≃+* F')
    (hτ : ∀ a : k, τ (algebraMap k F a) = algebraMap k F' a)
    (v : AlgebraicCurve.Place k F) (x : F') :
    x ∈ (Place.mapEquiv τ hτ v).toValuationSubring ↔ τ.symm x ∈ v.toValuationSubring :=
  Iff.rfl

@[scoped simp]
theorem Place.mapEquiv_toValuationSubring (τ : F ≃+* F')
    (hτ : ∀ a : k, τ (algebraMap k F a) = algebraMap k F' a) (v : AlgebraicCurve.Place k F) :
    (Place.mapEquiv τ hτ v).toValuationSubring = vsMapEquiv τ v.toValuationSubring := rfl

p2m_reactivate "P2MW.S_AlgebraicGeometry_RelPicard_isNodeUnitModule_foldr_ofPoint_of_forall_eq_ord_of_hasValue.EPkgTwist P2MW.S_AlgebraicGeometry_RelPicard_isNodeUnitModule_foldr_ofPoint_of_forall_eq_ord_of_hasValue.EPrincI.Place"

def Place.mapEquivRingEquiv (τ : F ≃+* F')
    (hτ : ∀ a : k, τ (algebraMap k F a) = algebraMap k F' a) (v : AlgebraicCurve.Place k F) :
    v.toValuationSubring ≃+* (Place.mapEquiv τ hτ v).toValuationSubring :=
  vsRingEquiv τ v.toValuationSubring

@[scoped simp]
theorem Place.coe_mapEquivRingEquiv_apply (τ : F ≃+* F')
    (hτ : ∀ a : k, τ (algebraMap k F a) = algebraMap k F' a) (v : AlgebraicCurve.Place k F)
    (x : v.toValuationSubring) :
    ((Place.mapEquivRingEquiv τ hτ v x : (Place.mapEquiv τ hτ v).toValuationSubring) : F')
      = τ x := rfl

p2m_reactivate "P2MW.S_AlgebraicGeometry_RelPicard_isNodeUnitModule_foldr_ofPoint_of_forall_eq_ord_of_hasValue.EPkgTwist P2MW.S_AlgebraicGeometry_RelPicard_isNodeUnitModule_foldr_ofPoint_of_forall_eq_ord_of_hasValue.EPrincI.Place"
theorem Place.mapEquivRingEquiv_algebraMap (τ : F ≃+* F')
    (hτ : ∀ a : k, τ (algebraMap k F a) = algebraMap k F' a) (v : AlgebraicCurve.Place k F)
    (a : k) :
    Place.mapEquivRingEquiv τ hτ v (algebraMap k v.toValuationSubring a)
      = algebraMap k (Place.mapEquiv τ hτ v).toValuationSubring a := by
  ext
  rw [Place.coe_mapEquivRingEquiv_apply, AlgebraicCurve.Place.coe_algebraMap,
    AlgebraicCurve.Place.coe_algebraMap, hτ]

theorem Place.ord_mapEquiv (τ : F ≃+* F')
    (hτ : ∀ a : k, τ (algebraMap k F a) = algebraMap k F' a) (v : AlgebraicCurve.Place k F)
    (f : F) : (Place.mapEquiv τ hτ v).ord (τ f) = v.ord f := by
  rcases eq_or_ne f 0 with rfl | hf
  · simp
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible v.toValuationSubring
  obtain ⟨u, hu⟩ := v.exists_unit_mul_zpow hf hπ
  set n := v.ord f with hn
  set e := Place.mapEquivRingEquiv τ hτ v with he
  have hπ' : Irreducible (e π) := (MulEquiv.irreducible_iff e).mpr hπ
  have hu' : IsUnit (e (u : v.toValuationSubring)) := u.isUnit.map e
  have hcoeu : ((hu'.unit : (Place.mapEquiv τ hτ v).toValuationSubring) : F')
      = τ ((u : v.toValuationSubring) : F) := by
    rw [IsUnit.unit_spec]
    rfl
  have hcoeπ : ((e π : (Place.mapEquiv τ hτ v).toValuationSubring) : F') = τ (π : F) := rfl
  have key : τ f = ((hu'.unit : (Place.mapEquiv τ hτ v).toValuationSubring) : F')
      * (((e π : (Place.mapEquiv τ hτ v).toValuationSubring) : F') ^ n) := by
    rw [hcoeu, hcoeπ, hu, map_mul, map_zpow₀]
  rw [key, (Place.mapEquiv τ hτ v).ord_unit_smul_zpow hu'.unit hπ' n]

theorem Place.hasValue_mapEquiv_iff (τ : F ≃+* F')
    (hτ : ∀ a : k, τ (algebraMap k F a) = algebraMap k F' a) (v : AlgebraicCurve.Place k F)
    (f : F) (a : k) : (Place.mapEquiv τ hτ v).HasValue (τ f) a ↔ v.HasValue f a := by
  have hmem : τ f ∈ (Place.mapEquiv τ hτ v).toValuationSubring ↔ f ∈ v.toValuationSubring := by
    rw [Place.mem_mapEquiv_iff, RingEquiv.symm_apply_apply]

  have hη : ∀ x : v.toValuationSubring,
      residue (Place.mapEquiv τ hτ v).toValuationSubring (Place.mapEquivRingEquiv τ hτ v x)
        = IsLocalRing.ResidueField.mapEquiv (Place.mapEquivRingEquiv τ hτ v)
            (residue v.toValuationSubring x) := fun x => by
    rw [IsLocalRing.ResidueField.mapEquiv_apply, IsLocalRing.ResidueField.map_residue]
    try rfl
  have hres : ∀ h : f ∈ v.toValuationSubring,
      residue (Place.mapEquiv τ hτ v).toValuationSubring ⟨τ f, hmem.mpr h⟩
          = algebraMap k (Place.mapEquiv τ hτ v).ResidueField a ↔
        residue v.toValuationSubring ⟨f, h⟩ = algebraMap k v.ResidueField a := fun h => by
    have hx : (⟨τ f, hmem.mpr h⟩ : (Place.mapEquiv τ hτ v).toValuationSubring)
        = Place.mapEquivRingEquiv τ hτ v ⟨f, h⟩ := rfl
    rw [hx, ← (Place.mapEquiv τ hτ v).residue_algebraMap a, ← v.residue_algebraMap a,
      ← Place.mapEquivRingEquiv_algebraMap τ hτ v a, hη, hη,
      (IsLocalRing.ResidueField.mapEquiv _).injective.eq_iff]
  constructor
  · rintro ⟨h, hr⟩
    exact ⟨hmem.mp h, (hres (hmem.mp h)).mp hr⟩
  · rintro ⟨h, hr⟩
    exact ⟨hmem.mpr h, (hres h).mpr hr⟩

theorem CurveModel.range_algebraMap_stalk_eq_mapEquiv (Mdl : AlgebraicCurve.CurveModel k F)
    (y : closedPoints Mdl.C) :
    letI := Mdl.functionFieldAlgebra
    (algebraMap (Mdl.C.presheaf.stalk y.1) Mdl.C.functionField).range =
      (EPrincI.Place.mapEquiv Mdl.ffEquiv Mdl.ffEquiv_algebraMap
        (Mdl.placeOfPoint y)).toValuationSubring.toSubring := by
  letI := Mdl.functionFieldAlgebra
  have h := Mdl.range_stalk_eq y
  ext x
  rw [RingHom.mem_range]
  change _ ↔ x ∈ (EPrincI.Place.mapEquiv Mdl.ffEquiv Mdl.ffEquiv_algebraMap
    (Mdl.placeOfPoint y)).toValuationSubring
  rw [Place.mem_mapEquiv_iff, ← ValuationSubring.mem_toSubring, ← h, RingHom.mem_range]
  constructor
  · rintro ⟨s, rfl⟩
    exact ⟨s, rfl⟩
  · rintro ⟨s, hs⟩
    exact ⟨s, Mdl.ffEquiv.symm.injective hs⟩

end EPrincI
p2m_reactivate "P2MW.S_AlgebraicGeometry_RelPicard_isNodeUnitModule_foldr_ofPoint_of_forall_eq_ord_of_hasValue.EPkgTwist P2MW.S_AlgebraicGeometry_RelPicard_isNodeUnitModule_foldr_ofPoint_of_forall_eq_ord_of_hasValue.EPrincI.Place P2MW.S_AlgebraicGeometry_RelPicard_isNodeUnitModule_foldr_ofPoint_of_forall_eq_ord_of_hasValue.EPrincI"

end
p2m_reactivate "P2MW.S_AlgebraicGeometry_RelPicard_isNodeUnitModule_foldr_ofPoint_of_forall_eq_ord_of_hasValue.EPkgTwist P2MW.S_AlgebraicGeometry_RelPicard_isNodeUnitModule_foldr_ofPoint_of_forall_eq_ord_of_hasValue.EPrincI.Place P2MW.S_AlgebraicGeometry_RelPicard_isNodeUnitModule_foldr_ofPoint_of_forall_eq_ord_of_hasValue.EPrincI"

noncomputable section

namespace BKeyAux

lemma app_map {Y : Scheme.{u}} {N N' : Y.Modules} (φ : N ⟶ N') {W W' : Y.Opens} (i : W' ⟶ W) (n : Γ(N, W)) :
    φ.app W' (N.presheaf.map i.op n) = N'.presheaf.map i.op (φ.app W n) := by
  have h := φ.mapPresheaf.naturality i.op
  exact ConcreteCategory.congr_hom h n

lemma res_res {Y : Scheme.{u}} (N : Y.Modules) {U V W : Y.Opens} (h₁ : V ≤ U) (h₂ : W ≤ V) (s : Γ(N, U)) :
    N.presheaf.map (homOfLE h₂).op (N.presheaf.map (homOfLE h₁).op s) = N.presheaf.map (homOfLE (h₂.trans h₁)).op s := by
  rw [← CategoryTheory.comp_apply, ← Functor.map_comp]
  rfl

lemma res_res' (Y : Scheme.{u}) {U V W : Y.Opens} (h₁ : V ≤ U) (h₂ : W ≤ V) (s : Γ(Y, U)) :
    Y.presheaf.map (homOfLE h₂).op (Y.presheaf.map (homOfLE h₁).op s) = Y.presheaf.map (homOfLE (h₂.trans h₁)).op s := by
  rw [← CategoryTheory.comp_apply, ← Functor.map_comp]
  rfl

lemma ne_zero_of_isFrameOn {Y : Scheme.{u}} {N : Y.Modules} {U : Y.Opens} {s : Γ(N, U)}
    (hs : Scheme.Modules.IsFrameOn s U) [Nontrivial Γ(Y, U)] : s ≠ 0 := by
  intro h0
  have hb := hs.bijective le_rfl le_rfl
  have h1 : (fun g : Γ(Y, U) => g • (N.presheaf.map (homOfLE le_rfl).op s : Γ(N, U))) 1 =
      (fun g : Γ(Y, U) => g • (N.presheaf.map (homOfLE le_rfl).op s : Γ(N, U))) 0 := by
    simp only [h0, map_zero, smul_zero]
  exact one_ne_zero (hb.1 h1)

end BKeyAux
p2m_reactivate "P2MW.S_AlgebraicGeometry_RelPicard_isNodeUnitModule_foldr_ofPoint_of_forall_eq_ord_of_hasValue.EPkgTwist P2MW.S_AlgebraicGeometry_RelPicard_isNodeUnitModule_foldr_ofPoint_of_forall_eq_ord_of_hasValue.EPrincI.Place P2MW.S_AlgebraicGeometry_RelPicard_isNodeUnitModule_foldr_ofPoint_of_forall_eq_ord_of_hasValue.EPrincI"

open BKeyAux in

def EPkgTwist.LocRead {K : Type u} [Field K] {Y : Scheme.{u}} (x : Y ⟶ Spec (CommRingCat.of K)) [IsIntegral Y]
    (M : Y.Modules) (W : Y.Opens) (e : Γ(M, W)) (y : Y)
    (v : letI := (AlgebraicCurve.baseToFunctionField x).toAlgebra
      AlgebraicCurve.Place K Y.functionField) (d : ℤ) : Prop :=
  letI := (AlgebraicCurve.baseToFunctionField x).toAlgebra
  ∃ (U₀ : Y.Opens) (_ : y ∈ U₀) (F : Γ(M, U₀)) (_ : Scheme.Modules.IsFrameOn F U₀)
    (W₀ : Y.Opens) (hW₀U : W₀ ≤ U₀) (hW₀W : W₀ ≤ W) (_ : Nonempty W₀) (num den : Γ(Y, W₀)),
    den • M.presheaf.map (homOfLE hW₀W).op e = num • M.presheaf.map (homOfLE hW₀U).op F ∧
    algebraMap Γ(Y, W₀) Y.functionField num ≠ 0 ∧ algebraMap Γ(Y, W₀) Y.functionField den ≠ 0 ∧
    v.ord (algebraMap Γ(Y, W₀) Y.functionField num) - v.ord (algebraMap Γ(Y, W₀) Y.functionField den) = d

open BKeyAux in

theorem EPkgTwist.locRead_punctured_eCan
    {K : Type u} [Field K] {Y : Scheme.{u}} (x : Y ⟶ Spec (CommRingCat.of K))
    [IsIntegral Y] [IsSeparated x] [QuasiCompact x] [SmoothOfRelativeDimension 1 x]
    (P : Spec (CommRingCat.of K) ⟶ Y) (hP : P ≫ x = 𝟙 _)
    (v : letI := (AlgebraicCurve.baseToFunctionField x).toAlgebra
      AlgebraicCurve.Place K Y.functionField)
    (hv : letI := (AlgebraicCurve.baseToFunctionField x).toAlgebra
      (algebraMap (Y.presheaf.stalk (P.base (IsLocalRing.closedPoint K))) Y.functionField).range =
        v.toValuationSubring.toSubring)
    (n m : ℕ) (N : Y.Modules)
    (U W : Y.Opens) (hWU : W ≤ U) (hPU : P.base (IsLocalRing.closedPoint K) ∈ U) [Nonempty W]
    (r : Γ(N, U)) (hr : Scheme.Modules.IsFrameOn r U)
    (σ : Γ((P.ker ^ n).invModule, W)) (hσ : σ = (P.ker ^ n).invModuleSection.app W (Scheme.Modules.unitSection W))
    (μ : Γ((P.ker ^ m).module, W)) (hμ : (P.ker ^ m).moduleι.app W μ = Scheme.Modules.unitSection W)
    (hσW : Scheme.Modules.IsFrameOn σ W) (hμW : Scheme.Modules.IsFrameOn μ W) :
    EPkgTwist.LocRead x ((P.ker ^ n).invModule ⊗ ((P.ker ^ m).module ⊗ N)) W
      (Scheme.Modules.tensorSections σ (Scheme.Modules.tensorSections μ (N.presheaf.map (homOfLE hWU).op r)))
      (P.base (IsLocalRing.closedPoint K)) v ((n : ℤ) - m) := by
  classical
  letI := (AlgebraicCurve.baseToFunctionField x).toAlgebra

  have hIinv : P.ker.IsInvertible := Scheme.Hom.isInvertible_ker_of_comp_eq_id P hP
  have hIn : (P.ker ^ n).IsInvertible := hIinv.pow n
  have hIm : (P.ker ^ m).IsInvertible := hIinv.pow m
  have hQinv : Scheme.Modules.IsInvertible (P.ker ^ n).invModule := hIn.isInvertible_invModule
  have hTinv : Scheme.Modules.IsInvertible (P.ker ^ m).module := hIm.isInvertible_module

  have hyclosed : IsClosed ({P.base (IsLocalRing.closedPoint K)} : Set Y) := by
    have := isClosedImmersion_of_comp_eq_id x P hP
    have h := P.isClosedEmbedding.isClosed_range
    have hr : Set.range P.base = {P.base (IsLocalRing.closedPoint K)} :=
      Set.range_eq_singleton_iff.mpr (fun z => congrArg P.base (Subsingleton.elim z (IsLocalRing.closedPoint K)))
    rwa [hr] at h

  have hres_id : ∀ (L : Y.Modules) (V : Y.Opens) (s : Γ(L, V)), L.presheaf.map (homOfLE (le_rfl : V ≤ V)).op s = s := by
    intro L V s
    have : (homOfLE (le_rfl : V ≤ V)) = 𝟙 _ := Subsingleton.elim _ _
    rw [this, op_id, CategoryTheory.Functor.map_id]; rfl

  obtain ⟨U₁, q, hyU₁, hq⟩ := hQinv.exists_isFrameOn (P.base (IsLocalRing.closedPoint K))
  obtain ⟨U₂, τ, hyU₂, hτ⟩ := hTinv.exists_isFrameOn (P.base (IsLocalRing.closedPoint K))
  obtain ⟨_, ⟨U₀, hU₀, rfl⟩, hyU₀, hU₀le⟩ := Y.isBasis_affineOpens.exists_subset_of_mem_open
    (show P.base (IsLocalRing.closedPoint K) ∈ ((U ⊓ U₁ ⊓ U₂ : Y.Opens) : Set Y) from ⟨⟨hPU, hyU₁⟩, hyU₂⟩)
    (U ⊓ U₁ ⊓ U₂).isOpen
  have hU₀U : U₀ ≤ U := fun z hz => (hU₀le hz).1.1
  have hU₀U₁ : U₀ ≤ U₁ := fun z hz => (hU₀le hz).1.2
  have hU₀U₂ : U₀ ≤ U₂ := fun z hz => (hU₀le hz).2
  haveI : Nonempty U₀ := ⟨⟨_, hyU₀⟩⟩

  have hW' : ((U₀ ⊓ W : Y.Opens) : Set Y).Nonempty := by
    obtain ⟨w⟩ := ‹Nonempty W›
    exact nonempty_preirreducible_inter U₀.isOpen W.isOpen ⟨_, hyU₀⟩ ⟨w.1, w.2⟩
  obtain ⟨z₀, hz₀⟩ := hW'
  obtain ⟨_, ⟨W₀, hW₀, rfl⟩, hzW₀, hW₀le⟩ := Y.isBasis_affineOpens.exists_subset_of_mem_open hz₀ (U₀ ⊓ W).isOpen
  have hW₀U₀ : W₀ ≤ U₀ := fun z hz => (hW₀le hz).1
  have hW₀W : W₀ ≤ W := fun z hz => (hW₀le hz).2
  have hW₀U : W₀ ≤ U := hW₀U₀.trans hU₀U
  have hW₀U₁ : W₀ ≤ U₁ := hW₀U₀.trans hU₀U₁
  have hW₀U₂ : W₀ ≤ U₂ := hW₀U₀.trans hU₀U₂
  haveI : Nonempty W₀ := ⟨⟨z₀, hzW₀⟩⟩

  set q₀ : Γ((P.ker ^ n).invModule, U₀) := ((P.ker ^ n).invModule).presheaf.map (homOfLE hU₀U₁).op q with hq₀
  set τ₀ : Γ((P.ker ^ m).module, U₀) := ((P.ker ^ m).module).presheaf.map (homOfLE hU₀U₂).op τ with hτ₀
  set r₀ : Γ(N, U₀) := N.presheaf.map (homOfLE hU₀U).op r with hr₀
  have hq₀f : Scheme.Modules.IsFrameOn q₀ U₀ := (hq.map (homOfLE hU₀U₁)).mono hU₀U₁
  have hτ₀f : Scheme.Modules.IsFrameOn τ₀ U₀ := (hτ.map (homOfLE hU₀U₂)).mono hU₀U₂
  have hr₀f : Scheme.Modules.IsFrameOn r₀ U₀ := (hr.map (homOfLE hU₀U)).mono hU₀U
  set F : Γ((P.ker ^ n).invModule ⊗ ((P.ker ^ m).module ⊗ N), U₀) :=
    Scheme.Modules.tensorSections q₀ (Scheme.Modules.tensorSections τ₀ r₀) with hF
  have hFf : Scheme.Modules.IsFrameOn F U₀ := hq₀f.tensorSections (hτ₀f.tensorSections hr₀f)

  obtain ⟨c, hc⟩ := (hq.bijective le_rfl le_rfl).2 ((P.ker ^ n).invModuleSection.app U₁ (Scheme.Modules.toUnitSection U₁ 1))
  have hc' : (P.ker ^ n).invModuleSection.app U₁ (Scheme.Modules.toUnitSection U₁ 1) = c • q := by
    rw [← hc, hres_id]
  set c₀ : Γ(Y, U₀) := Y.presheaf.map (homOfLE hU₀U₁).op c with hc₀
  have hideal_n : (P.ker ^ n).ideal ⟨U₀, hU₀⟩ = Ideal.span {c₀} := by
    have h := Scheme.Modules.IsInvertible.ideal_zeroSchemeIdeal_eq_span_of_app_eq_smul hQinv q hq
      ((P.ker ^ n).invModuleSection) c hc' ⟨U₀, hU₀⟩ hU₀U₁
    rwa [hIn.zeroSchemeIdeal_invModuleSection] at h
  have hord_c : v.ord (algebraMap Γ(Y, U₀) Y.functionField c₀) = n :=
    (Scheme.Hom.ord_eq_of_ker_pow_ideal_eq_span x P hP n U₀ hU₀ c₀ hideal_n _ hyU₀ hyclosed v hv).1 rfl

  set G : Γ(Y, U₀) := Scheme.Modules.ofUnitSection U₀ ((P.ker ^ m).moduleι.app U₀ τ₀) with hG
  obtain ⟨hrange, hinjι⟩ := (P.ker ^ m).range_moduleIota_app_and_injective ⟨U₀, hU₀⟩
  have hideal_m : (P.ker ^ m).ideal ⟨U₀, hU₀⟩ = Ideal.span {G} := by
    apply le_antisymm
    · intro a ha
      have ha' : a ∈ Set.range ((P.ker ^ m).moduleι.app U₀) := by rw [hrange]; exact ha
      obtain ⟨t, rfl⟩ := ha'
      obtain ⟨b, hb⟩ := (hτ₀f.bijective le_rfl le_rfl).2 t
      rw [Ideal.mem_span_singleton']
      refine ⟨b, ?_⟩
      rw [← hb, hres_id, Scheme.Modules.Hom.app_smul]
      rfl
    · rw [Ideal.span_le, Set.singleton_subset_iff]
      have hGm : G ∈ Set.range ((P.ker ^ m).moduleι.app U₀) := ⟨τ₀, rfl⟩
      rw [hrange] at hGm
      exact hGm
  have hord_G : v.ord (algebraMap Γ(Y, U₀) Y.functionField G) = m :=
    (Scheme.Hom.ord_eq_of_ker_pow_ideal_eq_span x P hP m U₀ hU₀ G hideal_m _ hyU₀ hyclosed v hv).1 rfl
  have hG0 : G ≠ 0 := by
    intro h0
    have hτ00 : τ₀ = 0 := hinjι (by rw [map_zero]; exact h0)
    exact ne_zero_of_isFrameOn hτ₀f hτ00

  set qW : Γ((P.ker ^ n).invModule, W₀) := ((P.ker ^ n).invModule).presheaf.map (homOfLE hW₀U₁).op q with hqW
  set μW : Γ((P.ker ^ m).module, W₀) := ((P.ker ^ m).module).presheaf.map (homOfLE hW₀W).op μ with hμW'
  set rW : Γ(N, W₀) := N.presheaf.map (homOfLE hW₀U).op r with hrW
  set B : Γ((P.ker ^ n).invModule ⊗ ((P.ker ^ m).module ⊗ N), W₀) :=
    Scheme.Modules.tensorSections qW (Scheme.Modules.tensorSections μW rW) with hB
  set cW : Γ(Y, W₀) := Y.presheaf.map (homOfLE hW₀U₀).op c₀ with hcW
  set GW : Γ(Y, W₀) := Y.presheaf.map (homOfLE hW₀U₀).op G with hGW

  have hσW₀ : ((P.ker ^ n).invModule).presheaf.map (homOfLE hW₀W).op σ = cW • qW := by
    have h1 : ((P.ker ^ n).invModule).presheaf.map (homOfLE hW₀W).op σ =
        (P.ker ^ n).invModuleSection.app W₀ (Scheme.Modules.unitSection W₀) := by
      rw [hσ, ← app_map, Scheme.Modules.map_unitSection]
    have h2 : ((P.ker ^ n).invModule).presheaf.map (homOfLE hW₀U₁).op
        ((P.ker ^ n).invModuleSection.app U₁ (Scheme.Modules.toUnitSection U₁ 1)) =
        (P.ker ^ n).invModuleSection.app W₀ (Scheme.Modules.unitSection W₀) := by
      rw [← app_map]
      change (P.ker ^ n).invModuleSection.app W₀ ((𝟙_ Y.Modules).presheaf.map (homOfLE hW₀U₁).op (Scheme.Modules.unitSection U₁)) = _
      rw [Scheme.Modules.map_unitSection]
    rw [h1, ← h2, hc', Scheme.Modules.map_smul, hcW, hc₀, res_res']

  have he : ((P.ker ^ n).invModule ⊗ ((P.ker ^ m).module ⊗ N)).presheaf.map (homOfLE hW₀W).op
      (Scheme.Modules.tensorSections σ (Scheme.Modules.tensorSections μ (N.presheaf.map (homOfLE hWU).op r))) = cW • B := by
    rw [Scheme.Modules.map_homOfLE_tensorSections, Scheme.Modules.map_homOfLE_tensorSections, res_res, hσW₀,
      Scheme.Modules.tensorSections_smul_left]

  have hτW₀ : ((P.ker ^ m).module).presheaf.map (homOfLE hW₀U₂).op τ = GW • μW := by
    obtain ⟨t', ht'⟩ := (hμW.bijective hW₀W hW₀W).2 (((P.ker ^ m).module).presheaf.map (homOfLE hW₀U₂).op τ)

    have hι := congrArg ((P.ker ^ m).moduleι.app W₀) ht'
    rw [Scheme.Modules.Hom.app_smul, app_map, hμ, Scheme.Modules.map_unitSection, Scheme.Modules.smul_unitSection,
      app_map] at hι

    have hGW' : GW = Y.presheaf.map (homOfLE hW₀U₂).op (Scheme.Modules.ofUnitSection U₂ ((P.ker ^ m).moduleι.app U₂ τ)) := by
      rw [hGW, hG, hτ₀, app_map, Scheme.Modules.ofUnitSection_map, res_res']
    rw [← ht']
    congr 1
    rw [hGW']
    exact hι

  have hFW : ((P.ker ^ n).invModule ⊗ ((P.ker ^ m).module ⊗ N)).presheaf.map (homOfLE hW₀U₀).op F = GW • B := by
    rw [hF, Scheme.Modules.map_homOfLE_tensorSections, Scheme.Modules.map_homOfLE_tensorSections, hq₀, hτ₀, hr₀,
      res_res, res_res, res_res, hτW₀, Scheme.Modules.tensorSections_smul_left, Scheme.Modules.tensorSections_smul_right]

  have hinjalg : Function.Injective (algebraMap Γ(Y, U₀) Y.functionField) := Y.germToFunctionField_injective U₀
  have haG : algebraMap Γ(Y, U₀) Y.functionField G ≠ 0 := (map_ne_zero_iff _ hinjalg).mpr hG0
  have halg : ∀ {V V' : Y.Opens} [Nonempty V] [Nonempty V'] (h : V' ≤ V) (s : Γ(Y, V)),
      algebraMap Γ(Y, V') Y.functionField (Y.presheaf.map (homOfLE h).op s) = algebraMap Γ(Y, V) Y.functionField s := by
    intro V V' _ _ h s
    exact TopCat.Presheaf.germ_res_apply Y.presheaf (homOfLE h) _ _ s

  have he0 : Scheme.Modules.tensorSections σ (Scheme.Modules.tensorSections μ (N.presheaf.map (homOfLE hWU).op r)) ≠ 0 :=
    ne_zero_of_isFrameOn (hσW.tensorSections (hμW.tensorSections ((hr.map (homOfLE hWU)).mono hWU)))
  have heW0 : ((P.ker ^ n).invModule ⊗ ((P.ker ^ m).module ⊗ N)).presheaf.map (homOfLE hW₀W).op
      (Scheme.Modules.tensorSections σ (Scheme.Modules.tensorSections μ (N.presheaf.map (homOfLE hWU).op r))) ≠ 0 :=
    ne_zero_of_isFrameOn (((hσW.tensorSections (hμW.tensorSections ((hr.map (homOfLE hWU)).mono hWU))).map (homOfLE hW₀W)).mono hW₀W)
  have hB0 : B ≠ 0 := by
    intro h0
    rw [h0, smul_zero] at he
    exact heW0 he
  have hcW0 : algebraMap Γ(Y, U₀) Y.functionField c₀ ≠ 0 := by
    intro h0
    have hc00 : c₀ = 0 := hinjalg (h0.trans (map_zero _).symm)
    have hcW00 : cW = 0 := by rw [hcW, hc00, map_zero]
    rw [hcW00, zero_smul] at he
    exact heW0 he

  refine ⟨U₀, hyU₀, F, hFf, W₀, hW₀U₀, hW₀W, inferInstance, cW, GW, ?_, ?_, ?_, ?_⟩
  · rw [he, hFW, smul_smul, smul_smul, mul_comm]
  · rwa [hcW, halg hW₀U₀ c₀]
  · rwa [hGW, halg hW₀U₀ G]
  · rw [hcW, hGW, halg hW₀U₀ c₀, halg hW₀U₀ G, hord_c, hord_G]

open BKeyAux in

theorem EPkgTwist.ord_presentation_of_locRead
    {K : Type u} [Field K] {Y : Scheme.{u}} (x : Y ⟶ Spec (CommRingCat.of K)) [IsIntegral Y]
    (M : Y.Modules) (W : Y.Opens) (e : Γ(M, W)) (y : Y) (hy : IsClosed ({y} : Set Y))
    (v : letI := (AlgebraicCurve.baseToFunctionField x).toAlgebra
      AlgebraicCurve.Place K Y.functionField)
    (hv : letI := (AlgebraicCurve.baseToFunctionField x).toAlgebra
      (algebraMap (Y.presheaf.stalk y) Y.functionField).range = v.toValuationSubring.toSubring)
    (d : ℤ) (hloc : EPkgTwist.LocRead x M W e y v d)
    (D_M : letI := (AlgebraicCurve.baseToFunctionField x).toAlgebra
      AlgebraicCurve.Divisor K Y.functionField)
    (φ : ∀ U : Y.Opens, Γ(M, U) →+ (Y.functionField : Type u))
    (hnat : ∀ (U V : Y.Opens) (h : V ≤ U), Nonempty V →
      ∀ s : Γ(M, U), φ V (M.presheaf.map (homOfLE h).op s) = φ U s)
    (hsmul : ∀ (U : Y.Opens) [Nonempty U] (a : Γ(Y, U)) (s : Γ(M, U)),
      φ U (a • s) = algebraMap Γ(Y, U) Y.functionField a * φ U s)
    (hinj : ∀ U : Y.Opens, Nonempty U → Function.Injective (φ U))
    (hgen : letI := (AlgebraicCurve.baseToFunctionField x).toAlgebra
      ∀ (U : Y.Opens) (s : Γ(M, U)) (y : Y), y ∈ U → IsClosed ({y} : Set Y) →
      (∀ (W : Y.Opens) (h : W ≤ U), y ∈ W → ∀ t : Γ(M, W), ∃ a : Γ(Y, W), t = a • M.presheaf.map (homOfLE h).op s) →
      ∀ w : AlgebraicCurve.Place K Y.functionField,
        (algebraMap (Y.presheaf.stalk y) Y.functionField).range = w.toValuationSubring.toSubring →
        WithZero.exp (D_M w) = w.adicValuation (φ U s)) :
    letI := (AlgebraicCurve.baseToFunctionField x).toAlgebra
    v.ord (φ W e) = d - D_M v := by
  classical
  letI := (AlgebraicCurve.baseToFunctionField x).toAlgebra
  obtain ⟨U₀, hyU₀, F, hFf, W₀, hW₀U, hW₀W, hneW₀, num, den, heq, hnum, hden, hd⟩ := hloc
  haveI : Nonempty W₀ := hneW₀
  haveI : Nonempty U₀ := ⟨⟨y, hyU₀⟩⟩

  have hordF : v.ord (φ U₀ F) = -D_M v := by
    have h := hgen U₀ F y hyU₀ hy (fun W' h' _ t => by
      obtain ⟨a, ha⟩ := (hFf.bijective h' h').2 t
      exact ⟨a, ha.symm⟩) v hv
    simp only [AlgebraicCurve.Place.ord, ← h, WithZero.log_exp]

  have hF0 : φ U₀ F ≠ 0 := fun h0 => ne_zero_of_isFrameOn hFf (hinj U₀ inferInstance (h0.trans (map_zero _).symm))

  have h1 : algebraMap Γ(Y, W₀) Y.functionField den * φ W e = algebraMap Γ(Y, W₀) Y.functionField num * φ U₀ F := by
    rw [← hnat W W₀ hW₀W inferInstance, ← hnat U₀ W₀ hW₀U inferInstance, ← hsmul, ← hsmul, heq]
  have he0 : φ W e ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at h1
    exact (mul_ne_zero hnum hF0) h1.symm
  have h2 := congrArg v.ord h1
  rw [v.ord_mul hden he0, v.ord_mul hnum hF0, hordF] at h2
  linarith

namespace BGlobAux

p2m_open "AlgebraicGeometry.Scheme.Modules"

lemma res_res {Y : Scheme.{u}} (N : Y.Modules) {U V W : Y.Opens} (h₁ : V ≤ U) (h₂ : W ≤ V) (s : Γ(N, U)) :
    N.presheaf.map (homOfLE h₂).op (N.presheaf.map (homOfLE h₁).op s) = N.presheaf.map (homOfLE (h₂.trans h₁)).op s := by
  rw [← CategoryTheory.comp_apply, ← Functor.map_comp]
  rfl

lemma res_res' (Y : Scheme.{u}) {U V W : Y.Opens} (h₁ : V ≤ U) (h₂ : W ≤ V) (s : Γ(Y, U)) :
    Y.presheaf.map (homOfLE h₂).op (Y.presheaf.map (homOfLE h₁).op s) = Y.presheaf.map (homOfLE (h₂.trans h₁)).op s := by
  rw [← CategoryTheory.comp_apply, ← Functor.map_comp]
  rfl

lemma isFrameOn_res {Y : Scheme.{u}} {N : Y.Modules} {U V : Y.Opens} {s : Γ(N, U)} (hs : IsFrameOn s U) (h : V ≤ U) :
    IsFrameOn (N.presheaf.map (homOfLE h).op s) V :=
  (hs.map (homOfLE h)).mono h

lemma isFrameOn_smul_of_isUnit {Y : Scheme.{u}} {N : Y.Modules} {U : Y.Opens} {s : Γ(N, U)} (hs : IsFrameOn s U)
    {a : Γ(Y, U)} (ha : IsUnit a) : IsFrameOn (a • s) U := by
  intro W hWU _
  have hb := hs.bijective hWU hWU
  have hmap : N.presheaf.map (homOfLE hWU).op (a • s) = Y.presheaf.map (homOfLE hWU).op a • N.presheaf.map (homOfLE hWU).op s :=
    Scheme.Modules.map_smul _ _ _ _
  have hcomp : (fun g : Γ(Y, W) => g • N.presheaf.map (homOfLE hWU).op (a • s)) =
      (fun g : Γ(Y, W) => g • N.presheaf.map (homOfLE hWU).op s) ∘ (fun g => g * Y.presheaf.map (homOfLE hWU).op a) := by
    funext g
    simp only [Function.comp_apply, hmap, smul_smul]
  rw [hcomp]
  exact hb.comp (IsUnit.isUnit_iff_mulRight_bijective.mp (ha.map (Y.presheaf.map (homOfLE hWU).op).hom))

end BGlobAux
p2m_reactivate "P2MW.S_AlgebraicGeometry_RelPicard_isNodeUnitModule_foldr_ofPoint_of_forall_eq_ord_of_hasValue.EPkgTwist P2MW.S_AlgebraicGeometry_RelPicard_isNodeUnitModule_foldr_ofPoint_of_forall_eq_ord_of_hasValue.EPrincI.Place P2MW.S_AlgebraicGeometry_RelPicard_isNodeUnitModule_foldr_ofPoint_of_forall_eq_ord_of_hasValue.EPrincI"

open BGlobAux _root_.AlgebraicGeometry.Scheme.Modules in

theorem EPkgTwist.exists_iso_unit_forall_algebraMap_app_eq_inv_mul_of_forall_ord_add_eq_zero
    {K : Type u} [Field K] {Y : Scheme.{u}} (x : Y ⟶ Spec (CommRingCat.of K))
    [IsIntegral Y] [IsProper x] [SmoothOfRelativeDimension 1 x]
    (M : Y.Modules) (hM : Scheme.Modules.IsInvertible M)
    (D_M : letI := (AlgebraicCurve.baseToFunctionField x).toAlgebra
      AlgebraicCurve.Divisor K Y.functionField)
    (φ : ∀ U : Y.Opens, Γ(M, U) →+ (Y.functionField : Type u))
    (hnat : ∀ (U V : Y.Opens) (hVU : V ≤ U), Nonempty V →
      ∀ s : Γ(M, U), φ V (M.presheaf.map (homOfLE hVU).op s) = φ U s)
    (hsmul : ∀ (U : Y.Opens) [Nonempty U] (a : Γ(Y, U)) (s : Γ(M, U)),
      φ U (a • s) = algebraMap Γ(Y, U) Y.functionField a * φ U s)
    (hinj : ∀ U : Y.Opens, Nonempty U → Function.Injective (φ U))
    (hrange : letI := (AlgebraicCurve.baseToFunctionField x).toAlgebra
      ∀ U : Y.Opens, IsAffineOpen U → Nonempty U →
        Set.range (φ U) = (AlgebraicCurve.lSpaceOn (AlgebraicCurve.placesOf x U) D_M : Set Y.functionField))
    (hgen : letI := (AlgebraicCurve.baseToFunctionField x).toAlgebra
      ∀ (U : Y.Opens) (s : Γ(M, U)) (y : Y), y ∈ U → IsClosed ({y} : Set Y) →
      (∀ (W : Y.Opens) (hWU : W ≤ U), y ∈ W → ∀ t : Γ(M, W), ∃ a : Γ(Y, W), t = a • M.presheaf.map (homOfLE hWU).op s) →
      ∀ w : AlgebraicCurve.Place K Y.functionField,
        (algebraMap (Y.presheaf.stalk y) Y.functionField).range = w.toValuationSubring.toSubring →
        WithZero.exp (D_M w) = w.adicValuation (φ U s))
    (h : Y.functionField) (hh : h ≠ 0)
    (hord : letI := (AlgebraicCurve.baseToFunctionField x).toAlgebra
      ∀ (y : Y), IsClosed ({y} : Set Y) → ∀ w : AlgebraicCurve.Place K Y.functionField,
        (algebraMap (Y.presheaf.stalk y) Y.functionField).range = w.toValuationSubring.toSubring →
        w.ord h + D_M w = 0)

    (hctr : letI := (AlgebraicCurve.baseToFunctionField x).toAlgebra
      ∀ (y : Y), IsClosed ({y} : Set Y) → ∃ w : AlgebraicCurve.Place K Y.functionField,
        (algebraMap (Y.presheaf.stalk y) Y.functionField).range = w.toValuationSubring.toSubring) :
    ∃ β : M ≅ 𝟙_ Y.Modules, ∀ (U : Y.Opens) [Nonempty U] (s : Γ(M, U)),
      algebraMap Γ(Y, U) Y.functionField (Scheme.Modules.ofUnitSection U (β.hom.app U s)) = h⁻¹ * φ U s := by
  classical
  letI := (AlgebraicCurve.baseToFunctionField x).toAlgebra
  haveI : Nonempty Y := inferInstance

  have hT : ∃ T : Γ(M, ⊤), φ ⊤ T = h := by

    have hmem : ∀ U : Y.Opens, h ∈ (AlgebraicCurve.lSpaceOn (AlgebraicCurve.placesOf x U) D_M : Set Y.functionField) := by
      intro U w hw
      obtain ⟨y, -, hy, hrg⟩ := hw
      have hordh : w.ord h + D_M w = 0 := hord y hy w hrg
      have h1 : w.adicValuation h ≠ 0 := (Valuation.ne_zero_iff _).mpr hh
      rw [← WithZero.exp_log h1]
      apply le_of_eq
      congr 1
      simp only [AlgebraicCurve.Place.ord] at hordh
      linarith

    let ι := {U : Y.Opens // IsAffineOpen U ∧ Nonempty U}
    have hex : ∀ i : ι, ∃ t : Γ(M, i.1), φ i.1 t = h := fun i => by
      have h2 : h ∈ Set.range (φ i.1) := by rw [hrange i.1 i.2.1 i.2.2]; exact hmem i.1
      exact h2
    choose sf hsf using hex

    let FM : TopCat.Sheaf Ab Y := ⟨M.presheaf, M.isSheaf⟩

    have hcompat : TopCat.Presheaf.IsCompatible FM.1 (fun i : ι => i.1) sf := by
      intro i j
      by_cases hne : Nonempty ((i.1 ⊓ j.1 : Y.Opens))
      · apply hinj _ hne
        change φ (i.1 ⊓ j.1) (M.presheaf.map (homOfLE inf_le_left).op (sf i)) =
          φ (i.1 ⊓ j.1) (M.presheaf.map (homOfLE inf_le_right).op (sf j))
        rw [hnat _ _ _ hne, hnat _ _ _ hne, hsf, hsf]
      ·
        have hbot : (i.1 ⊓ j.1 : Y.Opens) = ⊥ := by
          ext z
          simp only [Opens.coe_bot, Set.mem_empty_iff_false, iff_false]
          exact fun hz => hne ⟨⟨z, hz⟩⟩
        apply FM.eq_of_locally_eq' (fun k : PEmpty.{u + 1} => (PEmpty.elim k : Y.Opens)) (i.1 ⊓ j.1) (fun k => PEmpty.elim k)
        · rw [hbot]; exact bot_le
        · exact fun k => PEmpty.elim k

    have hcov : (⊤ : Y.Opens) ≤ ⨆ i : ι, i.1 := by
      intro z _
      obtain ⟨_, ⟨U, hU, rfl⟩, hzU, -⟩ := Y.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ z) isOpen_univ
      exact Opens.mem_iSup.mpr ⟨⟨U, hU, ⟨⟨z, hzU⟩⟩⟩, hzU⟩
    obtain ⟨T, hT, -⟩ := FM.existsUnique_gluing' (fun i : ι => i.1) ⊤ (fun i => homOfLE le_top) hcov sf hcompat
    refine ⟨T, ?_⟩

    obtain ⟨z⟩ := ‹Nonempty Y›
    obtain ⟨_, ⟨U, hU, rfl⟩, hzU, -⟩ := Y.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ z) isOpen_univ
    let i0 : ι := ⟨U, hU, ⟨⟨z, hzU⟩⟩⟩
    have h3 : M.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op T = sf i0 := hT i0
    rw [← hnat ⊤ U le_top i0.2.2, h3]
    exact hsf i0
  obtain ⟨T, hTh⟩ := hT

  have hlocal : ∀ y : Y, IsClosed ({y} : Set Y) → ∃ V : Y.Opens, y ∈ V ∧ IsFrameOn (M.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op T) V := by
    intro y hy
    obtain ⟨Us, s, hyUs, hs⟩ := hM.exists_isFrameOn y
    haveI : Nonempty Us := ⟨⟨y, hyUs⟩⟩

    obtain ⟨a, ha⟩ := (hs.bijective le_rfl le_rfl).2 (M.presheaf.map (homOfLE (le_top : Us ≤ ⊤)).op T)
    have hres_id : M.presheaf.map (homOfLE (le_rfl : Us ≤ Us)).op s = s := by
      have : (homOfLE (le_rfl : Us ≤ Us)) = 𝟙 _ := Subsingleton.elim _ _
      rw [this, op_id, CategoryTheory.Functor.map_id]; rfl
    rw [hres_id] at ha
    dsimp only at ha

    obtain ⟨w, hw⟩ := hctr y hy
    have hgs : WithZero.exp (D_M w) = w.adicValuation (φ Us s) :=
      hgen Us s y hyUs hy (fun W hWU _ t => by
        obtain ⟨b, hb⟩ := (hs.bijective hWU hWU).2 t
        exact ⟨b, hb.symm⟩) w hw
    have hφT : φ Us (M.presheaf.map (homOfLE (le_top : Us ≤ ⊤)).op T) = h := by rw [hnat ⊤ Us le_top inferInstance, hTh]
    have hprod : algebraMap Γ(Y, Us) Y.functionField a * φ Us s = h := by rw [← hsmul, ha, hφT]

    have hordh : w.ord h + D_M w = 0 := hord y hy w hw
    have hval_h : w.adicValuation h = WithZero.exp (D_M w) := by
      have h1 : w.adicValuation h ≠ 0 := (Valuation.ne_zero_iff _).mpr hh
      rw [← WithZero.exp_log h1]
      congr 1
      simp only [AlgebraicCurve.Place.ord] at hordh
      linarith
    have hval_a : w.adicValuation (algebraMap Γ(Y, Us) Y.functionField a) = 1 := by
      have h2 := congrArg w.adicValuation hprod
      rw [map_mul, ← hgs, hval_h] at h2
      have h3 : WithZero.exp (D_M w) ≠ 0 := WithZero.exp_ne_zero
      exact (mul_eq_right₀ h3).mp h2

    have hgerm : IsUnit (Y.presheaf.germ Us y hyUs a) := by

      set S : CommRingCat := Y.presheaf.stalk y
      let A : ValuationSubring Y.functionField := w.toValuationSubring
      have hφmem : ∀ t : S, algebraMap S Y.functionField t ∈ A := fun t => by
        have h4 : algebraMap S Y.functionField t ∈ (algebraMap S Y.functionField).range := ⟨t, rfl⟩
        rw [hw] at h4
        exact h4
      let ψ : S →+* A := (algebraMap S Y.functionField).codRestrict A hφmem
      have hψinj : Function.Injective ψ := fun a1 b1 hab =>
        IsFractionRing.injective S Y.functionField (congrArg Subtype.val hab)
      have hunitA : IsUnit (ψ (Y.presheaf.germ Us y hyUs a)) := by
        rw [← AlgebraicCurve.Place.adicValuation_coe_eq_one_iff]
        change w.adicValuation (algebraMap S Y.functionField (Y.presheaf.germ Us y hyUs a)) = 1
        rw [← hval_a]
        congr 1
        change (Y.presheaf.germ Us y hyUs ≫ Y.presheaf.stalkSpecializes ((genericPoint_spec Y).specializes trivial)) a = _
        rw [TopCat.Presheaf.germ_stalkSpecializes]
        rfl

      have hψsurj : Function.Surjective ψ := fun a1 => by
        have ha1 : (a1 : Y.functionField) ∈ (algebraMap S Y.functionField).range := by rw [hw]; exact a1.2
        obtain ⟨t, ht⟩ := ha1
        exact ⟨t, Subtype.ext ht⟩
      let eSA : S ≃+* A := RingEquiv.ofBijective ψ ⟨hψinj, hψsurj⟩
      exact (isUnit_map_iff eSA _).mp hunitA
    obtain ⟨V, iV, hyV, hunit⟩ := AlgebraicGeometry.RingedSpace.isUnit_res_of_isUnit_germ (X := Y.toLocallyRingedSpace.toRingedSpace)
      Us a y hyUs hgerm
    refine ⟨V, hyV, ?_⟩
    have hVUs : V ≤ Us := iV.le
    have hTV : M.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op T =
        Y.presheaf.map (homOfLE hVUs).op a • M.presheaf.map (homOfLE hVUs).op s := by
      rw [← Scheme.Modules.map_smul, ha, res_res]
    rw [hTV]
    have hiV : iV = homOfLE hVUs := Subsingleton.elim _ _
    rw [hiV] at hunit
    exact isFrameOn_smul_of_isUnit (isFrameOn_res hs hVUs) hunit

  have hframe : IsFrameOn T ⊤ := by
    haveI : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace x

    let ι := {y : Y // IsClosed ({y} : Set Y)}
    let V : ι → Y.Opens := fun i => (hlocal i.1 i.2).choose
    have hV : ∀ i : ι, i.1 ∈ V i ∧ IsFrameOn (M.presheaf.map (homOfLE (le_top : V i ≤ ⊤)).op T) (V i) :=
      fun i => (hlocal i.1 i.2).choose_spec
    have hcov : (⨆ i, V i) = ⊤ := by
      apply top_unique
      intro z _

      obtain ⟨y, hy, hyc⟩ := (isClosed_closure (s := ({z} : Set Y))).exists_closed_singleton ⟨z, subset_closure rfl⟩
      have hz : z ∈ V ⟨y, hyc⟩ := by
        have hyV : y ∈ V ⟨y, hyc⟩ := (hV ⟨y, hyc⟩).1
        by_contra hzV
        have : y ∈ closure ({z} : Set Y) := hy
        rw [mem_closure_iff] at this
        obtain ⟨t, ht, ht'⟩ := this (V ⟨y, hyc⟩) (V ⟨y, hyc⟩).isOpen hyV
        rw [Set.mem_singleton_iff] at ht'
        exact hzV (ht' ▸ ht)
      exact Opens.mem_iSup.mpr ⟨⟨y, hyc⟩, hz⟩

    have hTi : ∀ i : ι, IsFrameOn T (V i) := by
      intro i W hWtop hWV
      have h := (hV i).2 hWV hWV

      have hres : M.presheaf.map (homOfLE hWV).op (M.presheaf.map (homOfLE (le_top : V i ≤ ⊤)).op T) =
          M.presheaf.map (homOfLE hWtop).op T := by
        rw [res_res]
      rw [hres] at h
      exact h
    have h := IsFrameOn.of_iSup V hTi
    rwa [hcov] at h

  let S : ∀ W : Y.Opens, Set (Γ(M, W) × Γ(𝟙_ Y.Modules, W)) :=
    fun W => {(M.presheaf.map (homOfLE (le_top : W ≤ ⊤)).op T, unitSection W)}
  obtain ⟨β, hβ⟩ := Scheme.Modules.exists_iso_app_eq_of_isFrameOn_of_eq_smul S
    (fun W pq hpq => by
      rw [Set.mem_singleton_iff] at hpq
      subst hpq
      exact ⟨isFrameOn_res hframe le_top, isFrameOn_unitSection W⟩)
    (fun z => ⟨⊤, trivial, ⟨_, rfl⟩⟩)
    (fun W W' hle pq hpq => by
      rw [Set.mem_singleton_iff] at hpq
      subst hpq
      show (_, _) ∈ S W'
      rw [res_res, map_unitSection]
      rfl)
    (fun W pq pq' hpq hpq' => by
      rw [Set.mem_singleton_iff] at hpq hpq'
      subst hpq; subst hpq'
      exact ⟨1, by rw [one_smul], by rw [one_smul]⟩)
  have hβT : ∀ W : Y.Opens, β.hom.app W (M.presheaf.map (homOfLE (le_top : W ≤ ⊤)).op T) = unitSection W :=
    fun W => hβ W _ rfl

  refine ⟨β, fun U _ s => ?_⟩
  obtain ⟨a, ha⟩ := (hframe.bijective (le_top : U ≤ ⊤) le_top).2 s
  dsimp only at ha

  have hφs : φ U s = algebraMap Γ(Y, U) Y.functionField a * h := by
    rw [← ha, hsmul, hnat ⊤ U le_top inferInstance, hTh]
  have hβs : Scheme.Modules.ofUnitSection U (β.hom.app U s) = a := by
    rw [← ha, Scheme.Modules.Hom.app_smul, hβT, smul_unitSection]
    rfl
  rw [hβs, hφs, mul_comm (algebraMap _ _ a) h, ← mul_assoc, inv_mul_cancel₀ hh, one_mul]

namespace EPrincI

noncomputable def modelIso {k : Type u} [Field k] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of k)) {F : Type u} [Field F] [Algebra k F]
    (Mdl : CurveModel k F) (e : Mdl.C ≅ C) : Mdl.C ⟶ pullback c (𝟙 (Spec (CommRingCat.of k))) :=
  e.hom ≫ inv (pullback.fst c (𝟙 (Spec (CommRingCat.of k))))

scoped instance isIso_modelIso {k : Type u} [Field k] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of k)) {F : Type u} [Field F]
    [Algebra k F] (Mdl : CurveModel k F) (e : Mdl.C ≅ C) : IsIso (modelIso c Mdl e) := by
  unfold modelIso; infer_instance

theorem comap_ker_eq_ker_of_isPullback' {X₀ X T Z : Scheme.{u}} {iX : Z ⟶ X₀} {g : Z ⟶ T} {f : X₀ ⟶ X}
    {iY : T ⟶ X} [IsClosedImmersion iY] (H : IsPullback iX g f iY) : iY.ker.comap f = iX.ker := by
  rw [← Scheme.IdealSheafData.ker_fst_of_isClosedImmersion, ← H.isoPullback_hom_fst,
    Scheme.Hom.ker_comp_of_isIso]

theorem comap_modelIso_ofPoint_I {k : Type u} [Field k] [IsAlgClosed k] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of k))
    [IsSeparated c] {F : Type u} [Field F] [Algebra k F]
    (Mdl : CurveModel k F) (e : Mdl.C ≅ C) (he : e.hom ≫ c = Mdl.toBase)
    (pt : Place k F → (Spec (CommRingCat.of k) ⟶ C)) (hpt : ∀ v, pt v ≫ c = 𝟙 _)
    (hpt' : ∀ v, pt v = (Mdl.pointEquivPlace.symm v).1 ≫ e.hom) (v : Place k F) :
    (RelEffCartierDiv.ofPoint c (pt v) (hpt v)).I.comap (modelIso c Mdl e) = ((Mdl.pointEquivPlace.symm v).1).ker := by
  have hsq : (Mdl.pointEquivPlace.symm v).1 ≫ modelIso c Mdl e = 𝟙 _ ≫ graphOver c (pt v) (hpt v) := by
    rw [Category.id_comp, ← cancel_mono (pullback.fst c (𝟙 (Spec (CommRingCat.of k)))), graphOver_fst, modelIso,
      Category.assoc, Category.assoc, IsIso.inv_hom_id, Category.comp_id, hpt']
  exact comap_ker_eq_ker_of_isPullback' (IsPullback.of_vert_isIso ⟨hsq⟩)

theorem ker_comap_ι_eq_top_iff {K : Type u} [Field K] {X : Scheme.{u}} (x : X ⟶ Spec (CommRingCat.of K)) [IsSeparated x]
    (P : Spec (CommRingCat.of K) ⟶ X) (hP : P ≫ x = 𝟙 _) (W : X.Opens) :
    P.ker.comap W.ι = ⊤ ↔ P.base (IsLocalRing.closedPoint K) ∉ W := by
  haveI : IsClosedImmersion P := by
    have : IsClosedImmersion (P ≫ x) := by rw [hP]; infer_instance
    exact .of_comp P x
  rw [← Scheme.IdealSheafData.support_eq_bot_iff, Scheme.IdealSheafData.support_comap]
  have hsupp : (P.ker.support : Set X) = {P.base (IsLocalRing.closedPoint K)} := by
    rw [Scheme.Hom.support_ker, P.isClosedEmbedding.isClosed_range.closure_eq]
    ext z
    constructor
    · rintro ⟨t, rfl⟩
      obtain rfl : t = IsLocalRing.closedPoint K := Subsingleton.elim _ _
      rfl
    · rintro rfl
      exact ⟨_, rfl⟩
  have key : ∀ w : W, w ∈ (P.ker.support.preimage W.ι.continuous : TopologicalSpace.Closeds W) ↔
      (w : X) = P.base (IsLocalRing.closedPoint K) := by
    intro w
    show W.ι w ∈ (P.ker.support : Set X) ↔ _
    rw [hsupp, Scheme.Opens.ι_apply, Set.mem_singleton_iff]
  constructor
  · intro h hmem
    have hw := (key ⟨_, hmem⟩).2 rfl
    rw [h] at hw
    exact (Set.mem_empty_iff_false _).1 (show (⟨_, hmem⟩ : W) ∈ ((⊥ : TopologicalSpace.Closeds W) : Set W) from hw)
  · intro h
    refine le_bot_iff.1 fun w hw => ?_
    exact absurd ((key w).1 hw ▸ w.2) h

theorem nonempty_compl_of_finite {k : Type u} [Field k] [IsAlgClosed k] {F : Type u} [Field F] [Algebra k F]
    (Mdl : CurveModel k F) (s : Finset (Place k F)) (W : Mdl.C.Opens)
    (hW : (W : Set Mdl.C) = (⋃ v ∈ s, {((Mdl.pointEquivPlace.symm v).1).base (IsLocalRing.closedPoint k)})ᶜ) :
    Nonempty (Scheme.Opens.toScheme W) := by
  haveI : Infinite (Place k F) := AlgebraicCurve.CurveModel.infinite_place Mdl
  haveI : Infinite (closedPoints Mdl.C) := Infinite.of_injective _ Mdl.placeEquiv.symm.injective
  haveI : Infinite Mdl.C := Infinite.of_injective (fun x : closedPoints Mdl.C => x.1) Subtype.val_injective
  have hfin : (⋃ v ∈ s, ({((Mdl.pointEquivPlace.symm v).1).base (IsLocalRing.closedPoint k)} : Set Mdl.C)).Finite :=
    Set.Finite.biUnion s.finite_toSet (fun _ _ => Set.finite_singleton _)
  have hinf : (W : Set Mdl.C).Infinite := by rw [hW]; exact hfin.infinite_compl
  obtain ⟨z, hz⟩ := hinf.nonempty
  exact ⟨(⟨z, hz⟩ : W)⟩

end EPrincI
p2m_reactivate "P2MW.S_AlgebraicGeometry_RelPicard_isNodeUnitModule_foldr_ofPoint_of_forall_eq_ord_of_hasValue.EPkgTwist P2MW.S_AlgebraicGeometry_RelPicard_isNodeUnitModule_foldr_ofPoint_of_forall_eq_ord_of_hasValue.EPrincI.Place P2MW.S_AlgebraicGeometry_RelPicard_isNodeUnitModule_foldr_ofPoint_of_forall_eq_ord_of_hasValue.EPrincI"

namespace EPkgTwist

p2m_open "P2MW.S_AlgebraicGeometry_RelPicard_isNodeUnitModule_foldr_ofPoint_of_forall_eq_ord_of_hasValue.BKeyAux AlgebraicGeometry.Scheme.Modules"

theorem locRead_of_isFrameOn {K : Type u} [Field K] {Y : Scheme.{u}} (x : Y ⟶ Spec (CommRingCat.of K)) [IsIntegral Y]
    (M : Y.Modules) (U W : Y.Opens) (hWU : W ≤ U) [Nonempty W] (y : Y) (hyU : y ∈ U)
    (v : letI := (AlgebraicCurve.baseToFunctionField x).toAlgebra
      AlgebraicCurve.Place K Y.functionField)
    (E : Γ(M, U)) (hE : IsFrameOn E U) :
    LocRead x M W (M.presheaf.map (homOfLE hWU).op E) y v 0 := by
  letI := (AlgebraicCurve.baseToFunctionField x).toAlgebra
  refine ⟨U, hyU, E, hE, W, hWU, le_rfl, inferInstance, 1, 1, ?_, ?_, ?_, ?_⟩
  · rw [res_res]
  · rw [map_one]; exact one_ne_zero
  · rw [map_one]; exact one_ne_zero
  · rw [sub_self]

theorem locRead_tensorSections_of_isFrameOn {K : Type u} [Field K] {Y : Scheme.{u}} (x : Y ⟶ Spec (CommRingCat.of K))
    [IsIntegral Y]
    (A B M' : Y.Modules) (W : Y.Opens) (e' : Γ(M', W)) (y : Y)
    (v : letI := (AlgebraicCurve.baseToFunctionField x).toAlgebra
      AlgebraicCurve.Place K Y.functionField) (d : ℤ)
    (h : LocRead x M' W e' y v d)
    (Uσ : Y.Opens) (hyσ : y ∈ Uσ) (hWσ : W ≤ Uσ)
    (σ : Γ(A, Uσ)) (hσ : IsFrameOn σ Uσ) (μ : Γ(B, Uσ)) (hμ : IsFrameOn μ Uσ) :
    LocRead x (A ⊗ (B ⊗ M')) W
      (tensorSections (A.presheaf.map (homOfLE hWσ).op σ) (tensorSections (B.presheaf.map (homOfLE hWσ).op μ) e')) y v d := by
  letI := (AlgebraicCurve.baseToFunctionField x).toAlgebra
  obtain ⟨U₀, hyU₀, F, hFf, W₀, hW₀U, hW₀W, hneW₀, num, den, heq, hnum, hden, hd⟩ := h
  refine ⟨U₀ ⊓ Uσ, ⟨hyU₀, hyσ⟩,
    tensorSections (A.presheaf.map (homOfLE inf_le_right).op σ)
      (tensorSections (B.presheaf.map (homOfLE inf_le_right).op μ) (M'.presheaf.map (homOfLE inf_le_left).op F)),
    ?_, W₀, le_inf hW₀U (hW₀W.trans hWσ), hW₀W, hneW₀, num, den, ?_, hnum, hden, hd⟩
  · exact ((hσ.map (homOfLE inf_le_right)).mono inf_le_right).tensorSections
      (((hμ.map (homOfLE inf_le_right)).mono inf_le_right).tensorSections
        ((hFf.map (homOfLE inf_le_left)).mono inf_le_left))
  · rw [map_homOfLE_tensorSections, map_homOfLE_tensorSections, map_homOfLE_tensorSections,
      map_homOfLE_tensorSections, res_res, res_res, res_res, res_res, res_res,
      ← tensorSections_smul_right, ← tensorSections_smul_right, heq, tensorSections_smul_right,
      tensorSections_smul_right]

def cplPts {Y : Scheme.{u}} {V : Type v} (pt : V → Y) (hc : ∀ w, IsClosed ({pt w} : Set Y)) (l : List V) : Y.Opens :=
  ⟨(⋃ w ∈ l, ({pt w} : Set Y))ᶜ, (Set.Finite.isClosed_biUnion (List.finite_toSet l) fun w _ => hc w).isOpen_compl⟩

theorem mem_cplPts {Y : Scheme.{u}} {V : Type v} (pt : V → Y) (hc : ∀ w, IsClosed ({pt w} : Set Y)) (l : List V) (z : Y) :
    z ∈ cplPts pt hc l ↔ ∀ w ∈ l, z ≠ pt w := by
  simp [cplPts]

theorem locRead_eCan {K : Type u} [Field K] {Y : Scheme.{u}} (x : Y ⟶ Spec (CommRingCat.of K))
    [IsIntegral Y] [IsSeparated x] [QuasiCompact x] [SmoothOfRelativeDimension 1 x]
    {V : Type v} [DecidableEq V] (Pt : V → (Spec (CommRingCat.of K) ⟶ Y)) (hPt : ∀ w, Pt w ≫ x = 𝟙 _)
    (hinj : Function.Injective fun w => (Pt w).base (IsLocalRing.closedPoint K))
    (D : V → ℤ) (l : List V) (hl : l.Nodup) (W : Y.Opens) [Nonempty W]
    (hW : ∀ w ∈ l, ((fun w => (Pt w).ker) w).comap W.ι = ⊤)
    (v₀ : V)
    (v : letI := (AlgebraicCurve.baseToFunctionField x).toAlgebra
      AlgebraicCurve.Place K Y.functionField)
    (hv : letI := (AlgebraicCurve.baseToFunctionField x).toAlgebra
      (algebraMap (Y.presheaf.stalk ((Pt v₀).base (IsLocalRing.closedPoint K))) Y.functionField).range =
        v.toValuationSubring.toSubring) :
    LocRead x (twistL (fun w => (Pt w).ker) D l) W (eCan (fun w => (Pt w).ker) D l W hW)
      ((Pt v₀).base (IsLocalRing.closedPoint K)) v (if v₀ ∈ l then D v₀ else 0) := by
  letI := (AlgebraicCurve.baseToFunctionField x).toAlgebra
  have hinv : ∀ w, (Pt w).ker.IsInvertible := fun w => Scheme.Hom.isInvertible_ker_of_comp_eq_id (Pt w) (hPt w)

  have notMem : ∀ {w : V} {U : Y.Opens}, (Pt w).ker.comap U.ι = ⊤ → (Pt w).base (IsLocalRing.closedPoint K) ∉ U :=
    fun {w U} h => (EPrincI.ker_comap_ι_eq_top_iff x (Pt w) (hPt w) U).mp h
  have comapTop : ∀ {w : V} {U : Y.Opens}, (Pt w).base (IsLocalRing.closedPoint K) ∉ U → (Pt w).ker.comap U.ι = ⊤ :=
    fun {w U} h => (EPrincI.ker_comap_ι_eq_top_iff x (Pt w) (hPt w) U).mpr h

  have hclosed : ∀ w, IsClosed ({(Pt w).base (IsLocalRing.closedPoint K)} : Set Y) := fun w => by
    have := isClosedImmersion_of_comp_eq_id x (Pt w) (hPt w)
    have h := (Pt w).isClosedEmbedding.isClosed_range
    have hr : Set.range (Pt w).base = {(Pt w).base (IsLocalRing.closedPoint K)} :=
      Set.range_eq_singleton_iff.mpr (fun z => congrArg (Pt w).base (Subsingleton.elim z (IsLocalRing.closedPoint K)))
    rwa [hr] at h

  have cpl_comap : ∀ (l' : List V), ∀ w ∈ l', (Pt w).ker.comap (cplPts _ hclosed l').ι = ⊤ := fun l' w hw =>
    comapTop (fun h => (mem_cplPts _ hclosed l' _).mp h w hw rfl)
  have le_cpl : ∀ {l' : List V} {U : Y.Opens}, (∀ w ∈ l', (Pt w).ker.comap U.ι = ⊤) → U ≤ cplPts _ hclosed l' :=
    fun {l' U} h z hz => (mem_cplPts _ hclosed l' z).mpr fun w hw hzw => notMem (h w hw) (hzw ▸ hz)
  induction l with
  | nil =>
    rw [if_neg (by simp)]
    have h3 := locRead_of_isFrameOn x (𝟙_ Y.Modules) ⊤ W le_top ((Pt v₀).base (IsLocalRing.closedPoint K)) trivial v
      (unitSection ⊤) (isFrameOn_unitSection ⊤)
    rw [map_unitSection] at h3
    exact h3
  | cons u l ih =>
    have hl' : l.Nodup := (List.nodup_cons.mp hl).2
    have hul : u ∉ l := (List.nodup_cons.mp hl).1
    have hW' : ∀ w ∈ l, (Pt w).ker.comap W.ι = ⊤ := fun w hw => hW w (List.mem_cons_of_mem u hw)
    by_cases hu : u = v₀
    · subst hu
      rw [if_pos List.mem_cons_self]

      have hyU : (Pt u).base (IsLocalRing.closedPoint K) ∈ cplPts _ hclosed l :=
        (mem_cplPts _ hclosed l _).mpr fun w hw h => hul (by rw [show u = w from hinj h]; exact hw)
      have hWU : W ≤ cplPts _ hclosed l := le_cpl hW'
      have h1 := locRead_punctured_eCan x (Pt u) (hPt u) v hv (D u).toNat (-(D u)).toNat
        (twistL (fun w => (Pt w).ker) D l) (cplPts _ hclosed l) W hWU hyU
        (eCan (fun w => (Pt w).ker) D l (cplPts _ hclosed l) (cpl_comap l))
        (isFrameOn_eCan (fun w => (Pt w).ker) D l (cplPts _ hclosed l) (cpl_comap l) (fun w _ => hinv w))
        (oneInv ((Pt u).ker ^ (D u).toNat) W) (oneInv_def _ _)
        (oneMod (comap_pow_eq_top (hW u List.mem_cons_self) (-(D u)).toNat)) (moduleι_oneMod _)
        (isFrameOn_oneInv ((hinv u).pow _) (comap_pow_eq_top (hW u List.mem_cons_self) _)) (isFrameOn_oneMod _)
      rw [map_eCan (fun w => (Pt w).ker) D l (homOfLE hWU) (cpl_comap l) hW', Int.toNat_sub_toNat_neg] at h1
      exact h1
    · have hif : (if v₀ ∈ u :: l then D v₀ else 0) = (if v₀ ∈ l then D v₀ else 0) := by
        simp [List.mem_cons, Ne.symm hu]
      rw [hif]

      have hyσ : (Pt v₀).base (IsLocalRing.closedPoint K) ∈ cplPts _ hclosed [u] :=
        (mem_cplPts _ hclosed [u] _).mpr fun w hw h =>
          hu ((List.mem_singleton.mp hw).symm.trans (hinj h).symm)
      have hWσ : W ≤ cplPts _ hclosed [u] :=
        le_cpl (fun w hw => by rw [List.mem_singleton.mp hw]; exact hW u List.mem_cons_self)
      have hσu : (Pt u).ker.comap (cplPts _ hclosed [u]).ι = ⊤ := cpl_comap [u] u (List.mem_singleton_self u)
      have h2 := locRead_tensorSections_of_isFrameOn x (((Pt u).ker ^ (D u).toNat).invModule)
        (((Pt u).ker ^ (-(D u)).toNat).module) (twistL (fun w => (Pt w).ker) D l) W
        (eCan (fun w => (Pt w).ker) D l W hW') ((Pt v₀).base (IsLocalRing.closedPoint K)) v _
        (ih hl' hW') (cplPts _ hclosed [u]) hyσ hWσ
        (oneInv _ (cplPts _ hclosed [u])) (isFrameOn_oneInv ((hinv u).pow _) (comap_pow_eq_top hσu _))
        (oneMod (comap_pow_eq_top hσu (-(D u)).toNat)) (isFrameOn_oneMod _)
      rw [map_oneInv, map_oneMod _ (homOfLE hWσ) (comap_pow_eq_top (hW u List.mem_cons_self) (-(D u)).toNat)] at h2
      exact h2

end EPkgTwist
p2m_reactivate "P2MW.S_AlgebraicGeometry_RelPicard_isNodeUnitModule_foldr_ofPoint_of_forall_eq_ord_of_hasValue.EPkgTwist P2MW.S_AlgebraicGeometry_RelPicard_isNodeUnitModule_foldr_ofPoint_of_forall_eq_ord_of_hasValue.EPrincI.Place P2MW.S_AlgebraicGeometry_RelPicard_isNodeUnitModule_foldr_ofPoint_of_forall_eq_ord_of_hasValue.EPrincI"

namespace EPrincI

open _root_.AlgebraicGeometry.Scheme.Modules in

theorem exists_iso_germ_eCan_eq_mul_model {k : Type u} [Field k] [IsAlgClosed k]
    {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of k)) [IsProper c] [SmoothOfRelativeDimension 1 c] [GeometricallyIntegral c]
    (F : Type u) [Field F] [Algebra k F] [HasPrincipalDivisors k F] (hCB : ConstantsAreBase k F)
    (Mdl : CurveModel k F) (e : Mdl.C ≅ C) (he : e.hom ≫ c = Mdl.toBase)
    (pt : Place k F → (Spec (CommRingCat.of k) ⟶ C)) (hpt : ∀ v, pt v ≫ c = 𝟙 _)
    (hpt' : ∀ v, pt v = (Mdl.pointEquivPlace.symm v).1 ≫ e.hom)
    (D : Place k F →₀ ℤ) (g : F) (hg : g ≠ 0) (ha : ∀ v : Place k F, D v = v.ord g) :
    ∃ (β' : EPkgTwist.twistL (fun v => ((RelEffCartierDiv.ofPoint c (pt v) (hpt v)).I).comap (modelIso c Mdl e)) ⇑D
        D.support.toList ≅ 𝟙_ Mdl.C.Modules) (cst : kˣ),
      ∀ (W' : Mdl.C.Opens)
        (hW' : ∀ v ∈ D.support.toList, (((RelEffCartierDiv.ofPoint c (pt v) (hpt v)).I).comap (modelIso c Mdl e)).comap W'.ι = ⊤)
        [Nonempty (Scheme.Opens.toScheme W')],
        Mdl.ffEquiv.symm (Mdl.C.germToFunctionField W' (β'.hom.app W'
          (EPkgTwist.eCan (fun v => ((RelEffCartierDiv.ofPoint c (pt v) (hpt v)).I).comap (modelIso c Mdl e)) ⇑D
            D.support.toList W' hW'))) = algebraMap k F (cst : k) * g := by
  classical

  have hQ' : (fun v => ((RelEffCartierDiv.ofPoint c (pt v) (hpt v)).I).comap (modelIso c Mdl e)) =
      fun v => ((Mdl.pointEquivPlace.symm v).1).ker :=
    funext (fun v => comap_modelIso_ofPoint_I c Mdl e he pt hpt hpt' v)
  suffices H : ∀ (Q : Place k F → Mdl.C.IdealSheafData), Q = (fun v => ((Mdl.pointEquivPlace.symm v).1).ker) →
      ∃ (β' : EPkgTwist.twistL Q ⇑D D.support.toList ≅ 𝟙_ Mdl.C.Modules) (cst : kˣ),
        ∀ (W' : Mdl.C.Opens) (hW' : ∀ v ∈ D.support.toList, (Q v).comap W'.ι = ⊤) [Nonempty (Scheme.Opens.toScheme W')],
          Mdl.ffEquiv.symm (Mdl.C.germToFunctionField W' (β'.hom.app W' (EPkgTwist.eCan Q ⇑D D.support.toList W' hW'))) =
            algebraMap k F (cst : k) * g from
    H _ hQ'
  intro Q hQ
  subst hQ

  letI := Mdl.functionFieldAlgebra
  set P : Place k F → (Spec (CommRingCat.of k) ⟶ Mdl.C) := fun v => (Mdl.pointEquivPlace.symm v).1 with hPdef
  have hP : ∀ v, P v ≫ Mdl.toBase = 𝟙 _ := fun v => (Mdl.pointEquivPlace.symm v).2
  set l := D.support.toList with hl
  set Q : Place k F → Mdl.C.IdealSheafData := fun v => ((Mdl.pointEquivPlace.symm v).1).ker with hQdef
  have hQinv : ∀ v, (Q v).IsInvertible := fun v => Scheme.Hom.isInvertible_ker_of_comp_eq_id (P v) (hP v)
  set M := EPkgTwist.twistL Q ⇑D l with hM
  have hMinv : Scheme.Modules.IsInvertible M := EPkgTwist.isInvertible_twistL Q ⇑D l (fun v _ => hQinv v)

  have hPpt : ∀ v, pointEquivClosedPoint Mdl.toBase (Mdl.pointEquivPlace.symm v) = Mdl.placeEquiv.symm v := by
    intro v
    change pointEquivClosedPoint Mdl.toBase (((pointEquivClosedPoint Mdl.toBase).trans Mdl.placeEquiv).symm v) = _
    simp only [Equiv.symm_trans_apply, Equiv.apply_symm_apply]
  have hPbase : ∀ v, (P v).base (IsLocalRing.closedPoint k) = (Mdl.placeEquiv.symm v).1 := fun v =>
    congrArg Subtype.val (hPpt v)
  have hplaceP : ∀ v, Mdl.placeOfPoint (pointEquivClosedPoint Mdl.toBase (Mdl.pointEquivPlace.symm v)) = v := by
    intro v; rw [hPpt, ← CurveModel.placeEquiv_apply, Equiv.apply_symm_apply]
  have hinjP : Function.Injective fun w => (P w).base (IsLocalRing.closedPoint k) := by
    intro w w' hww
    have h1 : Mdl.placeEquiv.symm w = Mdl.placeEquiv.symm w' := Subtype.ext (by rw [← hPbase, ← hPbase]; exact hww)
    exact Mdl.placeEquiv.symm.injective h1

  obtain ⟨D_M, φ, hnat, hsmul, hinj, hrange, hgen⟩ :=
    Scheme.Modules.IsInvertible.exists_divisor_range_eq_lSpaceOn Mdl.toBase M hMinv

  let W₀ : Mdl.C.Opens := ⟨(⋃ v ∈ D.support, {(P v).base (IsLocalRing.closedPoint k)})ᶜ, by
    rw [isOpen_compl_iff]
    refine Set.Finite.isClosed_biUnion (Finset.finite_toSet _) (fun v _ => ?_)
    rw [hPbase]
    exact (Mdl.placeEquiv.symm v).2⟩
  haveI hW₀ne : Nonempty (Scheme.Opens.toScheme W₀) := nonempty_compl_of_finite Mdl D.support W₀ rfl
  have hW₀ : ∀ v ∈ l, (Q v).comap W₀.ι = ⊤ := by
    intro v hv
    rw [ker_comap_ι_eq_top_iff Mdl.toBase (P v) (hP v) W₀]
    intro hmem
    apply hmem
    simp only [Set.mem_iUnion, Set.mem_singleton_iff]
    exact ⟨v, Finset.mem_toList.mp hv, rfl⟩
  have hframe₀ : IsFrameOn (EPkgTwist.eCan Q ⇑D l W₀ hW₀) W₀ := EPkgTwist.isFrameOn_eCan Q ⇑D l W₀ hW₀ (fun v _ => hQinv v)
  set e₀ : Mdl.C.functionField := φ W₀ (EPkgTwist.eCan Q ⇑D l W₀ hW₀) with he₀def
  have he₀ : e₀ ≠ 0 := fun h0 =>
    BKeyAux.ne_zero_of_isFrameOn hframe₀ (hinj W₀ inferInstance (h0.trans (map_zero _).symm))

  set τ : F ≃+* Mdl.C.functionField := Mdl.ffEquiv with hτdef
  have hτ : ∀ a : k, τ (algebraMap k F a) = algebraMap k Mdl.C.functionField a := Mdl.ffEquiv_algebraMap
  have hτg : τ g ≠ 0 := (map_ne_zero τ).mpr hg
  set h : Mdl.C.functionField := e₀ * (τ g)⁻¹ with hhdef
  have hh : h ≠ 0 := mul_ne_zero he₀ (inv_ne_zero hτg)

  have hctr' : ∀ (y : Mdl.C) (hy : IsClosed ({y} : Set Mdl.C)),
      (algebraMap (Mdl.C.presheaf.stalk y) Mdl.C.functionField).range =
        (EPrincI.Place.mapEquiv τ hτ (Mdl.placeOfPoint ⟨y, hy⟩)).toValuationSubring.toSubring :=
    fun y hy => CurveModel.range_algebraMap_stalk_eq_mapEquiv Mdl ⟨y, hy⟩

  have hord : ∀ (y : Mdl.C), IsClosed ({y} : Set Mdl.C) → ∀ w : Place k Mdl.C.functionField,
      (algebraMap (Mdl.C.presheaf.stalk y) Mdl.C.functionField).range = w.toValuationSubring.toSubring →
      w.ord h + D_M w = 0 := by
    intro y hy w hw
    set v₀ : Place k F := Mdl.placeOfPoint ⟨y, hy⟩ with hv₀
    have hw' : w = EPrincI.Place.mapEquiv τ hτ v₀ := by
      apply AlgebraicCurve.Place.ext
      apply ValuationSubring.toSubring_injective
      rw [← hw, hctr' y hy]
    have hyv₀ : (P v₀).base (IsLocalRing.closedPoint k) = y := by
      rw [hPbase, hv₀, ← CurveModel.placeEquiv_apply, Equiv.symm_apply_apply]

    have hLI := EPkgTwist.locRead_eCan Mdl.toBase P hP hinjP ⇑D l (Finset.nodup_toList _) W₀ hW₀ v₀ w
      (by rw [hyv₀]; exact hw)
    rw [hyv₀] at hLI
    have hordE : w.ord e₀ = (if v₀ ∈ l then D v₀ else 0) - D_M w :=
      EPkgTwist.ord_presentation_of_locRead Mdl.toBase M W₀ _ y hy w hw _ hLI D_M φ hnat hsmul hinj hgen

    have hordg : w.ord (τ g) = D v₀ := by rw [hw', EPrincI.Place.ord_mapEquiv, ← ha]
    rw [hhdef, w.ord_mul he₀ (inv_ne_zero hτg), AlgebraicCurve.Place.ord_inv, hordE, hordg]
    split_ifs with hmem
    · ring
    · have hD0 : D v₀ = 0 := Finsupp.notMem_support_iff.mp (fun hs => hmem (Finset.mem_toList.mpr hs))
      rw [hD0]; ring
  have hctr : ∀ (y : Mdl.C), IsClosed ({y} : Set Mdl.C) → ∃ w : Place k Mdl.C.functionField,
      (algebraMap (Mdl.C.presheaf.stalk y) Mdl.C.functionField).range = w.toValuationSubring.toSubring :=
    fun y hy => ⟨_, hctr' y hy⟩

  obtain ⟨β, hβ⟩ := EPkgTwist.exists_iso_unit_forall_algebraMap_app_eq_inv_mul_of_forall_ord_add_eq_zero Mdl.toBase M hMinv
    D_M φ hnat hsmul hinj hrange hgen h hh hord hctr
  refine ⟨β, 1, fun W' hW' _ => ?_⟩

  have hne : Nonempty (Scheme.Opens.toScheme (W' ⊓ W₀)) := by
    obtain ⟨a⟩ := ‹Nonempty (Scheme.Opens.toScheme W')›
    obtain ⟨b⟩ := hW₀ne
    obtain ⟨z, hz⟩ := nonempty_preirreducible_inter W'.isOpen W₀.isOpen ⟨a.1, a.2⟩ ⟨b.1, b.2⟩
    exact ⟨⟨z, hz⟩⟩
  have hWW : ∀ v ∈ l, (Q v).comap (W' ⊓ W₀ : Mdl.C.Opens).ι = ⊤ :=
    fun v hv => EPkgTwist.comap_ι_eq_top_of_le (hW₀ v hv) inf_le_right
  have h1 : φ W' (EPkgTwist.eCan Q ⇑D l W' hW') = e₀ := by
    rw [← hnat W' (W' ⊓ W₀) inf_le_left hne, EPkgTwist.map_eCan Q ⇑D l (homOfLE inf_le_left) hW' hWW,
      ← EPkgTwist.map_eCan Q ⇑D l (homOfLE inf_le_right) hW₀ hWW, hnat W₀ (W' ⊓ W₀) inf_le_right hne]

  have h2 := hβ W' (EPkgTwist.eCan Q ⇑D l W' hW')
  change τ.symm (algebraMap Γ(Mdl.C, W') Mdl.C.functionField
    (Scheme.Modules.ofUnitSection W' (β.hom.app W' (EPkgTwist.eCan Q ⇑D l W' hW')))) = _
  rw [h2, h1, hhdef, mul_inv, inv_inv, mul_assoc, mul_comm (τ g), ← mul_assoc, inv_mul_cancel₀ he₀, one_mul,
    Units.val_one, map_one, one_mul]
  exact τ.symm_apply_apply g

end EPrincI
p2m_reactivate "P2MW.S_AlgebraicGeometry_RelPicard_isNodeUnitModule_foldr_ofPoint_of_forall_eq_ord_of_hasValue.EPkgTwist P2MW.S_AlgebraicGeometry_RelPicard_isNodeUnitModule_foldr_ofPoint_of_forall_eq_ord_of_hasValue.EPrincI.Place P2MW.S_AlgebraicGeometry_RelPicard_isNodeUnitModule_foldr_ofPoint_of_forall_eq_ord_of_hasValue.EPrincI"

end
p2m_reactivate "P2MW.S_AlgebraicGeometry_RelPicard_isNodeUnitModule_foldr_ofPoint_of_forall_eq_ord_of_hasValue.EPkgTwist P2MW.S_AlgebraicGeometry_RelPicard_isNodeUnitModule_foldr_ofPoint_of_forall_eq_ord_of_hasValue.EPrincI.Place P2MW.S_AlgebraicGeometry_RelPicard_isNodeUnitModule_foldr_ofPoint_of_forall_eq_ord_of_hasValue.EPrincI"

noncomputable section

namespace EPkgTwist

p2m_open "AlgebraicGeometry.Scheme.IdealSheafData AlgebraicGeometry.Scheme.Modules TopologicalSpace"

section Alpha4

variable {Y Y' : Scheme.{u}} (f : Y' ⟶ Y)

theorem pullbackTensorUnitObjIso_eq_pullbackUnitIso :
    Scheme.Modules.pullbackTensorUnitObjIso f = Scheme.Modules.pullbackUnitIso f := by
  ext : 1
  apply Scheme.Modules.pullback_hom_ext
  intro U s
  have hs : s = (ofUnitSection U s) • unitSection U := by rw [smul_unitSection]; rfl
  have h1 := pullbackTensorUnitObjIso_hom_app_pullbackLocalSection_unitSection f U
  have h2 : (Scheme.Modules.pullbackUnitIso f).hom.app (f ⁻¹ᵁ U) (pullbackLocalSection f (unitSection U)) = unitSection (f ⁻¹ᵁ U) := by
    have := pullbackUnitIso_hom_app_pullbackLocalSection_toUnitSection f U 1
    rw [map_one] at this
    exact this
  rw [hs, pullbackLocalSection_smul, Scheme.Modules.Hom.app_smul, Scheme.Modules.Hom.app_smul]
  exact congrArg _ (h1.trans h2.symm)

theorem pullbackLocalSection_unitSection (U : Y.Opens) :
    pullbackLocalSection f (unitSection U) = (Scheme.Modules.pullbackUnitIso f).inv.app (f ⁻¹ᵁ U) (unitSection (f ⁻¹ᵁ U)) := by
  have h2 : (Scheme.Modules.pullbackUnitIso f).hom.app (f ⁻¹ᵁ U) (pullbackLocalSection f (unitSection U)) = unitSection (f ⁻¹ᵁ U) := by
    have := pullbackUnitIso_hom_app_pullbackLocalSection_toUnitSection f U 1
    rw [map_one] at this
    exact this
  have h := congrArg ((Scheme.Modules.pullbackUnitIso f).inv.app (f ⁻¹ᵁ U)) h2
  rw [← CategoryTheory.comp_apply, ← Scheme.Modules.Hom.comp_app, Iso.hom_inv_id, Scheme.Modules.Hom.id_app,
    CategoryTheory.id_apply] at h
  exact h

theorem unitToPushforwardUnit_val_app (U : Y.Opens) (r : Γ(Y, U)) :
    (ConcreteCategory.hom ((f.unitToPushforwardUnit).val.app (Opposite.op U))) r = f.app U r := rfl

theorem moduleToPushforwardComapModule_comp_map_moduleι (I : Y.IdealSheafData) :
    I.moduleToPushforwardComapModule f ≫ (SheafOfModules.pushforward f.toRingCatSheafHom).map (I.comap f).moduleι =
      I.moduleι ≫ f.unitToPushforwardUnit := by
  rw [Scheme.IdealSheafData.moduleToPushforwardComapModule, Category.assoc]
  exact (congrArg (kernel.lift _ _ (I.kernelι_unitToPushforwardUnit_map_eq_zero f) ≫ ·)
    (PreservesKernel.iso_inv_ι _ _)).trans (kernel.lift_ι _ _ _)

theorem map_moduleι_comp_pullbackUnitIso_hom (I : Y.IdealSheafData) :
    (Scheme.Modules.pullback f).map I.moduleι ≫ (Scheme.Modules.pullbackUnitIso f).hom =
      I.pullbackModuleComparison f ≫ (I.comap f).moduleι := by
  apply Scheme.Modules.pullback_hom_ext
  intro U s
  have e1 : ((Scheme.Modules.pullback f).map I.moduleι).app (f ⁻¹ᵁ U) (pullbackLocalSection f s) =
      pullbackLocalSection f (I.moduleι.app U s) := (pullbackLocalSection_app f I.moduleι s).symm
  have e2 : (Scheme.Modules.pullbackUnitIso f).hom.app (f ⁻¹ᵁ U) (pullbackLocalSection f (I.moduleι.app U s)) =
      toUnitSection (f ⁻¹ᵁ U) (f.app U (ofUnitSection U (I.moduleι.app U s))) :=
    pullbackUnitIso_hom_app_pullbackLocalSection_toUnitSection f U (ofUnitSection U (I.moduleι.app U s))
  have e3 : (I.pullbackModuleComparison f).app (f ⁻¹ᵁ U) (pullbackLocalSection f s) =
      ((I.moduleToPushforwardComapModule f).app U s : Γ((I.comap f).module, f ⁻¹ᵁ U)) :=
    homEquiv_symm_app_pullbackLocalSection f (I.moduleToPushforwardComapModule f) s
  have e4 : (I.comap f).moduleι.app (f ⁻¹ᵁ U) ((I.moduleToPushforwardComapModule f).app U s : Γ((I.comap f).module, f ⁻¹ᵁ U)) =
      (ConcreteCategory.hom ((f.unitToPushforwardUnit).val.app (Opposite.op U))) (I.moduleι.app U s) :=
    congrArg (fun φ => (ConcreteCategory.hom (SheafOfModules.Hom.val φ |>.app (Opposite.op U))) s)
      (moduleToPushforwardComapModule_comp_map_moduleι f I)
  have lhs : ((Scheme.Modules.pullback f).map I.moduleι ≫ (Scheme.Modules.pullbackUnitIso f).hom).app (f ⁻¹ᵁ U)
      (pullbackLocalSection f s) = toUnitSection (f ⁻¹ᵁ U) (f.app U (ofUnitSection U (I.moduleι.app U s))) := by
    rw [Scheme.Modules.Hom.comp_app, CategoryTheory.comp_apply]
    exact (congrArg _ e1).trans e2
  have rhs : (I.pullbackModuleComparison f ≫ (I.comap f).moduleι).app (f ⁻¹ᵁ U) (pullbackLocalSection f s) =
      (ConcreteCategory.hom ((f.unitToPushforwardUnit).val.app (Opposite.op U))) (I.moduleι.app U s) := by
    rw [Scheme.Modules.Hom.comp_app, CategoryTheory.comp_apply]
    exact (congrArg _ e3).trans e4
  exact lhs.trans (rhs.trans (unitToPushforwardUnit_val_app f U _)).symm

variable {V : Type v}

theorem moduleComparisonIso_hom_app_pullbackLocalSection_oneMod (I : Y.IdealSheafData) (hI : I.IsInvertible)
    (hI' : (I.comap f).IsInvertible) {W : Y.Opens} (hW : I.comap W.ι = ⊤) (hW' : (I.comap f).comap ((f ⁻¹ᵁ W : Y'.Opens)).ι = ⊤) :
    (moduleComparisonIso f I hI hI').hom.app (f ⁻¹ᵁ W) (pullbackLocalSection f (oneMod hW)) = oneMod hW' := by
  apply eq_oneMod_of_moduleι_eq
  have h1 : (Scheme.Modules.pullbackUnitIso f).hom.app (f ⁻¹ᵁ W) (pullbackLocalSection f (unitSection W)) = unitSection (f ⁻¹ᵁ W) := by
    have := pullbackUnitIso_hom_app_pullbackLocalSection_toUnitSection f W 1
    rw [map_one] at this
    exact this
  have hsq := congrArg (fun φ => Scheme.Modules.Hom.app φ (f ⁻¹ᵁ W) (pullbackLocalSection f (oneMod hW)))
    (map_moduleι_comp_pullbackUnitIso_hom f I)
  have e1 : ((Scheme.Modules.pullback f).map I.moduleι).app (f ⁻¹ᵁ W) (pullbackLocalSection f (oneMod hW)) =
      pullbackLocalSection f (I.moduleι.app W (oneMod hW)) := (pullbackLocalSection_app f I.moduleι (oneMod hW)).symm
  dsimp only at hsq
  have lhs : ((Scheme.Modules.pullback f).map I.moduleι ≫ (Scheme.Modules.pullbackUnitIso f).hom).app (f ⁻¹ᵁ W)
      (pullbackLocalSection f (oneMod hW)) = unitSection (f ⁻¹ᵁ W) := by
    rw [Scheme.Modules.Hom.comp_app, CategoryTheory.comp_apply]
    exact (congrArg _ e1).trans ((congrArg (fun t => (Scheme.Modules.pullbackUnitIso f).hom.app (f ⁻¹ᵁ W)
      (pullbackLocalSection f t)) (moduleι_oneMod hW)).trans h1)
  have rhs : (I.pullbackModuleComparison f ≫ (I.comap f).moduleι).app (f ⁻¹ᵁ W) (pullbackLocalSection f (oneMod hW)) =
      (I.comap f).moduleι.app (f ⁻¹ᵁ W) ((moduleComparisonIso f I hI hI').hom.app (f ⁻¹ᵁ W) (pullbackLocalSection f (oneMod hW))) := by
    rw [Scheme.Modules.Hom.comp_app, CategoryTheory.comp_apply]; rfl
  exact rhs.symm.trans (hsq.symm.trans lhs)

theorem pullbackUnitIso_inv_map_invModuleSection_dualComparison (I : Y.IdealSheafData) (hI : I.IsInvertible)
    (hI' : (I.comap f).IsInvertible) :
    (Scheme.Modules.pullbackUnitIso f).inv ≫ (Scheme.Modules.pullback f).map I.invModuleSection ≫
        dualComparison f (moduleComparisonIso f I hI hI').inv =
      (I.comap f).invModuleSection := by

  rw [← pullbackTensorUnitObjIso_eq_pullbackUnitIso]
  show (Scheme.Modules.pullbackTensorUnitObjIso f).inv ≫
      (Scheme.Modules.pullback f).map (MonoidalClosed.curry ((ρ_ I.module).hom ≫ I.moduleι)) ≫
        MonoidalClosed.curry ((moduleComparisonIso f I hI hI').inv ▷ _ ≫
          (Functor.Monoidal.μIso (Scheme.Modules.pullback f) I.module (Scheme.Modules.dual I.module)).hom ≫
            (Scheme.Modules.pullback f).map ((ihom.ev I.module).app (𝟙_ Y.Modules)) ≫
              (Scheme.Modules.pullbackTensorUnitObjIso f).hom) =
      MonoidalClosed.curry ((ρ_ (I.comap f).module).hom ≫ (I.comap f).moduleι)
  rw [← MonoidalClosed.curry_natural_left, ← MonoidalClosed.curry_natural_left]
  congr 1

  rw [MonoidalCategory.whisker_exchange_assoc, MonoidalCategory.whisker_exchange_assoc]

  rw [Functor.Monoidal.μIso_hom, Functor.LaxMonoidal.μ_natural_right_assoc, ← Functor.map_comp_assoc,
    MonoidalClosed.whiskerLeft_curry_ihom_ev_app]
  have hmc := (Scheme.Modules.pullback f).map_comp_assoc (ρ_ I.module).hom I.moduleι (Scheme.Modules.pullbackTensorUnitObjIso f).hom
  erw [hmc]

  rw [Scheme.Modules.pullbackTensorUnitObjIso, Iso.symm_inv, Iso.symm_hom, Functor.Monoidal.εIso_hom,
    ← Functor.LaxMonoidal.right_unitality_assoc]

  rw [MonoidalCategory.rightUnitor_naturality_assoc]
  congr 1
  rw [show (Functor.Monoidal.εIso (Scheme.Modules.pullback f)).inv = (Scheme.Modules.pullbackUnitIso f).hom from
      congrArg Iso.hom (pullbackTensorUnitObjIso_eq_pullbackUnitIso f)]
  erw [map_moduleι_comp_pullbackUnitIso_hom]
  rw [← moduleComparisonIso_hom f I hI hI', Iso.inv_hom_id_assoc]

theorem invModuleComparisonIso_hom_app_pullbackLocalSection_oneInv (I : Y.IdealSheafData) (hI : I.IsInvertible)
    (hI' : (I.comap f).IsInvertible) (W : Y.Opens) :
    (invModuleComparisonIso f I hI hI').hom.app (f ⁻¹ᵁ W) (pullbackLocalSection f (oneInv I W)) = oneInv (I.comap f) (f ⁻¹ᵁ W) := by
  have hM := congrArg (fun φ => Scheme.Modules.Hom.app φ (f ⁻¹ᵁ W) (unitSection (f ⁻¹ᵁ W)))
    (pullbackUnitIso_inv_map_invModuleSection_dualComparison f I hI hI')
  simp only [Scheme.Modules.Hom.comp_app, CategoryTheory.comp_apply] at hM
  have e1 : pullbackLocalSection f (oneInv I W) =
      ((Scheme.Modules.pullback f).map I.invModuleSection).app (f ⁻¹ᵁ W) (pullbackLocalSection f (unitSection W)) :=
    pullbackLocalSection_app f I.invModuleSection (unitSection W)
  rw [e1, pullbackLocalSection_unitSection]
  exact hM

theorem Hom.comp_app_apply {X : Scheme.{u}} {M N K : X.Modules} (φ : M ⟶ N) (ψ : N ⟶ K) (U : X.Opens) (x : Γ(M, U)) :
    (φ ≫ ψ).app U x = ψ.app U (φ.app U x) := rfl

theorem twistLComparisonIso_hom_app_pullbackLocalSection_eCan_cons_raw (P : V → Y.IdealSheafData) (Q : V → Y'.IdealSheafData)
    (D : V → ℤ) (v : V) (l : List V)
    (h : ∀ w ∈ v :: l, (P w).IsInvertible ∧ (P w).comap f = Q w ∧ (Q w).IsInvertible) (U : Y.Opens)
    (hU : ∀ w ∈ v :: l, (P w).comap U.ι = ⊤)
    (hP : (P v).IsInvertible) (hcv : ∀ n : ℕ, (P v ^ n).comap f = Q v ^ n) (hPc : ∀ n : ℕ, ((P v ^ n).comap f).IsInvertible) :
    (twistLComparisonIso f P Q D (v :: l) h).hom.app (f ⁻¹ᵁ U) (pullbackLocalSection f (eCan P D (v :: l) U hU)) =
      (Scheme.Modules.pullbackTensorObjIso f _ _ ≪≫
        ((invModuleComparisonIso f (P v ^ (D v).toNat) (hP.pow _) (hPc _) ≪≫
            eqToIso (congrArg Scheme.IdealSheafData.invModule (hcv _))) ⊗ᵢ
          (Scheme.Modules.pullbackTensorObjIso f _ _ ≪≫
            ((moduleComparisonIso f (P v ^ (-(D v)).toNat) (hP.pow _) (hPc _) ≪≫
                eqToIso (congrArg Scheme.IdealSheafData.module (hcv _))) ⊗ᵢ
              twistLComparisonIso f P Q D l (fun w hw => h w (List.mem_cons_of_mem v hw)))))).hom.app (f ⁻¹ᵁ U)
        (pullbackLocalSection f
          (tensorSections (oneInv (P v ^ (D v).toNat) U)
            (tensorSections (oneMod (comap_pow_eq_top (hU v List.mem_cons_self) (-(D v)).toNat))
              (eCan P D l U (fun w hw => hU w (List.mem_cons_of_mem v hw)))))) := rfl

theorem twistLComparisonIso_hom_app_pullbackLocalSection_eCan_cons (P : V → Y.IdealSheafData) (Q : V → Y'.IdealSheafData)
    (D : V → ℤ) (v : V) (l : List V)
    (h : ∀ w ∈ v :: l, (P w).IsInvertible ∧ (P w).comap f = Q w ∧ (Q w).IsInvertible) (U : Y.Opens)
    (hU : ∀ w ∈ v :: l, (P w).comap U.ι = ⊤)
    (hP : (P v).IsInvertible) (hcv : ∀ n : ℕ, (P v ^ n).comap f = Q v ^ n) (hPc : ∀ n : ℕ, ((P v ^ n).comap f).IsInvertible) :
    (twistLComparisonIso f P Q D (v :: l) h).hom.app (f ⁻¹ᵁ U) (pullbackLocalSection f (eCan P D (v :: l) U hU)) =
      tensorSections
        (((invModuleComparisonIso f (P v ^ (D v).toNat) (hP.pow _) (hPc _) ≪≫
            eqToIso (congrArg Scheme.IdealSheafData.invModule (hcv _))).hom).app (f ⁻¹ᵁ U)
              (pullbackLocalSection f (oneInv (P v ^ (D v).toNat) U)))
        (tensorSections
          (((moduleComparisonIso f (P v ^ (-(D v)).toNat) (hP.pow _) (hPc _) ≪≫
              eqToIso (congrArg Scheme.IdealSheafData.module (hcv _))).hom).app (f ⁻¹ᵁ U)
                (pullbackLocalSection f (oneMod (comap_pow_eq_top (hU v List.mem_cons_self) (-(D v)).toNat))))
          ((twistLComparisonIso f P Q D l (fun w hw => h w (List.mem_cons_of_mem v hw))).hom.app (f ⁻¹ᵁ U)
            (pullbackLocalSection f (eCan P D l U (fun w hw => hU w (List.mem_cons_of_mem v hw)))))) := by
  rw [twistLComparisonIso_hom_app_pullbackLocalSection_eCan_cons_raw f P Q D v l h U hU hP hcv hPc,
    Iso.trans_hom (Scheme.Modules.pullbackTensorObjIso f _ _), Scheme.Modules.Hom.comp_app, CategoryTheory.comp_apply,
    pullbackTensorObjIso_hom_app_pullbackLocalSection, tensorIso_hom, tensorHom_app_tensorSections,
    Iso.trans_hom (Scheme.Modules.pullbackTensorObjIso f _ _), Scheme.Modules.Hom.comp_app, CategoryTheory.comp_apply,
    pullbackTensorObjIso_hom_app_pullbackLocalSection, tensorIso_hom, tensorHom_app_tensorSections]

theorem twistLComparisonIso_hom_app_pullbackLocalSection_eCan (P : V → Y.IdealSheafData) (Q : V → Y'.IdealSheafData) (D : V → ℤ) :
    ∀ (l : List V) (h : ∀ v ∈ l, (P v).IsInvertible ∧ (P v).comap f = Q v ∧ (Q v).IsInvertible)
      (W : Y.Opens) (hW : ∀ v ∈ l, (P v).comap W.ι = ⊤) (hW' : ∀ v ∈ l, (Q v).comap ((f ⁻¹ᵁ W : Y'.Opens)).ι = ⊤),
      (twistLComparisonIso f P Q D l h).hom.app (f ⁻¹ᵁ W) (pullbackLocalSection f (eCan P D l W hW)) =
        eCan Q D l (f ⁻¹ᵁ W) hW' := by
  intro l
  induction l with
  | nil =>
      intro h W hW hW'
      exact pullbackTensorUnitObjIso_hom_app_pullbackLocalSection_unitSection f W
  | cons v l ihl =>
      intro h W hW hW'
      have hP : (P v).IsInvertible := (h v List.mem_cons_self).1
      have hPQ : (P v).comap f = Q v := (h v List.mem_cons_self).2.1
      have hcv : ∀ n : ℕ, (P v ^ n).comap f = Q v ^ n := fun n => by rw [comap_pow, hPQ]
      have hPc : ∀ n : ℕ, ((P v ^ n).comap f).IsInvertible := fun n => by rw [hcv]; exact (h v List.mem_cons_self).2.2.pow n
      have ih := ihl (fun w hw => h w (List.mem_cons_of_mem v hw)) W
        (fun w hw => hW w (List.mem_cons_of_mem v hw)) (fun w hw => hW' w (List.mem_cons_of_mem v hw))
      have hA : ((invModuleComparisonIso f (P v ^ (D v).toNat) (hP.pow _) (hPc _) ≪≫
          eqToIso (congrArg Scheme.IdealSheafData.invModule (hcv _))).hom).app (f ⁻¹ᵁ W)
          (pullbackLocalSection f (oneInv (P v ^ (D v).toNat) W)) = oneInv (Q v ^ (D v).toNat) (f ⁻¹ᵁ W) := by
        rw [Iso.trans_hom, Hom.comp_app_apply,
          invModuleComparisonIso_hom_app_pullbackLocalSection_oneInv, eqToIso.hom, eqToHom_invModule_app_oneInv (hcv _)]
      have hB : ((moduleComparisonIso f (P v ^ (-(D v)).toNat) (hP.pow _) (hPc _) ≪≫
          eqToIso (congrArg Scheme.IdealSheafData.module (hcv _))).hom).app (f ⁻¹ᵁ W)
          (pullbackLocalSection f (oneMod (comap_pow_eq_top (hW v List.mem_cons_self) (-(D v)).toNat))) =
          oneMod (comap_pow_eq_top (hW' v List.mem_cons_self) (-(D v)).toNat) := by
        have hc' : ((P v ^ (-(D v)).toNat).comap f).comap ((f ⁻¹ᵁ W : Y'.Opens)).ι = ⊤ := by
          rw [hcv]; exact comap_pow_eq_top (hW' v List.mem_cons_self) _
        rw [Iso.trans_hom, Hom.comp_app_apply,
          moduleComparisonIso_hom_app_pullbackLocalSection_oneMod f _ (hP.pow _) (hPc _) _ hc', eqToIso.hom,
          eqToHom_module_app_oneMod (hcv _)]
      rw [twistLComparisonIso_hom_app_pullbackLocalSection_eCan_cons f P Q D v l h W hW hP hcv hPc, hA, hB, ih,
        eCan_cons Q D v l (f ⁻¹ᵁ W) hW']

end Alpha4
p2m_reactivate "P2MW.S_AlgebraicGeometry_RelPicard_isNodeUnitModule_foldr_ofPoint_of_forall_eq_ord_of_hasValue.EPkgTwist P2MW.S_AlgebraicGeometry_RelPicard_isNodeUnitModule_foldr_ofPoint_of_forall_eq_ord_of_hasValue.EPrincI.Place P2MW.S_AlgebraicGeometry_RelPicard_isNodeUnitModule_foldr_ofPoint_of_forall_eq_ord_of_hasValue.EPrincI"

end EPkgTwist
p2m_reactivate "P2MW.S_AlgebraicGeometry_RelPicard_isNodeUnitModule_foldr_ofPoint_of_forall_eq_ord_of_hasValue.EPkgTwist P2MW.S_AlgebraicGeometry_RelPicard_isNodeUnitModule_foldr_ofPoint_of_forall_eq_ord_of_hasValue.EPrincI.Place P2MW.S_AlgebraicGeometry_RelPicard_isNodeUnitModule_foldr_ofPoint_of_forall_eq_ord_of_hasValue.EPrincI"

namespace EPkg

p2m_open "P2MW.S_AlgebraicGeometry_RelPicard_isNodeUnitModule_foldr_ofPoint_of_forall_eq_ord_of_hasValue.EPkgTwist AlgebraicGeometry.Scheme.IdealSheafData"

def coOpen {X C : Scheme.{u}} (i : C ⟶ X) [IsClosedImmersion i] : X.Opens :=
  ⟨(Set.range i.base)ᶜ, i.isClosedEmbedding.isClosed_range.isOpen_compl⟩

@[scoped simp] theorem coe_coOpen {X C : Scheme.{u}} (i : C ⟶ X) [IsClosedImmersion i] :
    (coOpen i : Set X) = (Set.range i.base)ᶜ := rfl

theorem ofPoint_I_congr {𝒞 S T : Scheme.{u}} (f : 𝒞 ⟶ S) [IsSeparated f] {g : T ⟶ S}
    {a a' : T ⟶ 𝒞} (ha : a ≫ f = g) (ha' : a' ≫ f = g) (h : a = a') :
    (RelEffCartierDiv.ofPoint f a ha).I = (RelEffCartierDiv.ofPoint f a' ha').I := by
  subst h; rfl

end EPkg
p2m_reactivate "P2MW.S_AlgebraicGeometry_RelPicard_isNodeUnitModule_foldr_ofPoint_of_forall_eq_ord_of_hasValue.EPkgTwist P2MW.S_AlgebraicGeometry_RelPicard_isNodeUnitModule_foldr_ofPoint_of_forall_eq_ord_of_hasValue.EPrincI.Place P2MW.S_AlgebraicGeometry_RelPicard_isNodeUnitModule_foldr_ofPoint_of_forall_eq_ord_of_hasValue.EPrincI P2MW.S_AlgebraicGeometry_RelPicard_isNodeUnitModule_foldr_ofPoint_of_forall_eq_ord_of_hasValue.EPkg"

namespace EPrincI

p2m_open "AlgebraicGeometry.Scheme.IdealSheafData AlgebraicCurve"

variable {k : Type u} [Field k]

scoped instance {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of k)) {F : Type u} [Field F] [Algebra k F]
    (Mdl : CurveModel k F) (e : Mdl.C ≅ C) : IsIso (modelIso c Mdl e) := by
  unfold modelIso; infer_instance

noncomputable def readF {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of k)) {F : Type u} [Field F] [Algebra k F]
    (Mdl : CurveModel k F) (e : Mdl.C ≅ C)
    (U : (pullback c (𝟙 (Spec (CommRingCat.of k)))).Opens) [Nonempty (Scheme.Opens.toScheme ((modelIso c Mdl e) ⁻¹ᵁ U))]
    (f : Γ(pullback c (𝟙 (Spec (CommRingCat.of k))), U)) : F :=
  Mdl.ffEquiv.symm (Mdl.C.germToFunctionField ((modelIso c Mdl e) ⁻¹ᵁ U) ((modelIso c Mdl e).app U f))

theorem appLE_rigSection_eq_of_hasValue_readF [IsAlgClosed k]
    {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of k)) [IsProper c] [SmoothOfRelativeDimension 1 c] [GeometricallyIntegral c]
    {F : Type u} [Field F] [Algebra k F] (Mdl : CurveModel k F) (e : Mdl.C ≅ C) (he : e.hom ≫ c = Mdl.toBase)
    (U : (pullback c (𝟙 (Spec (CommRingCat.of k)))).Opens) [Nonempty (Scheme.Opens.toScheme ((modelIso c Mdl e) ⁻¹ᵁ U))]
    (f : Γ(pullback c (𝟙 (Spec (CommRingCat.of k))), U))
    (q : Spec (CommRingCat.of k) ⟶ C) (hq : q ≫ c = 𝟙 _)
    (hqU : ⊤ ≤ (RelPicard.rigSection c (𝟙 (Spec (CommRingCat.of k))) ⟨q, hq⟩) ⁻¹ᵁ U)
    (a : k)
    (hval : (Mdl.pointEquivPlace ⟨q ≫ e.inv, by rw [← he, Category.assoc, e.inv_hom_id_assoc]; exact hq⟩).HasValue
      (readF c Mdl e U f) a) :
    (RelPicard.rigSection c (𝟙 (Spec (CommRingCat.of k))) ⟨q, hq⟩).appLE U ⊤ hqU f =
      (Scheme.ΓSpecIso (CommRingCat.of k)).inv a := by
  classical

  have hp : (q ≫ e.inv) ≫ Mdl.toBase = 𝟙 _ := by rw [← he, Category.assoc, e.inv_hom_id_assoc]; exact hq
  set p : Spec (CommRingCat.of k) ⟶ Mdl.C := q ≫ e.inv with hpdef
  let xC : closedPoints Mdl.C := pointEquivClosedPoint Mdl.toBase ⟨p, hp⟩
  have hxC : xC.1 = p.base (IsLocalRing.closedPoint k) := rfl
  have hv : Mdl.pointEquivPlace ⟨p, hp⟩ = Mdl.placeOfPoint xC := rfl
  rw [hv] at hval

  set mI := modelIso c Mdl e with hmI
  have hσ : RelPicard.rigSection c (𝟙 (Spec (CommRingCat.of k))) ⟨q, hq⟩ = p ≫ mI := by
    have hpm : p ≫ mI ≫ pullback.fst c (𝟙 (Spec (CommRingCat.of k))) = q := by
      rw [hpdef, hmI]
      simp only [modelIso, Category.assoc, IsIso.inv_hom_id, Category.comp_id, e.inv_hom_id_assoc, e.inv_hom_id]
    have h2 : pullback.snd c (𝟙 (Spec (CommRingCat.of k))) = pullback.fst c (𝟙 (Spec (CommRingCat.of k))) ≫ c := by
      rw [pullback.condition, Category.comp_id]
    apply pullback.hom_ext
    · simp only [Category.assoc, hpm, RelPicard.rigSection, pullback.lift_fst, Category.id_comp]
    · simp only [Category.assoc, h2, RelPicard.rigSection, pullback.lift_fst_assoc, Category.id_comp]
      rw [reassoc_of% hpm, hq]

  set V : Mdl.C.Opens := mI ⁻¹ᵁ U with hV
  have hxV : p.base (IsLocalRing.closedPoint k) ∈ V := by
    have h := hqU (Set.mem_univ (IsLocalRing.closedPoint k))
    rw [hσ] at h
    exact h

  have heval : ∀ {Y : Scheme.{u}} (g : Spec (CommRingCat.of k) ⟶ Y) (W : Y.Opens) (hW : g.base (IsLocalRing.closedPoint k) ∈ W)
      (hle : ⊤ ≤ g ⁻¹ᵁ W) (s : Γ(Y, W)),
      g.appLE W ⊤ hle s = (Scheme.ΓSpecIso (CommRingCat.of k)).inv
        (Scheme.stalkClosedPointTo g (Y.presheaf.germ W _ hW s)) := by
    intro Y g W hW hle s
    have h := Scheme.germ_stalkClosedPointTo g W hW
    have h' : Scheme.stalkClosedPointTo g (Y.presheaf.germ W _ hW s) =
        (Scheme.ΓSpecIso (CommRingCat.of k)).hom ((Spec (CommRingCat.of k)).presheaf.map
          (eqToHom (Scheme.preimage_eq_top_of_closedPoint_mem g hW).symm).op (g.app W s)) := by
      have := congrArg (fun φ => φ.hom s) h
      simpa using this
    rw [h']
    change _ = ((Scheme.ΓSpecIso (CommRingCat.of k)).hom ≫ (Scheme.ΓSpecIso (CommRingCat.of k)).inv) _
    rw [Iso.hom_inv_id]
    change (g.app W ≫ (Spec (CommRingCat.of k)).presheaf.map (homOfLE hle).op) s =
      (g.app W ≫ (Spec (CommRingCat.of k)).presheaf.map _) s
    congr 3
    try exact Subsingleton.elim _ _

  have hmain : ∀ (g : Spec (CommRingCat.of k) ⟶ pullback c (𝟙 (Spec (CommRingCat.of k)))) (hg : g = p ≫ mI)
      (hm : g.base (IsLocalRing.closedPoint k) ∈ U),
      Scheme.stalkClosedPointTo g ((pullback c (𝟙 (Spec (CommRingCat.of k)))).presheaf.germ U _ hm f) =
        Scheme.stalkClosedPointTo p (Mdl.C.presheaf.germ V _ hxV (mI.app U f)) := by
    intro g hg hm
    subst hg
    rw [Scheme.stalkClosedPointTo_comp]
    change ((pullback c (𝟙 (Spec (CommRingCat.of k)))).presheaf.germ U (mI.base (p.base (IsLocalRing.closedPoint k))) hm ≫
      mI.stalkMap _ ≫ Scheme.stalkClosedPointTo p) f =
      (Mdl.C.presheaf.germ V _ hxV ≫ Scheme.stalkClosedPointTo p) (mI.app U f)
    rw [Scheme.Hom.germ_stalkMap_assoc]
    rfl
  have hmem : (RelPicard.rigSection c (𝟙 (Spec (CommRingCat.of k))) ⟨q, hq⟩).base (IsLocalRing.closedPoint k) ∈ U :=
    hqU (Set.mem_univ _)
  rw [heval _ U hmem hqU f, hmain _ hσ hmem]
  congr 1

  let S : CommRingCat := Mdl.C.presheaf.stalk (p.base (IsLocalRing.closedPoint k))
  let A : ValuationSubring F := (Mdl.placeOfPoint xC).toValuationSubring
  let φ : S →+* F := (Mdl.ffEquiv.symm : Mdl.C.functionField ≃+* F).toRingHom.comp (algebraMap S Mdl.C.functionField)
  have hφrange : φ.range = A.toSubring := Mdl.range_stalk_eq xC
  have hφmem : ∀ s : S, φ s ∈ A := fun s => by
    have h : φ s ∈ φ.range := ⟨s, rfl⟩
    rw [hφrange] at h
    exact h
  let ψ : S →+* A := φ.codRestrict A hφmem
  have hψ : ∀ s : S, (ψ s : F) = φ s := fun _ => rfl
  have hψinj : Function.Injective ψ := by
    intro a1 b1 h
    have h' : φ a1 = φ b1 := by rw [← hψ, ← hψ, h]
    exact IsFractionRing.injective S Mdl.C.functionField (Mdl.ffEquiv.symm.injective h')
  have hψsurj : Function.Surjective ψ := by
    intro a1
    have ha : (a1 : F) ∈ φ.range := by rw [hφrange]; exact a1.2
    obtain ⟨s, hs⟩ := ha
    exact ⟨s, Subtype.ext hs⟩
  let eSA : S ≃+* A := RingEquiv.ofBijective ψ ⟨hψinj, hψsurj⟩

  let cst : k → S := fun b =>
    Mdl.C.presheaf.germ ⊤ (p.base (IsLocalRing.closedPoint k)) trivial (Mdl.toBase.appTop ((Scheme.ΓSpecIso (CommRingCat.of k)).inv b))
  have hgerm : ∀ t : Γ(Mdl.C, ⊤), algebraMap S Mdl.C.functionField (Mdl.C.presheaf.germ ⊤ (p.base (IsLocalRing.closedPoint k)) trivial t)
      = Mdl.C.presheaf.germ ⊤ (genericPoint Mdl.C) trivial t := by
    intro t
    change (Mdl.C.presheaf.germ ⊤ (p.base (IsLocalRing.closedPoint k)) trivial ≫ Mdl.C.presheaf.stalkSpecializes
      ((genericPoint_spec Mdl.C).specializes trivial)) t = _
    rw [TopCat.Presheaf.germ_stalkSpecializes]
  have hφc : ∀ b : k, φ (cst b) = algebraMap k F b := by
    intro b
    have h1 : algebraMap S Mdl.C.functionField (cst b) = baseToFunctionField Mdl.toBase b := hgerm _
    simp only [φ, RingHom.coe_comp, Function.comp_apply, h1, ← Mdl.ffEquiv_algebraMap]
    exact Mdl.ffEquiv.symm_apply_apply _
  have hψc : ∀ b : k, ψ (cst b) = algebraMap k A b := fun b =>
    Subtype.ext (by rw [hψ, hφc]; rfl)

  set s₀ : S := Mdl.C.presheaf.germ V _ hxV (mI.app U f) with hs₀
  have hφs₀ : φ s₀ = readF c Mdl e U f := by
    change Mdl.ffEquiv.symm (algebraMap S Mdl.C.functionField s₀) = Mdl.ffEquiv.symm _
    congr 1
    change (Mdl.C.presheaf.germ V (p.base (IsLocalRing.closedPoint k)) hxV ≫ Mdl.C.presheaf.stalkSpecializes
      ((genericPoint_spec Mdl.C).specializes trivial)) (mI.app U f) = _
    rw [TopCat.Presheaf.germ_stalkSpecializes]

  obtain ⟨hgmem, hres⟩ := hval
  have hψs₀ : ψ s₀ = ⟨readF c Mdl e U f, hgmem⟩ := Subtype.ext hφs₀
  have hm' : ψ (s₀ - cst a) ∈ IsLocalRing.maximalIdeal A := by
    rw [map_sub, ← IsLocalRing.residue_eq_zero_iff, map_sub, sub_eq_zero, hψs₀, hψc]
    exact hres
  have hm : s₀ - cst a ∈ IsLocalRing.maximalIdeal S := by
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    intro hu
    exact ((IsLocalRing.mem_maximalIdeal _).mp hm') (hu.map ψ)

  have hev0 : (Scheme.stalkClosedPointTo p).hom (s₀ - cst a) = 0 := by
    by_contra hne
    have hu : IsUnit ((Scheme.stalkClosedPointTo p).hom (s₀ - cst a)) := isUnit_iff_ne_zero.mpr hne
    exact ((IsLocalRing.mem_maximalIdeal _).mp hm) ((isUnit_map_iff (Scheme.stalkClosedPointTo p).hom _).mp hu)
  have hevc : (Scheme.stalkClosedPointTo p).hom (cst a) = a := by
    have h := Scheme.germ_stalkClosedPointTo p ⊤ trivial
    have h' := congrArg (fun ψ' => ψ'.hom (Mdl.toBase.appTop ((Scheme.ΓSpecIso (CommRingCat.of k)).inv a))) h
    simp only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply] at h'
    refine h'.trans ?_
    have hpa : (p.app ⊤).hom ((Mdl.toBase.appTop).hom ((Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom a)) =
        (Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom a := by
      change ((p ≫ Mdl.toBase).appTop).hom _ = _
      rw [hp]
      rfl
    erw [hpa]
    simp only [Iso.trans_hom, Functor.mapIso_hom, Iso.op_hom, CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply]
    simp
    try exact CategoryTheory.Iso.inv_hom_id_apply _ _
  have hfin : (Scheme.stalkClosedPointTo p).hom s₀ = a := by
    have h := hev0
    simp only [map_sub, sub_eq_zero] at h
    rw [h, hevc]
  exact hfin

def awayFrom {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of k)) [IsSeparated c]
    {V : Type u} (pt : V → (Spec (CommRingCat.of k) ⟶ C)) (hpt : ∀ v, pt v ≫ c = 𝟙 _) (l : List V) :
    (pullback c (𝟙 (Spec (CommRingCat.of k)))).Opens :=
  ⟨(⋃ v ∈ l, Set.range (graphOver c (pt v) (hpt v)).base)ᶜ, by
    refine (Set.Finite.isClosed_biUnion (List.finite_toSet l) fun v _ => ?_).isOpen_compl
    exact (graphOver c (pt v) (hpt v)).isClosedEmbedding.isClosed_range⟩

end EPrincI
p2m_reactivate "P2MW.S_AlgebraicGeometry_RelPicard_isNodeUnitModule_foldr_ofPoint_of_forall_eq_ord_of_hasValue.EPkgTwist P2MW.S_AlgebraicGeometry_RelPicard_isNodeUnitModule_foldr_ofPoint_of_forall_eq_ord_of_hasValue.EPrincI.Place P2MW.S_AlgebraicGeometry_RelPicard_isNodeUnitModule_foldr_ofPoint_of_forall_eq_ord_of_hasValue.EPrincI P2MW.S_AlgebraicGeometry_RelPicard_isNodeUnitModule_foldr_ofPoint_of_forall_eq_ord_of_hasValue.EPkg"

namespace EPrincD

p2m_open "AlgebraicGeometry.Scheme.IdealSheafData"

theorem coe_support_ofPoint_I
    {𝒞 S : Scheme.{u}} (f : 𝒞 ⟶ S) [IsSeparated f] {T : Scheme.{u}} {g : T ⟶ S}
    (a : T ⟶ 𝒞) (ha : a ≫ f = g) :
    ((RelEffCartierDiv.ofPoint f a ha).I.support : Set ↥(pullback f g)) = Set.range (graphOver f a ha) := by
  rw [RelEffCartierDiv.ofPoint_I, Scheme.Hom.support_ker,
    (graphOver f a ha).isClosedEmbedding.isClosed_range.closure_eq]

theorem supportedIn_ofPoint_of_range_subset
    {𝒞 S : Scheme.{u}} (f : 𝒞 ⟶ S) [IsSeparated f] {T : Scheme.{u}} {g : T ⟶ S}
    (a : T ⟶ 𝒞) (ha : a ≫ f = g) (U : 𝒞.Opens) (haU : Set.range a ⊆ (U : Set 𝒞)) :
    (RelEffCartierDiv.ofPoint f a ha).SupportedIn U := by
  rw [RelEffCartierDiv.supportedIn_iff]
  intro x hx
  have hx' : x ∈ ((RelEffCartierDiv.ofPoint f a ha).I.support : Set ↥(pullback f g)) := hx
  rw [coe_support_ofPoint_I] at hx'
  obtain ⟨y, rfl⟩ := hx'
  rw [← Scheme.Hom.comp_apply, graphOver_fst]
  exact haU ⟨y, rfl⟩

theorem comap_ker_graphOver_eq_top_of_forall_notMem
    {𝒞 S : Scheme.{u}} (f : 𝒞 ⟶ S) [IsSeparated f] {T : Scheme.{u}} {g : T ⟶ S}
    (a : T ⟶ 𝒞) (ha : a ≫ f = g) {Y : Scheme.{u}} (φ : Y ⟶ pullback f g)
    (hφ : ∀ y : Y, φ.base y ∉ Set.range (graphOver f a ha).base) :
    (RelEffCartierDiv.ofPoint f a ha).I.comap φ = ⊤ := by
  haveI : IsEmpty ↥(pullback φ (graphOver f a ha)) := ⟨fun z => by
    have key := congrArg (fun ψ => ψ.base z) (pullback.condition (f := φ) (g := graphOver f a ha))
    exact hφ _ ⟨_, key.symm⟩⟩
  rw [RelEffCartierDiv.ofPoint_I, ← ker_fst_of_isClosedImmersion]
  exact Scheme.ker_eq_top_of_isEmpty _

section Frame

variable {k : Type u} [Field k] [IsAlgClosed k]
  {X C C' : Scheme.{u}} (x : X ⟶ Spec (CommRingCat.of k)) [IsSeparated x]
  (c : C ⟶ Spec (CommRingCat.of k)) [SmoothOfRelativeDimension 1 c] (c' : C' ⟶ Spec (CommRingCat.of k))
  (i : SchemeHomOver c x) (i' : SchemeHomOver c' x) [IsClosedImmersion i.1] [IsClosedImmersion i'.1]
  {ι : Type v}
  (p : ι → SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) c) (p' : ι → SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) c')
  (hinter : ∀ (q : C) (q' : C'), i.1.base q = i'.1.base q' →
    ∃ j, q = (p j).1.base (IsLocalRing.closedPoint k) ∧ q' = (p' j).1.base (IsLocalRing.closedPoint k))
  (F : Type u) [Field F] [Algebra k F]
  (Mdl : CurveModel k F) (e : Mdl.C ≅ C) (he : e.hom ≫ c = Mdl.toBase)
  (pt : Place k F → (Spec (CommRingCat.of k) ⟶ C)) (hpt : ∀ v, pt v ≫ c = 𝟙 _)
  (hpt' : ∀ v, pt v = (Mdl.pointEquivPlace.symm v).1 ≫ e.hom)
  (plc : ι → Place k F)
  (hplc : ∀ j, plc j = Mdl.pointEquivPlace ⟨(p j).1 ≫ e.inv, by rw [← he, Category.assoc, e.inv_hom_id_assoc]; exact (p j).2⟩)
  (D : Place k F →₀ ℤ) (hD : ∀ j, D (plc j) = 0)

include hinter he hpt hpt' hplc hD in

theorem notMem_range_of_mem_support (v : Place k F) (hv : v ∈ D.support) :
    (pt v ≫ i.1).base (IsLocalRing.closedPoint k) ∉ Set.range i'.1.base := by
  rintro ⟨q', hq'⟩
  obtain ⟨j, hj, -⟩ := hinter ((pt v).base (IsLocalRing.closedPoint k)) q'
    (by rw [hq', Scheme.Hom.comp_apply])

  haveI : Smooth c := SmoothOfRelativeDimension.smooth 1 c
  have heq : pt v = (p j).1 := ext_of_apply_closedPoint_eq c (hpt v) (p j).2 hj

  have hplace : v = plc j := by
    rw [hplc j, ← Mdl.pointEquivPlace.apply_symm_apply v]
    congr 1
    apply Subtype.ext
    change (Mdl.pointEquivPlace.symm v).1 = (p j).1 ≫ e.inv
    rw [← heq, hpt' v, Category.assoc, e.hom_inv_id, Category.comp_id]
  exact (Finsupp.mem_support_iff.mp hv) (hplace ▸ hD j)

include hinter he hpt hpt' hplc hD in
theorem range_subset_coOpen_of_mem_support (v : Place k F) (hv : v ∈ D.support) :
    Set.range (pt v ≫ i.1).base ⊆ ((EPkg.coOpen i'.1 : X.Opens) : Set X) := by
  rintro _ ⟨t, rfl⟩
  obtain rfl : t = IsLocalRing.closedPoint k := Subsingleton.elim _ _
  exact notMem_range_of_mem_support x c c' i i' p p' hinter F Mdl e he pt hpt hpt' plc hplc D hD v hv

include hinter he hpt hpt' hplc hD in

theorem graphOver_node_notMem_range (j : ι) (v : Place k F) (hv : v ∈ D.support) :
    (graphOver (g := 𝟙 (Spec (CommRingCat.of k))) x ((p j).1 ≫ i.1) (by rw [Category.assoc, i.2]; exact (p j).2)).base
        (IsLocalRing.closedPoint k) ∉
      Set.range (graphOver (g := 𝟙 (Spec (CommRingCat.of k))) x (pt v ≫ i.1)
        (by rw [Category.assoc, i.2]; exact hpt v)).base := by
  rintro ⟨t, ht⟩
  obtain rfl : t = IsLocalRing.closedPoint k := Subsingleton.elim _ _
  have h1 := congrArg (fun z => (pullback.fst x (𝟙 (Spec (CommRingCat.of k)))).base z) ht
  simp only [← Scheme.Hom.comp_apply, graphOver_fst] at h1

  rw [Scheme.Hom.comp_apply, Scheme.Hom.comp_apply] at h1
  have h2 : (pt v).base (IsLocalRing.closedPoint k) = (p j).1.base (IsLocalRing.closedPoint k) :=
    i.1.isClosedEmbedding.injective h1
  haveI : Smooth c := SmoothOfRelativeDimension.smooth 1 c
  have heq : pt v = (p j).1 := ext_of_apply_closedPoint_eq c (hpt v) (p j).2 h2
  have hplace : v = plc j := by
    rw [hplc j, ← Mdl.pointEquivPlace.apply_symm_apply v]
    congr 1
    apply Subtype.ext
    change (Mdl.pointEquivPlace.symm v).1 = (p j).1 ≫ e.inv
    rw [← heq, hpt' v, Category.assoc, e.hom_inv_id, Category.comp_id]
  exact (Finsupp.mem_support_iff.mp hv) (hplace ▸ hD j)

end Frame
p2m_reactivate "P2MW.S_AlgebraicGeometry_RelPicard_isNodeUnitModule_foldr_ofPoint_of_forall_eq_ord_of_hasValue.EPkgTwist P2MW.S_AlgebraicGeometry_RelPicard_isNodeUnitModule_foldr_ofPoint_of_forall_eq_ord_of_hasValue.EPrincI.Place P2MW.S_AlgebraicGeometry_RelPicard_isNodeUnitModule_foldr_ofPoint_of_forall_eq_ord_of_hasValue.EPrincI P2MW.S_AlgebraicGeometry_RelPicard_isNodeUnitModule_foldr_ofPoint_of_forall_eq_ord_of_hasValue.EPkg"

end EPrincD
p2m_reactivate "P2MW.S_AlgebraicGeometry_RelPicard_isNodeUnitModule_foldr_ofPoint_of_forall_eq_ord_of_hasValue.EPkgTwist P2MW.S_AlgebraicGeometry_RelPicard_isNodeUnitModule_foldr_ofPoint_of_forall_eq_ord_of_hasValue.EPrincI.Place P2MW.S_AlgebraicGeometry_RelPicard_isNodeUnitModule_foldr_ofPoint_of_forall_eq_ord_of_hasValue.EPrincI P2MW.S_AlgebraicGeometry_RelPicard_isNodeUnitModule_foldr_ofPoint_of_forall_eq_ord_of_hasValue.EPkg"

section Skel
set_option backward.isDefEq.respectTransparency false
open Opposite TopologicalSpace

namespace TwoGluedCurvesN7

variable {κ : Type u} [Field κ]
  {X C₁ C₂ : Scheme.{u}} (x : X ⟶ Spec (.of κ))
  {c₁ : C₁ ⟶ Spec (.of κ)} {c₂ : C₂ ⟶ Spec (.of κ)}
  (i₁ : SchemeHomOver c₁ x) (i₂ : SchemeHomOver c₂ x)
  {ι : Type v} (p₁ : ι → SchemeHomOver (𝟙 (Spec (.of κ))) c₁) (p₂ : ι → SchemeHomOver (𝟙 (Spec (.of κ))) c₂)
  {T : Scheme.{u}} (h : T ⟶ Spec (.of κ))

abbrev P₁ : (pullback x h).Modules :=
  (Scheme.Modules.pushforward (curveChange i₁.1 i₁.2 h)).obj (SheafOfModules.unit (pullback c₁ h).ringCatSheaf)

abbrev P₂ : (pullback x h).Modules :=
  (Scheme.Modules.pushforward (curveChange i₂.1 i₂.2 h)).obj (SheafOfModules.unit (pullback c₂ h).ringCatSheaf)

def toR₁ (W : (pullback x h).Opens) (f : Γ(P₁ x i₁ h, W)) : Γ(pullback c₁ h, (curveChange i₁.1 i₁.2 h) ⁻¹ᵁ W) := f
def ofR₁ (W : (pullback x h).Opens) (f : Γ(pullback c₁ h, (curveChange i₁.1 i₁.2 h) ⁻¹ᵁ W)) : Γ(P₁ x i₁ h, W) := f
def toR₂ (W : (pullback x h).Opens) (g : Γ(P₂ x i₂ h, W)) : Γ(pullback c₂ h, (curveChange i₂.1 i₂.2 h) ⁻¹ᵁ W) := g
def ofR₂ (W : (pullback x h).Opens) (g : Γ(pullback c₂ h, (curveChange i₂.1 i₂.2 h) ⁻¹ᵁ W)) : Γ(P₂ x i₂ h, W) := g
@[scoped simp] lemma toR₁_ofR₁ (W : (pullback x h).Opens) (f) : toR₁ x i₁ h W (ofR₁ x i₁ h W f) = f := rfl
@[scoped simp] lemma ofR₁_toR₁ (W : (pullback x h).Opens) (f) : ofR₁ x i₁ h W (toR₁ x i₁ h W f) = f := rfl
@[scoped simp] lemma toR₂_ofR₂ (W : (pullback x h).Opens) (g) : toR₂ x i₂ h W (ofR₂ x i₂ h W g) = g := rfl
@[scoped simp] lemma ofR₂_toR₂ (W : (pullback x h).Opens) (g) : ofR₂ x i₂ h W (toR₂ x i₂ h W g) = g := rfl
lemma toR₁_injective (W : (pullback x h).Opens) : Function.Injective (toR₁ x i₁ h W) := fun _ _ e => e
lemma toR₂_injective (W : (pullback x h).Opens) : Function.Injective (toR₂ x i₂ h W) := fun _ _ e => e
lemma toR₁_smul (W : (pullback x h).Opens) (r : Γ(pullback x h, W)) (f : Γ(P₁ x i₁ h, W)) :
    toR₁ x i₁ h W (r • f) = (curveChange i₁.1 i₁.2 h).app W r * toR₁ x i₁ h W f := rfl
lemma toR₂_smul (W : (pullback x h).Opens) (r : Γ(pullback x h, W)) (g : Γ(P₂ x i₂ h, W)) :
    toR₂ x i₂ h W (r • g) = (curveChange i₂.1 i₂.2 h).app W r * toR₂ x i₂ h W g := rfl
lemma toR₁_map {W W' : (pullback x h).Opens} (e : W' ⟶ W) (f : Γ(P₁ x i₁ h, W)) :
    toR₁ x i₁ h W' ((P₁ x i₁ h).presheaf.map e.op f) =
      (pullback c₁ h).presheaf.map (homOfLE ((curveChange i₁.1 i₁.2 h).preimage_mono e.le)).op (toR₁ x i₁ h W f) := rfl
lemma toR₂_map {W W' : (pullback x h).Opens} (e : W' ⟶ W) (g : Γ(P₂ x i₂ h, W)) :
    toR₂ x i₂ h W' ((P₂ x i₂ h).presheaf.map e.op g) =
      (pullback c₂ h).presheaf.map (homOfLE ((curveChange i₂.1 i₂.2 h).preimage_mono e.le)).op (toR₂ x i₂ h W g) := rfl

lemma pair_ext {W : (pullback x h).Opens} {p q : Γ(P₁ x i₁ h, W) × Γ(P₂ x i₂ h, W)}
    (h1 : toR₁ x i₁ h W p.1 = toR₁ x i₁ h W q.1) (h2 : toR₂ x i₂ h W p.2 = toR₂ x i₂ h W q.2) : p = q :=
  Prod.ext h1 h2

def nv₁ (j : ι) (W : (pullback x h).Opens) (f : Γ(pullback c₁ h, (curveChange i₁.1 i₁.2 h) ⁻¹ᵁ W)) :
    Γ(T, nodeLocus x i₁ i₂ p₁ p₂ h j W) :=
  (nodeSectionFst p₁ h j).appLE ((curveChange i₁.1 i₁.2 h) ⁻¹ᵁ W) (nodeLocus x i₁ i₂ p₁ p₂ h j W) inf_le_left f

def nv₂ (j : ι) (W : (pullback x h).Opens) (g : Γ(pullback c₂ h, (curveChange i₂.1 i₂.2 h) ⁻¹ᵁ W)) :
    Γ(T, nodeLocus x i₁ i₂ p₁ p₂ h j W) :=
  (nodeSectionSnd p₂ h j).appLE ((curveChange i₂.1 i₂.2 h) ⁻¹ᵁ W) (nodeLocus x i₁ i₂ p₁ p₂ h j W) inf_le_right g

abbrev uOn (u : ι → Γ(T, ⊤)ˣ) (j : ι) (V : T.Opens) : Γ(T, V) := T.presheaf.map (homOfLE le_top).op (u j : Γ(T, ⊤))

lemma nodeCondition_iff (u : ι → Γ(T, ⊤)ˣ) (W : (pullback x h).Opens) (j : ι) (f) (g) :
    NodeCondition x i₁ i₂ p₁ p₂ h u W j f g ↔
      nv₁ x i₁ i₂ p₁ p₂ h j W f = uOn u j _ * nv₂ x i₁ i₂ p₁ p₂ h j W g := Iff.rfl

lemma nodeLocus_mono (j : ι) {W W' : (pullback x h).Opens} (hW : W' ≤ W) :
    nodeLocus x i₁ i₂ p₁ p₂ h j W' ≤ nodeLocus x i₁ i₂ p₁ p₂ h j W :=
  inf_le_inf ((nodeSectionFst p₁ h j).preimage_mono ((curveChange i₁.1 i₁.2 h).preimage_mono hW))
    ((nodeSectionSnd p₂ h j).preimage_mono ((curveChange i₂.1 i₂.2 h).preimage_mono hW))

abbrev ρ {V V' : T.Opens} (hV : V' ≤ V) : Γ(T, V) →+* Γ(T, V') := (T.presheaf.map (homOfLE hV).op).hom

lemma ρ_ρ {V V' V'' : T.Opens} (hV : V' ≤ V) (hV' : V'' ≤ V') (a : Γ(T, V)) :
    ρ hV' (ρ hV a) = ρ (hV'.trans hV) a := by
  change (T.presheaf.map _ ≫ T.presheaf.map _) a = _
  rw [← Functor.map_comp]; rfl

lemma ρ_uOn (u : ι → Γ(T, ⊤)ˣ) (j : ι) {V V' : T.Opens} (hV : V' ≤ V) :
    ρ hV (uOn u j V) = uOn u j V' := ρ_ρ _ _ _

lemma nv₁_res (j : ι) {W W' : (pullback x h).Opens} (hW : W' ≤ W) (f : Γ(pullback c₁ h, (curveChange i₁.1 i₁.2 h) ⁻¹ᵁ W)) :
    nv₁ x i₁ i₂ p₁ p₂ h j W' ((pullback c₁ h).presheaf.map (homOfLE ((curveChange i₁.1 i₁.2 h).preimage_mono hW)).op f) =
      ρ (nodeLocus_mono x i₁ i₂ p₁ p₂ h j hW) (nv₁ x i₁ i₂ p₁ p₂ h j W f) := by
  unfold nv₁
  rw [← CommRingCat.comp_apply, Scheme.Hom.map_appLE, ← CommRingCat.comp_apply, Scheme.Hom.appLE_map]

lemma nv₂_res (j : ι) {W W' : (pullback x h).Opens} (hW : W' ≤ W) (g : Γ(pullback c₂ h, (curveChange i₂.1 i₂.2 h) ⁻¹ᵁ W)) :
    nv₂ x i₁ i₂ p₁ p₂ h j W' ((pullback c₂ h).presheaf.map (homOfLE ((curveChange i₂.1 i₂.2 h).preimage_mono hW)).op g) =
      ρ (nodeLocus_mono x i₁ i₂ p₁ p₂ h j hW) (nv₂ x i₁ i₂ p₁ p₂ h j W g) := by
  unfold nv₂
  rw [← CommRingCat.comp_apply, Scheme.Hom.map_appLE, ← CommRingCat.comp_apply, Scheme.Hom.appLE_map]

lemma nv₁_mul_app (j : ι) (hK : nodeSectionFst p₁ h j ≫ curveChange i₁.1 i₁.2 h = nodeSectionSnd p₂ h j ≫ curveChange i₂.1 i₂.2 h)
    (W : (pullback x h).Opens) (r : Γ(pullback x h, W)) (f : Γ(pullback c₁ h, (curveChange i₁.1 i₁.2 h) ⁻¹ᵁ W)) :
    nv₁ x i₁ i₂ p₁ p₂ h j W ((curveChange i₁.1 i₁.2 h).app W r * f) =
      (nodeSectionSnd p₂ h j ≫ curveChange i₂.1 i₂.2 h).appLE W (nodeLocus x i₁ i₂ p₁ p₂ h j W) (by exact inf_le_right) r *
        nv₁ x i₁ i₂ p₁ p₂ h j W f := by
  unfold nv₁
  rw [map_mul]
  congr 1
  have e₁ : (nodeSectionFst p₁ h j).appLE ((curveChange i₁.1 i₁.2 h) ⁻¹ᵁ W)
        (nodeLocus x i₁ i₂ p₁ p₂ h j W) inf_le_left ((curveChange i₁.1 i₁.2 h).app W r) =
      (nodeSectionFst p₁ h j ≫ curveChange i₁.1 i₁.2 h).appLE W
        (nodeLocus x i₁ i₂ p₁ p₂ h j W) (by exact inf_le_left) r := by
    rw [Scheme.Hom.comp_appLE]; rfl
  rw [e₁, Scheme.Hom.appLE, Scheme.Hom.appLE, Scheme.Hom.congr_app hK W, Category.assoc, ← Functor.map_comp]
  rfl

lemma nv₂_mul_app (j : ι) (W : (pullback x h).Opens) (r : Γ(pullback x h, W)) (g : Γ(pullback c₂ h, (curveChange i₂.1 i₂.2 h) ⁻¹ᵁ W)) :
    nv₂ x i₁ i₂ p₁ p₂ h j W ((curveChange i₂.1 i₂.2 h).app W r * g) =
      (nodeSectionSnd p₂ h j ≫ curveChange i₂.1 i₂.2 h).appLE W (nodeLocus x i₁ i₂ p₁ p₂ h j W) (by exact inf_le_right) r *
        nv₂ x i₁ i₂ p₁ p₂ h j W g := by
  unfold nv₂
  rw [map_mul]
  congr 1

theorem nodeSection_comp_eq (hnode : ∀ j, (p₁ j).1 ≫ i₁.1 = (p₂ j).1 ≫ i₂.1) (j : ι) :
    nodeSectionFst p₁ h j ≫ curveChange i₁.1 i₁.2 h = nodeSectionSnd p₂ h j ≫ curveChange i₂.1 i₂.2 h := by
  let ν : SchemeHomOver (𝟙 (Spec (.of κ))) x :=
    ⟨(p₁ j).1 ≫ i₁.1, by rw [Category.assoc, i₁.2, (p₁ j).2]⟩
  have h1 : nodeSectionFst p₁ h j ≫ curveChange i₁.1 i₁.2 h = rigSection x h ν :=
    rigSection_curveChange i₁.1 i₁.2 (ε' := p₁ j) (ε := ν) rfl h
  have h2 : nodeSectionSnd p₂ h j ≫ curveChange i₂.1 i₂.2 h = rigSection x h ν :=
    rigSection_curveChange i₂.1 i₂.2 (ε' := p₂ j) (ε := ν) (hnode j).symm h
  rw [h1, h2]

lemma mem_nodeLocus (hnode : ∀ j, (p₁ j).1 ≫ i₁.1 = (p₂ j).1 ≫ i₂.1) (j : ι) (W : (pullback x h).Opens) (t : T)
    (ht : (nodeSectionFst p₁ h j ≫ curveChange i₁.1 i₁.2 h).base t ∈ W) :
    t ∈ nodeLocus x i₁ i₂ p₁ p₂ h j W := by
  refine ⟨ht, ?_⟩
  show (nodeSectionSnd p₂ h j ≫ curveChange i₂.1 i₂.2 h).base t ∈ W
  rw [← nodeSection_comp_eq x i₁ i₂ p₁ p₂ h hnode j]
  exact ht

end TwoGluedCurvesN7
p2m_reactivate "P2MW.S_AlgebraicGeometry_RelPicard_isNodeUnitModule_foldr_ofPoint_of_forall_eq_ord_of_hasValue.EPkgTwist P2MW.S_AlgebraicGeometry_RelPicard_isNodeUnitModule_foldr_ofPoint_of_forall_eq_ord_of_hasValue.EPrincI.Place P2MW.S_AlgebraicGeometry_RelPicard_isNodeUnitModule_foldr_ofPoint_of_forall_eq_ord_of_hasValue.EPrincI P2MW.S_AlgebraicGeometry_RelPicard_isNodeUnitModule_foldr_ofPoint_of_forall_eq_ord_of_hasValue.EPkg P2MW.S_AlgebraicGeometry_RelPicard_isNodeUnitModule_foldr_ofPoint_of_forall_eq_ord_of_hasValue.TwoGluedCurvesN7"

namespace TwoGluedCurvesN7

p2m_open "AlgebraicGeometry.Scheme.Modules"

variable {Y Z : Scheme.{u}} (f : Z ⟶ Y) (L : Y.Modules)

def jOf (e : (Scheme.Modules.pullback f).obj L ≅ SheafOfModules.unit Z.ringCatSheaf) :
    L ⟶ (Scheme.Modules.pushforward f).obj (SheafOfModules.unit Z.ringCatSheaf) :=
  ((pullbackPushforwardAdjunction f).homEquiv _ _) e.hom

theorem isUnit_of_isFrameOn_unit {V : Z.Opens}
    (v : Γ((SheafOfModules.unit Z.ringCatSheaf : Z.Modules), V)) (hv : Scheme.Modules.IsFrameOn v V) :
    IsUnit (show Γ(Z, V) from v) := by
  have hmap : ∀ w : Γ((SheafOfModules.unit Z.ringCatSheaf : Z.Modules), V),
      (Scheme.Modules.presheaf (SheafOfModules.unit Z.ringCatSheaf : Z.Modules)).map (homOfLE (le_refl V)).op w = w :=
    fun w => by
    rw [show (homOfLE (le_refl V)).op = 𝟙 (Opposite.op V) from rfl, CategoryTheory.Functor.map_id]
    rfl
  obtain ⟨g, hg⟩ := (hv le_rfl le_rfl).2 (show Γ((SheafOfModules.unit Z.ringCatSheaf : Z.Modules), V) from (1 : Γ(Z, V)))
  change g • ((Scheme.Modules.presheaf (SheafOfModules.unit Z.ringCatSheaf : Z.Modules)).map (homOfLE (le_refl V)).op v) =
    (show Γ((SheafOfModules.unit Z.ringCatSheaf : Z.Modules), V) from (1 : Γ(Z, V))) at hg
  rw [hmap] at hg
  have hg' : g * (show Γ(Z, V) from v) = 1 := hg
  exact IsUnit.of_mul_eq_one _ (by rw [mul_comm]; exact hg')

theorem isUnit_jOf_app_of_isFrameOn
    (e : (Scheme.Modules.pullback f).obj L ≅ SheafOfModules.unit Z.ringCatSheaf)
    {U : Y.Opens} (s : Γ(L, U)) (hs : Scheme.Modules.IsFrameOn s U) :
    IsUnit (show Γ(Z, f ⁻¹ᵁ U) from (jOf f L e).app U s) := by
  have hframe := (hs.pullbackLocalSection f).map_iso e
  have heq : e.hom.app (f ⁻¹ᵁ U) (Scheme.Modules.pullbackLocalSection f s) = (jOf f L e).app U s := by
    rw [Scheme.Modules.app_pullbackLocalSection]
    rfl
  rw [heq] at hframe
  exact isUnit_of_isFrameOn_unit _ hframe

end TwoGluedCurvesN7
p2m_reactivate "P2MW.S_AlgebraicGeometry_RelPicard_isNodeUnitModule_foldr_ofPoint_of_forall_eq_ord_of_hasValue.EPkgTwist P2MW.S_AlgebraicGeometry_RelPicard_isNodeUnitModule_foldr_ofPoint_of_forall_eq_ord_of_hasValue.EPrincI.Place P2MW.S_AlgebraicGeometry_RelPicard_isNodeUnitModule_foldr_ofPoint_of_forall_eq_ord_of_hasValue.EPrincI P2MW.S_AlgebraicGeometry_RelPicard_isNodeUnitModule_foldr_ofPoint_of_forall_eq_ord_of_hasValue.EPkg P2MW.S_AlgebraicGeometry_RelPicard_isNodeUnitModule_foldr_ofPoint_of_forall_eq_ord_of_hasValue.TwoGluedCurvesN7"

namespace TwoGluedCurvesN7

set_option quotPrecheck false

variable {κ : Type u} [Field κ]
  {X C₁ C₂ : Scheme.{u}} (x : X ⟶ Spec (.of κ))
  {c₁ : C₁ ⟶ Spec (.of κ)} {c₂ : C₂ ⟶ Spec (.of κ)}
  (i₁ : SchemeHomOver c₁ x) (i₂ : SchemeHomOver c₂ x)
  {ι : Type v} (p₁ : ι → SchemeHomOver (𝟙 (Spec (.of κ))) c₁) (p₂ : ι → SchemeHomOver (𝟙 (Spec (.of κ))) c₂)
  {T : Scheme.{u}} (h : T ⟶ Spec (.of κ))
  {L : (pullback x h).Modules} (j₁ : L ⟶ P₁ x i₁ h) (j₂ : L ⟶ P₂ x i₂ h)

local notation "nl" => nodeLocus x i₁ i₂ p₁ p₂ h

def aVal (j : ι) (W : (pullback x h).Opens) (e : Γ(L, W)) : Γ(T, nl j W) :=
  nv₁ x i₁ i₂ p₁ p₂ h j W (toR₁ x i₁ h W (j₁.app W e))

def bVal (j : ι) (W : (pullback x h).Opens) (e : Γ(L, W)) : Γ(T, nl j W) :=
  nv₂ x i₁ i₂ p₁ p₂ h j W (toR₂ x i₂ h W (j₂.app W e))

local notation "AV" => aVal x i₁ i₂ p₁ p₂ h j₁
local notation "BV" => bVal x i₁ i₂ p₁ p₂ h j₂

lemma app_map {N N' : (pullback x h).Modules} (φ : N ⟶ N') {W W' : (pullback x h).Opens} (i : W' ⟶ W) (n : Γ(N, W)) :
    φ.app W' (N.presheaf.map i.op n) = N'.presheaf.map i.op (φ.app W n) :=
  ConcreteCategory.congr_hom (φ.mapPresheaf.naturality i.op) n

lemma aVal_res (j : ι) {W W' : (pullback x h).Opens} (hW : W' ≤ W) (e : Γ(L, W)) :
    AV j W' (L.presheaf.map (homOfLE hW).op e) = ρ (nodeLocus_mono x i₁ i₂ p₁ p₂ h j hW) (AV j W e) := by
  unfold aVal
  rw [app_map, toR₁_map, nv₁_res x i₁ i₂ p₁ p₂ h j hW]

lemma bVal_res (j : ι) {W W' : (pullback x h).Opens} (hW : W' ≤ W) (e : Γ(L, W)) :
    BV j W' (L.presheaf.map (homOfLE hW).op e) = ρ (nodeLocus_mono x i₁ i₂ p₁ p₂ h j hW) (BV j W e) := by
  unfold bVal
  rw [app_map, toR₂_map, nv₂_res x i₁ i₂ p₁ p₂ h j hW]

lemma aVal_smul (j : ι) (hK : nodeSectionFst p₁ h j ≫ curveChange i₁.1 i₁.2 h = nodeSectionSnd p₂ h j ≫ curveChange i₂.1 i₂.2 h)
    (W : (pullback x h).Opens) (g : Γ(pullback x h, W)) (e : Γ(L, W)) :
    AV j W (g • e) = (nodeSectionSnd p₂ h j ≫ curveChange i₂.1 i₂.2 h).appLE W (nl j W) (by exact inf_le_right) g * AV j W e := by
  unfold aVal
  rw [Scheme.Modules.Hom.app_smul, toR₁_smul, nv₁_mul_app x i₁ i₂ p₁ p₂ h j hK]

lemma bVal_smul (j : ι) (W : (pullback x h).Opens) (g : Γ(pullback x h, W)) (e : Γ(L, W)) :
    BV j W (g • e) = (nodeSectionSnd p₂ h j ≫ curveChange i₂.1 i₂.2 h).appLE W (nl j W) (by exact inf_le_right) g * BV j W e := by
  unfold bVal
  rw [Scheme.Modules.Hom.app_smul, toR₂_smul, nv₂_mul_app]

theorem cross (j : ι) (hK : nodeSectionFst p₁ h j ≫ curveChange i₁.1 i₁.2 h = nodeSectionSnd p₂ h j ≫ curveChange i₂.1 i₂.2 h)
    {U U' : (pullback x h).Opens} (e : Γ(L, U)) (e' : Γ(L, U')) (he : Scheme.Modules.IsFrameOn e U)
    {Zt : T.Opens} (hZ : Zt ≤ nl j U) (hZ' : Zt ≤ nl j U') :
    ρ hZ (AV j U e) * ρ hZ' (BV j U' e') = ρ hZ' (AV j U' e') * ρ hZ (BV j U e) := by

  have hZV : Zt ≤ nl j (U ⊓ U') := fun t ht => ⟨⟨(hZ ht).1, (hZ' ht).1⟩, ⟨(hZ ht).2, (hZ' ht).2⟩⟩
  set eV : Γ(L, U ⊓ U') := L.presheaf.map (homOfLE inf_le_left).op e with heV
  set e'V : Γ(L, U ⊓ U') := L.presheaf.map (homOfLE inf_le_right).op e' with he'V
  obtain ⟨g, hg⟩ := (he inf_le_left inf_le_left).2 e'V
  change g • eV = e'V at hg
  have r1 : ρ hZ (AV j U e) = ρ hZV (AV j (U ⊓ U') eV) := by rw [heV, aVal_res, ρ_ρ]
  have r2 : ρ hZ (BV j U e) = ρ hZV (BV j (U ⊓ U') eV) := by rw [heV, bVal_res, ρ_ρ]
  have r3 : ρ hZ' (AV j U' e') = ρ hZV (AV j (U ⊓ U') e'V) := by rw [he'V, aVal_res, ρ_ρ]
  have r4 : ρ hZ' (BV j U' e') = ρ hZV (BV j (U ⊓ U') e'V) := by rw [he'V, bVal_res, ρ_ρ]
  rw [r1, r2, r3, r4, ← hg, aVal_smul x i₁ i₂ p₁ p₂ h j₁ j hK, bVal_smul, map_mul, map_mul]
  ring

variable (hj : ∀ (U : (pullback x h).Opens) (e : Γ(L, U)), Scheme.Modules.IsFrameOn e U →
    IsUnit (toR₁ x i₁ h U (j₁.app U e)) ∧ IsUnit (toR₂ x i₂ h U (j₂.app U e)))

include hj in

theorem exists_unit (hL : Scheme.Modules.IsInvertible L) (hnode : ∀ j, (p₁ j).1 ≫ i₁.1 = (p₂ j).1 ≫ i₂.1) (j : ι) :
    ∃ uj : Γ(T, ⊤)ˣ, ∀ (W : (pullback x h).Opens) (e : Γ(L, W)), Scheme.Modules.IsFrameOn e W →
      AV j W e = T.presheaf.map (homOfLE le_top).op (uj : Γ(T, ⊤)) * BV j W e := by
  classical
  have hK := nodeSection_comp_eq x i₁ i₂ p₁ p₂ h hnode j

  have hfr : ∀ t : T, ∃ (U : (pullback x h).Opens) (s : Γ(L, U)),
      (nodeSectionFst p₁ h j ≫ curveChange i₁.1 i₁.2 h).base t ∈ U ∧ Scheme.Modules.IsFrameOn s U :=
    fun t => hL.exists_isFrameOn _
  choose U s hyU hs using hfr
  let V : T → T.Opens := fun t => nl j (U t)
  have htV : ∀ t, t ∈ V t := fun t => mem_nodeLocus x i₁ i₂ p₁ p₂ h hnode j (U t) t (hyU t)
  have hcov : (⊤ : T.Opens) ≤ iSup V := fun t _ => Opens.mem_iSup.mpr ⟨t, htV t⟩
  have ha : ∀ t, IsUnit (AV j (U t) (s t)) := fun t => (hj _ _ (hs t)).1.map _
  have hb : ∀ t, IsUnit (BV j (U t) (s t)) := fun t => (hj _ _ (hs t)).2.map _
  let r : ∀ t, Γ(T, V t) := fun t => AV j (U t) (s t) * ↑((hb t).unit⁻¹)
  let r' : ∀ t, Γ(T, V t) := fun t => BV j (U t) (s t) * ↑((ha t).unit⁻¹)

  have key : ∀ (t t' : T) (Zt : T.Opens) (hZ : Zt ≤ V t) (hZ' : Zt ≤ V t'), ρ hZ (r t) = ρ hZ' (r t') := by
    intro t t' Zt hZ hZ'
    have hx := cross x i₁ i₂ p₁ p₂ h j₁ j₂ j hK (s t) (s t') (hs t) hZ hZ'
    have h2 : ρ hZ (BV j (U t) (s t)) * ρ hZ ↑((hb t).unit⁻¹) = 1 := by
      rw [← map_mul, IsUnit.mul_val_inv, map_one]
    have h3 : ρ hZ' (BV j (U t') (s t')) * ρ hZ' ↑((hb t').unit⁻¹) = 1 := by
      rw [← map_mul, IsUnit.mul_val_inv, map_one]
    simp only [r, map_mul]
    linear_combination (ρ hZ ↑((hb t).unit⁻¹)) * (ρ hZ' ↑((hb t').unit⁻¹)) * hx
      - (ρ hZ (AV j (U t) (s t))) * (ρ hZ ↑((hb t).unit⁻¹)) * h3
      + (ρ hZ' (AV j (U t') (s t'))) * (ρ hZ' ↑((hb t').unit⁻¹)) * h2
  have key' : ∀ (t t' : T) (Zt : T.Opens) (hZ : Zt ≤ V t) (hZ' : Zt ≤ V t'), ρ hZ (r' t) = ρ hZ' (r' t') := by
    intro t t' Zt hZ hZ'
    have hx := cross x i₁ i₂ p₁ p₂ h j₁ j₂ j hK (s t) (s t') (hs t) hZ hZ'
    have h2 : ρ hZ (AV j (U t) (s t)) * ρ hZ ↑((ha t).unit⁻¹) = 1 := by
      rw [← map_mul, IsUnit.mul_val_inv, map_one]
    have h3 : ρ hZ' (AV j (U t') (s t')) * ρ hZ' ↑((ha t').unit⁻¹) = 1 := by
      rw [← map_mul, IsUnit.mul_val_inv, map_one]
    simp only [r', map_mul]
    linear_combination (-(ρ hZ ↑((ha t).unit⁻¹)) * (ρ hZ' ↑((ha t').unit⁻¹))) * hx
      - (ρ hZ (BV j (U t) (s t))) * (ρ hZ ↑((ha t).unit⁻¹)) * h3
      + (ρ hZ' (BV j (U t') (s t'))) * (ρ hZ' ↑((ha t').unit⁻¹)) * h2

  obtain ⟨uj, huj, -⟩ := TopCat.Sheaf.existsUnique_gluing' T.sheaf V ⊤ (fun t => homOfLE le_top) hcov r
    (fun t t' => key t t' _ inf_le_left inf_le_right)
  obtain ⟨wj, hwj, -⟩ := TopCat.Sheaf.existsUnique_gluing' T.sheaf V ⊤ (fun t => homOfLE le_top) hcov r'
    (fun t t' => key' t t' _ inf_le_left inf_le_right)
  have huj' : ∀ t, ρ (le_top : V t ≤ ⊤) uj = r t := huj
  have hwj' : ∀ t, ρ (le_top : V t ≤ ⊤) wj = r' t := hwj
  have hmul : uj * wj = 1 := by
    refine TopCat.Sheaf.eq_of_locally_eq' T.sheaf V ⊤ (fun t => homOfLE le_top) hcov _ _ fun t => ?_
    change ρ (le_top : V t ≤ ⊤) (uj * wj) = ρ (le_top : V t ≤ ⊤) 1
    rw [map_mul, map_one, huj', hwj']
    have h1 := (ha t).mul_val_inv
    have h2 := (hb t).mul_val_inv
    simp only [r, r']
    linear_combination (BV j (U t) (s t) * ↑((hb t).unit⁻¹)) * h1 + h2
  have hunit : IsUnit uj := IsUnit.of_mul_eq_one wj hmul
  refine ⟨hunit.unit, fun W e he => ?_⟩
  rw [IsUnit.unit_spec]

  refine TopCat.Sheaf.eq_of_locally_eq' T.sheaf (fun t => nl j W ⊓ V t) (nl j W) (fun t => homOfLE inf_le_left)
    (fun t ht => Opens.mem_iSup.mpr ⟨t, ht, htV t⟩) _ _ fun t => ?_
  change ρ (inf_le_left : nl j W ⊓ V t ≤ nl j W) (AV j W e) =
    ρ (inf_le_left : nl j W ⊓ V t ≤ nl j W) (T.presheaf.map (homOfLE le_top).op uj * BV j W e)
  have hu : ρ (inf_le_left : nl j W ⊓ V t ≤ nl j W) (T.presheaf.map (homOfLE le_top).op uj) =
      ρ (inf_le_right : nl j W ⊓ V t ≤ V t) (r t) := by
    rw [← huj' t, ρ_ρ]
    exact (ρ_ρ _ _ _).symm
  have hx := cross x i₁ i₂ p₁ p₂ h j₁ j₂ j hK e (s t) he (inf_le_left : nl j W ⊓ V t ≤ nl j W) inf_le_right
  have h3 : ρ (inf_le_right : nl j W ⊓ V t ≤ V t) (BV j (U t) (s t)) * ρ inf_le_right ↑((hb t).unit⁻¹) = 1 := by
    rw [← map_mul, IsUnit.mul_val_inv, map_one]
  rw [map_mul, hu]
  simp only [r, map_mul]
  linear_combination (ρ (inf_le_right : nl j W ⊓ V t ≤ V t) ↑((hb t).unit⁻¹)) * hx
    - (ρ (inf_le_left : nl j W ⊓ V t ≤ nl j W) (AV j W e)) * h3

end TwoGluedCurvesN7
p2m_reactivate "P2MW.S_AlgebraicGeometry_RelPicard_isNodeUnitModule_foldr_ofPoint_of_forall_eq_ord_of_hasValue.EPkgTwist P2MW.S_AlgebraicGeometry_RelPicard_isNodeUnitModule_foldr_ofPoint_of_forall_eq_ord_of_hasValue.EPrincI.Place P2MW.S_AlgebraicGeometry_RelPicard_isNodeUnitModule_foldr_ofPoint_of_forall_eq_ord_of_hasValue.EPrincI P2MW.S_AlgebraicGeometry_RelPicard_isNodeUnitModule_foldr_ofPoint_of_forall_eq_ord_of_hasValue.EPkg P2MW.S_AlgebraicGeometry_RelPicard_isNodeUnitModule_foldr_ofPoint_of_forall_eq_ord_of_hasValue.TwoGluedCurvesN7"

namespace TwoGluedCurvesN7

theorem exists_units_isNodeUnitModule_and_ratio
    (κ : Type u) [Field κ] [IsAlgClosed κ]
    {X C₁ C₂ : Scheme.{u}} (x : X ⟶ Spec (.of κ)) [IsReduced X]
    {c₁ : C₁ ⟶ Spec (.of κ)} {c₂ : C₂ ⟶ Spec (.of κ)}
    (i₁ : SchemeHomOver c₁ x) (i₂ : SchemeHomOver c₂ x)
    [IsClosedImmersion i₁.1] [IsClosedImmersion i₂.1]
    (hjs : ∀ z : X, z ∈ Set.range i₁.1.base ∨ z ∈ Set.range i₂.1.base)
    {ι : Type v} [Finite ι]
    (p₁ : ι → SchemeHomOver (𝟙 (Spec (.of κ))) c₁) (p₂ : ι → SchemeHomOver (𝟙 (Spec (.of κ))) c₂)
    (hinj : Function.Injective fun j => (p₁ j).1.base (IsLocalRing.closedPoint κ))
    (hnode : ∀ j, (p₁ j).1 ≫ i₁.1 = (p₂ j).1 ≫ i₂.1)
    (hinter : ∀ (q₁ : C₁) (q₂ : C₂), i₁.1.base q₁ = i₂.1.base q₂ →
      ∃ j, q₁ = (p₁ j).1.base (IsLocalRing.closedPoint κ) ∧ q₂ = (p₂ j).1.base (IsLocalRing.closedPoint κ))
    (hcr : IsReduced (pullback i₁.1 i₂.1))
    {T : Scheme.{u}} (h : T ⟶ Spec (.of κ)) (L : (pullback x h).Modules) (hL : Scheme.Modules.IsInvertible L)
    (e₁ : (Scheme.Modules.pullback (curveChange i₁.1 i₁.2 h)).obj L ≅ SheafOfModules.unit (pullback c₁ h).ringCatSheaf)
    (e₂ : (Scheme.Modules.pullback (curveChange i₂.1 i₂.2 h)).obj L ≅ SheafOfModules.unit (pullback c₂ h).ringCatSheaf) :
    ∃ u : ι → Γ(T, ⊤)ˣ, IsNodeUnitModule x i₁ i₂ p₁ p₂ h u L ∧
      ∀ (j : ι) (W : (pullback x h).Opens) (e : Γ(L, W)), Scheme.Modules.IsFrameOn e W →
        aVal x i₁ i₂ p₁ p₂ h (jOf (curveChange i₁.1 i₁.2 h) L e₁) j W e =
          T.presheaf.map (homOfLE le_top).op (u j : Γ(T, ⊤)) * bVal x i₁ i₂ p₁ p₂ h (jOf (curveChange i₂.1 i₂.2 h) L e₂) j W e := by
  classical
  let J₁ : L ⟶ P₁ x i₁ h := jOf (curveChange i₁.1 i₁.2 h) L e₁
  let J₂ : L ⟶ P₂ x i₂ h := jOf (curveChange i₂.1 i₂.2 h) L e₂
  have hj : ∀ (U : (pullback x h).Opens) (e : Γ(L, U)), Scheme.Modules.IsFrameOn e U →
      IsUnit (toR₁ x i₁ h U (J₁.app U e)) ∧ IsUnit (toR₂ x i₂ h U (J₂.app U e)) := fun U e he =>
    ⟨isUnit_jOf_app_of_isFrameOn _ L e₁ e he, isUnit_jOf_app_of_isFrameOn _ L e₂ e he⟩
  have hu := fun j => exists_unit x i₁ i₂ p₁ p₂ h J₁ J₂ hj hL hnode j
  choose u hu using hu
  refine ⟨u, ⟨J₁, J₂, ?_⟩, hu⟩
  apply injective_and_range_eq_nodeCondition_of_forall_exists_isFrameOn κ x i₁ i₂ hjs p₁ p₂ hinj hnode hinter hcr u J₁ J₂
  intro y
  obtain ⟨W, e, hyW, he⟩ := hL.exists_isFrameOn y
  exact ⟨W, e, toR₁ x i₁ h W (J₁.app W e), toR₂ x i₂ h W (J₂.app W e), hyW, he, rfl, rfl, (hj W e he).1,
    (hj W e he).2, fun j => (nodeCondition_iff x i₁ i₂ p₁ p₂ h u W j _ _).mpr (hu j W e he)⟩

end TwoGluedCurvesN7
p2m_reactivate "P2MW.S_AlgebraicGeometry_RelPicard_isNodeUnitModule_foldr_ofPoint_of_forall_eq_ord_of_hasValue.EPkgTwist P2MW.S_AlgebraicGeometry_RelPicard_isNodeUnitModule_foldr_ofPoint_of_forall_eq_ord_of_hasValue.EPrincI.Place P2MW.S_AlgebraicGeometry_RelPicard_isNodeUnitModule_foldr_ofPoint_of_forall_eq_ord_of_hasValue.EPrincI P2MW.S_AlgebraicGeometry_RelPicard_isNodeUnitModule_foldr_ofPoint_of_forall_eq_ord_of_hasValue.EPkg P2MW.S_AlgebraicGeometry_RelPicard_isNodeUnitModule_foldr_ofPoint_of_forall_eq_ord_of_hasValue.TwoGluedCurvesN7"

end Skel
p2m_reactivate "P2MW.S_AlgebraicGeometry_RelPicard_isNodeUnitModule_foldr_ofPoint_of_forall_eq_ord_of_hasValue.EPkgTwist P2MW.S_AlgebraicGeometry_RelPicard_isNodeUnitModule_foldr_ofPoint_of_forall_eq_ord_of_hasValue.EPrincI.Place P2MW.S_AlgebraicGeometry_RelPicard_isNodeUnitModule_foldr_ofPoint_of_forall_eq_ord_of_hasValue.EPrincI P2MW.S_AlgebraicGeometry_RelPicard_isNodeUnitModule_foldr_ofPoint_of_forall_eq_ord_of_hasValue.EPkg P2MW.S_AlgebraicGeometry_RelPicard_isNodeUnitModule_foldr_ofPoint_of_forall_eq_ord_of_hasValue.TwoGluedCurvesN7"

namespace TwoGluedCurvesN7

open Opposite TopologicalSpace

theorem opens_eq_top_of_mem {k : Type u} [Field k] (V : (Spec (CommRingCat.of k)).Opens)
    (h : IsLocalRing.closedPoint k ∈ V) : V = ⊤ :=
  top_le_iff.mp fun t _ => by obtain rfl : t = IsLocalRing.closedPoint k := Subsingleton.elim _ _; exact h

theorem units_eq_of_nodeValues {k : Type u} [Field k]
    {X C₁ C₂ : Scheme.{u}} {x : X ⟶ Spec (.of k)}
    {c₁ : C₁ ⟶ Spec (.of k)} {c₂ : C₂ ⟶ Spec (.of k)}
    {i₁ : SchemeHomOver c₁ x} {i₂ : SchemeHomOver c₂ x}
    {ι : Type v} {p₁ : ι → SchemeHomOver (𝟙 (Spec (.of k))) c₁} {p₂ : ι → SchemeHomOver (𝟙 (Spec (.of k))) c₂}
    {L : (pullback x (𝟙 (Spec (.of k)))).Modules}
    (J₁ : L ⟶ P₁ x i₁ (𝟙 _)) (J₂ : L ⟶ P₂ x i₂ (𝟙 _)) (u : ι → Γ(Spec (.of k), ⊤)ˣ)
    (hu : ∀ (j : ι) (W : (pullback x (𝟙 (Spec (.of k)))).Opens) (e : Γ(L, W)), Scheme.Modules.IsFrameOn e W →
      aVal x i₁ i₂ p₁ p₂ (𝟙 _) J₁ j W e =
        (Spec (.of k)).presheaf.map (homOfLE le_top).op (u j : Γ(Spec (.of k), ⊤)) * bVal x i₁ i₂ p₁ p₂ (𝟙 _) J₂ j W e)
    (j : ι) (W : (pullback x (𝟙 (Spec (.of k)))).Opens) (ee : Γ(L, W)) (hee : Scheme.Modules.IsFrameOn ee W)
    (hjW : IsLocalRing.closedPoint k ∈ nodeLocus x i₁ i₂ p₁ p₂ (𝟙 _) j W)
    (a : Γ(Spec (.of k), ⊤))
    (ha : aVal x i₁ i₂ p₁ p₂ (𝟙 _) J₁ j W ee = (Spec (.of k)).presheaf.map (homOfLE le_top).op a)
    (hb : bVal x i₁ i₂ p₁ p₂ (𝟙 _) J₂ j W ee = 1) :
    (u j : Γ(Spec (.of k), ⊤)) = a := by
  have h := hu j W ee hee
  rw [ha, hb, mul_one] at h

  have htop : nodeLocus x i₁ i₂ p₁ p₂ (𝟙 _) j W = ⊤ := opens_eq_top_of_mem _ hjW
  have hinj : Function.Injective ((Spec (.of k)).presheaf.map (homOfLE (le_top : nodeLocus x i₁ i₂ p₁ p₂ (𝟙 _) j W ≤ ⊤)).op) := by
    have : (homOfLE (le_top : nodeLocus x i₁ i₂ p₁ p₂ (𝟙 _) j W ≤ ⊤)).op = eqToHom (by rw [htop]) := Subsingleton.elim _ _
    rw [this, eqToHom_map]
    exact (ConcreteCategory.bijective_of_isIso _).1
  exact (hinj h).symm

end TwoGluedCurvesN7
p2m_reactivate "P2MW.S_AlgebraicGeometry_RelPicard_isNodeUnitModule_foldr_ofPoint_of_forall_eq_ord_of_hasValue.EPkgTwist P2MW.S_AlgebraicGeometry_RelPicard_isNodeUnitModule_foldr_ofPoint_of_forall_eq_ord_of_hasValue.EPrincI.Place P2MW.S_AlgebraicGeometry_RelPicard_isNodeUnitModule_foldr_ofPoint_of_forall_eq_ord_of_hasValue.EPrincI P2MW.S_AlgebraicGeometry_RelPicard_isNodeUnitModule_foldr_ofPoint_of_forall_eq_ord_of_hasValue.EPkg P2MW.S_AlgebraicGeometry_RelPicard_isNodeUnitModule_foldr_ofPoint_of_forall_eq_ord_of_hasValue.TwoGluedCurvesN7"

namespace EPkgTwist

p2m_open "AlgebraicGeometry.Scheme.IdealSheafData AlgebraicGeometry.Scheme.Modules"

variable {Y Y' : Scheme.{u}} {V : Type v}

theorem comap_preimage_ι_eq_top (f : Y' ⟶ Y) {I : Y.IdealSheafData} {J : Y'.IdealSheafData}
    (hJ : I.comap f = J) {W : Y.Opens} (hW : I.comap W.ι = ⊤) : J.comap ((f ⁻¹ᵁ W : Y'.Opens)).ι = ⊤ := by
  rw [← hJ, ← comap_comp, ← morphismRestrict_ι, comap_comp, hW, comap_top]

theorem jOf_app_eCan_eq_one (f : Y' ⟶ Y) (P : V → Y.IdealSheafData) (D : V → ℤ) (l : List V)
    (h : ∀ v ∈ l, (P v).IsInvertible ∧ (P v).comap f = ⊤ ∧ (⊤ : Y'.IdealSheafData).IsInvertible)
    (W : Y.Opens) (hW : ∀ v ∈ l, (P v).comap W.ι = ⊤) :
    (TwoGluedCurvesN7.jOf f (twistL P D l) (twistLComparisonIso f P (fun _ => ⊤) D l h ≪≫ twistLTopIso D l)).app W
        (eCan P D l W hW) = (1 : Γ(Y', f ⁻¹ᵁ W)) := by
  have hW' : ∀ v ∈ l, ((fun _ => (⊤ : Y'.IdealSheafData)) v).comap ((f ⁻¹ᵁ W : Y'.Opens)).ι = ⊤ :=
    fun _ _ => comap_top _
  have heq : (twistLComparisonIso f P (fun _ => ⊤) D l h ≪≫ twistLTopIso D l).hom.app (f ⁻¹ᵁ W)
      (pullbackLocalSection f (eCan P D l W hW)) =
      (TwoGluedCurvesN7.jOf f (twistL P D l) (twistLComparisonIso f P (fun _ => ⊤) D l h ≪≫ twistLTopIso D l)).app W
        (eCan P D l W hW) := by
    rw [app_pullbackLocalSection]; rfl
  rw [← heq, Iso.trans_hom, Scheme.Modules.Hom.comp_app, CategoryTheory.comp_apply,
    twistLComparisonIso_hom_app_pullbackLocalSection_eCan f P _ D l h W hW hW',
    twistLTopIso_hom_app_eCan D l (f ⁻¹ᵁ W) hW']
  rfl

end EPkgTwist
p2m_reactivate "P2MW.S_AlgebraicGeometry_RelPicard_isNodeUnitModule_foldr_ofPoint_of_forall_eq_ord_of_hasValue.EPkgTwist P2MW.S_AlgebraicGeometry_RelPicard_isNodeUnitModule_foldr_ofPoint_of_forall_eq_ord_of_hasValue.EPrincI.Place P2MW.S_AlgebraicGeometry_RelPicard_isNodeUnitModule_foldr_ofPoint_of_forall_eq_ord_of_hasValue.EPrincI P2MW.S_AlgebraicGeometry_RelPicard_isNodeUnitModule_foldr_ofPoint_of_forall_eq_ord_of_hasValue.EPkg P2MW.S_AlgebraicGeometry_RelPicard_isNodeUnitModule_foldr_ofPoint_of_forall_eq_ord_of_hasValue.TwoGluedCurvesN7"

namespace TwoGluedCurvesN7

variable {κ : Type u} [Field κ]
  {X C₁ C₂ : Scheme.{u}} (x : X ⟶ Spec (.of κ))
  {c₁ : C₁ ⟶ Spec (.of κ)} {c₂ : C₂ ⟶ Spec (.of κ)}
  (i₁ : SchemeHomOver c₁ x) (i₂ : SchemeHomOver c₂ x)
  {ι : Type v} (p₁ : ι → SchemeHomOver (𝟙 (Spec (.of κ))) c₁) (p₂ : ι → SchemeHomOver (𝟙 (Spec (.of κ))) c₂)
  {T : Scheme.{u}} (h : T ⟶ Spec (.of κ))

theorem toR₂_jOf_app_eCan_eq_one {V : Type v} (P : V → (pullback x h).IdealSheafData) (D : V → ℤ) (l : List V)
    (hP : ∀ v ∈ l, (P v).IsInvertible ∧ (P v).comap (curveChange i₂.1 i₂.2 h) = ⊤ ∧
      (⊤ : (pullback c₂ h).IdealSheafData).IsInvertible)
    (W : (pullback x h).Opens) (hW : ∀ v ∈ l, (P v).comap W.ι = ⊤) :
    toR₂ x i₂ h W ((jOf (curveChange i₂.1 i₂.2 h) (EPkgTwist.twistL P D l)
      (EPkgTwist.twistLComparisonIso (curveChange i₂.1 i₂.2 h) P (fun _ => ⊤) D l hP ≪≫
        EPkgTwist.twistLTopIso D l)).app W (EPkgTwist.eCan P D l W hW)) = 1 :=
  EPkgTwist.jOf_app_eCan_eq_one _ P D l hP W hW

theorem nv₂_one (j : ι) (W : (pullback x h).Opens) : nv₂ x i₁ i₂ p₁ p₂ h j W 1 = 1 := by
  unfold nv₂; exact map_one _

theorem nv₁_one (j : ι) (W : (pullback x h).Opens) : nv₁ x i₁ i₂ p₁ p₂ h j W 1 = 1 := by
  unfold nv₁; exact map_one _

end TwoGluedCurvesN7
p2m_reactivate "P2MW.S_AlgebraicGeometry_RelPicard_isNodeUnitModule_foldr_ofPoint_of_forall_eq_ord_of_hasValue.EPkgTwist P2MW.S_AlgebraicGeometry_RelPicard_isNodeUnitModule_foldr_ofPoint_of_forall_eq_ord_of_hasValue.EPrincI.Place P2MW.S_AlgebraicGeometry_RelPicard_isNodeUnitModule_foldr_ofPoint_of_forall_eq_ord_of_hasValue.EPrincI P2MW.S_AlgebraicGeometry_RelPicard_isNodeUnitModule_foldr_ofPoint_of_forall_eq_ord_of_hasValue.EPkg P2MW.S_AlgebraicGeometry_RelPicard_isNodeUnitModule_foldr_ofPoint_of_forall_eq_ord_of_hasValue.TwoGluedCurvesN7"

namespace EPkgTwist

p2m_open "AlgebraicGeometry.Scheme.Modules"

variable {Y Y' : Scheme.{u}}

def pullbackEquivOfIsIso (φ : Y' ⟶ Y) [IsIso φ] : Y.Modules ≌ Y'.Modules :=
  CategoryTheory.Equivalence.mk (Scheme.Modules.pullback φ) (Scheme.Modules.pullback (inv φ))
    ((Scheme.Modules.pullbackId Y).symm ≪≫ Scheme.Modules.pullbackCongr (IsIso.inv_hom_id φ).symm ≪≫
      (Scheme.Modules.pullbackComp (inv φ) φ).symm)
    (Scheme.Modules.pullbackComp φ (inv φ) ≪≫ Scheme.Modules.pullbackCongr (IsIso.hom_inv_id φ) ≪≫
      Scheme.Modules.pullbackId Y')

scoped instance isEquivalence_pullback_of_isIso (φ : Y' ⟶ Y) [IsIso φ] : (Scheme.Modules.pullback φ).IsEquivalence :=
  (pullbackEquivOfIsIso φ).isEquivalence_functor

scoped instance isIso_unit_pullbackPushforwardAdjunction_of_isIso (φ : Y' ⟶ Y) [IsIso φ] :
    IsIso (Scheme.Modules.pullbackPushforwardAdjunction φ).unit := by
  infer_instance

scoped instance isIso_unitToPushforwardUnit_of_isIso (φ : Y' ⟶ Y) [IsIso φ] :
    IsIso (show (𝟙_ Y.Modules) ⟶ (Scheme.Modules.pushforward φ).obj (𝟙_ Y'.Modules) from φ.unitToPushforwardUnit) := by
  rw [Scheme.Modules.Hom.isIso_iff_isIso_app]
  intro U
  rw [ConcreteCategory.isIso_iff_bijective]
  exact ConcreteCategory.bijective_of_isIso (φ.app U)

def transposeOfPullbackIso (φ : Y' ⟶ Y) (M : Y.Modules)
    (e' : (Scheme.Modules.pullback φ).obj M ≅ 𝟙_ Y'.Modules) :
    M ⟶ (Scheme.Modules.pushforward φ).obj (𝟙_ Y'.Modules) :=
  ((Scheme.Modules.pullbackPushforwardAdjunction φ).homEquiv _ _) e'.hom

scoped instance isIso_transposeOfPullbackIso (φ : Y' ⟶ Y) [IsIso φ] (M : Y.Modules)
    (e' : (Scheme.Modules.pullback φ).obj M ≅ 𝟙_ Y'.Modules) : IsIso (transposeOfPullbackIso φ M e') := by
  unfold transposeOfPullbackIso
  rw [Adjunction.homEquiv_unit]
  haveI h1 : IsIso ((Scheme.Modules.pullbackPushforwardAdjunction φ).unit.app M) := inferInstance
  haveI h2 : IsIso ((Scheme.Modules.pushforward φ).map e'.hom) := inferInstance
  exact @IsIso.comp_isIso _ _ _ _ _ _ _ h1 h2

def isoUnitOfPullbackIso (φ : Y' ⟶ Y) [IsIso φ] (M : Y.Modules)
    (e' : (Scheme.Modules.pullback φ).obj M ≅ 𝟙_ Y'.Modules) : M ≅ 𝟙_ Y.Modules :=
  asIso (transposeOfPullbackIso φ M e') ≪≫
    (@asIso _ _ _ _ (show (𝟙_ Y.Modules) ⟶ (Scheme.Modules.pushforward φ).obj (𝟙_ Y'.Modules) from φ.unitToPushforwardUnit)
      (isIso_unitToPushforwardUnit_of_isIso φ)).symm

theorem app_isoUnitOfPullbackIso_hom (φ : Y' ⟶ Y) [IsIso φ] (M : Y.Modules)
    (e' : (Scheme.Modules.pullback φ).obj M ≅ 𝟙_ Y'.Modules) (W : Y.Opens) (s : Γ(M, W)) :
    φ.app W ((isoUnitOfPullbackIso φ M e').hom.app W s) =
      e'.hom.app (φ ⁻¹ᵁ W) (Scheme.Modules.pullbackLocalSection φ s) := by

  have h1 : (transposeOfPullbackIso φ M e').app W s = e'.hom.app (φ ⁻¹ᵁ W) (Scheme.Modules.pullbackLocalSection φ s) := by
    rw [Scheme.Modules.app_pullbackLocalSection]; rfl

  have h2 : ∀ t : Γ((Scheme.Modules.pushforward φ).obj (𝟙_ Y'.Modules), W),
      φ.app W ((inv (show (𝟙_ Y.Modules) ⟶ (Scheme.Modules.pushforward φ).obj (𝟙_ Y'.Modules) from
        φ.unitToPushforwardUnit)).app W t) = t := fun t => by
    have h := congrArg (fun ψ => Scheme.Modules.Hom.app ψ W t)
      (IsIso.inv_hom_id (show (𝟙_ Y.Modules) ⟶ (Scheme.Modules.pushforward φ).obj (𝟙_ Y'.Modules) from
        φ.unitToPushforwardUnit))
    simp only [Scheme.Modules.Hom.comp_app, Scheme.Modules.Hom.id_app, CategoryTheory.comp_apply,
      CategoryTheory.id_apply] at h
    exact h
  rw [isoUnitOfPullbackIso, Iso.trans_hom, asIso_hom, Iso.symm_hom, asIso_inv, Scheme.Modules.Hom.comp_app,
    CategoryTheory.comp_apply, h1]
  exact h2 _

end EPkgTwist
p2m_reactivate "P2MW.S_AlgebraicGeometry_RelPicard_isNodeUnitModule_foldr_ofPoint_of_forall_eq_ord_of_hasValue.EPkgTwist P2MW.S_AlgebraicGeometry_RelPicard_isNodeUnitModule_foldr_ofPoint_of_forall_eq_ord_of_hasValue.EPrincI.Place P2MW.S_AlgebraicGeometry_RelPicard_isNodeUnitModule_foldr_ofPoint_of_forall_eq_ord_of_hasValue.EPrincI P2MW.S_AlgebraicGeometry_RelPicard_isNodeUnitModule_foldr_ofPoint_of_forall_eq_ord_of_hasValue.EPkg P2MW.S_AlgebraicGeometry_RelPicard_isNodeUnitModule_foldr_ofPoint_of_forall_eq_ord_of_hasValue.TwoGluedCurvesN7"

namespace EPrincI

theorem exists_iso_readF_eCan_eq_mul {k : Type u} [Field k] [IsAlgClosed k]
    {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of k)) [IsProper c] [SmoothOfRelativeDimension 1 c] [GeometricallyIntegral c]
    (F : Type u) [Field F] [Algebra k F] [HasPrincipalDivisors k F] (hCB : ConstantsAreBase k F)
    (Mdl : CurveModel k F) (e : Mdl.C ≅ C) (he : e.hom ≫ c = Mdl.toBase)
    (pt : Place k F → (Spec (CommRingCat.of k) ⟶ C)) (hpt : ∀ v, pt v ≫ c = 𝟙 _)
    (hpt' : ∀ v, pt v = (Mdl.pointEquivPlace.symm v).1 ≫ e.hom)
    (D : Place k F →₀ ℤ) (g : F) (hg : g ≠ 0) (ha : ∀ v : Place k F, D v = v.ord g) :
    ∃ (β : EPkgTwist.twistL (fun v => (RelEffCartierDiv.ofPoint c (pt v) (hpt v)).I) ⇑D D.support.toList ≅
        𝟙_ (pullback c (𝟙 (Spec (CommRingCat.of k)))).Modules) (cst : kˣ),
      ∀ (W : (pullback c (𝟙 (Spec (CommRingCat.of k)))).Opens)
        (hW : ∀ v ∈ D.support.toList, (RelEffCartierDiv.ofPoint c (pt v) (hpt v)).I.comap W.ι = ⊤)
        [Nonempty (Scheme.Opens.toScheme ((modelIso c Mdl e) ⁻¹ᵁ W))],
        readF c Mdl e W (β.hom.app W (EPkgTwist.eCan (fun v => (RelEffCartierDiv.ofPoint c (pt v) (hpt v)).I) ⇑D
          D.support.toList W hW)) = algebraMap k F (cst : k) * g := by
  set φ := modelIso c Mdl e with hφ
  set Q : Place k F → (pullback c (𝟙 (Spec (CommRingCat.of k)))).IdealSheafData :=
    fun v => (RelEffCartierDiv.ofPoint c (pt v) (hpt v)).I with hQ
  have invQ : ∀ v, (Q v).IsInvertible := fun v => RelEffCartierDiv.isInvertible_I _
  have invQ' : ∀ v, ((Q v).comap φ).IsInvertible := fun v => (invQ v).comap_of_isOpenImmersion φ
  obtain ⟨β', cst, hβ'⟩ := exists_iso_germ_eCan_eq_mul_model c F hCB Mdl e he pt hpt hpt' D g hg ha
  let θφ := EPkgTwist.twistLComparisonIso φ Q (fun v => (Q v).comap φ) ⇑D D.support.toList
    (fun v _ => ⟨invQ v, rfl, invQ' v⟩)
  refine ⟨EPkgTwist.isoUnitOfPullbackIso φ _ (θφ ≪≫ β'), cst, fun W hW _ => ?_⟩
  have hW' : ∀ v ∈ D.support.toList, ((Q v).comap φ).comap (φ ⁻¹ᵁ W).ι = ⊤ := fun v hv =>
    EPkgTwist.comap_preimage_ι_eq_top φ rfl (hW v hv)
  unfold readF
  rw [EPkgTwist.app_isoUnitOfPullbackIso_hom, Iso.trans_hom, Scheme.Modules.Hom.comp_app, CategoryTheory.comp_apply,
    EPkgTwist.twistLComparisonIso_hom_app_pullbackLocalSection_eCan φ Q _ ⇑D _ _ W hW hW']
  exact hβ' (φ ⁻¹ᵁ W) hW'

end EPrincI
p2m_reactivate "P2MW.S_AlgebraicGeometry_RelPicard_isNodeUnitModule_foldr_ofPoint_of_forall_eq_ord_of_hasValue.EPkgTwist P2MW.S_AlgebraicGeometry_RelPicard_isNodeUnitModule_foldr_ofPoint_of_forall_eq_ord_of_hasValue.EPrincI.Place P2MW.S_AlgebraicGeometry_RelPicard_isNodeUnitModule_foldr_ofPoint_of_forall_eq_ord_of_hasValue.EPrincI P2MW.S_AlgebraicGeometry_RelPicard_isNodeUnitModule_foldr_ofPoint_of_forall_eq_ord_of_hasValue.EPkg P2MW.S_AlgebraicGeometry_RelPicard_isNodeUnitModule_foldr_ofPoint_of_forall_eq_ord_of_hasValue.TwoGluedCurvesN7"

theorem solution
    {k : Type u} [Field k] [IsAlgClosed k]
    {X C C' : Scheme.{u}} (x : X ⟶ Spec (CommRingCat.of k)) [IsSeparated x] (hXred : IsReduced X)
    (c : C ⟶ Spec (CommRingCat.of k)) (c' : C' ⟶ Spec (CommRingCat.of k))
    [IsProper c] [SmoothOfRelativeDimension 1 c] [GeometricallyIntegral c]
    (i : SchemeHomOver c x) (i' : SchemeHomOver c' x) [IsClosedImmersion i.1] [IsClosedImmersion i'.1]
    (hjs : ∀ z : X, z ∈ Set.range i.1.base ∨ z ∈ Set.range i'.1.base)
    (hcr : IsReduced (pullback i.1 i'.1))
    {ι : Type v} [Finite ι]
    (p : ι → SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) c) (p' : ι → SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) c')
    (hinj : Function.Injective fun j => (p j).1.base (IsLocalRing.closedPoint k))
    (hnode : ∀ j, (p j).1 ≫ i.1 = (p' j).1 ≫ i'.1)
    (hinter : ∀ (q : C) (q' : C'), i.1.base q = i'.1.base q' →
      ∃ j, q = (p j).1.base (IsLocalRing.closedPoint k) ∧ q' = (p' j).1.base (IsLocalRing.closedPoint k))

    (F : Type u) [Field F] [Algebra k F] [HasPrincipalDivisors k F] (hCB : ConstantsAreBase k F)
    (Mdl : CurveModel k F) (e : Mdl.C ≅ C) (he : e.hom ≫ c = Mdl.toBase)
    (pt : Place k F → (Spec (CommRingCat.of k) ⟶ C)) (hpt : ∀ v, pt v ≫ c = 𝟙 _)
    (hpt' : ∀ v, pt v = (Mdl.pointEquivPlace.symm v).1 ≫ e.hom)
    (plc : ι → Place k F)
    (hplc : ∀ j, plc j = Mdl.pointEquivPlace ⟨(p j).1 ≫ e.inv, by rw [← he, Category.assoc, e.inv_hom_id_assoc]; exact (p j).2⟩)

    (D : Place k F →₀ ℤ) (g : F) (va : ι → kˣ) (hg : g ≠ 0)
    (ha : ∀ v : Place k F, D v = v.ord g) (hD : ∀ j, D (plc j) = 0)
    (hv : ∀ j, (plc j).HasValue g (va j)) :
    IsNodeUnitModule x i i' p p' (𝟙 (Spec (CommRingCat.of k)))
      (fun j => Units.map (Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom.toMonoidHom (va j))
      (((D.support.toList).foldr
          (fun v M => ((RelEffCartierDiv.ofPoint x (pt v ≫ i.1) (by rw [Category.assoc, i.2]; exact hpt v)).I ^ (D v).toNat).invModule ⊗
            ((RelEffCartierDiv.ofPoint x (pt v ≫ i.1) (by rw [Category.assoc, i.2]; exact hpt v)).I ^ (-(D v)).toNat).module ⊗ M)
          (𝟙_ (pullback x (𝟙 (Spec (CommRingCat.of k)))).Modules))) := by

  classical
  haveI : IsReduced X := hXred

  obtain ⟨hIso, hSm⟩ :=
    isIso_morphismRestrict_and_smoothOfRelativeDimension_one_of_coe_eq_compl_range_of_isClosedImmersion
      x hXred c i i'.1 hjs (EPkg.coOpen i'.1) (EPkg.coe_coOpen _)
  haveI := hIso; haveI := hSm

  let P : Place k F → (pullback x (𝟙 (Spec (CommRingCat.of k)))).IdealSheafData := fun v =>
    (RelEffCartierDiv.ofPoint x (pt v ≫ i.1) (by rw [Category.assoc, i.2]; exact hpt v)).I
  let Q : Place k F → (pullback c (𝟙 (Spec (CommRingCat.of k)))).IdealSheafData := fun v =>
    (RelEffCartierDiv.ofPoint c (pt v) (hpt v)).I
  let l := D.support.toList

  have rg : ∀ v ∈ l, Set.range (pt v ≫ i.1).base ⊆ ((EPkg.coOpen i'.1 : X.Opens) : Set X) := fun v hv =>
    EPrincD.range_subset_coOpen_of_mem_support x c c' i i' p p' hinter F Mdl e he pt hpt hpt' plc hplc D hD v
      (Finset.mem_toList.mp hv)
  have invP : ∀ v ∈ l, (P v).IsInvertible := fun v hv =>
    RelEffCartierDiv.isInvertible_I_of_supportedIn (EPkg.coOpen i'.1) _
      (EPrincD.supportedIn_ofPoint_of_range_subset x _ _ _ (rg v hv))
  have invQ : ∀ v, (Q v).IsInvertible := fun v => RelEffCartierDiv.isInvertible_I _

  have hc₁ : ∀ v ∈ l, (P v).comap (curveChange i.1 i.2 (𝟙 _)) = Q v := fun v hv =>
    (RelEffCartierDiv.comap_curveChange_ofPoint_comp_eq_and_isIso_pullbackModuleComparison_of_isIso_morphismRestrict
      x c i.1 i.2 (𝟙 _) (pt v) (hpt v) (EPkg.coOpen i'.1) (rg v hv)).1
  have hc₂ : ∀ v ∈ l, (P v).comap (curveChange i'.1 i'.2 (𝟙 _)) = ⊤ := fun v hv => by
    refine (RelEffCartierDiv.comap_curveChange_ofPoint_eq_top_and_isIso_pullbackModuleComparison_of_disjoint
      x c' i'.1 i'.2 (𝟙 _) (pt v ≫ i.1) (by rw [Category.assoc, i.2]; exact hpt v) ?_ (EPkg.coOpen i'.1) (rg v hv)).1
    exact Set.disjoint_left.mpr (fun y hy hy' => rg v hv hy hy')

  let θ₁ := EPkgTwist.twistLComparisonIso (curveChange i.1 i.2 (𝟙 _)) P Q ⇑D l
    (fun v hv => ⟨invP v hv, hc₁ v hv, invQ v⟩)
  let θ₂ := EPkgTwist.twistLComparisonIso (curveChange i'.1 i'.2 (𝟙 _)) P (fun _ => ⊤) ⇑D l
    (fun v hv => ⟨invP v hv, hc₂ v hv, Scheme.IdealSheafData.isInvertible_top⟩)
  let e₂ : (Scheme.Modules.pullback (curveChange i'.1 i'.2 (𝟙 _))).obj (EPkgTwist.twistL P ⇑D l) ≅
      SheafOfModules.unit (pullback c' (𝟙 (Spec (CommRingCat.of k)))).ringCatSheaf :=
    θ₂ ≪≫ EPkgTwist.twistLTopIso ⇑D l
  have hN : Scheme.Modules.IsInvertible (EPkgTwist.twistL P ⇑D l) := EPkgTwist.isInvertible_twistL P ⇑D l invP

  obtain ⟨β, cst, hβ⟩ := EPrincI.exists_iso_readF_eCan_eq_mul c F hCB Mdl e he pt hpt hpt' D g hg ha
  let e₁ : (Scheme.Modules.pullback (curveChange i.1 i.2 (𝟙 _))).obj (EPkgTwist.twistL P ⇑D l) ≅
      SheafOfModules.unit (pullback c (𝟙 (Spec (CommRingCat.of k)))).ringCatSheaf := θ₁ ≪≫ β

  obtain ⟨u, hNU, hu⟩ := TwoGluedCurvesN7.exists_units_isNodeUnitModule_and_ratio k x i i' hjs p p' hinj hnode hinter hcr
    (𝟙 _) (EPkgTwist.twistL P ⇑D l) hN e₁ e₂

  let V : (pullback x (𝟙 (Spec (CommRingCat.of k)))).Opens :=
    EPrincI.awayFrom x (fun v => pt v ≫ i.1) (fun v => by rw [Category.assoc, i.2]; exact hpt v) l
  have hV : ∀ v ∈ l, (P v).comap V.ι = ⊤ := fun v hv =>
    EPrincD.comap_ker_graphOver_eq_top_of_forall_notMem x _ _ V.ι (fun y hy => y.2 (Set.mem_biUnion hv hy))
  have hnodeV : ∀ j, (graphOver (g := 𝟙 (Spec (CommRingCat.of k))) x ((p j).1 ≫ i.1)
      (by rw [Category.assoc, i.2]; exact (p j).2)).base (IsLocalRing.closedPoint k) ∈ V := fun j => by
    change _ ∈ (⋃ v ∈ l, Set.range (graphOver x (pt v ≫ i.1) _).base)ᶜ
    rw [Set.mem_compl_iff, Set.mem_iUnion₂]
    rintro ⟨v, hv, hmem⟩
    exact EPrincD.graphOver_node_notMem_range x c c' i i' p p' hinter F Mdl e he pt hpt hpt' plc hplc D hD j v
      (Finset.mem_toList.mp hv) hmem
  have hsec : ∀ j, nodeSectionFst p (𝟙 (Spec (CommRingCat.of k))) j ≫ curveChange i.1 i.2 (𝟙 _) =
      graphOver (g := 𝟙 (Spec (CommRingCat.of k))) x ((p j).1 ≫ i.1) (by rw [Category.assoc, i.2]; exact (p j).2) := by
    intro j
    apply pullback.hom_ext
    · simp only [nodeSectionFst, rigSection, curveChange, graphOver_eq_lift, pullback.map, Category.assoc, pullback.lift_fst,
        pullback.lift_fst_assoc, Category.id_comp]
    · simp only [nodeSectionFst, rigSection, curveChange, graphOver_eq_lift, pullback.map, Category.assoc, pullback.lift_snd,
        pullback.lift_snd_assoc, Category.id_comp, Category.comp_id]
  have hjV : ∀ j, IsLocalRing.closedPoint k ∈ nodeLocus x i i' p p' (𝟙 _) j V := fun j =>
    TwoGluedCurvesN7.mem_nodeLocus x i i' p p' (𝟙 _) hnode j V _ (by rw [hsec]; exact hnodeV j)

  have hc₁' : ∀ v ∈ l, (Q v).comap ((curveChange i.1 i.2 (𝟙 _)) ⁻¹ᵁ V).ι = ⊤ := fun v hv =>
    EPkgTwist.comap_preimage_ι_eq_top _ (hc₁ v hv) (hV v hv)
  have VALS : ∀ j : ι, ∃ (W : (pullback x (𝟙 (Spec (CommRingCat.of k)))).Opens) (ee : Γ(EPkgTwist.twistL P ⇑D l, W)),
      Scheme.Modules.IsFrameOn ee W ∧
      IsLocalRing.closedPoint k ∈ nodeLocus x i i' p p' (𝟙 _) j W ∧
      TwoGluedCurvesN7.aVal x i i' p p' (𝟙 _) (TwoGluedCurvesN7.jOf (curveChange i.1 i.2 (𝟙 _)) _ e₁) j W ee =
        (Spec (CommRingCat.of k)).presheaf.map (homOfLE le_top).op
          ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ((cst : k) * (va j : k))) ∧
      TwoGluedCurvesN7.bVal x i i' p p' (𝟙 _) (TwoGluedCurvesN7.jOf (curveChange i'.1 i'.2 (𝟙 _)) _ e₂) j W ee = 1 := by
    intro j
    refine ⟨V, EPkgTwist.eCan P ⇑D l V hV, EPkgTwist.isFrameOn_eCan P ⇑D l V hV invP, hjV j, ?_, ?_⟩
    ·
      let W₁ : (pullback c (𝟙 (Spec (CommRingCat.of k)))).Opens := (curveChange i.1 i.2 (𝟙 (Spec (CommRingCat.of k)))) ⁻¹ᵁ V

      have hJ : (TwoGluedCurvesN7.jOf (curveChange i.1 i.2 (𝟙 (Spec (CommRingCat.of k)))) _ e₁).app V (EPkgTwist.eCan P ⇑D l V hV) =
          β.hom.app W₁ (EPkgTwist.eCan Q ⇑D l W₁ hc₁') := by
        have heq : e₁.hom.app W₁ (Scheme.Modules.pullbackLocalSection (curveChange i.1 i.2 (𝟙 (Spec (CommRingCat.of k))))
            (EPkgTwist.eCan P ⇑D l V hV)) =
            (TwoGluedCurvesN7.jOf (curveChange i.1 i.2 (𝟙 (Spec (CommRingCat.of k)))) _ e₁).app V (EPkgTwist.eCan P ⇑D l V hV) := by
          rw [Scheme.Modules.app_pullbackLocalSection]; rfl
        rw [← heq]
        change (θ₁ ≪≫ β).hom.app W₁ (Scheme.Modules.pullbackLocalSection (curveChange i.1 i.2 (𝟙 (Spec (CommRingCat.of k)))) (EPkgTwist.eCan P ⇑D l V hV)) = _
        rw [Iso.trans_hom, Scheme.Modules.Hom.comp_app, CategoryTheory.comp_apply,
          EPkgTwist.twistLComparisonIso_hom_app_pullbackLocalSection_eCan _ P Q ⇑D l _ V hV hc₁']

      have hq : ⊤ ≤ (rigSection c (𝟙 (Spec (CommRingCat.of k))) ⟨(p j).1, (p j).2⟩) ⁻¹ᵁ W₁ := by
        intro t _
        obtain rfl : t = IsLocalRing.closedPoint k := Subsingleton.elim _ _
        exact (hjV j).1
      haveI : Nonempty (Scheme.Opens.toScheme ((EPrincI.modelIso c Mdl e) ⁻¹ᵁ W₁)) := by
        refine ⟨⟨(inv (EPrincI.modelIso c Mdl e)).base
          ((rigSection c (𝟙 (Spec (CommRingCat.of k))) ⟨(p j).1, (p j).2⟩).base (IsLocalRing.closedPoint k)), ?_⟩⟩
        change (EPrincI.modelIso c Mdl e).base ((inv (EPrincI.modelIso c Mdl e)).base _) ∈ W₁
        rw [← Scheme.Hom.comp_apply, IsIso.inv_hom_id]
        exact hq trivial

      have hval : (Mdl.pointEquivPlace ⟨(p j).1 ≫ e.inv, by rw [← he, Category.assoc, e.inv_hom_id_assoc]; exact (p j).2⟩).HasValue
          (EPrincI.readF c Mdl e W₁ (β.hom.app W₁ (EPkgTwist.eCan Q ⇑D l W₁ hc₁'))) ((cst : k) * (va j : k)) := by
        rw [← hplc j, hβ W₁ hc₁']
        exact (Place.hasValue_algebraMap _ _).mul (hv j)
      have hγ := EPrincI.appLE_rigSection_eq_of_hasValue_readF c Mdl e he W₁ _ (p j).1 (p j).2 hq _ hval

      change TwoGluedCurvesN7.nv₁ x i i' p p' (𝟙 _) j V (TwoGluedCurvesN7.toR₁ x i (𝟙 _) V
        ((TwoGluedCurvesN7.jOf (curveChange i.1 i.2 (𝟙 (Spec (CommRingCat.of k)))) _ e₁).app V (EPkgTwist.eCan P ⇑D l V hV))) = _
      rw [hJ]
      change (nodeSectionFst p (𝟙 (Spec (CommRingCat.of k))) j).appLE W₁ (nodeLocus x i i' p p' (𝟙 _) j V) inf_le_left
        (β.hom.app W₁ (EPkgTwist.eCan Q ⇑D l W₁ hc₁')) = _
      have happ : (nodeSectionFst p (𝟙 (Spec (CommRingCat.of k))) j).appLE W₁ (nodeLocus x i i' p p' (𝟙 _) j V) inf_le_left =
          (rigSection c (𝟙 (Spec (CommRingCat.of k))) ⟨(p j).1, (p j).2⟩).appLE W₁ ⊤ hq ≫
            (Spec (CommRingCat.of k)).presheaf.map (homOfLE le_top).op := by
        rw [Scheme.Hom.appLE_map]; rfl
      rw [happ, CategoryTheory.comp_apply, hγ]
    ·
      change TwoGluedCurvesN7.nv₂ x i i' p p' (𝟙 _) j V (TwoGluedCurvesN7.toR₂ x i' (𝟙 _) V
        ((TwoGluedCurvesN7.jOf (curveChange i'.1 i'.2 (𝟙 _)) _ e₂).app V (EPkgTwist.eCan P ⇑D l V hV))) = 1
      rw [TwoGluedCurvesN7.toR₂_jOf_app_eCan_eq_one x i' (𝟙 _) P ⇑D l _ V hV, TwoGluedCurvesN7.nv₂_one]

  have hu' : ∀ j, u j = Units.map (Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom.toMonoidHom cst *
      Units.map (Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom.toMonoidHom (va j) := by
    intro j
    obtain ⟨W, ee, hee, hjW, ha, hb⟩ := VALS j
    ext
    rw [Units.val_mul, Units.coe_map, Units.coe_map, ← map_mul]
    exact TwoGluedCurvesN7.units_eq_of_nodeValues _ _ u hu j W ee hee hjW _ ha hb
  have key := hNU.smul_units (Units.map (Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom.toMonoidHom cst)⁻¹
  convert key using 2 with j
  rw [hu', ← mul_assoc, inv_mul_cancel, one_mul]
  rfl

end
p2m_reactivate "P2MW.S_AlgebraicGeometry_RelPicard_isNodeUnitModule_foldr_ofPoint_of_forall_eq_ord_of_hasValue.EPkgTwist P2MW.S_AlgebraicGeometry_RelPicard_isNodeUnitModule_foldr_ofPoint_of_forall_eq_ord_of_hasValue.EPrincI.Place P2MW.S_AlgebraicGeometry_RelPicard_isNodeUnitModule_foldr_ofPoint_of_forall_eq_ord_of_hasValue.EPrincI P2MW.S_AlgebraicGeometry_RelPicard_isNodeUnitModule_foldr_ofPoint_of_forall_eq_ord_of_hasValue.EPkg P2MW.S_AlgebraicGeometry_RelPicard_isNodeUnitModule_foldr_ofPoint_of_forall_eq_ord_of_hasValue.TwoGluedCurvesN7"

end S_AlgebraicGeometry_RelPicard_isNodeUnitModule_foldr_ofPoint_of_forall_eq_ord_of_hasValue
end P2MW
export P2MW.S_AlgebraicGeometry_RelPicard_isNodeUnitModule_foldr_ofPoint_of_forall_eq_ord_of_hasValue (solution)
