-- Prove2me | solution 1 for AlgebraicGeometry.RelPicard.exists_gluedTwist_admissible_of_twoGluedSmoothCurves
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:03.589526+00:00
-- url     : https://prove2.me/submissions/111b1e8e-c001-57a2-927d-b8ea8151bef7

import Mathlib
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
import Theorems.Thm_AlgebraicGeometry_RelEffCartierDiv_comap_curveChange_ofPoint_comp_eq_and_isIso_pullbackModuleComparison_of_isIso_morphismRestrict
import Theorems.Thm_AlgebraicGeometry_RelEffCartierDiv_comap_curveChange_ofPoint_eq_top_and_isIso_pullbackModuleComparison_of_disjoint
import Theorems.Thm_AlgebraicGeometry_RelPicard_isNodeUnitModule_foldr_ofPoint_tensor_foldr_ofPoint_of_forall_eq_ord_of_twoGluedSmoothCurves
import Theorems.Thm_AlgebraicGeometry_isIso_morphismRestrict_and_smoothOfRelativeDimension_one_of_coe_eq_compl_range_of_isClosedImmersion
import Theorems.Thm_AlgebraicGeometry_RelEffCartierDiv_isInvertible_I_of_supportedIn
import Theorems.Thm_AlgebraicGeometry_RelEffCartierDiv_supportedIn_ofPoint
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_RelPicard_exists_gluedTwist_admissible_of_twoGluedSmoothCurves
p2m_attr_erase "instance" "AlgebraicGeometry.RelEffCartierDiv.isClosedImmersion_subschemeι_resProdMap AlgebraicGeometry.RelEffCartierDiv.isOpenImmersion_resProdMap SheafOfModules.isIso_ihomModelToIhom AlgebraicGeometry.ChowDatum.hι_closed AlgebraicGeometry.ChowDatumProj.hιN_closed AlgebraicGeometry.ChowDatumProj.hp_proper AlgebraicGeometry.ChowDatum.hp_isoU AlgebraicGeometry.ChowDatum.hp_proper AlgebraicGeometry.ProjSpace.algebraAway AlgebraicGeometry.ProjSpace.instIsProperProdOverπ AlgebraicGeometry.ChowDatumProj.hp_isoU AlgebraicGeometry.ProjSpace.isProper_π AlgebraicGeometry.ProjSpace.finiteType_mvPolynomial AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation TwoChartCech.Sections.M0_moduleA TwoChartCech.Sections.M1_module TwoChartCech.Cover.A01_algebra TwoChartCech.Cover.A0_algebra TwoChartCech.Cover.A1_commRing TwoChartCech.Cover.A1_algebra TwoChartCech.Sections.M01_module TwoChartCech.Sections.M0_addCommGroup TwoChartCech.Sections.M0_tower TwoChartCech.Sections.M01_addCommGroup TwoChartCech.Cover.A0_commRing TwoChartCech.Sections.M1_tower TwoChartCech.Sections.M01_moduleA TwoChartCech.Sections.M0_module TwoChartCech.Sections.M1_moduleA TwoChartCech.Sections.M1_addCommGroup TwoChartCech.Cover.A01_commRing TwoChartCech.Sections.M01_tower CoherentBaseChange.TwoTermComplex.C0_module CoherentBaseChange.TwoTermComplex.C0_addCommGroup CoherentBaseChange.TwoTermComplex.C1_module CoherentBaseChange.TwoTermComplex.C1_addCommGroup CoherentBaseChange.TwoTermComplex.C0_free CoherentBaseChange.TwoTermComplex.C1_finite CoherentBaseChange.TwoTermComplex.C0_finite"
p2m_attr_erase "instance" "CoherentBaseChange.TwoTermComplex.C1_free AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupDivisor AlgebraicCurve.Pic0.instModuleZModTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instDistribMulActionTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instSMulTorsion AlgebraicCurve.SemilinearAut.instMulActionSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instSMulCommClassZModTorsion AlgebraicCurve.SemilinearAut.instMulSemiringActionSubtypeProdRingAutMemSubgroup instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions"
p2m_attr_erase "simp" "AlgebraicGeometry.Scheme.Modules.toUnitSection_ofUnitSection AlgebraicGeometry.Scheme.Modules.pullbackSection_def AlgebraicGeometry.Scheme.Modules.ofUnitSection_toUnitSection AlgebraicGeometry.RelEffCartierDiv.restrictAlong_extendAlong AlgebraicGeometry.RelEffCartierDiv.extendAlong_I AlgebraicGeometry.RelEffCartierDiv.resProdMap_snd AlgebraicGeometry.RelEffCartierDiv.restrictAlong_I AlgebraicGeometry.RelEffCartierDiv.extendAlong_restrictAlong AlgebraicGeometry.RelEffCartierDiv.resProdMap_fst_assoc AlgebraicGeometry.RelEffCartierDiv.resProdMap_snd_assoc AlgebraicGeometry.RelEffCartierDiv.resProdMap_fst AlgebraicGeometry.Scheme.Modules.tensorSections_zero_right AlgebraicGeometry.Scheme.Modules.map_unitSection AlgebraicGeometry.Scheme.Modules.tensorSectionsBilin_apply AlgebraicGeometry.Scheme.Modules.tensorPowSection_zero AlgebraicGeometry.Scheme.Modules.tensorSections_zero_left AlgebraicGeometry.Scheme.Modules.tensorPow_zero AlgebraicGeometry.Scheme.Modules.tensorPow_succ AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_neg AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_zero AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_sub AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_add PresheafOfModules.InternalHom.IsSheafAux.appAt_toPresheafHom SheafOfModules.ihomSectionsEquivFamily_unit AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_apply SheafOfModules.ihomEval_unit_app AlgebraicGeometry.Scheme.Modules.ihomEval_zero_right AlgebraicGeometry.Scheme.Modules.ihomEval_zero_left AlgebraicGeometry.Scheme.Modules.homOfFamily_app_apply SheafOfModules.unit_ihomSectionsEquivFamily AlgebraicGeometry.Scheme.Modules.familyOfHom_app AlgebraicGeometry.Scheme.Modules.restrictUnitIso_hom_app_apply AlgebraicGeometry.Scheme.Modules.restrictUnitIso_inv_app_apply AlgebraicGeometry.Scheme.Modules.restrictHomOfFamily_app_apply AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_symm_apply AlgebraicGeometry.Scheme.Modules.ProjPresentation.mk.injEq AlgebraicGeometry.Scheme.Modules.ProjPresentation.mk.sizeOf_spec AlgebraicGeometry.ChowDatumProj.mk.sizeOf_spec AlgebraicGeometry.ChowDatum.mk.sizeOf_spec AlgebraicGeometry.ChowDatumProj.mk.injEq"
p2m_attr_erase "simp" "AlgebraicGeometry.ChowDatum.mk.injEq AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.coe_cechH0Equiv_apply AlgebraicCurve.cechH1ToH1_mk AlgebraicCurve.lSpaceOn_univ AlgebraicCurve.lSpaceOn_empty TwoChartCech.Sections.mk.injEq TwoChartCech.Cover.mk.injEq TwoChartCech.GrothendieckComplex.mk.injEq TwoChartCech.Sections.mk.sizeOf_spec TwoChartCech.Cover.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r0_apply TwoChartCech.GrothendieckComplex.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r1_apply CoherentBaseChange.TwoTermComplex.mk.sizeOf_spec CoherentBaseChange.TwoTermComplex.mk.injEq AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk"
p2m_attr_erase "simp" "ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.SemilinearAut.toRingAut_inv AlgebraicCurve.SemilinearAut.smul_def AlgebraicCurve.SemilinearAut.smul_single AlgebraicCurve.SemilinearAut.smul_toValuationSubring AlgebraicCurve.SemilinearAut.baseAut_inv AlgebraicCurve.SemilinearAut.baseAut_ofAlgAut AlgebraicCurve.SemilinearAut.toRingAut_ofAlgAut AlgebraicCurve.SemilinearAut.torsionRep_apply AlgebraicCurve.SemilinearAut.toRingAut_one AlgebraicCurve.SemilinearAut.deg_smul AlgebraicCurve.SemilinearAut.degree_smul AlgebraicCurve.SemilinearAut.coe_degZeroSMulHom AlgebraicCurve.SemilinearAut.baseAut_mul AlgebraicCurve.SemilinearAut.coe_smulValuationSubringEquiv_apply AlgebraicCurve.SemilinearAut.baseAut_one AlgebraicCurve.SemilinearAut.ofAlgAut_smul AlgebraicCurve.SemilinearAut.coe_torsion_smul AlgebraicCurve.SemilinearAut.toRingAut_mul AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.jqNModC_one ModularCurve.qExpand_coeff_mul ModularCurve.qExpandₐ_apply ModularCurve.jqN_one ModularCurve.qExpand_single ModularCurve.dedekindPsi_one ModularCurve.ModularPolynomialData.mk.sizeOf_spec"
p2m_attr_erase "simp" "ModularCurve.evalAtJ_X ModularCurve.ModularPolynomialData.mk.injEq ModularCurve.constantCoeff_jNum ModularCurve.constantCoeff_eisenstein4 ModularCurve.qExpand_C ModularCurve.coeff_jq_neg_one ModularCurve.constantCoeff_jNumQ ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one"
set_option autoImplicit false

universe u v

p2m_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry NeronModelInfra GoodReductionJacobian AlgebraicGeometry.RelPicard AlgebraicGeometry.TwoGluedCurves AlgebraicCurve"

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
p2m_reactivate "P2MW.S_AlgebraicGeometry_RelPicard_exists_gluedTwist_admissible_of_twoGluedSmoothCurves.EPkgTwist"

namespace EPkg

p2m_open "P2MW.S_AlgebraicGeometry_RelPicard_exists_gluedTwist_admissible_of_twoGluedSmoothCurves.EPkgTwist AlgebraicGeometry.Scheme.IdealSheafData"

def coOpen {X C : Scheme.{u}} (i : C ⟶ X) [IsClosedImmersion i] : X.Opens :=
  ⟨(Set.range i.base)ᶜ, i.isClosedEmbedding.isClosed_range.isOpen_compl⟩

@[scoped simp] theorem coe_coOpen {X C : Scheme.{u}} (i : C ⟶ X) [IsClosedImmersion i] :
    (coOpen i : Set X) = (Set.range i.base)ᶜ := rfl

theorem ofPoint_I_congr {𝒞 S T : Scheme.{u}} (f : 𝒞 ⟶ S) [IsSeparated f] {g : T ⟶ S}
    {a a' : T ⟶ 𝒞} (ha : a ≫ f = g) (ha' : a' ≫ f = g) (h : a = a') :
    (RelEffCartierDiv.ofPoint f a ha).I = (RelEffCartierDiv.ofPoint f a' ha').I := by
  subst h; rfl

section KPoints

variable {k : Type u} [Field k]

theorem isClosed_singleton_base {Y : Scheme.{u}} (y : Y ⟶ Spec (CommRingCat.of k))
    (p : Spec (CommRingCat.of k) ⟶ Y) (hp : p ≫ y = 𝟙 _) :
    IsClosed ({p.base (IsLocalRing.closedPoint k)} : Set Y) := by
  have := isClosedImmersion_of_comp_eq_id _ _ hp
  have h := p.isClosedEmbedding.isClosed_range
  rwa [Set.range_eq_singleton] at h
  exact fun t => congrArg p.base (Subsingleton.elim _ _)

end KPoints
p2m_reactivate "P2MW.S_AlgebraicGeometry_RelPicard_exists_gluedTwist_admissible_of_twoGluedSmoothCurves.EPkgTwist"

section Frame

variable {k : Type u} [Field k] [IsAlgClosed k]
  {X C₁ C₂ : Scheme.{u}} (x : X ⟶ Spec (CommRingCat.of k)) [IsProper x]
  (c₁ : C₁ ⟶ Spec (CommRingCat.of k)) (c₂ : C₂ ⟶ Spec (CommRingCat.of k))
  [SmoothOfRelativeDimension 1 c₂]
  (i₁ : SchemeHomOver c₁ x) (i₂ : SchemeHomOver c₂ x) [IsClosedImmersion i₁.1] [IsClosedImmersion i₂.1]
  (F : Type u) [Field F] [Algebra k F]
  (Mdl₁ : CurveModel k F) (e₁ : Mdl₁.C ≅ C₁) (he₁ : e₁.hom ≫ c₁ = Mdl₁.toBase)
  (pt₁ : Place k F → (Spec (CommRingCat.of k) ⟶ C₁)) (hpt₁ : ∀ v, pt₁ v ≫ c₁ = 𝟙 _)
  (hpt₁' : ∀ v, pt₁ v = (Mdl₁.pointEquivPlace.symm v).1 ≫ e₁.hom)
  (S : Finset (Place k F × Place k F))
  (nd : ↥S ≃ SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) (pullback.fst i₁.1 i₂.1 ≫ c₁))
  (hS₁ : ∀ σ : ↥S,
      (σ : Place k F × Place k F).1 = Mdl₁.pointEquivPlace ⟨((nd σ).1 ≫ pullback.fst i₁.1 i₂.1) ≫ e₁.inv,
          by rw [← he₁, Category.assoc, e₁.inv_hom_id_assoc, Category.assoc]; exact (nd σ).2⟩)

include hpt₁ hpt₁' hS₁ in

theorem exists_eq_fst_of_mem_range (v : Place k F)
    (hv : (pt₁ v ≫ i₁.1).base (IsLocalRing.closedPoint k) ∈ Set.range i₂.1.base) :
    ∃ σ : ↥S, (σ : Place k F × Place k F).1 = v := by
  obtain ⟨q₂, hq⟩ := hv

  have hP : (pt₁ v ≫ i₁.1) ≫ x = 𝟙 _ := by rw [Category.assoc, i₁.2]; exact hpt₁ v
  have hcl : IsClosed ({q₂} : Set C₂) := by
    have h1 := (isClosed_singleton_base x _ hP).preimage i₂.1.continuous
    have : i₂.1.base ⁻¹' {(pt₁ v ≫ i₁.1).base (IsLocalRing.closedPoint k)} = {q₂} := by
      ext q; simp only [Set.mem_preimage, Set.mem_singleton_iff]
      constructor
      · intro h; exact i₂.1.isClosedEmbedding.injective (h.trans hq.symm)
      · rintro rfl; exact hq
    rwa [this] at h1

  haveI : Smooth c₂ := SmoothOfRelativeDimension.smooth 1 c₂
  haveI : LocallyOfFiniteType c₂ := inferInstance
  let Q : Spec (CommRingCat.of k) ⟶ C₂ := pointOfClosedPoint c₂ q₂ hcl
  have hQ : Q ≫ c₂ = 𝟙 _ := pointOfClosedPoint_comp c₂ q₂ hcl
  have hQpt : Q.base (IsLocalRing.closedPoint k) = q₂ := pointOfClosedPoint_apply c₂ q₂ hcl _

  have hQx : (Q ≫ i₂.1) ≫ x = 𝟙 _ := by rw [Category.assoc, i₂.2]; exact hQ
  have heq : pt₁ v ≫ i₁.1 = Q ≫ i₂.1 := by
    refine ext_of_apply_closedPoint_eq x hP hQx ?_
    rw [Scheme.Hom.comp_apply, Scheme.Hom.comp_apply, hQpt, hq, Scheme.Hom.comp_apply]

  let z : Spec (CommRingCat.of k) ⟶ pullback i₁.1 i₂.1 := pullback.lift (pt₁ v) Q heq
  have hz : z ≫ (pullback.fst i₁.1 i₂.1 ≫ c₁) = 𝟙 _ := by
    rw [← Category.assoc, pullback.lift_fst]; exact hpt₁ v
  obtain ⟨σ, hσ⟩ := nd.surjective ⟨z, hz⟩
  refine ⟨σ, ?_⟩
  rw [hS₁ σ, ← Mdl₁.pointEquivPlace.apply_symm_apply v]
  congr 1
  apply Subtype.ext
  change ((nd σ).1 ≫ pullback.fst i₁.1 i₂.1) ≫ e₁.inv = (Mdl₁.pointEquivPlace.symm v).1
  rw [hσ]
  change (z ≫ pullback.fst i₁.1 i₂.1) ≫ e₁.inv = _
  rw [pullback.lift_fst, hpt₁' v, Category.assoc, e₁.hom_inv_id, Category.comp_id]

end Frame
p2m_reactivate "P2MW.S_AlgebraicGeometry_RelPicard_exists_gluedTwist_admissible_of_twoGluedSmoothCurves.EPkgTwist"

theorem exists_eq_snd_of_mem_range {k : Type u} [Field k] [IsAlgClosed k]
    {X C₁ C₂ : Scheme.{u}} (x : X ⟶ Spec (CommRingCat.of k)) [IsProper x]
    (c₁ : C₁ ⟶ Spec (CommRingCat.of k)) (c₂ : C₂ ⟶ Spec (CommRingCat.of k))
    [SmoothOfRelativeDimension 1 c₁]
    (i₁ : SchemeHomOver c₁ x) (i₂ : SchemeHomOver c₂ x) [IsClosedImmersion i₁.1]
    (hc : pullback.snd i₁.1 i₂.1 ≫ c₂ = pullback.fst i₁.1 i₂.1 ≫ c₁)
    (F : Type u) [Field F] [Algebra k F]
    (Mdl₂ : CurveModel k F) (e₂ : Mdl₂.C ≅ C₂) (he₂ : e₂.hom ≫ c₂ = Mdl₂.toBase)
    (pt₂ : Place k F → (Spec (CommRingCat.of k) ⟶ C₂)) (hpt₂ : ∀ v, pt₂ v ≫ c₂ = 𝟙 _)
    (hpt₂' : ∀ v, pt₂ v = (Mdl₂.pointEquivPlace.symm v).1 ≫ e₂.hom)
    (S : Finset (Place k F × Place k F))
    (nd : ↥S ≃ SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) (pullback.fst i₁.1 i₂.1 ≫ c₁))
    (hS₂ : ∀ σ : ↥S,
      (σ : Place k F × Place k F).2 = Mdl₂.pointEquivPlace ⟨((nd σ).1 ≫ pullback.snd i₁.1 i₂.1) ≫ e₂.inv,
          by rw [← he₂, Category.assoc, e₂.inv_hom_id_assoc, Category.assoc, hc]; exact (nd σ).2⟩)
    (v : Place k F)
    (hv : (pt₂ v ≫ i₂.1).base (IsLocalRing.closedPoint k) ∈ Set.range i₁.1.base) :
    ∃ σ : ↥S, (σ : Place k F × Place k F).2 = v := by
  obtain ⟨q₁, hq⟩ := hv
  have hP : (pt₂ v ≫ i₂.1) ≫ x = 𝟙 _ := by rw [Category.assoc, i₂.2]; exact hpt₂ v
  have hcl : IsClosed ({q₁} : Set C₁) := by
    have h1 := (isClosed_singleton_base x _ hP).preimage i₁.1.continuous
    have : i₁.1.base ⁻¹' {(pt₂ v ≫ i₂.1).base (IsLocalRing.closedPoint k)} = {q₁} := by
      ext q; simp only [Set.mem_preimage, Set.mem_singleton_iff]
      constructor
      · intro h; exact i₁.1.isClosedEmbedding.injective (h.trans hq.symm)
      · rintro rfl; exact hq
    rwa [this] at h1
  haveI : Smooth c₁ := SmoothOfRelativeDimension.smooth 1 c₁
  haveI : LocallyOfFiniteType c₁ := inferInstance
  let Q : Spec (CommRingCat.of k) ⟶ C₁ := pointOfClosedPoint c₁ q₁ hcl
  have hQ : Q ≫ c₁ = 𝟙 _ := pointOfClosedPoint_comp c₁ q₁ hcl
  have hQpt : Q.base (IsLocalRing.closedPoint k) = q₁ := pointOfClosedPoint_apply c₁ q₁ hcl _
  have hQx : (Q ≫ i₁.1) ≫ x = 𝟙 _ := by rw [Category.assoc, i₁.2]; exact hQ
  have heq : Q ≫ i₁.1 = pt₂ v ≫ i₂.1 := by
    refine ext_of_apply_closedPoint_eq x hQx hP ?_
    rw [Scheme.Hom.comp_apply, Scheme.Hom.comp_apply, hQpt, hq, Scheme.Hom.comp_apply]
  let z : Spec (CommRingCat.of k) ⟶ pullback i₁.1 i₂.1 := pullback.lift Q (pt₂ v) heq
  have hz : z ≫ (pullback.fst i₁.1 i₂.1 ≫ c₁) = 𝟙 _ := by
    rw [← Category.assoc, pullback.lift_fst]; exact hQ
  obtain ⟨σ, hσ⟩ := nd.surjective ⟨z, hz⟩
  refine ⟨σ, ?_⟩
  rw [hS₂ σ, ← Mdl₂.pointEquivPlace.apply_symm_apply v]
  congr 1
  apply Subtype.ext
  change ((nd σ).1 ≫ pullback.snd i₁.1 i₂.1) ≫ e₂.inv = (Mdl₂.pointEquivPlace.symm v).1
  rw [hσ]
  change (z ≫ pullback.snd i₁.1 i₂.1) ≫ e₂.inv = _
  rw [pullback.lift_snd, hpt₂' v, Category.assoc, e₂.hom_inv_id, Category.comp_id]

end EPkg
p2m_reactivate "P2MW.S_AlgebraicGeometry_RelPicard_exists_gluedTwist_admissible_of_twoGluedSmoothCurves.EPkgTwist P2MW.S_AlgebraicGeometry_RelPicard_exists_gluedTwist_admissible_of_twoGluedSmoothCurves.EPkg"

theorem solution
    {k : Type u} [Field k] [IsAlgClosed k]
    {X C₁ C₂ : Scheme.{u}} (x : X ⟶ Spec (CommRingCat.of k)) [IsProper x] (hXred : IsReduced X)
    (c₁ : C₁ ⟶ Spec (CommRingCat.of k)) (c₂ : C₂ ⟶ Spec (CommRingCat.of k))
    [IsProper c₁] [SmoothOfRelativeDimension 1 c₁] [GeometricallyIntegral c₁]
    [IsProper c₂] [SmoothOfRelativeDimension 1 c₂] [GeometricallyIntegral c₂]
    (i₁ : SchemeHomOver c₁ x) (i₂ : SchemeHomOver c₂ x) [IsClosedImmersion i₁.1] [IsClosedImmersion i₂.1]
    (hjs : ∀ z : X, z ∈ Set.range i₁.1.base ∨ z ∈ Set.range i₂.1.base)
    (hcr : IsReduced (pullback i₁.1 i₂.1)) (s : ℕ) (hs : Nat.card ↥(pullback i₁.1 i₂.1) = s) (hs0 : 0 < s)

    (hc : pullback.snd i₁.1 i₂.1 ≫ c₂ = pullback.fst i₁.1 i₂.1 ≫ c₁)
    (F : Type u) [Field F] [Algebra k F] [HasPrincipalDivisors k F] (hCB : ConstantsAreBase k F)
    (Mdl₁ : CurveModel k F) (e₁ : Mdl₁.C ≅ C₁) (he₁ : e₁.hom ≫ c₁ = Mdl₁.toBase)
    (Mdl₂ : CurveModel k F) (e₂ : Mdl₂.C ≅ C₂) (he₂ : e₂.hom ≫ c₂ = Mdl₂.toBase)

    (pt₁ : Place k F → (Spec (CommRingCat.of k) ⟶ C₁)) (hpt₁ : ∀ v, pt₁ v ≫ c₁ = 𝟙 _)
    (hpt₁' : ∀ v, pt₁ v = (Mdl₁.pointEquivPlace.symm v).1 ≫ e₁.hom)
    (pt₂ : Place k F → (Spec (CommRingCat.of k) ⟶ C₂)) (hpt₂ : ∀ v, pt₂ v ≫ c₂ = 𝟙 _)
    (hpt₂' : ∀ v, pt₂ v = (Mdl₂.pointEquivPlace.symm v).1 ≫ e₂.hom)
    (S : Finset (Place k F × Place k F))
    (nd : ↥S ≃ SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) (pullback.fst i₁.1 i₂.1 ≫ c₁))
    (hS : ∀ σ : ↥S,
        (σ : Place k F × Place k F).1 = Mdl₁.pointEquivPlace ⟨((nd σ).1 ≫ pullback.fst i₁.1 i₂.1) ≫ e₁.inv,
            by rw [← he₁, Category.assoc, e₁.inv_hom_id_assoc, Category.assoc]; exact (nd σ).2⟩ ∧
        (σ : Place k F × Place k F).2 = Mdl₂.pointEquivPlace ⟨((nd σ).1 ≫ pullback.snd i₁.1 i₂.1) ≫ e₂.inv,
            by rw [← he₂, Category.assoc, e₂.inv_hom_id_assoc, Category.assoc, hc]; exact (nd σ).2⟩) :
    ∃ E : ↥(GluingData.admissible S) → (pullback x (𝟙 (Spec (CommRingCat.of k)))).Modules,

      (∀ a, Scheme.Modules.IsInvertible (E a)) ∧

      (∀ a b, Nonempty (E (a + b) ≅ E a ⊗ E b)) ∧

      (∀ a : ↥(GluingData.admissible S), (a : GluingData k F S).1 = 0 → (a : GluingData k F S).2.1 = 0 →
        Nonempty (E a ≅ 𝟙_ (pullback x (𝟙 (Spec (CommRingCat.of k)))).Modules)) ∧

      (∀ a : ↥(GluingData.admissible S),
        Nonempty ((Scheme.Modules.pullback (curveChange i₁.1 i₁.2 (𝟙 (Spec (CommRingCat.of k))))).obj (E a) ≅
          ((((a : GluingData k F S).1).support.toList).foldr
            (fun v M => ((RelEffCartierDiv.ofPoint c₁ (pt₁ v) (hpt₁ v)).I ^ (((a : GluingData k F S).1) v).toNat).invModule ⊗
              ((RelEffCartierDiv.ofPoint c₁ (pt₁ v) (hpt₁ v)).I ^ (-(((a : GluingData k F S).1) v)).toNat).module ⊗ M)
            (𝟙_ (pullback c₁ (𝟙 (Spec (CommRingCat.of k)))).Modules))) ∧
        Nonempty ((Scheme.Modules.pullback (curveChange i₂.1 i₂.2 (𝟙 (Spec (CommRingCat.of k))))).obj (E a) ≅
          ((((a : GluingData k F S).2.1).support.toList).foldr
            (fun v M => ((RelEffCartierDiv.ofPoint c₂ (pt₂ v) (hpt₂ v)).I ^ (((a : GluingData k F S).2.1) v).toNat).invModule ⊗
              ((RelEffCartierDiv.ofPoint c₂ (pt₂ v) (hpt₂ v)).I ^ (-(((a : GluingData k F S).2.1) v)).toNat).module ⊗ M)
            (𝟙_ (pullback c₂ (𝟙 (Spec (CommRingCat.of k)))).Modules)))) ∧

      (∀ (a : ↥(GluingData.admissible S)) (g₁ g₂ : F) (va vb : ↥S → kˣ), g₁ ≠ 0 → g₂ ≠ 0 →
        (∀ v : Place k F, (a : GluingData k F S).1 v = v.ord g₁) → (∀ v : Place k F, (a : GluingData k F S).2.1 v = v.ord g₂) →
        (∀ σ : ↥S, (σ : Place k F × Place k F).1.HasValue g₁ (va σ) ∧ (σ : Place k F × Place k F).2.HasValue g₂ (vb σ)) →
        IsNodeUnitModule x i₁ i₂
          (fun σ => ⟨(nd σ).1 ≫ pullback.fst i₁.1 i₂.1, by rw [Category.assoc]; exact (nd σ).2⟩)
          (fun σ => ⟨(nd σ).1 ≫ pullback.snd i₁.1 i₂.1, by rw [Category.assoc, hc]; exact (nd σ).2⟩)
          (𝟙 (Spec (CommRingCat.of k)))
          (fun σ => Units.map (Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom.toMonoidHom (va σ / vb σ))
          (E a)) ∧

      (∀ (P Q : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) c₁)
        (_ : (P.1 ≫ i₁.1).base (IsLocalRing.closedPoint k) ∉ Set.range i₂.1.base)
        (_ : (Q.1 ≫ i₁.1).base (IsLocalRing.closedPoint k) ∉ Set.range i₂.1.base)
        (a : ↥(GluingData.admissible S))
        (_ : (a : GluingData k F S).1 = Finsupp.single (Mdl₁.pointEquivPlace ⟨P.1 ≫ e₁.inv, by rw [← he₁, Category.assoc, e₁.inv_hom_id_assoc]; exact P.2⟩) 1 - Finsupp.single (Mdl₁.pointEquivPlace ⟨Q.1 ≫ e₁.inv, by rw [← he₁, Category.assoc, e₁.inv_hom_id_assoc]; exact Q.2⟩) 1)
        (_ : (a : GluingData k F S).2.1 = 0),
        Nonempty (E a ≅
          (RelEffCartierDiv.ofPoint x (P.1 ≫ i₁.1) (by rw [Category.assoc, i₁.2]; exact P.2)).lineBundle ⊗
            (RelEffCartierDiv.ofPoint x (Q.1 ≫ i₁.1) (by rw [Category.assoc, i₁.2]; exact Q.2)).idealModule)) ∧

      (∀ (P Q : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) c₂)
        (_ : (P.1 ≫ i₂.1).base (IsLocalRing.closedPoint k) ∉ Set.range i₁.1.base)
        (_ : (Q.1 ≫ i₂.1).base (IsLocalRing.closedPoint k) ∉ Set.range i₁.1.base)
        (a : ↥(GluingData.admissible S))
        (_ : (a : GluingData k F S).1 = 0)
        (_ : (a : GluingData k F S).2.1 = Finsupp.single (Mdl₂.pointEquivPlace ⟨P.1 ≫ e₂.inv, by rw [← he₂, Category.assoc, e₂.inv_hom_id_assoc]; exact P.2⟩) 1 - Finsupp.single (Mdl₂.pointEquivPlace ⟨Q.1 ≫ e₂.inv, by rw [← he₂, Category.assoc, e₂.inv_hom_id_assoc]; exact Q.2⟩) 1),
        Nonempty (E a ≅
          (RelEffCartierDiv.ofPoint x (P.1 ≫ i₂.1) (by rw [Category.assoc, i₂.2]; exact P.2)).lineBundle ⊗
            (RelEffCartierDiv.ofPoint x (Q.1 ≫ i₂.1) (by rw [Category.assoc, i₂.2]; exact Q.2)).idealModule)) := by
  classical

  obtain ⟨hIso₁, hSm₁⟩ :=
    isIso_morphismRestrict_and_smoothOfRelativeDimension_one_of_coe_eq_compl_range_of_isClosedImmersion
      x hXred c₁ i₁ i₂.1 hjs (EPkg.coOpen i₂.1) (EPkg.coe_coOpen _)
  obtain ⟨hIso₂, hSm₂⟩ :=
    isIso_morphismRestrict_and_smoothOfRelativeDimension_one_of_coe_eq_compl_range_of_isClosedImmersion
      x hXred c₂ i₂ i₁.1 (fun z => (hjs z).symm) (EPkg.coOpen i₁.1) (EPkg.coe_coOpen _)

  let P₁ : Place k F → (pullback x (𝟙 (Spec (CommRingCat.of k)))).IdealSheafData := fun v =>
    (RelEffCartierDiv.ofPoint x (pt₁ v ≫ i₁.1) (by rw [Category.assoc, i₁.2]; exact hpt₁ v)).I
  let P₂ : Place k F → (pullback x (𝟙 (Spec (CommRingCat.of k)))).IdealSheafData := fun v =>
    (RelEffCartierDiv.ofPoint x (pt₂ v ≫ i₂.1) (by rw [Category.assoc, i₂.2]; exact hpt₂ v)).I
  let Q₁ : Place k F → (pullback c₁ (𝟙 (Spec (CommRingCat.of k)))).IdealSheafData := fun v =>
    (RelEffCartierDiv.ofPoint c₁ (pt₁ v) (hpt₁ v)).I
  let Q₂ : Place k F → (pullback c₂ (𝟙 (Spec (CommRingCat.of k)))).IdealSheafData := fun v =>
    (RelEffCartierDiv.ofPoint c₂ (pt₂ v) (hpt₂ v)).I

  have off₁ : ∀ (a : ↥(GluingData.admissible S)) (v : Place k F), v ∈ ((a : GluingData k F S).1).support →
      (pt₁ v ≫ i₁.1).base (IsLocalRing.closedPoint k) ∉ Set.range i₂.1.base := by
    intro a v hv hmem
    obtain ⟨σ, hσ⟩ := EPkg.exists_eq_fst_of_mem_range x c₁ c₂ i₁ i₂ F Mdl₁ e₁ he₁ pt₁ hpt₁ hpt₁' S nd
      (fun σ => (hS σ).1) v hmem
    have h0 := (((GluingData.mem_admissible S).mp a.2).2.2 σ.1 σ.2).1
    rw [hσ] at h0
    exact (Finsupp.mem_support_iff.mp hv) h0
  have off₂ : ∀ (a : ↥(GluingData.admissible S)) (v : Place k F), v ∈ ((a : GluingData k F S).2.1).support →
      (pt₂ v ≫ i₂.1).base (IsLocalRing.closedPoint k) ∉ Set.range i₁.1.base := by
    intro a v hv hmem
    obtain ⟨σ, hσ⟩ := EPkg.exists_eq_snd_of_mem_range x c₁ c₂ i₁ i₂ hc F Mdl₂ e₂ he₂ pt₂ hpt₂ hpt₂' S nd
      (fun σ => (hS σ).2) v hmem
    have h0 := (((GluingData.mem_admissible S).mp a.2).2.2 σ.1 σ.2).2
    rw [hσ] at h0
    exact (Finsupp.mem_support_iff.mp hv) h0

  have rg₁ : ∀ (a : ↥(GluingData.admissible S)) (v : Place k F), v ∈ ((a : GluingData k F S).1).support →
      Set.range (pt₁ v ≫ i₁.1).base ⊆ ((EPkg.coOpen i₂.1 : X.Opens) : Set X) := by
    rintro a v hv _ ⟨t, rfl⟩
    obtain rfl : t = IsLocalRing.closedPoint k := Subsingleton.elim _ _
    exact off₁ a v hv
  have rg₂ : ∀ (a : ↥(GluingData.admissible S)) (v : Place k F), v ∈ ((a : GluingData k F S).2.1).support →
      Set.range (pt₂ v ≫ i₂.1).base ⊆ ((EPkg.coOpen i₁.1 : X.Opens) : Set X) := by
    rintro a v hv _ ⟨t, rfl⟩
    obtain rfl : t = IsLocalRing.closedPoint k := Subsingleton.elim _ _
    exact off₂ a v hv

  have inv₁ : ∀ (a : ↥(GluingData.admissible S)) (v : Place k F), v ∈ ((a : GluingData k F S).1).support →
      (P₁ v).IsInvertible := by
    intro a v hv
    haveI := hSm₁
    exact RelEffCartierDiv.isInvertible_I_of_supportedIn (EPkg.coOpen i₂.1) _
      (RelEffCartierDiv.supportedIn_ofPoint _ _ _ (fun t => rg₁ a v hv ⟨t, rfl⟩))
  have inv₂ : ∀ (a : ↥(GluingData.admissible S)) (v : Place k F), v ∈ ((a : GluingData k F S).2.1).support →
      (P₂ v).IsInvertible := by
    intro a v hv
    haveI := hSm₂
    exact RelEffCartierDiv.isInvertible_I_of_supportedIn (EPkg.coOpen i₁.1) _
      (RelEffCartierDiv.supportedIn_ofPoint _ _ _ (fun t => rg₂ a v hv ⟨t, rfl⟩))
  have hTop₁ : SmoothOfRelativeDimension 1 ((⊤ : C₁.Opens).ι ≫ c₁) := by
    have : SmoothOfRelativeDimension (0 + 1) ((⊤ : C₁.Opens).ι ≫ c₁) := inferInstance
    simpa using this
  have hTop₂ : SmoothOfRelativeDimension 1 ((⊤ : C₂.Opens).ι ≫ c₂) := by
    have : SmoothOfRelativeDimension (0 + 1) ((⊤ : C₂.Opens).ι ≫ c₂) := inferInstance
    simpa using this
  have invQ₁ : ∀ v, (Q₁ v).IsInvertible := fun v => by
    haveI := hTop₁
    exact RelEffCartierDiv.isInvertible_I_of_supportedIn (⊤ : C₁.Opens) _
      (RelEffCartierDiv.supportedIn_ofPoint _ _ _ (fun _ => trivial))
  have invQ₂ : ∀ v, (Q₂ v).IsInvertible := fun v => by
    haveI := hTop₂
    exact RelEffCartierDiv.isInvertible_I_of_supportedIn (⊤ : C₂.Opens) _
      (RelEffCartierDiv.supportedIn_ofPoint _ _ _ (fun _ => trivial))

  let E : ↥(GluingData.admissible S) → (pullback x (𝟙 (Spec (CommRingCat.of k)))).Modules := fun a =>
    EPkgTwist.twist P₁ (a : GluingData k F S).1 ⊗ EPkgTwist.twist P₂ (a : GluingData k F S).2.1
  refine ⟨E, ?inv, ?mul, ?zero, ?res, ?princ, ?pin₁, ?pin₂⟩
  case inv =>
    intro a
    exact (EPkgTwist.isInvertible_twist P₁ _ (inv₁ a)).tensor (EPkgTwist.isInvertible_twist P₂ _ (inv₂ a))
  case mul =>
    intro a b
    change Nonempty (EPkgTwist.twist P₁ ((a : GluingData k F S).1 + (b : GluingData k F S).1) ⊗
        EPkgTwist.twist P₂ ((a : GluingData k F S).2.1 + (b : GluingData k F S).2.1) ≅ E a ⊗ E b)
    obtain ⟨m₁⟩ := EPkgTwist.nonempty_twist_add_iso P₁ (a : GluingData k F S).1 (b : GluingData k F S).1 (fun v hv => by
      rcases Finset.mem_union.mp hv with h | h
      exacts [inv₁ a v h, inv₁ b v h])
    obtain ⟨m₂⟩ := EPkgTwist.nonempty_twist_add_iso P₂ (a : GluingData k F S).2.1 (b : GluingData k F S).2.1 (fun v hv => by
      rcases Finset.mem_union.mp hv with h | h
      exacts [inv₂ a v h, inv₂ b v h])
    exact ⟨(m₁ ⊗ᵢ m₂) ≪≫ EPkgTwist.shuffle _ _ _ _⟩
  case zero =>
    intro a h1 h2
    exact ⟨(eqToIso (congrArg (EPkgTwist.twist P₁) h1) ⊗ᵢ eqToIso (congrArg (EPkgTwist.twist P₂) h2)) ≪≫
      (eqToIso (EPkgTwist.twist_zero P₁) ⊗ᵢ eqToIso (EPkgTwist.twist_zero P₂)) ≪≫ λ_ _⟩
  case res =>
    intro a
    haveI := hIso₁; haveI := hSm₁; haveI := hIso₂; haveI := hSm₂
    constructor
    ·
      obtain ⟨r₁⟩ := EPkgTwist.nonempty_pullback_twistL_iso (curveChange i₁.1 i₁.2 (𝟙 _)) P₁ Q₁
        (⇑(a : GluingData k F S).1) ((a : GluingData k F S).1).support.toList (fun v hv => by
          have hv' := Finset.mem_toList.mp hv
          refine ⟨inv₁ a v hv', ?_, invQ₁ v⟩
          exact (RelEffCartierDiv.comap_curveChange_ofPoint_comp_eq_and_isIso_pullbackModuleComparison_of_isIso_morphismRestrict
            x c₁ i₁.1 i₁.2 (𝟙 _) (pt₁ v) (hpt₁ v) (EPkg.coOpen i₂.1) (rg₁ a v hv')).1)
      obtain ⟨r₂⟩ := EPkgTwist.nonempty_pullback_twistL_iso (curveChange i₁.1 i₁.2 (𝟙 _)) P₂ (fun _ => ⊤)
        (⇑(a : GluingData k F S).2.1) ((a : GluingData k F S).2.1).support.toList (fun v hv => by
          have hv' := Finset.mem_toList.mp hv
          refine ⟨inv₂ a v hv', ?_, Scheme.IdealSheafData.isInvertible_top⟩
          refine (RelEffCartierDiv.comap_curveChange_ofPoint_eq_top_and_isIso_pullbackModuleComparison_of_disjoint
            x c₁ i₁.1 i₁.2 (𝟙 _) (pt₂ v ≫ i₂.1) (by rw [Category.assoc, i₂.2]; exact hpt₂ v) ?_
            (EPkg.coOpen i₁.1) (rg₂ a v hv')).1
          exact Set.disjoint_left.mpr (fun y hy hy' => (rg₂ a v hv' hy) hy'))
      obtain ⟨u₂⟩ := EPkgTwist.nonempty_twistL_iso_unit_of_forall_eq_top
        (fun _ => (⊤ : (pullback c₁ (𝟙 (Spec (CommRingCat.of k)))).IdealSheafData))
        (⇑(a : GluingData k F S).2.1) ((a : GluingData k F S).2.1).support.toList (fun _ _ => rfl)
      exact ⟨Scheme.Modules.pullbackTensorObjIso _ _ _ ≪≫ (r₁ ⊗ᵢ (r₂ ≪≫ u₂)) ≪≫ ρ_ _⟩
    ·
      obtain ⟨r₁⟩ := EPkgTwist.nonempty_pullback_twistL_iso (curveChange i₂.1 i₂.2 (𝟙 _)) P₁ (fun _ => ⊤)
        (⇑(a : GluingData k F S).1) ((a : GluingData k F S).1).support.toList (fun v hv => by
          have hv' := Finset.mem_toList.mp hv
          refine ⟨inv₁ a v hv', ?_, Scheme.IdealSheafData.isInvertible_top⟩
          refine (RelEffCartierDiv.comap_curveChange_ofPoint_eq_top_and_isIso_pullbackModuleComparison_of_disjoint
            x c₂ i₂.1 i₂.2 (𝟙 _) (pt₁ v ≫ i₁.1) (by rw [Category.assoc, i₁.2]; exact hpt₁ v) ?_
            (EPkg.coOpen i₂.1) (rg₁ a v hv')).1
          exact Set.disjoint_left.mpr (fun y hy hy' => (rg₁ a v hv' hy) hy'))
      obtain ⟨r₂⟩ := EPkgTwist.nonempty_pullback_twistL_iso (curveChange i₂.1 i₂.2 (𝟙 _)) P₂ Q₂
        (⇑(a : GluingData k F S).2.1) ((a : GluingData k F S).2.1).support.toList (fun v hv => by
          have hv' := Finset.mem_toList.mp hv
          refine ⟨inv₂ a v hv', ?_, invQ₂ v⟩
          exact (RelEffCartierDiv.comap_curveChange_ofPoint_comp_eq_and_isIso_pullbackModuleComparison_of_isIso_morphismRestrict
            x c₂ i₂.1 i₂.2 (𝟙 _) (pt₂ v) (hpt₂ v) (EPkg.coOpen i₁.1) (rg₂ a v hv')).1)
      obtain ⟨u₁⟩ := EPkgTwist.nonempty_twistL_iso_unit_of_forall_eq_top
        (fun _ => (⊤ : (pullback c₂ (𝟙 (Spec (CommRingCat.of k)))).IdealSheafData))
        (⇑(a : GluingData k F S).1) ((a : GluingData k F S).1).support.toList (fun _ _ => rfl)
      exact ⟨Scheme.Modules.pullbackTensorObjIso _ _ _ ≪≫ ((r₁ ≪≫ u₁) ⊗ᵢ r₂) ≪≫ λ_ _⟩
  case princ =>
    intro a g₁ g₂ va vb hg₁ hg₂ ha₁ ha₂ hv
    exact isNodeUnitModule_foldr_ofPoint_tensor_foldr_ofPoint_of_forall_eq_ord_of_twoGluedSmoothCurves
      x hXred c₁ c₂ i₁ i₂ hjs hcr s hs hs0 hc F hCB Mdl₁ e₁ he₁ Mdl₂ e₂ he₂ pt₁ hpt₁ hpt₁' pt₂ hpt₂ hpt₂' S nd hS
      a g₁ g₂ va vb hg₁ hg₂ ha₁ ha₂ hv
  case pin₁ =>
    intro P Q hP hQ a ha1 ha2

    set vP : Place k F := Mdl₁.pointEquivPlace ⟨P.1 ≫ e₁.inv, by rw [← he₁, Category.assoc, e₁.inv_hom_id_assoc]; exact P.2⟩ with hvP
    set vQ : Place k F := Mdl₁.pointEquivPlace ⟨Q.1 ≫ e₁.inv, by rw [← he₁, Category.assoc, e₁.inv_hom_id_assoc]; exact Q.2⟩ with hvQ
    have hptP : pt₁ vP = P.1 := by
      rw [hpt₁' vP, hvP, Equiv.symm_apply_apply, Category.assoc, e₁.inv_hom_id, Category.comp_id]
    have hptQ : pt₁ vQ = Q.1 := by
      rw [hpt₁' vQ, hvQ, Equiv.symm_apply_apply, Category.assoc, e₁.inv_hom_id, Category.comp_id]
    have hIP : P₁ vP = (RelEffCartierDiv.ofPoint x (P.1 ≫ i₁.1) (by rw [Category.assoc, i₁.2]; exact P.2)).I :=
      EPkg.ofPoint_I_congr x _ _ (by rw [hptP])
    have hIQ : P₁ vQ = (RelEffCartierDiv.ofPoint x (Q.1 ≫ i₁.1) (by rw [Category.assoc, i₁.2]; exact Q.2)).I :=
      EPkg.ofPoint_I_congr x _ _ (by rw [hptQ])
    have hinvP : (P₁ vP).IsInvertible := by
      rw [hIP]; haveI := hSm₁
      refine RelEffCartierDiv.isInvertible_I_of_supportedIn (EPkg.coOpen i₂.1) _
        (RelEffCartierDiv.supportedIn_ofPoint _ _ _ (fun t => ?_))
      obtain rfl : t = IsLocalRing.closedPoint k := Subsingleton.elim _ _
      exact hP
    have hinvQ : (P₁ vQ).IsInvertible := by
      rw [hIQ]; haveI := hSm₁
      refine RelEffCartierDiv.isInvertible_I_of_supportedIn (EPkg.coOpen i₂.1) _
        (RelEffCartierDiv.supportedIn_ofPoint _ _ _ (fun t => ?_))
      obtain rfl : t = IsLocalRing.closedPoint k := Subsingleton.elim _ _
      exact hQ
    obtain ⟨w⟩ := EPkgTwist.nonempty_twist_single_sub_single_iso P₁ vP vQ hinvP hinvQ
    exact ⟨(eqToIso (congrArg (EPkgTwist.twist P₁) ha1) ⊗ᵢ
        (eqToIso (congrArg (EPkgTwist.twist P₂) ha2) ≪≫ eqToIso (EPkgTwist.twist_zero P₂))) ≪≫ ρ_ _ ≪≫ w ≪≫
      (eqToIso (congrArg Scheme.IdealSheafData.invModule hIP) ⊗ᵢ eqToIso (congrArg Scheme.IdealSheafData.module hIQ))⟩
  case pin₂ =>
    intro P Q hP hQ a ha1 ha2
    set vP : Place k F := Mdl₂.pointEquivPlace ⟨P.1 ≫ e₂.inv, by rw [← he₂, Category.assoc, e₂.inv_hom_id_assoc]; exact P.2⟩ with hvP
    set vQ : Place k F := Mdl₂.pointEquivPlace ⟨Q.1 ≫ e₂.inv, by rw [← he₂, Category.assoc, e₂.inv_hom_id_assoc]; exact Q.2⟩ with hvQ
    have hptP : pt₂ vP = P.1 := by
      rw [hpt₂' vP, hvP, Equiv.symm_apply_apply, Category.assoc, e₂.inv_hom_id, Category.comp_id]
    have hptQ : pt₂ vQ = Q.1 := by
      rw [hpt₂' vQ, hvQ, Equiv.symm_apply_apply, Category.assoc, e₂.inv_hom_id, Category.comp_id]
    have hIP : P₂ vP = (RelEffCartierDiv.ofPoint x (P.1 ≫ i₂.1) (by rw [Category.assoc, i₂.2]; exact P.2)).I :=
      EPkg.ofPoint_I_congr x _ _ (by rw [hptP])
    have hIQ : P₂ vQ = (RelEffCartierDiv.ofPoint x (Q.1 ≫ i₂.1) (by rw [Category.assoc, i₂.2]; exact Q.2)).I :=
      EPkg.ofPoint_I_congr x _ _ (by rw [hptQ])
    have hinvP : (P₂ vP).IsInvertible := by
      rw [hIP]; haveI := hSm₂
      refine RelEffCartierDiv.isInvertible_I_of_supportedIn (EPkg.coOpen i₁.1) _
        (RelEffCartierDiv.supportedIn_ofPoint _ _ _ (fun t => ?_))
      obtain rfl : t = IsLocalRing.closedPoint k := Subsingleton.elim _ _
      exact hP
    have hinvQ : (P₂ vQ).IsInvertible := by
      rw [hIQ]; haveI := hSm₂
      refine RelEffCartierDiv.isInvertible_I_of_supportedIn (EPkg.coOpen i₁.1) _
        (RelEffCartierDiv.supportedIn_ofPoint _ _ _ (fun t => ?_))
      obtain rfl : t = IsLocalRing.closedPoint k := Subsingleton.elim _ _
      exact hQ
    obtain ⟨w⟩ := EPkgTwist.nonempty_twist_single_sub_single_iso P₂ vP vQ hinvP hinvQ
    exact ⟨((eqToIso (congrArg (EPkgTwist.twist P₁) ha1) ≪≫ eqToIso (EPkgTwist.twist_zero P₁)) ⊗ᵢ
        eqToIso (congrArg (EPkgTwist.twist P₂) ha2)) ≪≫ λ_ _ ≪≫ w ≪≫
      (eqToIso (congrArg Scheme.IdealSheafData.invModule hIP) ⊗ᵢ eqToIso (congrArg Scheme.IdealSheafData.module hIQ))⟩

end
p2m_reactivate "P2MW.S_AlgebraicGeometry_RelPicard_exists_gluedTwist_admissible_of_twoGluedSmoothCurves.EPkgTwist P2MW.S_AlgebraicGeometry_RelPicard_exists_gluedTwist_admissible_of_twoGluedSmoothCurves.EPkg"

end S_AlgebraicGeometry_RelPicard_exists_gluedTwist_admissible_of_twoGluedSmoothCurves
end P2MW
export P2MW.S_AlgebraicGeometry_RelPicard_exists_gluedTwist_admissible_of_twoGluedSmoothCurves (solution)
