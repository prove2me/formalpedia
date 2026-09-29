-- Prove2me | solution 1 for AlgebraicCurve.CurveModel.finrank_H0_sectionsOf_invModule_prod_ker_tensor_module_prod_ker_eq_ell
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:01.734404+00:00
-- url     : https://prove2.me/submissions/f79859dd-464f-5df7-8014-84dee409189a

import Mathlib
import Definitions.Def_AlgebraicCurve_CurveModel
import Definitions.Def_AlgebraicCurve_AdelicIndex
import Definitions.Def_AlgebraicGeometry_TwoChartCechSectionsOf
import Definitions.Def_AlgebraicGeometry_IdealSheafModule
import Definitions.Def_SheafOfModules_Monoidal
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicCurve_RelCartier
import Definitions.Def_AlgebraicGeometry_IdealSheafModuleMaps
import Definitions.Def_AlgebraicGeometry_ModulesPullbackMonoidal
import Theorems.Thm_AlgebraicCurve_CurveModel_exists_divisorClassMap
import Theorems.Thm_AlgebraicCurve_isCurveOver_of_ringEquiv_functionField_of_isIntegral_of_smoothOfRelativeDimension_one
import Theorems.Thm_AlgebraicGeometry_Scheme_TwoAffineOpenCover_exists_linearEquiv_sectionsOf_of_iso
import Theorems.Thm_AlgebraicGeometry_Scheme_Hom_isInvertible_ker_of_comp_eq_id
import Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_isInvertible_invModule
import Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_isInvertible_module
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_tensor
import Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_nonempty_mul_invModule_iso_tensor
import Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_nonempty_mul_module_iso_tensor
import Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_comap_mul
import Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_nonempty_pullback_invModule_iso
import Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_isIso_pullbackModuleComparison
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_CurveModel_finrank_H0_sectionsOf_invModule_prod_ker_tensor_module_prod_ker_eq_ell
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupDivisor AlgebraicCurve.Pic0.instModuleZModTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instDistribMulActionTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instSMulTorsion AlgebraicCurve.SemilinearAut.instMulActionSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instSMulCommClassZModTorsion AlgebraicCurve.SemilinearAut.instMulSemiringActionSubtypeProdRingAutMemSubgroup instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions SheafOfModules.isIso_ihomModelToIhom"
p2m_attr_erase "simp" "AlgebraicCurve.coe_cechH0Equiv_apply AlgebraicCurve.cechH1ToH1_mk AlgebraicCurve.lSpaceOn_univ AlgebraicCurve.lSpaceOn_empty AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Divisor.degree_pushforwardAlong"
p2m_attr_erase "simp" "AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.SemilinearAut.toRingAut_inv AlgebraicCurve.SemilinearAut.smul_def AlgebraicCurve.SemilinearAut.smul_single AlgebraicCurve.SemilinearAut.smul_toValuationSubring AlgebraicCurve.SemilinearAut.baseAut_inv AlgebraicCurve.SemilinearAut.baseAut_ofAlgAut AlgebraicCurve.SemilinearAut.toRingAut_ofAlgAut AlgebraicCurve.SemilinearAut.torsionRep_apply AlgebraicCurve.SemilinearAut.toRingAut_one AlgebraicCurve.SemilinearAut.deg_smul AlgebraicCurve.SemilinearAut.degree_smul AlgebraicCurve.SemilinearAut.coe_degZeroSMulHom AlgebraicCurve.SemilinearAut.baseAut_mul AlgebraicCurve.SemilinearAut.coe_smulValuationSubringEquiv_apply AlgebraicCurve.SemilinearAut.baseAut_one AlgebraicCurve.SemilinearAut.ofAlgAut_smul AlgebraicCurve.SemilinearAut.coe_torsion_smul AlgebraicCurve.SemilinearAut.toRingAut_mul AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.jqNModC_one ModularCurve.qExpand_coeff_mul ModularCurve.qExpandₐ_apply ModularCurve.jqN_one ModularCurve.qExpand_single ModularCurve.dedekindPsi_one ModularCurve.ModularPolynomialData.mk.sizeOf_spec ModularCurve.evalAtJ_X ModularCurve.ModularPolynomialData.mk.injEq ModularCurve.constantCoeff_jNum ModularCurve.constantCoeff_eisenstein4 ModularCurve.qExpand_C ModularCurve.coeff_jq_neg_one ModularCurve.constantCoeff_jNumQ ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single"
p2m_attr_erase "simp" "ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq AlgebraicGeometry.Scheme.Modules.tensorPow_zero AlgebraicGeometry.Scheme.Modules.tensorPow_succ AlgebraicGeometry.Scheme.Modules.tensorSections_zero_right AlgebraicGeometry.Scheme.Modules.map_unitSection AlgebraicGeometry.Scheme.Modules.tensorSectionsBilin_apply AlgebraicGeometry.Scheme.Modules.tensorPowSection_zero AlgebraicGeometry.Scheme.Modules.tensorSections_zero_left AlgebraicGeometry.Scheme.Modules.toUnitSection_ofUnitSection AlgebraicGeometry.Scheme.Modules.pullbackSection_def AlgebraicGeometry.Scheme.Modules.ofUnitSection_toUnitSection PresheafOfModules.InternalHom.IsSheafAux.appAt_toPresheafHom SheafOfModules.ihomSectionsEquivFamily_unit AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_apply SheafOfModules.ihomEval_unit_app AlgebraicGeometry.Scheme.Modules.ihomEval_zero_right"
p2m_attr_erase "simp" "AlgebraicGeometry.Scheme.Modules.ihomEval_zero_left AlgebraicGeometry.Scheme.Modules.homOfFamily_app_apply SheafOfModules.unit_ihomSectionsEquivFamily AlgebraicGeometry.Scheme.Modules.familyOfHom_app AlgebraicGeometry.Scheme.Modules.restrictUnitIso_hom_app_apply AlgebraicGeometry.Scheme.Modules.restrictUnitIso_inv_app_apply AlgebraicGeometry.Scheme.Modules.restrictHomOfFamily_app_apply AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_symm_apply"

set_option autoImplicit false

universe u

p2m_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry AlgebraicCurve"

namespace CurveModelBridge

theorem comap_hom_eq_map_inv {X Y : Scheme.{u}} (e : Y ≅ X) (J : X.IdealSheafData) :
    J.comap e.hom = J.map e.inv := by
  apply le_antisymm
  · rw [Scheme.IdealSheafData.le_map_iff_comap_le, ← Scheme.IdealSheafData.comap_comp, e.inv_hom_id,
      Scheme.IdealSheafData.comap_id]
  · have h : ((J.map e.inv).comap e.inv).comap e.hom ≤ J.comap e.hom :=
      Scheme.IdealSheafData.comap_mono e.hom (Scheme.IdealSheafData.comap_map_le J e.inv)
    rwa [← Scheme.IdealSheafData.comap_comp, e.hom_inv_id, Scheme.IdealSheafData.comap_id] at h

theorem ker_comap_iso {X Y T : Scheme.{u}} (e : Y ≅ X) (p : T ⟶ X) :
    p.ker.comap e.hom = (p ≫ e.inv).ker := by
  rw [comap_hom_eq_map_inv, Scheme.Hom.ker_comp]

theorem comap_prod {X Y : Scheme.{u}} (f : Y ⟶ X) {n : ℕ} (I : Fin n → X.IdealSheafData) :
    (∏ i, I i).comap f = ∏ i, (I i).comap f := by
  induction n with
  | zero =>
    simp only [Finset.univ_eq_empty, Finset.prod_empty, Scheme.IdealSheafData.one_eq_top]
    exact Scheme.IdealSheafData.comap_top f
  | succ n ih =>
    rw [Fin.prod_univ_succ, Fin.prod_univ_succ, Scheme.IdealSheafData.comap_mul, ih]

theorem isInvertible_prod {X : Scheme.{u}} {n : ℕ} (I : Fin n → X.IdealSheafData)
    (h : ∀ i, (I i).IsInvertible) : (∏ i, I i).IsInvertible := by
  induction n with
  | zero =>
    simp only [Finset.univ_eq_empty, Finset.prod_empty, Scheme.IdealSheafData.one_eq_top]
    exact Scheme.IdealSheafData.isInvertible_top
  | succ n ih =>
    rw [Fin.prod_univ_succ]
    exact (h 0).mul (ih _ fun i => h i.succ)

section model

variable {K : Type u} [Field K] [IsAlgClosed K] {F : Type u} [Field F] [Algebra K F]

abbrev Pt (M : CurveModel K F) := {p : Spec (CommRingCat.of K) ⟶ M.C // p ≫ M.toBase = 𝟙 _}

omit [IsAlgClosed K] in
theorem isInvertible_ker (M : CurveModel K F) (p : Pt M) : p.1.ker.IsInvertible :=
  Scheme.Hom.isInvertible_ker_of_comp_eq_id (p := M.toBase) p.1 p.2

theorem cl_prod_ker (M : CurveModel K F) (cl : M.C.Modules → Pic K F)
    (h_iso : ∀ L L' : M.C.Modules, Scheme.Modules.IsInvertible L → Nonempty (L ≅ L') → cl L = cl L')
    (h_tensor : ∀ L L' : M.C.Modules, Scheme.Modules.IsInvertible L → Scheme.Modules.IsInvertible L' →
      cl (L ⊗ L') = cl L + cl L')
    (h_ker : ∀ (P : Pt M) (n : ℕ),
      cl (((P.1.ker) ^ n).invModule) = QuotientAddGroup.mk (n • Finsupp.single (M.pointEquivPlace P) (1 : ℤ)) ∧
        cl (((P.1.ker) ^ n).module) = QuotientAddGroup.mk (-(n • Finsupp.single (M.pointEquivPlace P) (1 : ℤ))))
    {n : ℕ} (P : Fin n → Pt M) :
    cl ((∏ m, (P m).1.ker).invModule) =
        QuotientAddGroup.mk (∑ m, Finsupp.single (M.pointEquivPlace (P m)) (1 : ℤ)) ∧
      cl ((∏ m, (P m).1.ker).module) =
        QuotientAddGroup.mk (-(∑ m, Finsupp.single (M.pointEquivPlace (P m)) (1 : ℤ))) := by
  induction n with
  | zero =>
    simp only [Finset.univ_eq_empty, Finset.prod_empty, Finset.sum_empty, neg_zero,
      Scheme.IdealSheafData.one_eq_top, QuotientAddGroup.mk_zero]
    have htop : (⊤ : M.C.IdealSheafData).IsInvertible := Scheme.IdealSheafData.isInvertible_top
    constructor
    · have h2 : cl ((⊤ * ⊤ : M.C.IdealSheafData).invModule) =
          cl ((⊤ : M.C.IdealSheafData).invModule ⊗ (⊤ : M.C.IdealSheafData).invModule) :=
        h_iso _ _ (htop.mul htop).isInvertible_invModule
          (Scheme.IdealSheafData.IsInvertible.nonempty_mul_invModule_iso_tensor htop htop)
      rw [Scheme.IdealSheafData.top_mul,
        h_tensor _ _ htop.isInvertible_invModule htop.isInvertible_invModule] at h2
      exact (add_left_cancel ((add_zero _).trans h2)).symm
    · have h2 : cl ((⊤ * ⊤ : M.C.IdealSheafData).module) =
          cl ((⊤ : M.C.IdealSheafData).module ⊗ (⊤ : M.C.IdealSheafData).module) :=
        h_iso _ _ (htop.mul htop).isInvertible_module
          (Scheme.IdealSheafData.IsInvertible.nonempty_mul_module_iso_tensor htop htop)
      rw [Scheme.IdealSheafData.top_mul,
        h_tensor _ _ htop.isInvertible_module htop.isInvertible_module] at h2
      exact (add_left_cancel ((add_zero _).trans h2)).symm
  | succ n ih =>
    obtain ⟨ih1, ih2⟩ := ih (fun i => P i.succ)
    have h0 : (P 0).1.ker.IsInvertible := isInvertible_ker M (P 0)
    have hrest : (∏ i : Fin n, (P i.succ).1.ker).IsInvertible :=
      isInvertible_prod _ fun i => isInvertible_ker M (P i.succ)
    obtain ⟨hk1, hk2⟩ := h_ker (P 0) 1
    simp only [pow_one, one_smul] at hk1 hk2
    rw [Fin.prod_univ_succ, Fin.sum_univ_succ]
    constructor
    · rw [h_iso _ _ (h0.mul hrest).isInvertible_invModule
          (Scheme.IdealSheafData.IsInvertible.nonempty_mul_invModule_iso_tensor h0 hrest),
        h_tensor _ _ h0.isInvertible_invModule hrest.isInvertible_invModule, hk1, ih1,
        ← QuotientAddGroup.mk_add]
    · rw [h_iso _ _ (h0.mul hrest).isInvertible_module
          (Scheme.IdealSheafData.IsInvertible.nonempty_mul_module_iso_tensor h0 hrest),
        h_tensor _ _ h0.isInvertible_module hrest.isInvertible_module, hk2, ih2,
        ← QuotientAddGroup.mk_add, ← neg_add]

theorem model_case (M : CurveModel K F) {a b : ℕ} (P : Fin a → Pt M) (Q : Fin b → Pt M)
    (𝒱 : M.C.TwoAffineOpenCover) :
    Module.Finite K (𝒱.sectionsOf M.toBase ((∏ m, (P m).1.ker).invModule ⊗ (∏ j, (Q j).1.ker).module)).H0 ∧
    Module.Finite K (𝒱.sectionsOf M.toBase ((∏ m, (P m).1.ker).invModule ⊗ (∏ j, (Q j).1.ker).module)).H1 ∧
    Module.finrank K (𝒱.sectionsOf M.toBase
        ((∏ m, (P m).1.ker).invModule ⊗ (∏ j, (Q j).1.ker).module)).H0 =
      ell ((∑ m, Finsupp.single (M.pointEquivPlace (P m)) (1 : ℤ)) -
           ∑ j, Finsupp.single (M.pointEquivPlace (Q j)) (1 : ℤ)) := by
  haveI : IsCurveOver K F :=
    isCurveOver_of_ringEquiv_functionField_of_isIntegral_of_smoothOfRelativeDimension_one
      M.toBase M.ffEquiv M.ffEquiv_algebraMap
  obtain ⟨cl, h_iso, h_tensor, -, h_ker, h_coh⟩ := CurveModel.exists_divisorClassMap M
  have hIP : (∏ m, (P m).1.ker).IsInvertible := isInvertible_prod _ fun m => isInvertible_ker M (P m)
  have hIQ : (∏ j, (Q j).1.ker).IsInvertible := isInvertible_prod _ fun j => isInvertible_ker M (Q j)
  obtain ⟨hclP, -⟩ := cl_prod_ker M cl h_iso h_tensor h_ker P
  obtain ⟨-, hclQ⟩ := cl_prod_ker M cl h_iso h_tensor h_ker Q
  have hinv : Scheme.Modules.IsInvertible ((∏ m, (P m).1.ker).invModule ⊗ (∏ j, (Q j).1.ker).module) :=
    hIP.isInvertible_invModule.tensor hIQ.isInvertible_module
  have hcl : QuotientAddGroup.mk ((∑ m, Finsupp.single (M.pointEquivPlace (P m)) (1 : ℤ)) -
        ∑ j, Finsupp.single (M.pointEquivPlace (Q j)) (1 : ℤ)) =
      cl ((∏ m, (P m).1.ker).invModule ⊗ (∏ j, (Q j).1.ker).module) := by
    rw [h_tensor _ _ hIP.isInvertible_invModule hIQ.isInvertible_module, hclP, hclQ,
      ← QuotientAddGroup.mk_add, sub_eq_add_neg]
  obtain ⟨hfin0, hfin1, hrank, -⟩ := h_coh 𝒱 _ hinv _ hcl
  exact ⟨hfin0, hfin1, hrank⟩

end model

end CurveModelBridge

open CurveModelBridge in
theorem solution
    {K : Type u} [Field K] [IsAlgClosed K] {X : Scheme.{u}} (x : X ⟶ Spec (CommRingCat.of K))
    [IsIntegral X] [IsProper x] [SmoothOfRelativeDimension 1 x]
    {F : Type u} [Field F] [Algebra K F] (M : CurveModel K F) (e : M.C ≅ X) (he : e.hom ≫ x = M.toBase)
    {a b : ℕ} (P : Fin a → {p : Spec (CommRingCat.of K) ⟶ X // p ≫ x = 𝟙 _})
    (Q : Fin b → {p : Spec (CommRingCat.of K) ⟶ X // p ≫ x = 𝟙 _}) (𝒱 : X.TwoAffineOpenCover) :
    Module.Finite K (𝒱.sectionsOf x ((∏ m, (P m).1.ker).invModule ⊗ (∏ j, (Q j).1.ker).module)).H0 ∧
    Module.Finite K (𝒱.sectionsOf x ((∏ m, (P m).1.ker).invModule ⊗ (∏ j, (Q j).1.ker).module)).H1 ∧
    Module.finrank K (𝒱.sectionsOf x
        ((∏ m, (P m).1.ker).invModule ⊗ (∏ j, (Q j).1.ker).module)).H0 =
      ell ((∑ m, Finsupp.single (M.pointEquivPlace ⟨(P m).1 ≫ e.inv, by
              rw [Category.assoc, ← he, e.inv_hom_id_assoc]; exact (P m).2⟩) (1 : ℤ)) -
           ∑ j, Finsupp.single (M.pointEquivPlace ⟨(Q j).1 ≫ e.inv, by
              rw [Category.assoc, ← he, e.inv_hom_id_assoc]; exact (Q j).2⟩) (1 : ℤ)) := by

  have hP' : ∀ m, ((P m).1 ≫ e.inv) ≫ M.toBase = 𝟙 _ := fun m => by
    rw [Category.assoc, ← he, e.inv_hom_id_assoc]; exact (P m).2
  have hQ' : ∀ j, ((Q j).1 ≫ e.inv) ≫ M.toBase = 𝟙 _ := fun j => by
    rw [Category.assoc, ← he, e.inv_hom_id_assoc]; exact (Q j).2
  let P' : Fin a → Pt M := fun m => ⟨(P m).1 ≫ e.inv, hP' m⟩
  let Q' : Fin b → Pt M := fun j => ⟨(Q j).1 ≫ e.inv, hQ' j⟩

  have hIP : (∏ m, (P m).1.ker).IsInvertible :=
    isInvertible_prod _ fun m => Scheme.Hom.isInvertible_ker_of_comp_eq_id (p := x) (P m).1 (P m).2
  have hIQ : (∏ j, (Q j).1.ker).IsInvertible :=
    isInvertible_prod _ fun j => Scheme.Hom.isInvertible_ker_of_comp_eq_id (p := x) (Q j).1 (Q j).2
  have hIP' : (∏ m, (P' m).1.ker).IsInvertible := isInvertible_prod _ fun m => isInvertible_ker M (P' m)
  have hIQ' : (∏ j, (Q' j).1.ker).IsInvertible := isInvertible_prod _ fun j => isInvertible_ker M (Q' j)

  have hcP : (∏ m, (P m).1.ker).comap e.hom = ∏ m, (P' m).1.ker := by
    rw [comap_prod]; simp only [ker_comap_iso, P']
  have hcQ : (∏ j, (Q j).1.ker).comap e.hom = ∏ j, (Q' j).1.ker := by
    rw [comap_prod]; simp only [ker_comap_iso, Q']
  have hcPinv : ((∏ m, (P m).1.ker).comap e.hom).IsInvertible := by rw [hcP]; exact hIP'
  have hcQinv : ((∏ j, (Q j).1.ker).comap e.hom).IsInvertible := by rw [hcQ]; exact hIQ'

  obtain ⟨i1⟩ := Scheme.IdealSheafData.IsInvertible.nonempty_pullback_invModule_iso e.hom hIP hcPinv
  haveI := Scheme.IdealSheafData.IsInvertible.isIso_pullbackModuleComparison e.hom hIQ hcQinv
  have eN : ((∏ m, (P' m).1.ker).invModule ⊗ (∏ j, (Q' j).1.ker).module) ≅
      (Scheme.Modules.pullback e.hom).obj ((∏ m, (P m).1.ker).invModule ⊗ (∏ j, (Q j).1.ker).module) :=
    eqToIso (by rw [hcP, hcQ]) ≪≫
      (tensorIso i1.symm (asIso ((∏ j, (Q j).1.ker).pullbackModuleComparison e.hom)).symm) ≪≫
      (Scheme.Modules.pullbackTensorObjIso e.hom _ _).symm

  obtain ⟨𝒱₀, -, -, ⟨f0⟩, ⟨f1⟩⟩ :=
    Scheme.TwoAffineOpenCover.exists_linearEquiv_sectionsOf_of_iso M.toBase x e he 𝒱 _ _ eN
  obtain ⟨hfin0, hfin1, hrank⟩ := model_case M P' Q' 𝒱₀
  refine ⟨?_, ?_, ?_⟩
  · haveI := hfin0; exact Module.Finite.equiv f0
  · haveI := hfin1; exact Module.Finite.equiv f1
  · rw [← f0.finrank_eq]; exact hrank

end S_AlgebraicCurve_CurveModel_finrank_H0_sectionsOf_invModule_prod_ker_tensor_module_prod_ker_eq_ell
end P2MW
export P2MW.S_AlgebraicCurve_CurveModel_finrank_H0_sectionsOf_invModule_prod_ker_tensor_module_prod_ker_eq_ell (solution)
