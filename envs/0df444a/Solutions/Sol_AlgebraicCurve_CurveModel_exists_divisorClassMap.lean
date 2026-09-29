-- Prove2me | solution 1 for AlgebraicCurve.CurveModel.exists_divisorClassMap
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:01.734404+00:00
-- url     : https://prove2.me/submissions/d3dd504c-9240-5285-8738-2f20398b9a5b

import Mathlib
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Definitions.Def_AlgebraicCurve_AdelicIndex
import Definitions.Def_AlgebraicCurve_CurveModel
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_SheafOfModules_Monoidal
import Definitions.Def_AlgebraicGeometry_IdealSheafModule
import Definitions.Def_AlgebraicGeometry_TwoChartCechSectionsOf
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import Definitions.Def_AlgebraicCurve_PlacesOf
import Definitions.Def_AlgebraicCurve_CechSectionsOfDivisor
import Definitions.Def_AlgebraicCurve_RelCartier
import Theorems.Thm_AlgebraicCurve_exists_placeEquiv_ord_eq_and_ell_mapDomain_eq
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_divisor_range_eq_lSpaceOn
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_exists_unit_range_eq_lSpaceOn_zero
import Theorems.Thm_AlgebraicCurve_finrank_H0_H1_sectionsOf_of_range_eq_lSpaceOn
import Theorems.Thm_AlgebraicCurve_ell_add_of_forall_eq_ord
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_isPrincipal_sub_sub_of_presentations_tensor
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_isPrincipal_sub_single_of_presentation_ker_pow
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_tensor
import Theorems.Thm_AlgebraicGeometry_Scheme_Hom_isInvertible_ker_of_comp_eq_id
import Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_pow
import Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_isInvertible_module
import Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_isInvertible_invModule
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_CurveModel_exists_divisorClassMap
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupDivisor AlgebraicCurve.Pic0.instModuleZModTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instDistribMulActionTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instSMulTorsion AlgebraicCurve.SemilinearAut.instMulActionSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instSMulCommClassZModTorsion AlgebraicCurve.SemilinearAut.instMulSemiringActionSubtypeProdRingAutMemSubgroup instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions PresheafOfModules.PullbackMonoidal.pullback_monoidal PresheafOfModules.PullbackMonoidal.isIso_δ PresheafOfModules.pushforward_laxMonoidal PresheafOfModules.PullbackMonoidal.isIso_η PresheafOfModules.free_monoidal PresheafOfModules.restrictScalars_laxMonoidal PresheafOfModules.PullbackMonoidal.isIso_δ_gS PresheafOfModules.pullback_oplaxMonoidal PresheafOfModules.PullbackMonoidal.instPreservesColimitsOfSizeCompOppositeCommRingCatRingCatForget₂RingHomCarrierCarrierPb PresheafOfModules.pullback_monoidal' AlgebraicGeometry.Scheme.Modules.preservesBinaryProducts_opensMap"
p2m_attr_erase "instance" "AlgebraicGeometry.Scheme.Modules.pullback_monoidal AlgebraicGeometry.Scheme.Modules.sheafify_isLocalization' AlgebraicGeometry.Scheme.Modules.preservesTerminal_opensMap AlgebraicGeometry.Scheme.Modules.pullback₀_monoidal AlgebraicGeometry.Scheme.Modules.preservesFiniteProducts_opensMap AlgebraicGeometry.Scheme.Modules.instLiftingPresheafOfModulesSheafifyPresheafWOpensCarrierCarrierCommRingCatGrothendieckTopologyObjFunctorOppositeIsSheafSheafCompPullback₀Pullback SheafOfModules.isIso_ihomModelToIhom"
p2m_attr_erase "simp" "AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.SemilinearAut.toRingAut_inv AlgebraicCurve.SemilinearAut.smul_def"
p2m_attr_erase "simp" "AlgebraicCurve.SemilinearAut.smul_single AlgebraicCurve.SemilinearAut.smul_toValuationSubring AlgebraicCurve.SemilinearAut.baseAut_inv AlgebraicCurve.SemilinearAut.baseAut_ofAlgAut AlgebraicCurve.SemilinearAut.toRingAut_ofAlgAut AlgebraicCurve.SemilinearAut.torsionRep_apply AlgebraicCurve.SemilinearAut.toRingAut_one AlgebraicCurve.SemilinearAut.deg_smul AlgebraicCurve.SemilinearAut.degree_smul AlgebraicCurve.SemilinearAut.coe_degZeroSMulHom AlgebraicCurve.SemilinearAut.baseAut_mul AlgebraicCurve.SemilinearAut.coe_smulValuationSubringEquiv_apply AlgebraicCurve.SemilinearAut.baseAut_one AlgebraicCurve.SemilinearAut.ofAlgAut_smul AlgebraicCurve.SemilinearAut.coe_torsion_smul AlgebraicCurve.SemilinearAut.toRingAut_mul AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.jqNModC_one ModularCurve.qExpand_coeff_mul ModularCurve.qExpandₐ_apply ModularCurve.jqN_one ModularCurve.qExpand_single ModularCurve.dedekindPsi_one ModularCurve.ModularPolynomialData.mk.sizeOf_spec ModularCurve.evalAtJ_X ModularCurve.ModularPolynomialData.mk.injEq ModularCurve.constantCoeff_jNum ModularCurve.constantCoeff_eisenstein4 ModularCurve.qExpand_C ModularCurve.coeff_jq_neg_one ModularCurve.constantCoeff_jNumQ ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen"
p2m_attr_erase "simp" "ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq AlgebraicGeometry.Scheme.Modules.tensorPow_zero AlgebraicGeometry.Scheme.Modules.tensorPow_succ AlgebraicGeometry.Scheme.Modules.tensorSections_zero_right AlgebraicGeometry.Scheme.Modules.map_unitSection AlgebraicGeometry.Scheme.Modules.tensorSectionsBilin_apply AlgebraicGeometry.Scheme.Modules.tensorPowSection_zero AlgebraicGeometry.Scheme.Modules.tensorSections_zero_left PresheafOfModules.freeεIso_hom_app PresheafOfModules.freeμIso_hom_app AlgebraicGeometry.Scheme.Modules.toUnitSection_ofUnitSection AlgebraicGeometry.Scheme.Modules.pullbackSection_def AlgebraicGeometry.Scheme.Modules.ofUnitSection_toUnitSection PresheafOfModules.InternalHom.IsSheafAux.appAt_toPresheafHom SheafOfModules.ihomSectionsEquivFamily_unit AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_apply SheafOfModules.ihomEval_unit_app AlgebraicGeometry.Scheme.Modules.ihomEval_zero_right AlgebraicGeometry.Scheme.Modules.ihomEval_zero_left AlgebraicGeometry.Scheme.Modules.homOfFamily_app_apply"
p2m_attr_erase "simp" "SheafOfModules.unit_ihomSectionsEquivFamily AlgebraicGeometry.Scheme.Modules.familyOfHom_app AlgebraicGeometry.Scheme.Modules.restrictUnitIso_hom_app_apply AlgebraicGeometry.Scheme.Modules.restrictUnitIso_inv_app_apply AlgebraicGeometry.Scheme.Modules.restrictHomOfFamily_app_apply AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_symm_apply"

set_option autoImplicit false

universe u v

p2m_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry AlgebraicCurve"

noncomputable section

namespace DivisorClassMapGlue

set_option maxHeartbeats 6400000 in
set_option synthInstance.maxHeartbeats 1600000 in
theorem isInvertible_of_iso {X : Scheme.{u}} {L L' : X.Modules} (e : L ≅ L')
    (h : Scheme.Modules.IsInvertible L) : Scheme.Modules.IsInvertible L' := by
  refine ⟨fun y => ?_⟩
  obtain ⟨U, hy, ⟨t⟩⟩ := h.1 y
  exact ⟨U, hy, ⟨(Scheme.Modules.pullback U.ι).mapIso e.symm ≪≫ t⟩⟩

section Presentation

variable {K : Type u} [Field K] {X : Scheme.{u}} (x : X ⟶ Spec (CommRingCat.of K)) [IsIntegral X]

structure IsPresentation (L : X.Modules)
    (D : letI := (baseToFunctionField x).toAlgebra
      Divisor K X.functionField)
    (φ : ∀ U : X.Opens, Γ(L, U) →+ (X.functionField : Type u)) : Prop where
  nat : ∀ (U V : X.Opens) (h : V ≤ U), Nonempty V →
    ∀ m : Γ(L, U), φ V (L.presheaf.map (homOfLE h).op m) = φ U m
  smul : ∀ (U : X.Opens) [Nonempty U] (a : Γ(X, U)) (m : Γ(L, U)),
    φ U (a • m) = algebraMap Γ(X, U) X.functionField a * φ U m
  inj : ∀ U : X.Opens, Nonempty U → Function.Injective (φ U)
  range : letI := (baseToFunctionField x).toAlgebra
    ∀ U : X.Opens, IsAffineOpen U → Nonempty U →
      Set.range (φ U) = (lSpaceOn (placesOf x U) D : Set X.functionField)

variable {x}

set_option maxHeartbeats 6400000 in
set_option synthInstance.maxHeartbeats 1600000 in
omit [IsIntegral X] in

theorem app_map_of_hom {L L' : X.Modules} (f : L ⟶ L') {U V : X.Opens} (i : V ≤ U) (m : Γ(L, U)) :
    (Scheme.Modules.Hom.app f V) (L.presheaf.map (homOfLE i).op m) =
      L'.presheaf.map (homOfLE i).op ((Scheme.Modules.Hom.app f U) m) := by
  have hn := (Scheme.Modules.Hom.mapPresheaf f).naturality (homOfLE i).op
  have hm := ConcreteCategory.congr_hom hn m
  simpa only [Scheme.Modules.mapPresheaf_app, ConcreteCategory.comp_apply] using hm

set_option maxHeartbeats 6400000 in
set_option synthInstance.maxHeartbeats 1600000 in

theorem IsPresentation.of_iso {L L' : X.Modules} (e : L ≅ L')
    {D : letI := (baseToFunctionField x).toAlgebra
      Divisor K X.functionField}
    {φ' : ∀ U : X.Opens, Γ(L', U) →+ (X.functionField : Type u)} (h : IsPresentation x L' D φ') :
    IsPresentation x L D (fun U => (φ' U).comp (Scheme.Modules.Hom.app e.hom U).hom) := by
  refine ⟨fun U V hVU hV m => ?_, fun U _ a m => ?_, fun U hU => ?_, fun U hU hne => ?_⟩
  · show φ' V ((Scheme.Modules.Hom.app e.hom V) (L.presheaf.map (homOfLE hVU).op m)) =
      φ' U ((Scheme.Modules.Hom.app e.hom U) m)
    rw [app_map_of_hom e.hom hVU m]
    exact h.nat U V hVU hV _
  · show φ' U ((Scheme.Modules.Hom.app e.hom U) (a • m)) =
      algebraMap Γ(X, U) X.functionField a * φ' U ((Scheme.Modules.Hom.app e.hom U) m)
    rw [Scheme.Modules.Hom.app_smul]
    exact h.smul U a _
  · exact (h.inj U hU).comp (ConcreteCategory.bijective_of_isIso (Scheme.Modules.Hom.app e.hom U)).1
  · letI := (baseToFunctionField x).toAlgebra
    have hs : Function.Surjective (Scheme.Modules.Hom.app e.hom U) :=
      (ConcreteCategory.bijective_of_isIso (Scheme.Modules.Hom.app e.hom U)).2
    show Set.range (φ' U ∘ (Scheme.Modules.Hom.app e.hom U)) = _
    rw [hs.range_comp]
    exact h.range U hU hne

variable (x)

set_option maxHeartbeats 6400000 in
set_option synthInstance.maxHeartbeats 1600000 in

theorem exists_isPresentation [IsSeparated x] [QuasiCompact x] [SmoothOfRelativeDimension 1 x]
    {L : X.Modules} (hL : Scheme.Modules.IsInvertible L) :
    letI := (baseToFunctionField x).toAlgebra
    ∃ (D : Divisor K X.functionField) (φ : ∀ U : X.Opens, Γ(L, U) →+ (X.functionField : Type u)),
      IsPresentation x L D φ := by
  obtain ⟨D, φ, hnat, hsmul, hinj, hrange, -⟩ :=
    Scheme.Modules.IsInvertible.exists_divisor_range_eq_lSpaceOn x L hL
  exact ⟨D, φ, ⟨hnat, hsmul, hinj, hrange⟩⟩

set_option maxHeartbeats 6400000 in
set_option synthInstance.maxHeartbeats 1600000 in

theorem exists_isPresentation_unit [SmoothOfRelativeDimension 1 x] :
    letI := (baseToFunctionField x).toAlgebra
    ∃ φ : ∀ U : X.Opens, Γ((𝟙_ X.Modules : X.Modules), U) →+ (X.functionField : Type u),
      IsPresentation x (𝟙_ X.Modules) 0 φ := by
  obtain ⟨φ, -, hnat, hsmul, hinj, hrange⟩ := Scheme.Modules.exists_unit_range_eq_lSpaceOn_zero x
  exact ⟨φ, ⟨hnat, hsmul, hinj, hrange⟩⟩

variable [IsAlgClosed K] [IsProper x] [SmoothOfRelativeDimension 1 x]

set_option maxHeartbeats 6400000 in
set_option synthInstance.maxHeartbeats 1600000 in

theorem IsPresentation.isPrincipal_tensor {L L' : X.Modules}
    (hL : Scheme.Modules.IsInvertible L) (hL' : Scheme.Modules.IsInvertible L')
    {D D' D'' : letI := (baseToFunctionField x).toAlgebra
      Divisor K X.functionField}
    {φ : ∀ U : X.Opens, Γ(L, U) →+ (X.functionField : Type u)}
    {φ' : ∀ U : X.Opens, Γ(L', U) →+ (X.functionField : Type u)}
    {φ'' : ∀ U : X.Opens, Γ(L ⊗ L', U) →+ (X.functionField : Type u)}
    (h : IsPresentation x L D φ) (h' : IsPresentation x L' D' φ') (h'' : IsPresentation x (L ⊗ L') D'' φ'') :
    letI := (baseToFunctionField x).toAlgebra
    Divisor.IsPrincipal (D'' - D - D') :=
  Scheme.Modules.isPrincipal_sub_sub_of_presentations_tensor x L L' hL hL' D D' D''
    φ h.nat h.smul h.inj h.range φ' h'.nat h'.smul h'.inj h'.range φ'' h''.nat h''.smul h''.inj h''.range

set_option maxHeartbeats 6400000 in
set_option synthInstance.maxHeartbeats 1600000 in

theorem IsPresentation.isPrincipal_sub_of_iso {L L' : X.Modules} (e : L ≅ L')
    (hL : Scheme.Modules.IsInvertible L)
    {D D' : letI := (baseToFunctionField x).toAlgebra
      Divisor K X.functionField}
    {φ : ∀ U : X.Opens, Γ(L, U) →+ (X.functionField : Type u)}
    {φ' : ∀ U : X.Opens, Γ(L', U) →+ (X.functionField : Type u)}
    (h : IsPresentation x L D φ) (h' : IsPresentation x L' D' φ') :
    letI := (baseToFunctionField x).toAlgebra
    Divisor.IsPrincipal (D - D') := by
  letI := (baseToFunctionField x).toAlgebra
  obtain ⟨φ₀, h₀⟩ := exists_isPresentation_unit x
  have hL' : Scheme.Modules.IsInvertible L' := isInvertible_of_iso e hL
  have key := IsPresentation.isPrincipal_tensor x hL' (Scheme.Modules.isInvertible_unit X) h' h₀
    (h.of_iso ((ρ_ L') ≪≫ e.symm))
  simpa only [sub_zero] using key

set_option maxHeartbeats 6400000 in
set_option synthInstance.maxHeartbeats 1600000 in

theorem IsPresentation.isPrincipal_of_unit
    {D : letI := (baseToFunctionField x).toAlgebra
      Divisor K X.functionField}
    {φ : ∀ U : X.Opens, Γ((𝟙_ X.Modules : X.Modules), U) →+ (X.functionField : Type u)}
    (h : IsPresentation x (𝟙_ X.Modules) D φ) :
    letI := (baseToFunctionField x).toAlgebra
    Divisor.IsPrincipal D := by
  letI := (baseToFunctionField x).toAlgebra
  obtain ⟨φ₀, h₀⟩ := exists_isPresentation_unit x
  have h1 : Scheme.Modules.IsInvertible (𝟙_ X.Modules) := Scheme.Modules.isInvertible_unit X
  have key := IsPresentation.isPrincipal_tensor x h1 h1 h h₀ (h₀.of_iso (λ_ (𝟙_ X.Modules)))
  have key' : Divisor.IsPrincipal (-D) := by simpa only [zero_sub, sub_zero] using key
  have h__af := (Divisor.principal (K := K) (F := X.functionField)).neg_mem key'
  simp only [neg_neg] at h__af
  exact h__af

set_option maxHeartbeats 6400000 in
set_option synthInstance.maxHeartbeats 1600000 in

theorem IsPresentation.isPrincipal_ker_pow (P : Spec (CommRingCat.of K) ⟶ X) (hP : P ≫ x = 𝟙 _) (n : ℕ)
    (w : letI := (baseToFunctionField x).toAlgebra
      Place K X.functionField)
    (hw : letI := (baseToFunctionField x).toAlgebra
      (algebraMap (X.presheaf.stalk (P.base (IsLocalRing.closedPoint K))) X.functionField).range =
        w.toValuationSubring.toSubring)
    {D D' : letI := (baseToFunctionField x).toAlgebra
      Divisor K X.functionField}
    {φ : ∀ U : X.Opens, Γ((P.ker ^ n).invModule, U) →+ (X.functionField : Type u)}
    {φ' : ∀ U : X.Opens, Γ((P.ker ^ n).module, U) →+ (X.functionField : Type u)}
    (h : IsPresentation x ((P.ker ^ n).invModule) D φ) (h' : IsPresentation x ((P.ker ^ n).module) D' φ') :
    letI := (baseToFunctionField x).toAlgebra
    Divisor.IsPrincipal (D - n • Finsupp.single w 1) ∧ Divisor.IsPrincipal (D' + n • Finsupp.single w 1) :=
  Scheme.Modules.isPrincipal_sub_single_of_presentation_ker_pow x P hP n w hw D D'
    φ h.nat h.smul h.inj h.range φ' h'.nat h'.smul h'.inj h'.range

set_option maxHeartbeats 6400000 in
set_option synthInstance.maxHeartbeats 1600000 in

theorem IsPresentation.numerics (𝒱 : X.TwoAffineOpenCover) {L : X.Modules}
    {D : letI := (baseToFunctionField x).toAlgebra
      Divisor K X.functionField}
    {φ : ∀ U : X.Opens, Γ(L, U) →+ (X.functionField : Type u)} (h : IsPresentation x L D φ) :
    letI := (baseToFunctionField x).toAlgebra
    Module.Finite K (𝒱.sectionsOf x L).H0 ∧ Module.Finite K (𝒱.sectionsOf x L).H1 ∧
      Module.finrank K (𝒱.sectionsOf x L).H0 = ell D ∧
      (Module.finrank K (𝒱.sectionsOf x L).H0 : ℤ) - Module.finrank K (𝒱.sectionsOf x L).H1
        = Divisor.degree D + 1 - genusFF K X.functionField := by
  obtain ⟨h0, h1, h2, -, h4⟩ :=
    AlgebraicCurve.finrank_H0_H1_sectionsOf_of_range_eq_lSpaceOn 𝒱 x L D φ h.nat h.smul h.inj h.range
  exact ⟨h0, h1, h2, h4⟩

end Presentation

section Transport

variable {K : Type u} [Field K] {F : Type v} [Field F] [Algebra K F] {F' : Type u} [Field F'] [Algebra K F']

set_option maxHeartbeats 6400000 in
set_option synthInstance.maxHeartbeats 1600000 in
theorem mapDomain_mapDomain_symm (π : Place K F ≃ Place K F') (E : Divisor K F') :
    Finsupp.mapDomain π (Finsupp.mapDomain π.symm E) = E := by
  rw [← Finsupp.mapDomain_comp, Equiv.self_comp_symm, Finsupp.mapDomain_id]

set_option maxHeartbeats 6400000 in
set_option synthInstance.maxHeartbeats 1600000 in

theorem isPrincipal_mapDomain_symm (π : Place K F ≃ Place K F')
    (hπ : ∀ D : Divisor K F, Divisor.IsPrincipal (Finsupp.mapDomain π D) ↔ Divisor.IsPrincipal D)
    {E : Divisor K F'} (hE : Divisor.IsPrincipal E) : Divisor.IsPrincipal (Finsupp.mapDomain π.symm E) := by
  rw [← hπ, mapDomain_mapDomain_symm]
  exact hE

set_option maxHeartbeats 6400000 in
set_option synthInstance.maxHeartbeats 1600000 in
theorem mapDomain_nsmul_single (π : Place K F ≃ Place K F') (w : Place K F') (n : ℕ) :
    Finsupp.mapDomain π.symm (n • Finsupp.single w (1 : ℤ)) = n • Finsupp.single (π.symm w) (1 : ℤ) := by
  rw [← Finsupp.mapDomain.addMonoidHom_apply, map_nsmul, Finsupp.mapDomain.addMonoidHom_apply,
    Finsupp.mapDomain_single]

set_option maxHeartbeats 6400000 in
set_option synthInstance.maxHeartbeats 1600000 in

theorem degree_eq_zero_of_isPrincipal [HasPrincipalDivisors K F] {P : Divisor K F}
    (hP : Divisor.IsPrincipal P) : Divisor.degree P = 0 := by
  obtain ⟨f, hf, hPf⟩ := hP
  obtain ⟨D₀, hD₀, hdeg⟩ := HasPrincipalDivisors.exists_divisor (K := K) f hf
  have : P = D₀ := Finsupp.ext fun w => (hPf w).trans (hD₀ w).symm
  rw [this, hdeg]

end Transport

end DivisorClassMapGlue

open DivisorClassMapGlue

set_option maxHeartbeats 6400000 in
set_option synthInstance.maxHeartbeats 1600000 in

theorem solution
    {k : Type u} [Field k] [IsAlgClosed k] {F : Type v} [Field F] [Algebra k F] [IsCurveOver k F] (M : CurveModel k F) :
    ∃ cl : M.C.Modules → Pic k F,
      (∀ L L' : M.C.Modules, Scheme.Modules.IsInvertible L → Nonempty (L ≅ L') → cl L = cl L') ∧
      (∀ L L' : M.C.Modules, Scheme.Modules.IsInvertible L → Scheme.Modules.IsInvertible L' →
        cl (L ⊗ L') = cl L + cl L') ∧
      cl (𝟙_ M.C.Modules) = 0 ∧
      (∀ (P : {p : Spec (CommRingCat.of k) ⟶ M.C // p ≫ M.toBase = 𝟙 _}) (n : ℕ),
        cl (((P.1.ker) ^ n).invModule) =
            QuotientAddGroup.mk (n • Finsupp.single (M.pointEquivPlace P) (1 : ℤ)) ∧
          cl (((P.1.ker) ^ n).module) =
            QuotientAddGroup.mk (-(n • Finsupp.single (M.pointEquivPlace P) (1 : ℤ)))) ∧
      (∀ (𝒱 : M.C.TwoAffineOpenCover) (L : M.C.Modules), Scheme.Modules.IsInvertible L →
        ∀ D : Divisor k F, QuotientAddGroup.mk D = cl L →
          Module.Finite k (𝒱.sectionsOf M.toBase L).H0 ∧ Module.Finite k (𝒱.sectionsOf M.toBase L).H1 ∧
          Module.finrank k (𝒱.sectionsOf M.toBase L).H0 = ell D ∧
          ((Module.finrank k (𝒱.sectionsOf M.toBase L).H0 : ℤ) - Module.finrank k (𝒱.sectionsOf M.toBase L).H1) -
            ((Module.finrank k (𝒱.sectionsOf M.toBase (𝟙_ M.C.Modules)).H0 : ℤ) -
              Module.finrank k (𝒱.sectionsOf M.toBase (𝟙_ M.C.Modules)).H1) = Divisor.degree D) := by
  classical
  letI := M.functionFieldAlgebra

  obtain ⟨π, hπ1, -, -, hπ4, hπ5, hπ6⟩ :=
    AlgebraicCurve.exists_placeEquiv_ord_eq_and_ell_mapDomain_eq M.ffAlgEquiv

  have hex : ∀ L : M.C.Modules, Scheme.Modules.IsInvertible L →
      ∃ (D : Divisor k M.C.functionField) (φ : ∀ U : M.C.Opens, Γ(L, U) →+ (M.C.functionField : Type u)),
        IsPresentation M.toBase L D φ := fun L hL => exists_isPresentation M.toBase hL
  choose Dp φp hp using hex

  obtain ⟨φ₀, h₀⟩ := exists_isPresentation_unit M.toBase

  let cl : M.C.Modules → Pic k F := fun L =>
    if hL : Scheme.Modules.IsInvertible L then QuotientAddGroup.mk (Finsupp.mapDomain π.symm (Dp L hL)) else 0
  have hcl : ∀ (L : M.C.Modules) (hL : Scheme.Modules.IsInvertible L),
      cl L = QuotientAddGroup.mk (Finsupp.mapDomain π.symm (Dp L hL)) := fun L hL => dif_pos hL
  have htr : ∀ {E : Divisor k M.C.functionField}, Divisor.IsPrincipal E →
      Finsupp.mapDomain π.symm E ∈ Divisor.principal (K := k) (F := F) :=
    fun hE => isPrincipal_mapDomain_symm π hπ6 hE
  refine ⟨cl, ?_, ?_, ?_, ?_, ?_⟩
  ·
    rintro L L' hL ⟨e⟩
    have hL' : Scheme.Modules.IsInvertible L' := isInvertible_of_iso e hL
    rw [hcl L hL, hcl L' hL', QuotientAddGroup.eq_iff_sub_mem, ← Finsupp.mapDomain_sub]
    exact htr (IsPresentation.isPrincipal_sub_of_iso M.toBase e hL (hp L hL) (hp L' hL'))
  ·
    intro L L' hL hL'
    have hLL' : Scheme.Modules.IsInvertible (L ⊗ L') := hL.tensor hL'
    rw [hcl L hL, hcl L' hL', hcl (L ⊗ L') hLL', ← QuotientAddGroup.mk_add, QuotientAddGroup.eq_iff_sub_mem,
      ← Finsupp.mapDomain_add, ← Finsupp.mapDomain_sub, ← sub_sub]
    exact htr (IsPresentation.isPrincipal_tensor M.toBase hL hL' (hp L hL) (hp L' hL') (hp (L ⊗ L') hLL'))
  ·
    have h1 : Scheme.Modules.IsInvertible (𝟙_ M.C.Modules) := Scheme.Modules.isInvertible_unit M.C
    rw [hcl _ h1, QuotientAddGroup.eq_zero_iff]
    exact htr (IsPresentation.isPrincipal_of_unit M.toBase (hp _ h1))
  ·
    intro P n
    have hI : P.1.ker.IsInvertible := Scheme.Hom.isInvertible_ker_of_comp_eq_id (p := M.toBase) P.1 P.2
    have hIn : (P.1.ker ^ n).IsInvertible := hI.pow n
    have hinv : Scheme.Modules.IsInvertible (P.1.ker ^ n).invModule := hIn.isInvertible_invModule
    have hmod : Scheme.Modules.IsInvertible (P.1.ker ^ n).module := hIn.isInvertible_module

    have hw : (algebraMap (M.C.presheaf.stalk (P.1.base (IsLocalRing.closedPoint k))) M.C.functionField).range =
        (π (M.pointEquivPlace P)).toValuationSubring.toSubring := by
      apply SetLike.coe_injective
      have e1 := hπ1 (M.pointEquivPlace P)
      have e2 := M.range_stalk_eq (pointEquivClosedPoint M.toBase P)
      rw [M.pointEquivPlace_apply]
      have e3 : ((M.placeOfPoint (pointEquivClosedPoint M.toBase P)).toValuationSubring : Set F) =
          M.ffEquiv.symm '' Set.range (algebraMap (M.C.presheaf.stalk (P.1.base (IsLocalRing.closedPoint k)))
            M.C.functionField) := by
        rw [← pointEquivClosedPoint_apply_coe, ← Set.range_comp]
        have := congrArg (fun S : Subring F => (S : Set F)) e2
        have h__af := this.symm
        simp only [RingHom.coe_range] at h__af
        exact h__af
      show Set.range _ =
        ((π (M.placeOfPoint (pointEquivClosedPoint M.toBase P))).toValuationSubring : Set M.C.functionField)
      rw [hπ1, e3, Set.image_image]
      ext y
      simp [M.ffAlgEquiv_apply]
    obtain ⟨hA, hB⟩ := IsPresentation.isPrincipal_ker_pow M.toBase P.1 P.2 n (π (M.pointEquivPlace P)) hw
      (hp _ hinv) (hp _ hmod)
    refine ⟨?_, ?_⟩
    · rw [hcl _ hinv, QuotientAddGroup.eq_iff_sub_mem, ← Equiv.symm_apply_apply π (M.pointEquivPlace P),
        ← mapDomain_nsmul_single, ← Finsupp.mapDomain_sub]
      exact htr hA
    · rw [hcl _ hmod, QuotientAddGroup.eq_iff_sub_mem, ← Equiv.symm_apply_apply π (M.pointEquivPlace P),
        ← mapDomain_nsmul_single, sub_neg_eq_add, ← Finsupp.mapDomain_add]
      exact htr hB
  ·
    intro 𝒱 L hL D hD
    obtain ⟨f0, f1, hH0, hχ⟩ := (hp L hL).numerics M.toBase 𝒱
    obtain ⟨-, -, -, hχ1⟩ := h₀.numerics M.toBase 𝒱
    rw [hcl L hL, QuotientAddGroup.eq_iff_sub_mem] at hD
    obtain ⟨g, hg, hPg⟩ := hD

    have hDeq : D = Finsupp.mapDomain π.symm (Dp L hL) + (D - Finsupp.mapDomain π.symm (Dp L hL)) := by abel
    have hell : ell D = ell (Dp L hL) := by
      rw [hDeq, AlgebraicCurve.ell_add_of_forall_eq_ord _ hg hPg, ← hπ4, mapDomain_mapDomain_symm]
    have hdeg : Divisor.degree D = Divisor.degree (Dp L hL) := by
      rw [hDeq, map_add, degree_eq_zero_of_isPrincipal ⟨g, hg, hPg⟩, add_zero, ← hπ5, mapDomain_mapDomain_symm]
    refine ⟨f0, f1, hH0.trans hell.symm, ?_⟩
    rw [hχ, hχ1, hdeg, map_zero]
    ring

#print axioms solution

end
end S_AlgebraicCurve_CurveModel_exists_divisorClassMap
end P2MW
export P2MW.S_AlgebraicCurve_CurveModel_exists_divisorClassMap (solution)
