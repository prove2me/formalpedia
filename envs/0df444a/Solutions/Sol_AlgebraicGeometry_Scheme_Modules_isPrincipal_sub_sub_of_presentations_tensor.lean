-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.Modules.isPrincipal_sub_sub_of_presentations_tensor
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.122355+00:00
-- url     : https://prove2.me/submissions/7fc0dfd8-d623-56fa-9b55-cf674c6d8167

import Mathlib
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Definitions.Def_AlgebraicCurve_CurveModel
import Definitions.Def_AlgebraicCurve_PlacesOf
import Definitions.Def_AlgebraicCurve_CechSectionsOfDivisor
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_SheafOfModules_Monoidal
import Definitions.Def_AlgebraicGeometry_IdealSheafModule
import Definitions.Def_AlgebraicGeometry_ModulesTensorPow
import Definitions.Def_AlgebraicGeometry_ModulesSectionsTensor
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_divisor_range_eq_lSpaceOn
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_exists_eq_mul_and_eq_add_ord_of_presentations
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_isFrameOn
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsFrameOn_tensorSections
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_tensor
import Theorems.Thm_AlgebraicCurve_exists_closedPoint_range_stalk_eq
import Theorems.Thm_P2M_Dup_AlgebraicCurve_Place_mem_iff_adicValuation_le_one
import Theorems.Thm_AlgebraicCurve_range_algebraMap_functionField_eq_iInf_of_isAffineOpen
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Scheme_Modules_isPrincipal_sub_sub_of_presentations_tensor
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupDivisor AlgebraicCurve.Pic0.instModuleZModTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instDistribMulActionTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instSMulTorsion AlgebraicCurve.SemilinearAut.instMulActionSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instSMulCommClassZModTorsion AlgebraicCurve.SemilinearAut.instMulSemiringActionSubtypeProdRingAutMemSubgroup instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions PresheafOfModules.PullbackMonoidal.pullback_monoidal PresheafOfModules.PullbackMonoidal.isIso_δ PresheafOfModules.pushforward_laxMonoidal PresheafOfModules.PullbackMonoidal.isIso_η PresheafOfModules.free_monoidal PresheafOfModules.restrictScalars_laxMonoidal PresheafOfModules.PullbackMonoidal.isIso_δ_gS"
p2m_attr_erase "instance" "PresheafOfModules.pullback_oplaxMonoidal PresheafOfModules.PullbackMonoidal.instPreservesColimitsOfSizeCompOppositeCommRingCatRingCatForget₂RingHomCarrierCarrierPb PresheafOfModules.pullback_monoidal' AlgebraicGeometry.Scheme.Modules.preservesBinaryProducts_opensMap AlgebraicGeometry.Scheme.Modules.pullback_monoidal AlgebraicGeometry.Scheme.Modules.sheafify_isLocalization' AlgebraicGeometry.Scheme.Modules.preservesTerminal_opensMap AlgebraicGeometry.Scheme.Modules.pullback₀_monoidal AlgebraicGeometry.Scheme.Modules.preservesFiniteProducts_opensMap AlgebraicGeometry.Scheme.Modules.instLiftingPresheafOfModulesSheafifyPresheafWOpensCarrierCarrierCommRingCatGrothendieckTopologyObjFunctorOppositeIsSheafSheafCompPullback₀Pullback"
p2m_attr_erase "simp" "AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence"
p2m_attr_erase "simp" "AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.SemilinearAut.toRingAut_inv AlgebraicCurve.SemilinearAut.smul_def AlgebraicCurve.SemilinearAut.smul_single AlgebraicCurve.SemilinearAut.smul_toValuationSubring AlgebraicCurve.SemilinearAut.baseAut_inv AlgebraicCurve.SemilinearAut.baseAut_ofAlgAut AlgebraicCurve.SemilinearAut.toRingAut_ofAlgAut AlgebraicCurve.SemilinearAut.torsionRep_apply AlgebraicCurve.SemilinearAut.toRingAut_one AlgebraicCurve.SemilinearAut.deg_smul AlgebraicCurve.SemilinearAut.degree_smul AlgebraicCurve.SemilinearAut.coe_degZeroSMulHom AlgebraicCurve.SemilinearAut.baseAut_mul AlgebraicCurve.SemilinearAut.coe_smulValuationSubringEquiv_apply AlgebraicCurve.SemilinearAut.baseAut_one AlgebraicCurve.SemilinearAut.ofAlgAut_smul AlgebraicCurve.SemilinearAut.coe_torsion_smul AlgebraicCurve.SemilinearAut.toRingAut_mul AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.jqNModC_one ModularCurve.qExpand_coeff_mul ModularCurve.qExpandₐ_apply ModularCurve.jqN_one ModularCurve.qExpand_single ModularCurve.dedekindPsi_one ModularCurve.ModularPolynomialData.mk.sizeOf_spec ModularCurve.evalAtJ_X ModularCurve.ModularPolynomialData.mk.injEq ModularCurve.constantCoeff_jNum ModularCurve.constantCoeff_eisenstein4 ModularCurve.qExpand_C ModularCurve.coeff_jq_neg_one ModularCurve.constantCoeff_jNumQ ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X"
p2m_attr_erase "simp" "ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq PresheafOfModules.freeεIso_hom_app PresheafOfModules.freeμIso_hom_app"

set_option autoImplicit false

universe u

p2m_open "CategoryTheory AlgebraicGeometry P2MW.S_AlgebraicGeometry_Scheme_Modules_isPrincipal_sub_sub_of_presentations_tensor.AlgebraicGeometry Opposite TopologicalSpace"

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "Scheme.germToFunctionField SmoothOfRelativeDimension IsProper Scheme.Hom Scheme.germToFunctionField_injective Scheme.Opens.ι_appIso Scheme.Hom.image_preimage_eq_opensRange_inf Spec IsIntegral Scheme Scheme.Hom.appIso Scheme.Hom.preimage_mono IsAffineOpen Scheme.Modules Scheme.Opens Scheme.Hom.image_mono Scheme.Hom.opensFunctor Scheme.Opens.opensRange_ι Scheme.Modules.IsInvertible Scheme.Modules.IsInvertible.exists_divisor_range_eq_lSpaceOn Scheme.Modules.exists_eq_mul_and_eq_add_ord_of_presentations"
namespace Scheme
p2m_export "AlgebraicGeometry.Scheme" "germToFunctionField ringCatSheaf Hom.id_app Hom germToFunctionField_injective Γ Opens.ι_appIso Hom.image_preimage_eq_opensRange_inf Hom.appIso functionField Hom.preimage_mono Hom.comp_app isBasis_affineOpens Modules Opens Hom.image_mono Hom.opensFunctor Opens.opensRange_ι restrict Modules.IsInvertible Modules.IsInvertible.exists_divisor_range_eq_lSpaceOn Modules.exists_eq_mul_and_eq_add_ord_of_presentations"
namespace Modules
p2m_export "AlgebraicGeometry.Scheme.Modules" "Hom.app_smul presheaf Hom.comp_app Hom mapPresheaf_app Hom.id_app restrict_map restrict map_smul IsInvertible tensor tensorSections tensorSections_smul_left tensorSections_smul_right map_homOfLE_tensorSections IsFrameOn IsInvertible.exists_divisor_range_eq_lSpaceOn exists_eq_mul_and_eq_add_ord_of_presentations"
namespace RatSec
p2m_open "AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme AlgebraicGeometry"

variable {X : Scheme.{u}} (M : X.Modules)

noncomputable abbrev rM {V W : X.Opens} (h : V ≤ W) : Γ(M, W) → Γ(M, V) := fun y => M.presheaf.map (homOfLE h).op y

noncomputable abbrev rO {V W : X.Opens} (h : V ≤ W) : Γ(X, W) → Γ(X, V) := fun g => X.presheaf.map (homOfLE h).op g

theorem rM_rM {V₁ V₂ V₃ : X.Opens} (h₂₁ : V₂ ≤ V₁) (h₃₂ : V₃ ≤ V₂) (y : Γ(M, V₁)) :
    rM M h₃₂ (rM M h₂₁ y) = rM M (h₃₂.trans h₂₁) y := by
  show (M.presheaf.map (homOfLE h₂₁).op ≫ M.presheaf.map (homOfLE h₃₂).op) y = _
  rw [← Functor.map_comp]; rfl

omit M in
theorem rO_rO {V₁ V₂ V₃ : X.Opens} (h₂₁ : V₂ ≤ V₁) (h₃₂ : V₃ ≤ V₂) (g : Γ(X, V₁)) :
    rO h₃₂ (rO h₂₁ g) = rO (h₃₂.trans h₂₁) g := by
  show (X.presheaf.map (homOfLE h₂₁).op ≫ X.presheaf.map (homOfLE h₃₂).op).hom g = _
  rw [← Functor.map_comp]; rfl

theorem rM_self {V : X.Opens} (h : V ≤ V) (y : Γ(M, V)) : rM M h y = y := by
  show (M.presheaf.map (homOfLE h).op) y = y
  rw [Subsingleton.elim (homOfLE h) (𝟙 V), op_id, M.presheaf.map_id]; rfl

omit M in
theorem rO_self {V : X.Opens} (h : V ≤ V) (g : Γ(X, V)) : rO h g = g := by
  show (X.presheaf.map (homOfLE h).op).hom g = g
  rw [Subsingleton.elim (homOfLE h) (𝟙 V), op_id, X.presheaf.map_id]; rfl

theorem rM_smul {V W : X.Opens} (h : V ≤ W) (g : Γ(X, W)) (y : Γ(M, W)) :
    rM M h (g • y) = rO h g • rM M h y := M.map_smul _ _ _

theorem rM_add {V W : X.Opens} (h : V ≤ W) (y y' : Γ(M, W)) :
    rM M h (y + y') = rM M h y + rM M h y' := map_add _ _ _

theorem rM_zero {V W : X.Opens} (h : V ≤ W) : rM M h (0 : Γ(M, W)) = 0 := map_zero _

theorem rM_sub {V W : X.Opens} (h : V ≤ W) (y y' : Γ(M, W)) :
    rM M h (y - y') = rM M h y - rM M h y' := map_sub _ _ _

omit M in
theorem rO_one {V W : X.Opens} (h : V ≤ W) : rO h (1 : Γ(X, W)) = 1 := map_one _

omit M in
theorem rO_mul {V W : X.Opens} (h : V ≤ W) (a b : Γ(X, W)) : rO h (a * b) = rO h a * rO h b := map_mul _ _ _

omit M in
theorem rO_zero {V W : X.Opens} (h : V ≤ W) : rO h (0 : Γ(X, W)) = 0 := map_zero _

section Transport

variable (V : X.Opens) (e : M.restrict V.ι ≅ SheafOfModules.unit V.toScheme.ringCatSheaf)

theorem hat_eq {W : X.Opens} (hWV : W ≤ V) : V.ι ''ᵁ V.ι ⁻¹ᵁ W = W := by
  rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι, inf_eq_right.mpr hWV]

theorem le_hat {W : X.Opens} (hWV : W ≤ V) : W ≤ V.ι ''ᵁ V.ι ⁻¹ᵁ W := (hat_eq V hWV).ge
theorem hat_le {W : X.Opens} (hWV : W ≤ V) : V.ι ''ᵁ V.ι ⁻¹ᵁ W ≤ W := (hat_eq V hWV).le

noncomputable def eApp (W : X.Opens) (m : Γ(M, V.ι ''ᵁ V.ι ⁻¹ᵁ W)) : Γ(X, V.ι ''ᵁ V.ι ⁻¹ᵁ W) :=
  (e.hom.app (V.ι ⁻¹ᵁ W)).hom m

noncomputable def eInv (W : X.Opens) (a : Γ(X, V.ι ''ᵁ V.ι ⁻¹ᵁ W)) : Γ(M, V.ι ''ᵁ V.ι ⁻¹ᵁ W) :=
  (e.inv.app (V.ι ⁻¹ᵁ W)).hom a

theorem eInv_eApp (W : X.Opens) (m : Γ(M, V.ι ''ᵁ V.ι ⁻¹ᵁ W)) : eInv M V e W (eApp M V e W m) = m := by
  show (e.hom.app (V.ι ⁻¹ᵁ W) ≫ e.inv.app (V.ι ⁻¹ᵁ W)).hom m = m
  rw [← Hom.comp_app, e.hom_inv_id, Hom.id_app]; rfl

theorem eApp_eInv (W : X.Opens) (a : Γ(X, V.ι ''ᵁ V.ι ⁻¹ᵁ W)) : eApp M V e W (eInv M V e W a) = a := by
  show (e.inv.app (V.ι ⁻¹ᵁ W) ≫ e.hom.app (V.ι ⁻¹ᵁ W)).hom a = a
  rw [← Hom.comp_app, e.inv_hom_id, Hom.id_app]; rfl

theorem eApp_zero (W : X.Opens) : eApp M V e W 0 = 0 := (e.hom.app (V.ι ⁻¹ᵁ W)).hom.map_zero

theorem eApp_add (W : X.Opens) (m m' : Γ(M, V.ι ''ᵁ V.ι ⁻¹ᵁ W)) :
    eApp M V e W (m + m') = eApp M V e W m + eApp M V e W m' := (e.hom.app (V.ι ⁻¹ᵁ W)).hom.map_add m m'

theorem eApp_injective (W : X.Opens) : Function.Injective (eApp M V e W) :=
  Function.LeftInverse.injective (eInv_eApp M V e W)

theorem restrict_smul_eq (W' : V.toScheme.Opens) (b : Γ(V.toScheme, W')) (m : Γ(M.restrict V.ι, W')) :
    (HSMul.hSMul (α := Γ(V.toScheme, W')) (β := Γ(M.restrict V.ι, W')) b m : Γ(M, V.ι ''ᵁ W'))
      = HSMul.hSMul (α := Γ(X, V.ι ''ᵁ W')) (β := Γ(M, V.ι ''ᵁ W')) ((Scheme.Hom.appIso V.ι W').inv b) m := rfl

theorem eApp_smul (W : X.Opens) (a : Γ(X, V.ι ''ᵁ V.ι ⁻¹ᵁ W)) (m : Γ(M, V.ι ''ᵁ V.ι ⁻¹ᵁ W)) :
    eApp M V e W (a • m) = a * eApp M V e W m := by
  have hinv : (Scheme.Hom.appIso V.ι (V.ι ⁻¹ᵁ W)).inv a = a := by
    rw [Scheme.Opens.ι_appIso]; rfl
  have h := Hom.app_smul e.hom (U := V.ι ⁻¹ᵁ W) a m
  have hl := restrict_smul_eq M V (V.ι ⁻¹ᵁ W) a m
  rw [hinv] at hl
  unfold eApp
  rw [← hl]
  exact h.trans rfl

theorem eApp_res {W₁ W₂ : X.Opens} (h : W₂ ≤ W₁) (m : Γ(M, V.ι ''ᵁ V.ι ⁻¹ᵁ W₁)) :
    eApp M V e W₂ (rM M (Scheme.Hom.image_mono V.ι (Scheme.Hom.preimage_mono V.ι h)) m)
      = rO (Scheme.Hom.image_mono V.ι (Scheme.Hom.preimage_mono V.ι h)) (eApp M V e W₁ m) := by
  have hnat := e.hom.mapPresheaf.naturality (homOfLE (Scheme.Hom.preimage_mono V.ι h)).op
  have hx := ConcreteCategory.congr_hom hnat m
  simp only [ConcreteCategory.comp_apply, mapPresheaf_app] at hx
  have e1 : (Scheme.Hom.opensFunctor V.ι).map (homOfLE (Scheme.Hom.preimage_mono V.ι h))
      = homOfLE (Scheme.Hom.image_mono V.ι (Scheme.Hom.preimage_mono V.ι h)) := Subsingleton.elim _ _
  rw [restrict_map, e1] at hx
  exact hx

noncomputable def ψ {W : X.Opens} (hWV : W ≤ V) (m : Γ(M, W)) : Γ(X, W) :=
  rO (le_hat V hWV) (eApp M V e W (rM M (hat_le V hWV) m))

noncomputable def ψinv {W : X.Opens} (hWV : W ≤ V) (a : Γ(X, W)) : Γ(M, W) :=
  rM M (le_hat V hWV) (eInv M V e W (rO (hat_le V hWV) a))

theorem rM_roundtrip {W : X.Opens} (hWV : W ≤ V) (m : Γ(M, W)) : rM M (le_hat V hWV) (rM M (hat_le V hWV) m) = m := by
  rw [rM_rM, rM_self]
theorem rM_roundtrip' {W : X.Opens} (hWV : W ≤ V) (m : Γ(M, V.ι ''ᵁ V.ι ⁻¹ᵁ W)) :
    rM M (hat_le V hWV) (rM M (le_hat V hWV) m) = m := by
  rw [rM_rM, rM_self]
omit M e in
theorem rO_roundtrip {W : X.Opens} (hWV : W ≤ V) (a : Γ(X, W)) : rO (le_hat V hWV) (rO (hat_le V hWV) a) = a := by
  rw [rO_rO, rO_self]
omit M e in
theorem rO_roundtrip' {W : X.Opens} (hWV : W ≤ V) (a : Γ(X, V.ι ''ᵁ V.ι ⁻¹ᵁ W)) :
    rO (hat_le V hWV) (rO (le_hat V hWV) a) = a := by
  rw [rO_rO, rO_self]

theorem ψ_ψinv {W : X.Opens} (hWV : W ≤ V) (a : Γ(X, W)) : ψ M V e hWV (ψinv M V e hWV a) = a := by
  simp only [ψ, ψinv]
  rw [rM_roundtrip' M V hWV, eApp_eInv, rO_roundtrip V hWV]

theorem ψinv_ψ {W : X.Opens} (hWV : W ≤ V) (m : Γ(M, W)) : ψinv M V e hWV (ψ M V e hWV m) = m := by
  simp only [ψ, ψinv]
  rw [rO_roundtrip' V hWV, eInv_eApp, rM_roundtrip M V hWV]

theorem ψ_injective {W : X.Opens} (hWV : W ≤ V) : Function.Injective (ψ M V e hWV) :=
  Function.LeftInverse.injective (ψinv_ψ M V e hWV)

theorem ψ_zero {W : X.Opens} (hWV : W ≤ V) : ψ M V e hWV 0 = 0 := by
  simp only [ψ]
  show rO (le_hat V hWV) (eApp M V e W ((M.presheaf.map _) 0)) = 0
  rw [map_zero, eApp_zero]; exact map_zero _

theorem ψ_add {W : X.Opens} (hWV : W ≤ V) (m m' : Γ(M, W)) :
    ψ M V e hWV (m + m') = ψ M V e hWV m + ψ M V e hWV m' := by
  simp only [ψ]
  rw [rM_add, eApp_add]
  exact map_add _ _ _

theorem ψ_smul {W : X.Opens} (hWV : W ≤ V) (a : Γ(X, W)) (m : Γ(M, W)) :
    ψ M V e hWV (a • m) = a * ψ M V e hWV m := by
  simp only [ψ]
  rw [rM_smul, eApp_smul]
  show (X.presheaf.map _).hom (_ * _) = a * _
  rw [map_mul]
  congr 1
  exact rO_roundtrip V hWV a

theorem ψ_res {W₁ W₂ : X.Opens} (h₁ : W₁ ≤ V) (h : W₂ ≤ W₁) (m : Γ(M, W₁)) :
    ψ M V e (h.trans h₁) (rM M h m) = rO h (ψ M V e h₁ m) := by
  simp only [ψ]
  have lhs : rM M (hat_le V (h.trans h₁)) (rM M h m)
      = rM M (Scheme.Hom.image_mono V.ι (Scheme.Hom.preimage_mono V.ι h)) (rM M (hat_le V h₁) m) := by
    rw [rM_rM, rM_rM]
  rw [lhs, eApp_res M V e h, rO_rO, rO_rO]

noncomputable def frame : Γ(M, V) := ψinv M V e le_rfl 1

theorem ψ_frame : ψ M V e le_rfl (frame M V e) = 1 := ψ_ψinv M V e le_rfl 1

theorem ψ_rM_frame {W : X.Opens} (hWV : W ≤ V) : ψ M V e hWV (rM M hWV (frame M V e)) = 1 := by
  have h := ψ_res M V e le_rfl hWV (frame M V e)
  rw [ψ_frame, rO_one] at h
  exact h

theorem eq_smul_frame {W : X.Opens} (hWV : W ≤ V) (m : Γ(M, W)) :
    m = ψ M V e hWV m • rM M hWV (frame M V e) := by
  apply ψ_injective M V e hWV
  rw [ψ_smul, ψ_rM_frame, mul_one]

end Transport

section Integral

variable [IsIntegral X]

omit M in
theorem nonempty_inf (U W : X.Opens) [hU : Nonempty U] [hW : Nonempty W] : Nonempty (U ⊓ W : X.Opens) := by
  obtain ⟨⟨u, hu⟩⟩ := hU
  obtain ⟨⟨w, hw⟩⟩ := hW
  obtain ⟨z, hz⟩ := nonempty_preirreducible_inter U.isOpen W.isOpen ⟨u, hu⟩ ⟨w, hw⟩
  exact ⟨⟨z, hz⟩⟩

omit M in

noncomputable abbrev alg (U : X.Opens) [Nonempty U] (a : Γ(X, U)) : X.functionField :=
  (X.germToFunctionField U).hom a

omit M in
theorem alg_rO {U W : X.Opens} [Nonempty U] [Nonempty W] (h : W ≤ U) (a : Γ(X, U)) :
    alg W (rO h a) = alg U a := by
  show (X.presheaf.map (homOfLE h).op ≫ X.germToFunctionField W).hom a = _
  unfold Scheme.germToFunctionField
  rw [TopCat.Presheaf.germ_res]

omit M in
theorem alg_injective (U : X.Opens) [Nonempty U] : Function.Injective (alg (X := X) U) :=
  Scheme.germToFunctionField_injective X U

omit M in
theorem rO_injective {U W : X.Opens} [Nonempty U] [Nonempty W] (h : W ≤ U) :
    Function.Injective (rO (X := X) h) := by
  intro a b hab
  apply alg_injective U
  rw [← alg_rO h, ← alg_rO h, hab]

omit M in
theorem alg_one (U : X.Opens) [Nonempty U] : alg U (1 : Γ(X, U)) = 1 := map_one _

omit M in
theorem alg_zero (U : X.Opens) [Nonempty U] : alg U (0 : Γ(X, U)) = 0 := map_zero _

omit M in
theorem alg_add (U : X.Opens) [Nonempty U] (a b : Γ(X, U)) : alg U (a + b) = alg U a + alg U b := map_add _ _ _

omit M in
theorem alg_mul (U : X.Opens) [Nonempty U] (a b : Γ(X, U)) : alg U (a * b) = alg U a * alg U b := map_mul _ _ _

end Integral

section Places

open AlgebraicCurve WithZero

variable {K : Type u} [Field K] (x : X ⟶ Spec (CommRingCat.of K)) [IsIntegral X] [SmoothOfRelativeDimension 1 x]

omit M in

theorem adicValuation_alg_le_one (W : X.Opens) (y : X) (hyW : y ∈ W) (hy : IsClosed ({y} : Set X))
    (v : letI := (baseToFunctionField x).toAlgebra; Place K X.functionField)
    (hv : letI := (baseToFunctionField x).toAlgebra
      (algebraMap (X.presheaf.stalk y) X.functionField).range = v.toValuationSubring.toSubring)
    (a : Γ(X, W)) :
    letI := (baseToFunctionField x).toAlgebra
    haveI : Nonempty W := ⟨⟨y, hyW⟩⟩
    v.adicValuation (alg W a) ≤ 1 := by
  letI := (baseToFunctionField x).toAlgebra
  haveI : Nonempty W := ⟨⟨y, hyW⟩⟩

  obtain ⟨W', hW'aff, hyW', hW'W⟩ :=
    (Opens.isBasis_iff_nbhd.mp X.isBasis_affineOpens) hyW
  haveI : Nonempty W' := ⟨⟨y, hyW'⟩⟩
  rw [← alg_rO hW'W a]
  apply (Place.mem_iff_adicValuation_le_one v).mp
  have hmem : alg W' (rO hW'W a) ∈ (algebraMap Γ(X, W') X.functionField).range := ⟨rO hW'W a, rfl⟩
  rw [range_algebraMap_functionField_eq_iInf_of_isAffineOpen x W' hW'aff] at hmem
  have h2 := (Subring.mem_iInf.mp hmem) v
  have h3 := (Subring.mem_iInf.mp h2) ⟨y, hyW', hy, hv⟩
  exact h3

def IsGeneratorAt (U : X.Opens) (s : Γ(M, U)) (y : X) : Prop :=
  ∀ (W : X.Opens) (h : W ≤ U), y ∈ W → ∀ m : Γ(M, W), ∃ a : Γ(X, W), m = a • rM M h s

omit x [IsIntegral X] in
theorem isGeneratorAt_frame (V : X.Opens) (e : M.restrict V.ι ≅ SheafOfModules.unit V.toScheme.ringCatSheaf)
    (y : X) : IsGeneratorAt M V (frame M V e) y :=
  fun _ h _ m => ⟨ψ M V e h m, eq_smul_frame M V e h m⟩

omit x [IsIntegral X] in
theorem isGeneratorAt_rM {U W : X.Opens} (h : W ≤ U) (s : Γ(M, U)) (y : X) (hs : IsGeneratorAt M U s y) :
    IsGeneratorAt M W (rM M h s) y := by
  intro W' h' hyW' m
  obtain ⟨a, ha⟩ := hs W' (h'.trans h) hyW' m
  exact ⟨a, by rw [rM_rM]; exact ha⟩

end Places

end AlgebraicGeometry.Scheme.Modules.RatSec

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "Scheme.germToFunctionField SmoothOfRelativeDimension IsProper Scheme.Hom Scheme.germToFunctionField_injective Scheme.Opens.ι_appIso Scheme.Hom.image_preimage_eq_opensRange_inf Spec IsIntegral Scheme Scheme.Hom.appIso Scheme.Hom.preimage_mono IsAffineOpen Scheme.Modules Scheme.Opens Scheme.Hom.image_mono Scheme.Hom.opensFunctor Scheme.Opens.opensRange_ι Scheme.Modules.IsInvertible Scheme.Modules.IsInvertible.exists_divisor_range_eq_lSpaceOn Scheme.Modules.exists_eq_mul_and_eq_add_ord_of_presentations"
namespace Scheme
p2m_export "AlgebraicGeometry.Scheme" "germToFunctionField ringCatSheaf Hom.id_app Hom germToFunctionField_injective Γ Opens.ι_appIso Hom.image_preimage_eq_opensRange_inf Hom.appIso functionField Hom.preimage_mono Hom.comp_app isBasis_affineOpens Modules Opens Hom.image_mono Hom.opensFunctor Opens.opensRange_ι restrict Modules.IsInvertible Modules.IsInvertible.exists_divisor_range_eq_lSpaceOn Modules.exists_eq_mul_and_eq_add_ord_of_presentations"
namespace Modules
p2m_export "AlgebraicGeometry.Scheme.Modules" "Hom.app_smul presheaf Hom.comp_app Hom mapPresheaf_app Hom.id_app restrict_map restrict map_smul IsInvertible tensor tensorSections tensorSections_smul_left tensorSections_smul_right map_homOfLE_tensorSections IsFrameOn IsInvertible.exists_divisor_range_eq_lSpaceOn exists_eq_mul_and_eq_add_ord_of_presentations"
namespace RatSec
p2m_open "AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme AlgebraicGeometry"

section TensorCalib

p2m_open "CategoryTheory.MonoidalCategory"

variable {X : Scheme.{u}} [IsIntegral X]

omit [IsIntegral X] in

theorem IsFrameOn.ne_zero_of_nontrivial {M : X.Modules} {U : X.Opens} [Nontrivial Γ(X, U)] {s : Γ(M, U)}
    (hs : IsFrameOn s U) : s ≠ 0 := by
  intro h
  have h1 : (1 : Γ(X, U)) • M.presheaf.map (homOfLE (le_refl U)).op s = 0 := by
    rw [h, map_zero, smul_zero]
  have := (hs.smul_eq_zero_iff le_rfl le_rfl (1 : Γ(X, U))).mp h1
  exact one_ne_zero this

variable {L L' : X.Modules}

theorem exists_forall_tensorSections_eq_mul
    (hL : Scheme.Modules.IsInvertible L) (hL' : Scheme.Modules.IsInvertible L')
    (φ : ∀ U : X.Opens, Γ(L, U) →+ (X.functionField : Type u))
    (φ' : ∀ U : X.Opens, Γ(L', U) →+ (X.functionField : Type u))
    (φ'' : ∀ U : X.Opens, Γ(L ⊗ L', U) →+ (X.functionField : Type u))
    (hnat : ∀ (U V : X.Opens) (h : V ≤ U), Nonempty V →
      ∀ m : Γ(L, U), φ V (L.presheaf.map (homOfLE h).op m) = φ U m)
    (hnat' : ∀ (U V : X.Opens) (h : V ≤ U), Nonempty V →
      ∀ m : Γ(L', U), φ' V (L'.presheaf.map (homOfLE h).op m) = φ' U m)
    (hnat'' : ∀ (U V : X.Opens) (h : V ≤ U), Nonempty V →
      ∀ m : Γ(L ⊗ L', U), φ'' V ((L ⊗ L').presheaf.map (homOfLE h).op m) = φ'' U m)
    (hsmul : ∀ (U : X.Opens) [Nonempty U] (a : Γ(X, U)) (m : Γ(L, U)),
      φ U (a • m) = algebraMap Γ(X, U) X.functionField a * φ U m)
    (hsmul' : ∀ (U : X.Opens) [Nonempty U] (a : Γ(X, U)) (m : Γ(L', U)),
      φ' U (a • m) = algebraMap Γ(X, U) X.functionField a * φ' U m)
    (hsmul'' : ∀ (U : X.Opens) [Nonempty U] (a : Γ(X, U)) (m : Γ(L ⊗ L', U)),
      φ'' U (a • m) = algebraMap Γ(X, U) X.functionField a * φ'' U m)
    (hinj : ∀ U : X.Opens, Nonempty U → Function.Injective (φ U))
    (hinj' : ∀ U : X.Opens, Nonempty U → Function.Injective (φ' U))
    (hinj'' : ∀ U : X.Opens, Nonempty U → Function.Injective (φ'' U)) :
    ∃ f : X.functionField, f ≠ 0 ∧ ∀ (U : X.Opens) [Nonempty U] (s : Γ(L, U)) (t : Γ(L', U)),
      φ'' U (tensorSections s t) = f * φ U s * φ' U t := by
  classical

  obtain ⟨U₁, s₁, hη₁, hs₁⟩ := hL.exists_isFrameOn (genericPoint X)
  obtain ⟨U₂, t₂, hη₂, ht₂⟩ := hL'.exists_isFrameOn (genericPoint X)
  let V : X.Opens := U₁ ⊓ U₂
  haveI : Nonempty V := ⟨⟨genericPoint X, hη₁, hη₂⟩⟩
  let s₀ : Γ(L, V) := rM L inf_le_left s₁
  let t₀ : Γ(L', V) := rM L' inf_le_right t₂
  have hs₀ : IsFrameOn s₀ V := (hs₁.map (homOfLE (inf_le_left : V ≤ U₁))).mono inf_le_left
  have ht₀ : IsFrameOn t₀ V := (ht₂.map (homOfLE (inf_le_right : V ≤ U₂))).mono inf_le_right
  have hst₀ : IsFrameOn (tensorSections s₀ t₀) V := hs₀.tensorSections ht₀
  have hφs : φ V s₀ ≠ 0 := fun h =>
    IsFrameOn.ne_zero_of_nontrivial hs₀ (hinj V inferInstance (by rw [h, map_zero]))
  have hφt : φ' V t₀ ≠ 0 := fun h =>
    IsFrameOn.ne_zero_of_nontrivial ht₀ (hinj' V inferInstance (by rw [h, map_zero]))
  have hφst : φ'' V (tensorSections s₀ t₀) ≠ 0 := fun h =>
    IsFrameOn.ne_zero_of_nontrivial hst₀ (hinj'' V inferInstance (by rw [h, map_zero]))
  refine ⟨φ'' V (tensorSections s₀ t₀) / (φ V s₀ * φ' V t₀), div_ne_zero hφst (mul_ne_zero hφs hφt), ?_⟩
  intro U hU s t
  let W : X.Opens := U ⊓ V
  haveI : Nonempty W := nonempty_inf U V

  obtain ⟨a, ha⟩ := (hs₀ (inf_le_right : W ≤ V) inf_le_right).2 (rM L (inf_le_left : W ≤ U) s)
  obtain ⟨b, hb⟩ := (ht₀ (inf_le_right : W ≤ V) inf_le_right).2 (rM L' (inf_le_left : W ≤ U) t)
  simp only at ha hb

  have e1 : φ'' U (tensorSections s t) = algebraMap Γ(X, W) X.functionField (a * b) * φ'' V (tensorSections s₀ t₀) := by
    rw [← hnat'' U W inf_le_left inferInstance (tensorSections s t), map_homOfLE_tensorSections]
    change φ'' W (tensorSections (rM L (inf_le_left : W ≤ U) s) (rM L' (inf_le_left : W ≤ U) t)) = _
    rw [← ha, ← hb, tensorSections_smul_left, tensorSections_smul_right, ← mul_smul,
      ← map_homOfLE_tensorSections, hsmul'', hnat'' V W inf_le_right inferInstance]
  have e2 : φ U s = algebraMap Γ(X, W) X.functionField a * φ V s₀ := by
    rw [← hnat U W inf_le_left inferInstance s]
    change φ W (rM L (inf_le_left : W ≤ U) s) = _
    rw [← ha, hsmul, hnat V W inf_le_right inferInstance]
  have e3 : φ' U t = algebraMap Γ(X, W) X.functionField b * φ' V t₀ := by
    rw [← hnat' U W inf_le_left inferInstance t]
    change φ' W (rM L' (inf_le_left : W ≤ U) t) = _
    rw [← hb, hsmul', hnat' V W inf_le_right inferInstance]
  rw [e1, e2, e3, map_mul]
  field_simp
  try ring

end TensorCalib

end AlgebraicGeometry.Scheme.Modules.RatSec

namespace AlgebraicGeometry p2m_export "AlgebraicGeometry" "Scheme.germToFunctionField SmoothOfRelativeDimension IsProper Scheme.Hom Scheme.germToFunctionField_injective Scheme.Opens.ι_appIso Scheme.Hom.image_preimage_eq_opensRange_inf Spec IsIntegral Scheme Scheme.Hom.appIso Scheme.Hom.preimage_mono IsAffineOpen Scheme.Modules Scheme.Opens Scheme.Hom.image_mono Scheme.Hom.opensFunctor Scheme.Opens.opensRange_ι Scheme.Modules.IsInvertible Scheme.Modules.IsInvertible.exists_divisor_range_eq_lSpaceOn Scheme.Modules.exists_eq_mul_and_eq_add_ord_of_presentations" namespace Scheme p2m_export "AlgebraicGeometry.Scheme" "germToFunctionField ringCatSheaf Hom.id_app Hom germToFunctionField_injective Γ Opens.ι_appIso Hom.image_preimage_eq_opensRange_inf Hom.appIso functionField Hom.preimage_mono Hom.comp_app isBasis_affineOpens Modules Opens Hom.image_mono Hom.opensFunctor Opens.opensRange_ι restrict Modules.IsInvertible Modules.IsInvertible.exists_divisor_range_eq_lSpaceOn Modules.exists_eq_mul_and_eq_add_ord_of_presentations" namespace Modules p2m_export "AlgebraicGeometry.Scheme.Modules" "Hom.app_smul presheaf Hom.comp_app Hom mapPresheaf_app Hom.id_app restrict_map restrict map_smul IsInvertible tensor tensorSections tensorSections_smul_left tensorSections_smul_right map_homOfLE_tensorSections IsFrameOn IsInvertible.exists_divisor_range_eq_lSpaceOn exists_eq_mul_and_eq_add_ord_of_presentations" end AlgebraicGeometry.Scheme.Modules
p2m_open_scoped "AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.Modules" in
open _root_.AlgebraicGeometry.Scheme.Modules _root_.P2MW.S_AlgebraicGeometry_Scheme_Modules_isPrincipal_sub_sub_of_presentations_tensor.AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme.Modules.RatSec AlgebraicCurve _root_.CategoryTheory.MonoidalCategory WithZero in

theorem AlgebraicGeometry.Scheme.Modules.isPrincipal_sub_sub_of_presentations_tensor'
    {K : Type u} [Field K] [IsAlgClosed K] {X : Scheme.{u}} (x : X ⟶ Spec (CommRingCat.of K))
    [IsIntegral X] [IsProper x] [SmoothOfRelativeDimension 1 x] (L L' : X.Modules)
    (hL : Scheme.Modules.IsInvertible L) (hL' : Scheme.Modules.IsInvertible L')
    (D D' D'' : letI := (AlgebraicCurve.baseToFunctionField x).toAlgebra
      AlgebraicCurve.Divisor K X.functionField)
    (φ : ∀ U : X.Opens, Γ(L, U) →+ (X.functionField : Type u))
    (hnat : ∀ (U V : X.Opens) (h : V ≤ U), Nonempty V →
      ∀ m : Γ(L, U), φ V ((L).presheaf.map (homOfLE h).op m) = φ U m)
    (hsmul : ∀ (U : X.Opens) [Nonempty U] (a : Γ(X, U)) (m : Γ(L, U)),
      φ U (a • m) = algebraMap Γ(X, U) X.functionField a * φ U m)
    (hinj : ∀ U : X.Opens, Nonempty U → Function.Injective (φ U))
    (hrange : letI := (AlgebraicCurve.baseToFunctionField x).toAlgebra
      ∀ U : X.Opens, IsAffineOpen U → Nonempty U →
        Set.range (φ U) = (AlgebraicCurve.lSpaceOn (AlgebraicCurve.placesOf x U) D : Set X.functionField))
    (φ' : ∀ U : X.Opens, Γ(L', U) →+ (X.functionField : Type u))
    (hnat' : ∀ (U V : X.Opens) (h : V ≤ U), Nonempty V →
      ∀ m : Γ(L', U), φ' V ((L').presheaf.map (homOfLE h).op m) = φ' U m)
    (hsmul' : ∀ (U : X.Opens) [Nonempty U] (a : Γ(X, U)) (m : Γ(L', U)),
      φ' U (a • m) = algebraMap Γ(X, U) X.functionField a * φ' U m)
    (hinj' : ∀ U : X.Opens, Nonempty U → Function.Injective (φ' U))
    (hrange' : letI := (AlgebraicCurve.baseToFunctionField x).toAlgebra
      ∀ U : X.Opens, IsAffineOpen U → Nonempty U →
        Set.range (φ' U) = (AlgebraicCurve.lSpaceOn (AlgebraicCurve.placesOf x U) D' : Set X.functionField))
    (φ'' : ∀ U : X.Opens, Γ(L ⊗ L', U) →+ (X.functionField : Type u))
    (hnat'' : ∀ (U V : X.Opens) (h : V ≤ U), Nonempty V →
      ∀ m : Γ(L ⊗ L', U), φ'' V ((L ⊗ L').presheaf.map (homOfLE h).op m) = φ'' U m)
    (hsmul'' : ∀ (U : X.Opens) [Nonempty U] (a : Γ(X, U)) (m : Γ(L ⊗ L', U)),
      φ'' U (a • m) = algebraMap Γ(X, U) X.functionField a * φ'' U m)
    (hinj'' : ∀ U : X.Opens, Nonempty U → Function.Injective (φ'' U))
    (hrange'' : letI := (AlgebraicCurve.baseToFunctionField x).toAlgebra
      ∀ U : X.Opens, IsAffineOpen U → Nonempty U →
        Set.range (φ'' U) = (AlgebraicCurve.lSpaceOn (AlgebraicCurve.placesOf x U) D'' : Set X.functionField)) :
    letI := (AlgebraicCurve.baseToFunctionField x).toAlgebra
    AlgebraicCurve.Divisor.IsPrincipal (D'' - D - D') := by
  classical
  letI := (AlgebraicCurve.baseToFunctionField x).toAlgebra

  obtain ⟨E, ψ, e1, e2, e3, e4, e5⟩ := Scheme.Modules.IsInvertible.exists_divisor_range_eq_lSpaceOn x L hL
  obtain ⟨E', ψ', e1', e2', e3', e4', e5'⟩ := Scheme.Modules.IsInvertible.exists_divisor_range_eq_lSpaceOn x L' hL'
  obtain ⟨E'', ψ'', e1'', e2'', e3'', e4'', e5''⟩ :=
    Scheme.Modules.IsInvertible.exists_divisor_range_eq_lSpaceOn x (L ⊗ L') (hL.tensor hL')

  obtain ⟨f, hf0, hf⟩ := exists_forall_tensorSections_eq_mul hL hL' ψ ψ' ψ'' e1 e1' e1'' e2 e2' e2'' e3 e3' e3''

  have hpt : ∀ v : Place K X.functionField, (E'' - E - E') v = v.ord f⁻¹ := by
    intro v
    obtain ⟨y, hy, hv⟩ := exists_closedPoint_range_stalk_eq x v

    obtain ⟨U₁, s₁, hy₁, hs₁⟩ := hL.exists_isFrameOn y
    obtain ⟨U₂, t₂, hy₂, ht₂⟩ := hL'.exists_isFrameOn y
    let W : X.Opens := U₁ ⊓ U₂
    have hyW : y ∈ W := ⟨hy₁, hy₂⟩
    haveI : Nonempty W := ⟨⟨y, hyW⟩⟩
    let s : Γ(L, W) := rM L inf_le_left s₁
    let t : Γ(L', W) := rM L' inf_le_right t₂
    have hs : IsFrameOn s W := (hs₁.map (homOfLE (inf_le_left : W ≤ U₁))).mono inf_le_left
    have ht : IsFrameOn t W := (ht₂.map (homOfLE (inf_le_right : W ≤ U₂))).mono inf_le_right
    have hst : IsFrameOn (tensorSections s t) W := hs.tensorSections ht

    have gen : ∀ {M : X.Modules} (m : Γ(M, W)), IsFrameOn m W →
        ∀ (W' : X.Opens) (h : W' ≤ W), y ∈ W' → ∀ m' : Γ(M, W'), ∃ a : Γ(X, W'),
          m' = a • M.presheaf.map (homOfLE h).op m := by
      intro M m hm W' h _ m'
      obtain ⟨a, ha⟩ := (hm h h).2 m'
      exact ⟨a, ha.symm⟩
    have k := e5 W s y hyW hy (gen s hs) v hv
    have k' := e5' W t y hyW hy (gen t ht) v hv
    have k'' := e5'' W (tensorSections s t) y hyW hy (gen _ hst) v hv
    rw [hf W s t, Valuation.map_mul, Valuation.map_mul, ← k, ← k'] at k''

    have hfv : v.adicValuation f ≠ 0 := (Valuation.ne_zero_iff _).mpr hf0
    have hfv' : v.adicValuation f = exp (-(v.ord f)) := by
      simp only [Place.ord, neg_neg, WithZero.exp_log hfv]
    rw [hfv', ← WithZero.exp_add, ← WithZero.exp_add, WithZero.exp_injective.eq_iff] at k''
    simp only [Finsupp.coe_sub, Pi.sub_apply, Place.ord_inv]
    omega
  have hP0 : Divisor.IsPrincipal (E'' - E - E') := ⟨f⁻¹, inv_ne_zero hf0, hpt⟩

  have hsec : ∀ {M : X.Modules}, Scheme.Modules.IsInvertible M → ∃ (U : X.Opens) (m : Γ(M, U)), m ≠ 0 := by
    intro M hM
    obtain ⟨U, s, hη, hs⟩ := hM.exists_isFrameOn (genericPoint X)
    haveI : Nonempty U := ⟨⟨_, hη⟩⟩
    exact ⟨U, s, IsFrameOn.ne_zero_of_nontrivial hs⟩

  obtain ⟨-, -, -, -, hP1⟩ := Scheme.Modules.exists_eq_mul_and_eq_add_ord_of_presentations x L D E φ ψ
    hnat e1 hsmul e2 hinj e3 hrange e4 (hsec hL)
  obtain ⟨-, -, -, -, hP2⟩ := Scheme.Modules.exists_eq_mul_and_eq_add_ord_of_presentations x L' D' E' φ' ψ'
    hnat' e1' hsmul' e2' hinj' e3' hrange' e4' (hsec hL')
  obtain ⟨-, -, -, -, hP3⟩ := Scheme.Modules.exists_eq_mul_and_eq_add_ord_of_presentations x (L ⊗ L') D'' E''
    φ'' ψ'' hnat'' e1'' hsmul'' e2'' hinj'' e3'' hrange'' e4'' (hsec (hL.tensor hL'))

  have key : D'' - D - D' = (D'' - E'') - (D - E) - (D' - E') + (E'' - E - E') := by abel
  rw [key]
  have mem : (D'' - E'') - (D - E) - (D' - E') + (E'' - E - E') ∈ Divisor.principal (K := K) (F := X.functionField) :=
    add_mem (sub_mem (sub_mem hP3 hP1) hP2) hP0
  exact mem

open _root_.AlgebraicGeometry _root_.P2MW.S_AlgebraicGeometry_Scheme_Modules_isPrincipal_sub_sub_of_presentations_tensor.AlgebraicGeometry _root_.CategoryTheory.MonoidalCategory in
theorem solution
    {K : Type u} [Field K] [IsAlgClosed K] {X : Scheme.{u}} (x : X ⟶ Spec (CommRingCat.of K))
    [IsIntegral X] [IsProper x] [SmoothOfRelativeDimension 1 x] (L L' : X.Modules)
    (hL : Scheme.Modules.IsInvertible L) (hL' : Scheme.Modules.IsInvertible L')
    (D D' D'' : letI := (AlgebraicCurve.baseToFunctionField x).toAlgebra
      AlgebraicCurve.Divisor K X.functionField)
    (φ : ∀ U : X.Opens, Γ(L, U) →+ (X.functionField : Type u))
    (hnat : ∀ (U V : X.Opens) (h : V ≤ U), Nonempty V →
      ∀ m : Γ(L, U), φ V ((L).presheaf.map (homOfLE h).op m) = φ U m)
    (hsmul : ∀ (U : X.Opens) [Nonempty U] (a : Γ(X, U)) (m : Γ(L, U)),
      φ U (a • m) = algebraMap Γ(X, U) X.functionField a * φ U m)
    (hinj : ∀ U : X.Opens, Nonempty U → Function.Injective (φ U))
    (hrange : letI := (AlgebraicCurve.baseToFunctionField x).toAlgebra
      ∀ U : X.Opens, IsAffineOpen U → Nonempty U →
        Set.range (φ U) = (AlgebraicCurve.lSpaceOn (AlgebraicCurve.placesOf x U) D : Set X.functionField))
    (φ' : ∀ U : X.Opens, Γ(L', U) →+ (X.functionField : Type u))
    (hnat' : ∀ (U V : X.Opens) (h : V ≤ U), Nonempty V →
      ∀ m : Γ(L', U), φ' V ((L').presheaf.map (homOfLE h).op m) = φ' U m)
    (hsmul' : ∀ (U : X.Opens) [Nonempty U] (a : Γ(X, U)) (m : Γ(L', U)),
      φ' U (a • m) = algebraMap Γ(X, U) X.functionField a * φ' U m)
    (hinj' : ∀ U : X.Opens, Nonempty U → Function.Injective (φ' U))
    (hrange' : letI := (AlgebraicCurve.baseToFunctionField x).toAlgebra
      ∀ U : X.Opens, IsAffineOpen U → Nonempty U →
        Set.range (φ' U) = (AlgebraicCurve.lSpaceOn (AlgebraicCurve.placesOf x U) D' : Set X.functionField))
    (φ'' : ∀ U : X.Opens, Γ(L ⊗ L', U) →+ (X.functionField : Type u))
    (hnat'' : ∀ (U V : X.Opens) (h : V ≤ U), Nonempty V →
      ∀ m : Γ(L ⊗ L', U), φ'' V ((L ⊗ L').presheaf.map (homOfLE h).op m) = φ'' U m)
    (hsmul'' : ∀ (U : X.Opens) [Nonempty U] (a : Γ(X, U)) (m : Γ(L ⊗ L', U)),
      φ'' U (a • m) = algebraMap Γ(X, U) X.functionField a * φ'' U m)
    (hinj'' : ∀ U : X.Opens, Nonempty U → Function.Injective (φ'' U))
    (hrange'' : letI := (AlgebraicCurve.baseToFunctionField x).toAlgebra
      ∀ U : X.Opens, IsAffineOpen U → Nonempty U →
        Set.range (φ'' U) = (AlgebraicCurve.lSpaceOn (AlgebraicCurve.placesOf x U) D'' : Set X.functionField)) :
    letI := (AlgebraicCurve.baseToFunctionField x).toAlgebra
    AlgebraicCurve.Divisor.IsPrincipal (D'' - D - D') :=
  AlgebraicGeometry.Scheme.Modules.isPrincipal_sub_sub_of_presentations_tensor' x L L' hL hL' D D' D'' φ hnat hsmul hinj
    hrange φ' hnat' hsmul' hinj' hrange' φ'' hnat'' hsmul'' hinj'' hrange''

end S_AlgebraicGeometry_Scheme_Modules_isPrincipal_sub_sub_of_presentations_tensor
end P2MW
export P2MW.S_AlgebraicGeometry_Scheme_Modules_isPrincipal_sub_sub_of_presentations_tensor (solution)
