-- Prove2me | solution 1 for AlgebraicCurve.CurveModel.exists_eq_appTop_of_isUnit
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:01.734404+00:00
-- url     : https://prove2.me/submissions/5aa43612-d0aa-5019-9a92-70259d15926d

import Mathlib
import Definitions.Def_AlgebraicCurve_CurveModel
import Theorems.Thm_AlgebraicCurve_RationalFunctionField_exists_algebraMap_of_forall_ord_eq_zero
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_CurveModel_exists_eq_appTop_of_isUnit
p2m_attr_erase "instance" "AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupDivisor AlgebraicCurve.Pic0.instModuleZModTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instDistribMulActionTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instSMulTorsion AlgebraicCurve.SemilinearAut.instMulActionSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instSMulCommClassZModTorsion AlgebraicCurve.SemilinearAut.instMulSemiringActionSubtypeProdRingAutMemSubgroup instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy"
p2m_attr_erase "simp" "AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.SemilinearAut.toRingAut_inv AlgebraicCurve.SemilinearAut.smul_def AlgebraicCurve.SemilinearAut.smul_single AlgebraicCurve.SemilinearAut.smul_toValuationSubring AlgebraicCurve.SemilinearAut.baseAut_inv AlgebraicCurve.SemilinearAut.baseAut_ofAlgAut AlgebraicCurve.SemilinearAut.toRingAut_ofAlgAut AlgebraicCurve.SemilinearAut.torsionRep_apply AlgebraicCurve.SemilinearAut.toRingAut_one AlgebraicCurve.SemilinearAut.deg_smul AlgebraicCurve.SemilinearAut.degree_smul AlgebraicCurve.SemilinearAut.coe_degZeroSMulHom AlgebraicCurve.SemilinearAut.baseAut_mul"
p2m_attr_erase "simp" "AlgebraicCurve.SemilinearAut.coe_smulValuationSubringEquiv_apply AlgebraicCurve.SemilinearAut.baseAut_one AlgebraicCurve.SemilinearAut.ofAlgAut_smul AlgebraicCurve.SemilinearAut.coe_torsion_smul AlgebraicCurve.SemilinearAut.toRingAut_mul AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.jqNModC_one ModularCurve.qExpand_coeff_mul ModularCurve.qExpandₐ_apply ModularCurve.jqN_one ModularCurve.qExpand_single ModularCurve.dedekindPsi_one ModularCurve.ModularPolynomialData.mk.sizeOf_spec ModularCurve.evalAtJ_X ModularCurve.ModularPolynomialData.mk.injEq ModularCurve.constantCoeff_jNum ModularCurve.constantCoeff_eisenstein4 ModularCurve.qExpand_C ModularCurve.coeff_jq_neg_one ModularCurve.constantCoeff_jNumQ ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply"

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry AlgebraicCurve

theorem solution
    (k : Type u) [Field k] [IsAlgClosed k] (M : CurveModel k (RatFunc k))
    (u : Γ(M.C, ⊤)) (hu : IsUnit u) :
    ∃ c : k, u = M.toBase.appTop ((Scheme.ΓSpecIso (CommRingCat.of k)).inv c) := by
  classical
  haveI := M.isIntegral
  obtain ⟨uu, rfl⟩ := hu

  let η := genericPoint M.C
  let γ : Γ(M.C, ⊤) →+* M.C.functionField := (M.C.presheaf.germ ⊤ η trivial).hom
  let g : RatFunc k := M.ffEquiv.symm (γ uu)
  have hg : g ≠ 0 := by
    have : IsUnit g := (Units.map (M.ffEquiv.symm.toRingHom.toMonoidHom.comp γ.toMonoidHom) uu).isUnit
    exact this.ne_zero

  have hord : ∀ v : Place k (RatFunc k), v.ord g = 0 := by
    intro v
    obtain ⟨x, rfl⟩ := M.placeOfPoint_bijective.2 v
    have hmem : ∀ w : Γ(M.C, ⊤)ˣ, M.ffEquiv.symm (γ w) ∈ (M.placeOfPoint x).toValuationSubring := by
      intro w
      have := M.range_stalk_eq x
      have hw : M.ffEquiv.symm (γ w) ∈ ((M.ffEquiv.symm : M.C.functionField ≃+* RatFunc k).toRingHom.comp
          (algebraMap (M.C.presheaf.stalk x.1) M.C.functionField)).range := by
        refine ⟨(M.C.presheaf.germ ⊤ x.1 trivial).hom w, ?_⟩
        change M.ffEquiv.symm (algebraMap _ _ ((M.C.presheaf.germ ⊤ x.1 trivial).hom (w : Γ(M.C, ⊤)))) = M.ffEquiv.symm (γ w)
        congr 1
        change ((M.C.presheaf.germ ⊤ x.1 trivial) ≫ M.C.presheaf.stalkSpecializes (genericPoint_specializes x.1)).hom _ = _
        rw [TopCat.Presheaf.germ_stalkSpecializes]
      rw [this] at hw
      exact hw

    have h1 : g ∈ (M.placeOfPoint x).toValuationSubring := hmem uu
    have h2 : g⁻¹ ∈ (M.placeOfPoint x).toValuationSubring := by
      have := hmem uu⁻¹
      have hinv : M.ffEquiv.symm (γ ↑uu⁻¹) = g⁻¹ := by
        let ψ : Γ(M.C, ⊤) →+* RatFunc k := M.ffEquiv.symm.toRingHom.comp γ
        change ((Units.map ψ.toMonoidHom uu⁻¹ : (RatFunc k)ˣ) : RatFunc k) = ((Units.map ψ.toMonoidHom uu : (RatFunc k)ˣ) : RatFunc k)⁻¹
        rw [map_inv, Units.val_inv_eq_inv_val]
      rwa [hinv] at this
    let gu : (M.placeOfPoint x).toValuationSubringˣ :=
      ⟨⟨g, h1⟩, ⟨g⁻¹, h2⟩, Subtype.ext (mul_inv_cancel₀ hg), Subtype.ext (inv_mul_cancel₀ hg)⟩
    exact (M.placeOfPoint x).ord_coe_unit gu

  obtain ⟨c, -, hc⟩ := RationalFunctionField.exists_algebraMap_of_forall_ord_eq_zero hg hord
  refine ⟨c, ?_⟩
  apply AlgebraicGeometry.germ_injective_of_isIntegral M.C η (U := ⊤) trivial
  change γ uu = γ (M.toBase.appTop ((Scheme.ΓSpecIso (CommRingCat.of k)).inv c))
  have h3 : γ uu = M.ffEquiv (algebraMap k (RatFunc k) c) := by
    rw [← hc]; exact (M.ffEquiv.apply_symm_apply _).symm
  rw [h3, M.ffEquiv_algebraMap]
  rfl

end S_AlgebraicCurve_CurveModel_exists_eq_appTop_of_isUnit
end P2MW
export P2MW.S_AlgebraicCurve_CurveModel_exists_eq_appTop_of_isUnit (solution)
