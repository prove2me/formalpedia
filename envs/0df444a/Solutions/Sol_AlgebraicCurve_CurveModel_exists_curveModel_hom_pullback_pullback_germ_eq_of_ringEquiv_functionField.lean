-- Prove2me | solution 1 for AlgebraicCurve.CurveModel.exists_curveModel_hom_pullback_pullback_germ_eq_of_ringEquiv_functionField
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:01.734404+00:00
-- url     : https://prove2.me/submissions/33aec0b7-57fe-5534-855c-2b084a9b4c46

import Mathlib
import Definitions.Def_AlgebraicCurve_CurveModel
import Theorems.Thm_AlgebraicGeometry_SmoothProperCurve_exists_curveModel_iso_pullback_germToFunctionField_eq_of_isAlgClosed
import Theorems.Thm_AlgebraicCurve_CurveModel_exists_curveModel_iso_ffEquiv_symm_germToFunctionField_eq_of_algEquiv
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_CurveModel_exists_curveModel_hom_pullback_pullback_germ_eq_of_ringEquiv_functionField
p2m_attr_erase "instance" "AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupDivisor AlgebraicCurve.Pic0.instModuleZModTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instDistribMulActionTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instSMulTorsion AlgebraicCurve.SemilinearAut.instMulActionSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instSMulCommClassZModTorsion AlgebraicCurve.SemilinearAut.instMulSemiringActionSubtypeProdRingAutMemSubgroup instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions"
p2m_attr_erase "simp" "AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.SemilinearAut.toRingAut_inv AlgebraicCurve.SemilinearAut.smul_def AlgebraicCurve.SemilinearAut.smul_single AlgebraicCurve.SemilinearAut.smul_toValuationSubring AlgebraicCurve.SemilinearAut.baseAut_inv AlgebraicCurve.SemilinearAut.baseAut_ofAlgAut AlgebraicCurve.SemilinearAut.toRingAut_ofAlgAut AlgebraicCurve.SemilinearAut.torsionRep_apply"
p2m_attr_erase "simp" "AlgebraicCurve.SemilinearAut.toRingAut_one AlgebraicCurve.SemilinearAut.deg_smul AlgebraicCurve.SemilinearAut.degree_smul AlgebraicCurve.SemilinearAut.coe_degZeroSMulHom AlgebraicCurve.SemilinearAut.baseAut_mul AlgebraicCurve.SemilinearAut.coe_smulValuationSubringEquiv_apply AlgebraicCurve.SemilinearAut.baseAut_one AlgebraicCurve.SemilinearAut.ofAlgAut_smul AlgebraicCurve.SemilinearAut.coe_torsion_smul AlgebraicCurve.SemilinearAut.toRingAut_mul AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.jqNModC_one ModularCurve.qExpand_coeff_mul ModularCurve.qExpandₐ_apply ModularCurve.jqN_one ModularCurve.qExpand_single ModularCurve.dedekindPsi_one ModularCurve.ModularPolynomialData.mk.sizeOf_spec ModularCurve.evalAtJ_X ModularCurve.ModularPolynomialData.mk.injEq ModularCurve.constantCoeff_jNum ModularCurve.constantCoeff_eisenstein4 ModularCurve.qExpand_C ModularCurve.coeff_jq_neg_one ModularCurve.constantCoeff_jNumQ ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply"
p2m_attr_erase "simp" "AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq"

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicCurve

namespace CMTransport

theorem nonempty_preimage_of_isIso {X Y : Scheme} (f : X ⟶ Y) [IsIso f] (U : Y.Opens)
    [h : Nonempty (Scheme.Opens.toScheme U)] : Nonempty (Scheme.Opens.toScheme (f ⁻¹ᵁ U)) := by
  obtain ⟨⟨y, hy⟩⟩ := h
  refine ⟨⟨(inv f).base y, ?_⟩⟩
  show f.base ((inv f).base y) ∈ (U : Set Y)
  have h1 : (inv f ≫ f).base y = y := by simp
  have h2 : (inv f ≫ f).base y = f.base ((inv f).base y) := Scheme.Hom.comp_apply _ _ _
  rw [← h2, h1]
  exact hy

end CMTransport

theorem solution
    {R₀ : Type} [CommRing R₀] {X : Scheme.{0}} (πX : X ⟶ Spec (CommRingCat.of R₀))
    [IsProper πX] [SmoothOfRelativeDimension 1 πX] [GeometricallyIntegral πX]
    {O : Type} [CommRing O] (j : R₀ →+* O) (k : Type) [Field k] [IsAlgClosed k] (i : O →+* k)
    (s : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of R₀))
    (hs : Spec.map (CommRingCat.ofHom i) ≫ Spec.map (CommRingCat.ofHom j) = s)
    [AlgebraicGeometry.IsIntegral ↑(pullback πX s)]
    {L : Type} [Field L] [Algebra k L] (eL : L ≃+* ↥((pullback πX s).functionField))
    (heL : ∀ z : k, eL (algebraMap k L z) = baseToFunctionField (pullback.snd πX s) z) :
    ∃ (𝔐 : AlgebraicCurve.CurveModel k L)
      (e : 𝔐.C ⟶ pullback (pullback.snd πX (Spec.map (CommRingCat.ofHom j))) (Spec.map (CommRingCat.ofHom i)))
      (_ : IsIso e),
      e ≫ pullback.snd (pullback.snd πX (Spec.map (CommRingCat.ofHom j))) (Spec.map (CommRingCat.ofHom i)) = 𝔐.toBase ∧
      ∀ (U : X.Opens) [Nonempty (Scheme.Opens.toScheme U)]
        [Nonempty (Scheme.Opens.toScheme ((pullback.fst πX s) ⁻¹ᵁ U))]
        [Nonempty (Scheme.Opens.toScheme ((e ≫ pullback.fst (pullback.snd πX (Spec.map (CommRingCat.ofHom j))) (Spec.map (CommRingCat.ofHom i)) ≫
          pullback.fst πX (Spec.map (CommRingCat.ofHom j))) ⁻¹ᵁ U))]
        (t : Γ(X, U)),
        𝔐.ffEquiv.symm (𝔐.C.germToFunctionField
          ((e ≫ pullback.fst (pullback.snd πX (Spec.map (CommRingCat.ofHom j))) (Spec.map (CommRingCat.ofHom i)) ≫
            pullback.fst πX (Spec.map (CommRingCat.ofHom j))) ⁻¹ᵁ U)
          (((e ≫ pullback.fst (pullback.snd πX (Spec.map (CommRingCat.ofHom j))) (Spec.map (CommRingCat.ofHom i)) ≫
            pullback.fst πX (Spec.map (CommRingCat.ofHom j))).app U).hom t)) =
        eL.symm ((pullback πX s).germToFunctionField ((pullback.fst πX s) ⁻¹ᵁ U) (((pullback.fst πX s).app U).hom t)) := by
  classical
  subst hs

  letI : Algebra k ↥((pullback πX (Spec.map (CommRingCat.ofHom i) ≫ Spec.map (CommRingCat.ofHom j))).functionField) :=
    (baseToFunctionField (pullback.snd πX (Spec.map (CommRingCat.ofHom i) ≫ Spec.map (CommRingCat.ofHom j)))).toAlgebra

  obtain ⟨_, _, 𝔐₁, e₁, he₁, hgerm₁⟩ :=
    AlgebraicGeometry.SmoothProperCurve.exists_curveModel_iso_pullback_germToFunctionField_eq_of_isAlgClosed
      R₀ πX k (Spec.map (CommRingCat.ofHom i) ≫ Spec.map (CommRingCat.ofHom j))

  let eL' : ↥((pullback πX (Spec.map (CommRingCat.ofHom i) ≫ Spec.map (CommRingCat.ofHom j))).functionField) ≃ₐ[k] L :=
    AlgEquiv.ofRingEquiv (f := eL.symm) (fun z => by
      rw [RingEquiv.symm_apply_eq]
      exact (heL z).symm)
  obtain ⟨𝔐, f, hf, hgerm₂⟩ :=
    AlgebraicCurve.CurveModel.exists_curveModel_iso_ffEquiv_symm_germToFunctionField_eq_of_algEquiv eL' 𝔐₁

  let paste := pullbackLeftPullbackSndIso πX (Spec.map (CommRingCat.ofHom j)) (Spec.map (CommRingCat.ofHom i))
  refine ⟨𝔐, f.hom ≫ e₁.hom ≫ paste.inv, inferInstance, ?_, ?_⟩
  ·
    rw [Category.assoc, Category.assoc, pullbackLeftPullbackSndIso_inv_snd_snd, he₁, hf]
  · intro U _ _ _ t

    have hcomp : (f.hom ≫ e₁.hom ≫ paste.inv) ≫
        pullback.fst (pullback.snd πX (Spec.map (CommRingCat.ofHom j))) (Spec.map (CommRingCat.ofHom i)) ≫
          pullback.fst πX (Spec.map (CommRingCat.ofHom j)) =
        f.hom ≫ e₁.hom ≫ pullback.fst πX (Spec.map (CommRingCat.ofHom i) ≫ Spec.map (CommRingCat.ofHom j)) := by
      simp only [Category.assoc, paste, pullbackLeftPullbackSndIso_inv_fst]

    have key : ∀ (g : 𝔐.C ⟶ X) (hg : g = f.hom ≫ e₁.hom ≫
        pullback.fst πX (Spec.map (CommRingCat.ofHom i) ≫ Spec.map (CommRingCat.ofHom j)))
        [Nonempty (Scheme.Opens.toScheme (g ⁻¹ᵁ U))],
        𝔐.ffEquiv.symm (𝔐.C.germToFunctionField (g ⁻¹ᵁ U) ((g.app U).hom t)) =
          eL.symm ((pullback πX (Spec.map (CommRingCat.ofHom i) ≫ Spec.map (CommRingCat.ofHom j))).germToFunctionField
            ((pullback.fst πX (Spec.map (CommRingCat.ofHom i) ≫ Spec.map (CommRingCat.ofHom j))) ⁻¹ᵁ U)
            (((pullback.fst πX (Spec.map (CommRingCat.ofHom i) ≫ Spec.map (CommRingCat.ofHom j))).app U).hom t)) := by
      intro g hg _
      subst hg

      set fst := pullback.fst πX (Spec.map (CommRingCat.ofHom i) ≫ Spec.map (CommRingCat.ofHom j)) with hfst
      set U₁ : (pullback πX (Spec.map (CommRingCat.ofHom i) ≫ Spec.map (CommRingCat.ofHom j))).Opens := fst ⁻¹ᵁ U with hU₁
      set V : 𝔐₁.C.Opens := e₁.hom ⁻¹ᵁ U₁ with hV
      haveI : Nonempty (Scheme.Opens.toScheme U₁) := inferInstance
      haveI hVne : Nonempty (Scheme.Opens.toScheme V) := CMTransport.nonempty_preimage_of_isIso e₁.hom U₁
      haveI hfVne : Nonempty (Scheme.Opens.toScheme (f.hom ⁻¹ᵁ V)) := CMTransport.nonempty_preimage_of_isIso f.hom V

      have hstepA : 𝔐.ffEquiv.symm (𝔐.C.germToFunctionField ((f.hom ≫ e₁.hom ≫ fst) ⁻¹ᵁ U)
            (((f.hom ≫ e₁.hom ≫ fst).app U).hom t)) =
          𝔐.ffEquiv.symm (𝔐.C.germToFunctionField (f.hom ⁻¹ᵁ V)
            ((f.hom.app V).hom ((e₁.hom.app U₁).hom ((fst.app U).hom t)))) := by
        congr 1
      rw [hstepA, hgerm₂ V ((e₁.hom.app U₁).hom ((fst.app U).hom t)), hgerm₁ U₁ ((fst.app U).hom t)]
      rfl
    exact key _ hcomp

end S_AlgebraicCurve_CurveModel_exists_curveModel_hom_pullback_pullback_germ_eq_of_ringEquiv_functionField
end P2MW
export P2MW.S_AlgebraicCurve_CurveModel_exists_curveModel_hom_pullback_pullback_germ_eq_of_ringEquiv_functionField (solution)
