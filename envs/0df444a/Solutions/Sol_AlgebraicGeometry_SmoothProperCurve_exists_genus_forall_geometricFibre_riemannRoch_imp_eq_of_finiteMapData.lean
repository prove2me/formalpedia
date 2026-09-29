-- Prove2me | solution 1 for AlgebraicGeometry.SmoothProperCurve.exists_genus_forall_geometricFibre_riemannRoch_imp_eq_of_finiteMapData
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.122355+00:00
-- url     : https://prove2.me/submissions/4e34d581-a43a-56e4-bcf2-e99413ebf896

import Mathlib
import Definitions.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier
import Definitions.Def_AlgebraicGeometry_SmoothProperCurveBase
import Definitions.Def_AlgebraicCurve_CurveModel
import Definitions.Def_AlgebraicCurve_AdelicIndex
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import Definitions.Def_AlgebraicGeometry_SmoothProperCurveFiniteMapData
import Definitions.Def_AlgebraicGeometry_TwoChartCech
import Definitions.Def_AlgebraicGeometry_CoherentBaseChange
import Definitions.Def_AlgebraicCurve_Repartitions
import Theorems.Thm_TwoChartCech_GrothendieckComplex_nonempty_of_isLocalRing
import Theorems.Thm_AlgebraicCurve_genusFF_eq_of_algEquiv
import Theorems.Thm_AlgebraicGeometry_Scheme_TwoAffineOpenCover_flat_sections_of_flat
import Theorems.Thm_AlgebraicGeometry_Scheme_TwoAffineOpenCover_finrank_cechDiff_baseChange_of_isAlgClosed
import Theorems.Thm_CoherentBaseChange_TwoTermComplex_natCast_finrank_ker_baseChange_sub_natCast_finrank_quotient_range_eq_chi
import Theorems.Thm_AlgebraicCurve_CurveModel_eq_genusFF_of_forall_ell_sub_ell_eq
import Theorems.Thm_AlgebraicCurve_nonempty_algEquiv_functionField_of_iso
import Theorems.Thm_AlgebraicGeometry_SmoothProperCurve_FiniteMapData_finite_H0_H1_lineBundle
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_SmoothProperCurve_exists_genus_forall_geometricFibre_riemannRoch_imp_eq_of_finiteMapData
p2m_attr_erase "instance" "AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupDivisor AlgebraicCurve.Pic0.instModuleZModTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instDistribMulActionTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instSMulTorsion AlgebraicCurve.SemilinearAut.instMulActionSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instSMulCommClassZModTorsion AlgebraicCurve.SemilinearAut.instMulSemiringActionSubtypeProdRingAutMemSubgroup instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions"
p2m_attr_erase "simp" "AlgebraicCurve.coe_cechH0Equiv_apply AlgebraicCurve.cechH1ToH1_mk AlgebraicCurve.lSpaceOn_univ AlgebraicCurve.lSpaceOn_empty AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Divisor.degree_pushforwardAlong"
p2m_attr_erase "simp" "AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.SemilinearAut.toRingAut_inv AlgebraicCurve.SemilinearAut.smul_def AlgebraicCurve.SemilinearAut.smul_single AlgebraicCurve.SemilinearAut.smul_toValuationSubring AlgebraicCurve.SemilinearAut.baseAut_inv AlgebraicCurve.SemilinearAut.baseAut_ofAlgAut AlgebraicCurve.SemilinearAut.toRingAut_ofAlgAut AlgebraicCurve.SemilinearAut.torsionRep_apply AlgebraicCurve.SemilinearAut.toRingAut_one AlgebraicCurve.SemilinearAut.deg_smul AlgebraicCurve.SemilinearAut.degree_smul AlgebraicCurve.SemilinearAut.coe_degZeroSMulHom AlgebraicCurve.SemilinearAut.baseAut_mul AlgebraicCurve.SemilinearAut.coe_smulValuationSubringEquiv_apply AlgebraicCurve.SemilinearAut.baseAut_one AlgebraicCurve.SemilinearAut.ofAlgAut_smul AlgebraicCurve.SemilinearAut.coe_torsion_smul AlgebraicCurve.SemilinearAut.toRingAut_mul AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.jqNModC_one ModularCurve.qExpand_coeff_mul ModularCurve.qExpandₐ_apply ModularCurve.jqN_one ModularCurve.qExpand_single ModularCurve.dedekindPsi_one ModularCurve.ModularPolynomialData.mk.sizeOf_spec ModularCurve.evalAtJ_X ModularCurve.ModularPolynomialData.mk.injEq ModularCurve.constantCoeff_jNum ModularCurve.constantCoeff_eisenstein4 ModularCurve.qExpand_C ModularCurve.coeff_jq_neg_one ModularCurve.constantCoeff_jNumQ ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single"
p2m_attr_erase "simp" "ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq"

set_option autoImplicit false

universe u

open scoped TensorProduct
p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.SmoothProperCurve NeronModelInfra AlgebraicCurve~cechDiff"

theorem BPAux.flat_prod {R : Type u} [CommRing R] {M N : Type u} [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] [Module.Flat R M] [Module.Flat R N] : Module.Flat R (M × N) := by
  rw [Module.Flat.iff_rTensor_injectiveₛ]
  intro P _ _ Q
  have hM : Function.Injective (Q.subtype.rTensor M) :=
    Module.Flat.rTensor_preserves_injective_linearMap _ Q.subtype_injective
  have hN : Function.Injective (Q.subtype.rTensor N) :=
    Module.Flat.rTensor_preserves_injective_linearMap _ Q.subtype_injective
  have key : (TensorProduct.prodRight R R P M N).toLinearMap ∘ₗ (Q.subtype.rTensor (M × N))
      = ((Q.subtype.rTensor M).prodMap (Q.subtype.rTensor N)) ∘ₗ
          (TensorProduct.prodRight R R Q M N).toLinearMap := by
    apply TensorProduct.ext'; intro a mn; simp [TensorProduct.prodRight_tmul]
  intro x y hxy
  have hL : ((TensorProduct.prodRight R R P M N).toLinearMap ∘ₗ (Q.subtype.rTensor (M × N))) x
      = ((TensorProduct.prodRight R R P M N).toLinearMap ∘ₗ (Q.subtype.rTensor (M × N))) y := by
    simp only [LinearMap.comp_apply, hxy]
  rw [key] at hL
  simp only [LinearMap.comp_apply] at hL
  exact (TensorProduct.prodRight R R Q M N).injective ((hM.prodMap hN) hL)

theorem solution
    (R : Type u) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R)) [IsProper c]
    [SmoothOfRelativeDimension 1 c] [GeometricallyIntegral c]
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c) (𝔉 : SmoothProperCurve.FiniteMapData c ε) :
    ∃ g : ℕ, ∀ (k : Type u) [Field k] [IsAlgClosed k] (s : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of R))
      (L : Type u) [Field L] [Algebra k L] (M : CurveModel k L) (e : M.C ≅ pullback c s)
      (_ : e.hom ≫ pullback.snd c s = M.toBase) (Kc : Divisor k L) (g' : ℕ),
      (∀ D : Divisor k L, (ell D : ℤ) - ell (Kc - D) = Divisor.degree D + 1 - g') → g' = g := by
  classical
  let 𝒱 : C.TwoAffineOpenCover := 𝔉.twoAffineOpenCover

  haveI : Module.Flat R (𝒱.cover c).A0 :=
    Scheme.TwoAffineOpenCover.flat_sections_of_flat c 𝒱.U0 𝒱.isAffineOpen_U0
  haveI : Module.Flat R (𝒱.cover c).A1 :=
    Scheme.TwoAffineOpenCover.flat_sections_of_flat c 𝒱.U1 𝒱.isAffineOpen_U1
  haveI : Module.Flat R (𝒱.cover c).A01 :=
    Scheme.TwoAffineOpenCover.flat_sections_of_flat c (𝒱.U0 ⊓ 𝒱.U1) 𝒱.isAffineOpen_inf
  haveI : Module.Flat R ((𝒱.structureSheafSections c).M0 × (𝒱.structureSheafSections c).M1) :=
    BPAux.flat_prod
  haveI : Module.Flat R (𝒱.structureSheafSections c).M01 := inferInstance
  obtain ⟨hfin0, hfin1⟩ :=
    AlgebraicGeometry.SmoothProperCurve.FiniteMapData.finite_H0_H1_lineBundle 𝔉 1
  haveI := hfin0
  haveI := hfin1
  obtain ⟨Γ⟩ := TwoChartCech.GrothendieckComplex.nonempty_of_isLocalRing
    (𝒱.structureSheafSections c).cechDiff
  refine ⟨(1 - Γ.G.chi).toNat, ?_⟩
  intro k _ _ s L _ _ M e he Kc g' hRR

  obtain ⟨f, rfl⟩ : ∃ f : CommRingCat.of R ⟶ CommRingCat.of k, Spec.map f = s :=
    ⟨Spec.preimage s, Spec.map_preimage s⟩
  letI : Algebra R k := f.hom.toAlgebra

  have h1 : g' = genusFF k L := CurveModel.eq_genusFF_of_forall_ell_sub_ell_eq M hRR

  have h2 : genusFF k L = (by
      letI := (baseToFunctionField
        (pullback.snd c (Scheme.TwoAffineOpenCover.specMap R k))).toAlgebra
      exact genusFF k (pullback c (Scheme.TwoAffineOpenCover.specMap R k)).functionField) := by
    letI := M.functionFieldAlgebra
    letI := (baseToFunctionField
      (pullback.snd c (Scheme.TwoAffineOpenCover.specMap R k))).toAlgebra
    obtain ⟨φ⟩ := nonempty_algEquiv_functionField_of_iso M.toBase
      (pullback.snd c (Scheme.TwoAffineOpenCover.specMap R k)) e he
    exact (genusFF_eq_of_algEquiv M.ffAlgEquiv).trans (genusFF_eq_of_algEquiv φ)

  obtain ⟨-, hk0, hk1⟩ :=
    Scheme.TwoAffineOpenCover.finrank_cechDiff_baseChange_of_isAlgClosed 𝒱 c k

  have e0 := LinearEquiv.ofBijective _ (Γ.bijective_kerMap k)
  have e1 := LinearEquiv.ofBijective _ (Γ.bijective_cokerMap k)
  have hchi := CoherentBaseChange.TwoTermComplex.natCast_finrank_ker_baseChange_sub_natCast_finrank_quotient_range_eq_chi Γ.G k
  rw [e0.finrank_eq, e1.finrank_eq, hk0, hk1] at hchi

  rw [h1, h2]
  omega

end S_AlgebraicGeometry_SmoothProperCurve_exists_genus_forall_geometricFibre_riemannRoch_imp_eq_of_finiteMapData
end P2MW
export P2MW.S_AlgebraicGeometry_SmoothProperCurve_exists_genus_forall_geometricFibre_riemannRoch_imp_eq_of_finiteMapData (solution)
