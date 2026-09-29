-- Prove2me | solution 1 for AlgebraicCurve.Place.exists_restrictAlong_eq_of_finiteDimensional_fieldRange
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:01.734404+00:00
-- url     : https://prove2.me/submissions/81fe55ed-cb86-520d-9f36-ac28ebc7d15c

import Definitions.Def_AlgebraicCurve_Correspondence
import Theorems.Thm_AlgebraicCurve_Place_exists_restrict_eq
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_Place_exists_restrictAlong_eq_of_finiteDimensional_fieldRange
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy"
p2m_attr_erase "simp" "AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.jqNModC_one ModularCurve.qExpand_coeff_mul ModularCurve.qExpandₐ_apply ModularCurve.jqN_one ModularCurve.qExpand_single ModularCurve.dedekindPsi_one ModularCurve.ModularPolynomialData.mk.sizeOf_spec ModularCurve.evalAtJ_X ModularCurve.ModularPolynomialData.mk.injEq ModularCurve.constantCoeff_jNum ModularCurve.constantCoeff_eisenstein4 ModularCurve.qExpand_C ModularCurve.coeff_jq_neg_one ModularCurve.constantCoeff_jNumQ ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single"
p2m_attr_erase "simp" "ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply"
set_option autoImplicit false

namespace AlgebraicCurve p2m_export "AlgebraicCurve" "algebraAlong isScalarTower_along isIntegral_along Place Place.exists_restrict_eq" namespace Place p2m_export "AlgebraicCurve.Place" "restrictAlong ext exists_restrict_eq" end AlgebraicCurve.Place
p2m_open_scoped "AlgebraicCurve AlgebraicCurve.Place" in
private theorem AlgebraicCurve.Place.solution_impl
    {K F F' : Type*} [Field K] [Field F] [Field F']
    [Algebra K F] [Algebra K F']
    (φ : F →ₐ[K] F') (hφ : φ.toRingHom.IsIntegral)
    [FiniteDimensional φ.fieldRange F'] [Algebra.IsSeparable φ.fieldRange F']
    (v : AlgebraicCurve.Place K F) :
    ∃ w : AlgebraicCurve.Place K F', w.restrictAlong φ hφ = v := by
  letI := AlgebraicCurve.algebraAlong φ
  haveI := AlgebraicCurve.isScalarTower_along φ
  haveI := AlgebraicCurve.isIntegral_along φ hφ

  let e : F ≃ₐ[K] φ.fieldRange := AlgEquiv.ofInjectiveField φ
  have he : RingHom.comp (algebraMap F F') ((e.symm : φ.fieldRange ≃+* F) : φ.fieldRange →+* F) =
      RingHom.comp ((RingEquiv.refl F' : F' ≃+* F') : F' →+* F') (algebraMap φ.fieldRange F') := by
    refine RingHom.ext fun r => ?_
    show φ (e.symm r) = (r : F')
    have h1 : ((e (e.symm r) : φ.fieldRange) : F') = φ (e.symm r) := rfl
    rw [← h1, e.apply_symm_apply]
  haveI : Module.Finite F F' :=
    Module.Finite.of_equiv_equiv (e.symm : φ.fieldRange ≃+* F) (RingEquiv.refl F') he
  haveI : Algebra.IsSeparable F F' :=
    Algebra.IsSeparable.of_equiv_equiv (e.symm : φ.fieldRange ≃+* F) (RingEquiv.refl F') he
  obtain ⟨W, hW⟩ := AlgebraicCurve.Place.exists_restrict_eq (K := K) (F' := F) (M := F') v
  exact ⟨W, hW⟩

theorem solution {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F'] (φ : F →ₐ[K] F') (hφ : φ.toRingHom.IsIntegral) [FiniteDimensional φ.fieldRange F'] [Algebra.IsSeparable φ.fieldRange F'] (v : AlgebraicCurve.Place K F) :
    ∃ w : AlgebraicCurve.Place K F', w.restrictAlong φ hφ = v :=
  AlgebraicCurve.Place.solution_impl φ hφ v

end S_AlgebraicCurve_Place_exists_restrictAlong_eq_of_finiteDimensional_fieldRange
end P2MW
export P2MW.S_AlgebraicCurve_Place_exists_restrictAlong_eq_of_finiteDimensional_fieldRange (solution)
