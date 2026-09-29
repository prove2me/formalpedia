-- Prove2me | solution 1 for AlgebraicCurve.residueTheorem_functionField_of_smoothOfRelativeDimension_one
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.4153+00:00
-- url     : https://prove2.me/submissions/96589840-730a-5085-8190-29392eb99dca

import Mathlib
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_CurveModel
import Definitions.Def_AlgebraicCurve_WeilOfKaehler
import Definitions.Def_AlgebraicCurve_CanonicalDivisor
import Definitions.Def_AlgebraicCurve_CanonicalLocalResidueInstanceV2
import Theorems.Thm_AlgebraicCurve_residueTheorem_of_perfectField
import Theorems.Thm_AlgebraicCurve_IsCurveOver_exists_separating_transcendental
import Theorems.Thm_AlgebraicCurve_isCurveOver_ratFunc
import Theorems.Thm_AlgebraicCurve_instHasCanonicalDivisorRatFuncPerfectField
import Theorems.Thm_AlgebraicCurve_dCoordGenerates_of_isCurveOver
import Theorems.Thm_AlgebraicCurve_essFiniteType_functionField
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_residueTheorem_functionField_of_smoothOfRelativeDimension_one
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupDivisor AlgebraicCurve.Pic0.instModuleZModTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instDistribMulActionTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instSMulTorsion AlgebraicCurve.SemilinearAut.instMulActionSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instSMulCommClassZModTorsion AlgebraicCurve.SemilinearAut.instMulSemiringActionSubtypeProdRingAutMemSubgroup instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions"
p2m_attr_erase "simp" "AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.SemilinearAut.toRingAut_inv AlgebraicCurve.SemilinearAut.smul_def AlgebraicCurve.SemilinearAut.smul_single AlgebraicCurve.SemilinearAut.smul_toValuationSubring AlgebraicCurve.SemilinearAut.baseAut_inv AlgebraicCurve.SemilinearAut.baseAut_ofAlgAut AlgebraicCurve.SemilinearAut.toRingAut_ofAlgAut AlgebraicCurve.SemilinearAut.torsionRep_apply AlgebraicCurve.SemilinearAut.toRingAut_one AlgebraicCurve.SemilinearAut.deg_smul AlgebraicCurve.SemilinearAut.degree_smul AlgebraicCurve.SemilinearAut.coe_degZeroSMulHom AlgebraicCurve.SemilinearAut.baseAut_mul AlgebraicCurve.SemilinearAut.coe_smulValuationSubringEquiv_apply AlgebraicCurve.SemilinearAut.baseAut_one AlgebraicCurve.SemilinearAut.ofAlgAut_smul"
p2m_attr_erase "simp" "AlgebraicCurve.SemilinearAut.coe_torsion_smul AlgebraicCurve.SemilinearAut.toRingAut_mul AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.jqNModC_one ModularCurve.qExpand_coeff_mul ModularCurve.qExpandₐ_apply ModularCurve.jqN_one ModularCurve.qExpand_single ModularCurve.dedekindPsi_one ModularCurve.ModularPolynomialData.mk.sizeOf_spec ModularCurve.evalAtJ_X ModularCurve.ModularPolynomialData.mk.injEq ModularCurve.constantCoeff_jNum ModularCurve.constantCoeff_eisenstein4 ModularCurve.qExpand_C ModularCurve.coeff_jq_neg_one ModularCurve.constantCoeff_jNumQ ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq"
p2m_attr_erase "simp" "AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq"

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry IntermediateField

namespace FFP

theorem essFiniteType_ratFunc (K : Type*) [Field K] : Algebra.EssFiniteType K (RatFunc K) :=
  haveI : Algebra.EssFiniteType (Polynomial K) (RatFunc K) :=
    Algebra.EssFiniteType.of_isLocalization _ (nonZeroDivisors (Polynomial K))
  Algebra.EssFiniteType.comp K (Polynomial K) (RatFunc K)

theorem residueTheorem_of_isCurveOver (K F : Type*) [Field K] [PerfectField K] [Field F] [Algebra K F]
    [Algebra.EssFiniteType K F] [AlgebraicCurve.IsCurveOver K F]
    [AlgebraicCurve.HasCanonicalDivisor (K := K) (F := F)] [∀ w : AlgebraicCurve.Place K F, w.DCoordGenerates] :
    AlgebraicCurve.ResidueTheorem K F := by
  classical

  obtain ⟨t, ht, hfd, hsep⟩ := AlgebraicCurve.IsCurveOver.exists_separating_transcendental (K := K) (F := F)
  let e : RatFunc K ≃ₐ[K] K⟮t⟯ := RatFunc.algEquivOfTranscendental t ht
  letI : Algebra (RatFunc K) F := ((algebraMap (K⟮t⟯) F).comp e.toAlgHom.toRingHom).toAlgebra
  have halg : ∀ x : RatFunc K, algebraMap (RatFunc K) F x = algebraMap (K⟮t⟯) F (e x) := fun _ => rfl
  haveI : IsScalarTower K (RatFunc K) F := IsScalarTower.of_algebraMap_eq fun a => by
    rw [halg, AlgEquiv.commutes, ← IsScalarTower.algebraMap_apply]
  have he : (algebraMap (RatFunc K) F).comp (↑e.symm.toRingEquiv : K⟮t⟯ →+* RatFunc K) =
      (↑(RingEquiv.refl F) : F →+* F).comp (algebraMap (K⟮t⟯) F) := by
    ext x
    simp only [RingHom.comp_apply, RingEquiv.coe_toRingHom, RingEquiv.refl_apply]
    rw [halg]
    exact congrArg (algebraMap (K⟮t⟯) F) (e.apply_symm_apply x)
  haveI : Module.Finite (RatFunc K) F := Module.Finite.of_equiv_equiv e.symm.toRingEquiv (RingEquiv.refl F) he
  haveI : Algebra.IsSeparable (RatFunc K) F := Algebra.IsSeparable.of_equiv_equiv e.symm.toRingEquiv (RingEquiv.refl F) he
  haveI : Algebra.IsIntegral (RatFunc K) F := Algebra.IsIntegral.of_finite (RatFunc K) F

  haveI : AlgebraicCurve.IsCurveOver K (RatFunc K) := AlgebraicCurve.isCurveOver_ratFunc K
  haveI : AlgebraicCurve.HasCanonicalDivisor (K := K) (F := RatFunc K) :=
    AlgebraicCurve.instHasCanonicalDivisorRatFuncPerfectField K
  haveI : Algebra.EssFiniteType K (RatFunc K) := essFiniteType_ratFunc K
  haveI : ∀ v : AlgebraicCurve.Place K (RatFunc K), v.DCoordGenerates := AlgebraicCurve.dCoordGenerates_of_isCurveOver
  exact @AlgebraicCurve.residueTheorem_of_perfectField K F _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _

end FFP

theorem solution
    {k : Type u} [Field k] [PerfectField k] {X : Scheme.{u}}
    (c : X ⟶ Spec (CommRingCat.of k)) [IsIntegral X] [SmoothOfRelativeDimension 1 c] :
    letI := (AlgebraicCurve.baseToFunctionField c).toAlgebra
    ∀ [AlgebraicCurve.IsCurveOver k X.functionField]
      [∀ v : AlgebraicCurve.Place k X.functionField, v.DCoordGenerates]
      [AlgebraicCurve.HasCanonicalDivisor (K := k) (F := X.functionField)],
      AlgebraicCurve.ResidueTheorem k X.functionField := by
  letI := (AlgebraicCurve.baseToFunctionField c).toAlgebra
  intro _ _ _
  haveI : Smooth c := SmoothOfRelativeDimension.smooth 1 c
  haveI : Algebra.EssFiniteType k X.functionField := AlgebraicCurve.essFiniteType_functionField c
  exact @FFP.residueTheorem_of_isCurveOver k X.functionField _ _ _ _ _ _ _ _

end S_AlgebraicCurve_residueTheorem_functionField_of_smoothOfRelativeDimension_one
end P2MW
export P2MW.S_AlgebraicCurve_residueTheorem_functionField_of_smoothOfRelativeDimension_one (solution)
