-- Prove2me | solution 1 for AlgebraicCurve.Place.card_fiberAlong_le_finrankAlong_and_iff
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:01.734404+00:00
-- url     : https://prove2.me/submissions/67010250-377d-5c91-8263-9cc5330f53cc

import Definitions.Def_AlgebraicCurve_Correspondence
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Theorems.Thm_AlgebraicCurve_fundamentalIdentityAlong
import Theorems.Thm_AlgebraicCurve_Place_one_le_ramificationIndexAlong
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_Place_card_fiberAlong_le_finrankAlong_and_iff
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy"
p2m_attr_erase "simp" "AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.jqNModC_one ModularCurve.qExpand_coeff_mul ModularCurve.qExpandₐ_apply ModularCurve.jqN_one ModularCurve.qExpand_single ModularCurve.dedekindPsi_one ModularCurve.ModularPolynomialData.mk.sizeOf_spec ModularCurve.evalAtJ_X ModularCurve.ModularPolynomialData.mk.injEq ModularCurve.constantCoeff_jNum ModularCurve.constantCoeff_eisenstein4 ModularCurve.qExpand_C ModularCurve.coeff_jq_neg_one ModularCurve.constantCoeff_jNumQ ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X"
p2m_attr_erase "simp" "ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply"

set_option autoImplicit false

open AlgebraicCurve

theorem solution
    {K F F' : Type*} [Field K] [IsAlgClosed K] [Field F] [Field F'] [Algebra K F] [Algebra K F']
    [IsCurveOver K F] [Algebra.EssFiniteType K F] [IsCurveOver K F'] [Algebra.EssFiniteType K F']
    (φ : F →ₐ[K] F') (hφ : φ.toRingHom.IsIntegral) (hfin : FiniteAlong K φ) (hsep : SeparableAlong K φ)
    (P : Place K F) :
    (Place.fiberAlong φ hφ P).card ≤ finrankAlong K φ ∧
      ((Place.fiberAlong φ hφ P).card = finrankAlong K φ ↔
        ∀ W ∈ Place.fiberAlong φ hφ P, W.ramificationIndexAlong φ = 1) := by
  have hFI := AlgebraicCurve.fundamentalIdentityAlong φ hφ hfin hsep
  letI := algebraAlong φ
  haveI := isScalarTower_along φ
  haveI := isIntegral_along φ hφ
  haveI : FundamentalIdentity K F F' := hFI

  have key := FundamentalIdentity.sum_ramificationIndex_mul_deg (K := K) (F := F) (F' := F') P
  simp only [IsCurveOver.deg_eq_one_of_isAlgClosed, Nat.cast_one, mul_one] at key
  have hsum : ∑ w ∈ Place.fiberAlong φ hφ P, w.ramificationIndexAlong φ = finrankAlong K φ := by
    change ∑ w ∈ P.fiber F', w.ramificationIndex F = Module.finrank F F'
    exact_mod_cast key
  have hone : ∀ w ∈ Place.fiberAlong φ hφ P, 1 ≤ w.ramificationIndexAlong φ :=
    fun w _ => AlgebraicCurve.Place.one_le_ramificationIndexAlong φ hφ w
  have hcard : (Place.fiberAlong φ hφ P).card = ∑ w ∈ Place.fiberAlong φ hφ P, 1 := by
    rw [Finset.card_eq_sum_ones]
  refine ⟨?_, ?_⟩
  · rw [hcard, ← hsum]; exact Finset.sum_le_sum hone
  · rw [hcard, ← hsum, Finset.sum_eq_sum_iff_of_le hone]
    exact ⟨fun h w hw => (h w hw).symm, fun h w hw => (h w hw).symm⟩

end S_AlgebraicCurve_Place_card_fiberAlong_le_finrankAlong_and_iff
end P2MW
export P2MW.S_AlgebraicCurve_Place_card_fiberAlong_le_finrankAlong_and_iff (solution)
