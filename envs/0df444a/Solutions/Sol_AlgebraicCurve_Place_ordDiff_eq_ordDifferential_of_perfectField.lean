-- Prove2me | solution 1 for AlgebraicCurve.Place.ordDiff_eq_ordDifferential_of_perfectField
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.4153+00:00
-- url     : https://prove2.me/submissions/f633f63b-5b23-56b2-a88b-772dac9b0c59

import Definitions.Def_AlgebraicCurve_Differentials
import Definitions.Def_ModularCurve_CanonicalDivisor
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_RegularDifferentials
import Theorems.Thm_AlgebraicCurve_IsCurveOver_exists_separating_transcendental
import Theorems.Thm_AlgebraicCurve_dCoordGenerates_of_isCurveOver
import Theorems.Thm_AlgebraicCurve_Place_diffCoeff_smul_D_of_ord_eq_one
import Theorems.Thm_AlgebraicCurve_Place_diffCoeff_smul_D_eq_of_ord_eq_one
import Theorems.Thm_AlgebraicCurve_Place_ord_diffCoeff_D_nonneg_of_perfectField
import Theorems.Thm_AlgebraicCurve_Place_ordDiff_zero_of_perfectField
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_Place_ordDiff_eq_ordDifferential_of_perfectField
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupDivisor AlgebraicCurve.Pic0.instModuleZModTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instDistribMulActionTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instSMulTorsion AlgebraicCurve.SemilinearAut.instMulActionSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instSMulCommClassZModTorsion AlgebraicCurve.SemilinearAut.instMulSemiringActionSubtypeProdRingAutMemSubgroup instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy"
p2m_attr_erase "simp" "AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.SemilinearAut.toRingAut_inv AlgebraicCurve.SemilinearAut.smul_def"
p2m_attr_erase "simp" "AlgebraicCurve.SemilinearAut.smul_single AlgebraicCurve.SemilinearAut.smul_toValuationSubring AlgebraicCurve.SemilinearAut.baseAut_inv AlgebraicCurve.SemilinearAut.baseAut_ofAlgAut AlgebraicCurve.SemilinearAut.toRingAut_ofAlgAut AlgebraicCurve.SemilinearAut.torsionRep_apply AlgebraicCurve.SemilinearAut.toRingAut_one AlgebraicCurve.SemilinearAut.deg_smul AlgebraicCurve.SemilinearAut.degree_smul AlgebraicCurve.SemilinearAut.coe_degZeroSMulHom AlgebraicCurve.SemilinearAut.baseAut_mul AlgebraicCurve.SemilinearAut.coe_smulValuationSubringEquiv_apply AlgebraicCurve.SemilinearAut.baseAut_one AlgebraicCurve.SemilinearAut.ofAlgAut_smul AlgebraicCurve.SemilinearAut.coe_torsion_smul AlgebraicCurve.SemilinearAut.toRingAut_mul AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.jqNModC_one ModularCurve.qExpand_coeff_mul ModularCurve.qExpandₐ_apply ModularCurve.jqN_one ModularCurve.qExpand_single ModularCurve.dedekindPsi_one ModularCurve.ModularPolynomialData.mk.sizeOf_spec ModularCurve.evalAtJ_X ModularCurve.ModularPolynomialData.mk.injEq ModularCurve.constantCoeff_jNum ModularCurve.constantCoeff_eisenstein4 ModularCurve.qExpand_C ModularCurve.coeff_jq_neg_one ModularCurve.constantCoeff_jNumQ ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen"
p2m_attr_erase "simp" "ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply"

set_option autoImplicit false

noncomputable section

open KaehlerDifferential

namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "Place.diffCoeff Place Place.ordDifferential IsCurveOver IsCurveOver.exists_separating_transcendental dCoordGenerates_of_isCurveOver Place.diffCoeff_smul_D_of_ord_eq_one Place.diffCoeff_smul_D_eq_of_ord_eq_one Place.ord_diffCoeff_D_nonneg_of_perfectField Place.ordDiff_zero_of_perfectField"
p2m_open "AlgebraicCurve"

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

namespace Place
p2m_export "AlgebraicCurve.Place" "diffCoeff ordDiff ordDiff_def ord_uniformizer_alt uniformizer_alt ord ord_zero ord_one ord_mul DCoordGenerates differentialCoeff differentialCoeff_smul_dCoord differentialCoeff_zero ordDifferential exists_ord_eq_one_and_dCoord_eq diffCoeff_smul_D_of_ord_eq_one diffCoeff_smul_D_eq_of_ord_eq_one ord_diffCoeff_D_nonneg_of_perfectField ordDiff_zero_of_perfectField"
p2m_open "AlgebraicCurve.Place"

variable (v : Place K F)

private theorem seamAux_coeff_ne_zero [v.DCoordGenerates] {ω : Ω[F⁄K]} (hω : ω ≠ 0) :
    v.differentialCoeff ω ≠ 0 := by
  intro h
  apply hω
  rw [← v.differentialCoeff_smul_dCoord ω, h, zero_smul]

end Place

private theorem seamAux_ordDiff_eq_ordDifferential
    [PerfectField K] [Algebra.EssFiniteType K F] [IsCurveOver K F]
    (v : Place K F) (ω : Ω[F⁄K]) :
    v.ordDiff ω = v.ordDifferential ω := by
  obtain ⟨s, -, hfd, -⟩ := IsCurveOver.exists_separating_transcendental (K := K) (F := F)
  haveI : FiniteDimensional (IntermediateField.adjoin K ({s} : Set F)) F := hfd
  haveI : ∀ w : Place K F, w.DCoordGenerates := dCoordGenerates_of_isCurveOver
  obtain ⟨π, hπ, hd⟩ := v.exists_ord_eq_one_and_dCoord_eq
  have ht : v.ord v.uniformizer_alt = 1 := v.ord_uniformizer_alt ⟨π, hπ⟩
  rcases eq_or_ne ω 0 with rfl | hω
  · rw [Place.ordDiff_zero_of_perfectField s v, Place.ordDifferential, v.differentialCoeff_zero,
      v.ord_zero]
  have hf : v.differentialCoeff ω • D K F π = ω := by
    rw [← hd]
    exact v.differentialCoeff_smul_dCoord ω
  have hf0 : v.differentialCoeff ω ≠ 0 := Place.seamAux_coeff_ne_zero v hω
  have hc : Place.diffCoeff v.uniformizer_alt (D K F π) • D K F v.uniformizer_alt = D K F π :=
    Place.diffCoeff_smul_D_of_ord_eq_one s v ht (D K F π)
  have hc' : Place.diffCoeff π (D K F v.uniformizer_alt) • D K F π = D K F v.uniformizer_alt :=
    Place.diffCoeff_smul_D_of_ord_eq_one s v hπ (D K F v.uniformizer_alt)
  have hcc' : Place.diffCoeff v.uniformizer_alt (D K F π) * Place.diffCoeff π (D K F v.uniformizer_alt) = 1 := by
    have h1 := Place.diffCoeff_smul_D_eq_of_ord_eq_one s v hπ
      (Place.diffCoeff v.uniformizer_alt (D K F π) * Place.diffCoeff π (D K F v.uniformizer_alt))
    rw [mul_smul, hc', hc] at h1
    have h2 := Place.diffCoeff_smul_D_eq_of_ord_eq_one s v hπ (1 : F)
    rw [one_smul] at h2
    exact h1.symm.trans h2
  have hcn : 0 ≤ v.ord (Place.diffCoeff v.uniformizer_alt (D K F π)) :=
    Place.ord_diffCoeff_D_nonneg_of_perfectField s v ht (by rw [hπ]; norm_num)
  have hc'n : 0 ≤ v.ord (Place.diffCoeff π (D K F v.uniformizer_alt)) :=
    Place.ord_diffCoeff_D_nonneg_of_perfectField s v hπ (by rw [ht]; norm_num)
  have hc0 : Place.diffCoeff v.uniformizer_alt (D K F π) ≠ 0 := left_ne_zero_of_mul_eq_one hcc'
  have hc'0 : Place.diffCoeff π (D K F v.uniformizer_alt) ≠ 0 := right_ne_zero_of_mul_eq_one hcc'
  have hsum := v.ord_mul hc0 hc'0
  rw [hcc', v.ord_one] at hsum
  have hcz : v.ord (Place.diffCoeff v.uniformizer_alt (D K F π)) = 0 := by omega
  have hω' : (v.differentialCoeff ω * Place.diffCoeff v.uniformizer_alt (D K F π)) • D K F v.uniformizer_alt
      = ω := by
    rw [mul_smul, hc, hf]
  have hcoef := Place.diffCoeff_smul_D_eq_of_ord_eq_one s v ht
    (v.differentialCoeff ω * Place.diffCoeff v.uniformizer_alt (D K F π))
  rw [hω'] at hcoef
  rw [Place.ordDifferential, v.ordDiff_def, hcoef, v.ord_mul hf0 hc0, hcz, add_zero]

end AlgebraicCurve

end

theorem solution {K F : Type*} [Field K]
    [Field F] [Algebra K F] [PerfectField K] [Algebra.EssFiniteType K F]
    [AlgebraicCurve.IsCurveOver K F] (v : AlgebraicCurve.Place K F) (ω : Ω[F⁄K]) :
    v.ordDiff ω = v.ordDifferential ω :=
  AlgebraicCurve.seamAux_ordDiff_eq_ordDifferential v ω

end S_AlgebraicCurve_Place_ordDiff_eq_ordDifferential_of_perfectField
end P2MW
export P2MW.S_AlgebraicCurve_Place_ordDiff_eq_ordDifferential_of_perfectField (solution)
