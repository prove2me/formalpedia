-- Prove2me | solution 1 for AlgebraicCurve.Pic0.exists_mk_eq_forall_notMem_support
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:01.734404+00:00
-- url     : https://prove2.me/submissions/51794e05-8b1f-5850-a239-92b955c5c9d3

import Theorems.Thm_AlgebraicCurve_Place_exists_forall_ord_eq_finset
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_Pic0_exists_mk_eq_forall_notMem_support
p2m_attr_erase "instance" "AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupDivisor AlgebraicCurve.Pic0.instModuleZModTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instDistribMulActionTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instSMulTorsion AlgebraicCurve.SemilinearAut.instMulActionSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instSMulCommClassZModTorsion AlgebraicCurve.SemilinearAut.instMulSemiringActionSubtypeProdRingAutMemSubgroup instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy"
p2m_attr_erase "simp" "AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.SemilinearAut.toRingAut_inv AlgebraicCurve.SemilinearAut.smul_def AlgebraicCurve.SemilinearAut.smul_single AlgebraicCurve.SemilinearAut.smul_toValuationSubring AlgebraicCurve.SemilinearAut.baseAut_inv AlgebraicCurve.SemilinearAut.baseAut_ofAlgAut AlgebraicCurve.SemilinearAut.toRingAut_ofAlgAut"
p2m_attr_erase "simp" "AlgebraicCurve.SemilinearAut.torsionRep_apply AlgebraicCurve.SemilinearAut.toRingAut_one AlgebraicCurve.SemilinearAut.deg_smul AlgebraicCurve.SemilinearAut.degree_smul AlgebraicCurve.SemilinearAut.coe_degZeroSMulHom AlgebraicCurve.SemilinearAut.baseAut_mul AlgebraicCurve.SemilinearAut.coe_smulValuationSubringEquiv_apply AlgebraicCurve.SemilinearAut.baseAut_one AlgebraicCurve.SemilinearAut.ofAlgAut_smul AlgebraicCurve.SemilinearAut.coe_torsion_smul AlgebraicCurve.SemilinearAut.toRingAut_mul AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.jqNModC_one ModularCurve.qExpand_coeff_mul ModularCurve.qExpandₐ_apply ModularCurve.jqN_one ModularCurve.qExpand_single ModularCurve.dedekindPsi_one ModularCurve.ModularPolynomialData.mk.sizeOf_spec ModularCurve.evalAtJ_X ModularCurve.ModularPolynomialData.mk.injEq ModularCurve.constantCoeff_jNum ModularCurve.constantCoeff_eisenstein4 ModularCurve.qExpand_C ModularCurve.coeff_jq_neg_one ModularCurve.constantCoeff_jNumQ ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply"

set_option Elab.async false

set_option autoImplicit false

noncomputable section

namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "Place.exists_forall_ord_eq_finset Place Divisor Divisor.degZero Divisor.mem_degZero Divisor.principal Divisor.mem_principal HasPrincipalDivisors Pic Pic0 Pic0.mk Pic0.mk_surjective HasPrincipalDivisors.exists_divisor"
p2m_open "AlgebraicCurve"

namespace WC1bSolMV

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

theorem exists_mk_eq_forall_notMem [HasPrincipalDivisors K F]
    (x : Pic0 K F) (S : Finset (Place K F)) :
    ∃ D : Divisor.degZero (K := K) (F := F),
      Pic0.mk D = x ∧ ∀ v ∈ (D : Divisor K F).support, v ∉ S := by
  classical

  obtain ⟨D₀, hD₀⟩ := Pic0.mk_surjective x

  obtain ⟨g, hg0, hgord⟩ := AlgebraicCurve.Place.exists_forall_ord_eq_finset (K := K) S (fun v => (D₀ : Divisor K F) v)

  obtain ⟨E, hEord, hEdeg⟩ := HasPrincipalDivisors.exists_divisor (K := K) (F := F) g hg0
  set E' : Divisor.degZero (K := K) (F := F) := ⟨E, Divisor.mem_degZero.mpr hEdeg⟩ with hE'
  have hEprin : E' ∈ (Divisor.principal (K := K) (F := F)).addSubgroupOf
      (Divisor.degZero (K := K) (F := F)) := by
    rw [AddSubgroup.mem_addSubgroupOf]
    exact Divisor.mem_principal.mpr ⟨g, hg0, fun v => hEord v⟩

  refine ⟨D₀ - E', ?_, ?_⟩
  · have hmkE : Pic0.mk E' = 0 := (QuotientAddGroup.eq_zero_iff E').mpr hEprin
    show QuotientAddGroup.mk (D₀ - E') = x
    rw [QuotientAddGroup.mk_sub, ← hD₀]
    show Pic0.mk D₀ - Pic0.mk E' = Pic0.mk D₀
    rw [hmkE, sub_zero]
  · intro v hv hvS
    refine (Finsupp.mem_support_iff.mp hv) ?_
    show (D₀ : Divisor K F) v - E v = 0
    rw [hEord v, hgord v hvS, sub_self]

end WC1bSolMV

end AlgebraicCurve

open _root_.AlgebraicCurve _root_.P2MW.S_AlgebraicCurve_Pic0_exists_mk_eq_forall_notMem_support.AlgebraicCurve in
theorem solution {K F : Type*} [Field K] [Field F] [Algebra K F] [HasPrincipalDivisors K F] (x : Pic0 K F) (S : Finset (Place K F)) :
    ∃ D : Divisor.degZero (K := K) (F := F), Pic0.mk D = x ∧ ∀ v ∈ (D : Divisor K F).support, v ∉ S :=
  AlgebraicCurve.WC1bSolMV.exists_mk_eq_forall_notMem x S

end

end S_AlgebraicCurve_Pic0_exists_mk_eq_forall_notMem_support
end P2MW
export P2MW.S_AlgebraicCurve_Pic0_exists_mk_eq_forall_notMem_support (solution)
