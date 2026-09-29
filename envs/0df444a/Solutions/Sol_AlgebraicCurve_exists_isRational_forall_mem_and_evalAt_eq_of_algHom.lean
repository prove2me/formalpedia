-- Prove2me | solution 1 for AlgebraicCurve.exists_isRational_forall_mem_and_evalAt_eq_of_algHom
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.4153+00:00
-- url     : https://prove2.me/submissions/3575261d-a0d2-5990-aec0-5f7e3c6fdcda

import Mathlib
import Definitions.Def_AlgebraicCurve_PlaceEvaluation
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_PlacesOverDVR
import Theorems.Thm_AlgebraicCurve_isCurveOver_iff_exists_transcendental_finiteDimensional
import Theorems.Thm_AlgebraicCurve_Place_exists_of_valuationSubring_of_finiteDimensional
import Theorems.Thm_AlgebraicCurve_Place_isRational_iff_deg_eq_one
import Theorems.Thm_AlgebraicCurve_Place_evalAt_congr
import Theorems.Thm_AlgebraicCurve_Place_evalAt_algebraMap
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_exists_isRational_forall_mem_and_evalAt_eq_of_algHom
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupDivisor AlgebraicCurve.Pic0.instModuleZModTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instDistribMulActionTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instSMulTorsion AlgebraicCurve.SemilinearAut.instMulActionSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instSMulCommClassZModTorsion AlgebraicCurve.SemilinearAut.instMulSemiringActionSubtypeProdRingAutMemSubgroup instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions"
p2m_attr_erase "simp" "AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.SemilinearAut.toRingAut_inv AlgebraicCurve.SemilinearAut.smul_def AlgebraicCurve.SemilinearAut.smul_single AlgebraicCurve.SemilinearAut.smul_toValuationSubring AlgebraicCurve.SemilinearAut.baseAut_inv AlgebraicCurve.SemilinearAut.baseAut_ofAlgAut AlgebraicCurve.SemilinearAut.toRingAut_ofAlgAut AlgebraicCurve.SemilinearAut.torsionRep_apply AlgebraicCurve.SemilinearAut.toRingAut_one AlgebraicCurve.SemilinearAut.deg_smul AlgebraicCurve.SemilinearAut.degree_smul AlgebraicCurve.SemilinearAut.coe_degZeroSMulHom AlgebraicCurve.SemilinearAut.baseAut_mul AlgebraicCurve.SemilinearAut.coe_smulValuationSubringEquiv_apply AlgebraicCurve.SemilinearAut.baseAut_one AlgebraicCurve.SemilinearAut.ofAlgAut_smul"
p2m_attr_erase "simp" "AlgebraicCurve.SemilinearAut.coe_torsion_smul AlgebraicCurve.SemilinearAut.toRingAut_mul AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.jqNModC_one ModularCurve.qExpand_coeff_mul ModularCurve.qExpandₐ_apply ModularCurve.jqN_one ModularCurve.qExpand_single ModularCurve.dedekindPsi_one ModularCurve.ModularPolynomialData.mk.sizeOf_spec ModularCurve.evalAtJ_X ModularCurve.ModularPolynomialData.mk.injEq ModularCurve.constantCoeff_jNum ModularCurve.constantCoeff_eisenstein4 ModularCurve.qExpand_C ModularCurve.coeff_jq_neg_one ModularCurve.constantCoeff_jNumQ ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none"

set_option autoImplicit false

open AlgebraicCurve IsLocalRing

theorem solution
    {L : Type*} [Field L] [IsAlgClosed L]
    {F : Type*} [Field F] [Algebra L F] [IsCurveOver L F] [Algebra.EssFiniteType L F]
    (B : Subalgebra L F) (χ : B →ₐ[L] L)
    (hB : ∃ z : B, (z : F) ∉ Set.range (algebraMap L F)) :
    ∃ P : Place L F, P.IsRational ∧
      ∀ z : B, (z : F) ∈ P.toValuationSubring ∧ P.evalAt (z : F) = χ z := by
  classical
  obtain ⟨z₀, hz₀⟩ := hB

  let I : Ideal ↥B.toSubring := RingHom.ker (χ.toRingHom : ↥B →+* L)
  have hI : I ≠ ⊤ := RingHom.ker_ne_top (χ.toRingHom : ↥B →+* L)
  obtain ⟨V, hBV, hIV⟩ := Ideal.image_subset_nonunits_valuationSubring I hI
  have hmemI : ∀ z : B, ((z : F) - algebraMap L F (χ z)) ∈ V.nonunits := by
    intro z
    refine hIV ⟨⟨(z : F) - algebraMap L F (χ z), B.sub_mem z.2 (B.algebraMap_mem (χ z))⟩, ?_, rfl⟩
    show (⟨(z : F) - algebraMap L F (χ z), _⟩ : ↥B) ∈ RingHom.ker (χ.toRingHom : ↥B →+* L)
    rw [RingHom.mem_ker]
    show χ (z - algebraMap L (↥B) (χ z)) = 0
    rw [map_sub, AlgHom.commutes]
    simp

  have hVL : ∀ a : L, algebraMap L F a ∈ V := fun a => hBV (B.algebraMap_mem a)
  have hne0 : (z₀ : F) - algebraMap L F (χ z₀) ≠ 0 := fun e => hz₀ ⟨χ z₀, (sub_eq_zero.mp e).symm⟩
  have hVtop : V ≠ ⊤ := by
    intro h
    rcases (ValuationSubring.mem_nonunits_iff_or V).mp (hmemI z₀) with h0 | hinv
    · exact hne0 h0
    · exact hinv (h.symm ▸ ValuationSubring.mem_top _)

  obtain ⟨t, -, hfd, -⟩ :=
    (AlgebraicCurve.isCurveOver_iff_exists_transcendental_finiteDimensional (K := L) (F := F)).mp inferInstance
  haveI := hfd
  obtain ⟨P, hP⟩ := AlgebraicCurve.Place.exists_of_valuationSubring_of_finiteDimensional t V hVL hVtop
  subst hP
  have hrat : P.IsRational := (Place.isRational_iff_deg_eq_one P).mpr (IsCurveOver.deg_eq_one_of_isAlgClosed P)
  refine ⟨P, hrat, fun z => ?_⟩
  have hzV : (z : F) ∈ P.toValuationSubring := hBV z.2
  refine ⟨hzV, ?_⟩
  by_cases hz : (z : F) - algebraMap L F (χ z) = 0
  · rw [sub_eq_zero.mp hz, Place.evalAt_algebraMap]
  · have hmem : (z : F) - algebraMap L F (χ z) ∈ P.toValuationSubring :=
      P.toValuationSubring.sub_mem hzV (P.algebraMap_mem' (χ z))
    have hmax : (⟨_, hmem⟩ : P.toValuationSubring) ∈ maximalIdeal P.toValuationSubring :=
      ValuationSubring.coe_mem_nonunits_iff.mp (hmemI z)
    have hpos : 0 < P.ord ((z : F) - algebraMap L F (χ z)) :=
      (Place.mem_maximalIdeal_iff_ord_pos P hz hmem).mp hmax
    rw [P.evalAt_congr hzV (P.algebraMap_mem' (χ z)) (Or.inr hpos), Place.evalAt_algebraMap]

#print axioms solution

end S_AlgebraicCurve_exists_isRational_forall_mem_and_evalAt_eq_of_algHom
end P2MW
export P2MW.S_AlgebraicCurve_exists_isRational_forall_mem_and_evalAt_eq_of_algHom (solution)
