-- Prove2me | solution 1 for AlgebraicCurve.hasPrincipalDivisors_adjoin_of_transcendental
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.4153+00:00
-- url     : https://prove2.me/submissions/38904e51-cb4d-538f-a36c-844c17b83510

import Definitions.Def_AlgebraicCurve_PlacesOverDVR
import Theorems.Thm_AlgebraicCurve_hasPrincipalDivisors_of_transcendental
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_hasPrincipalDivisors_adjoin_of_transcendental
p2m_attr_erase "instance" "AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupDivisor AlgebraicCurve.Pic0.instModuleZModTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instDistribMulActionTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instSMulTorsion AlgebraicCurve.SemilinearAut.instMulActionSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instSMulCommClassZModTorsion AlgebraicCurve.SemilinearAut.instMulSemiringActionSubtypeProdRingAutMemSubgroup instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy"
p2m_attr_erase "simp" "AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.SemilinearAut.toRingAut_inv AlgebraicCurve.SemilinearAut.smul_def AlgebraicCurve.SemilinearAut.smul_single AlgebraicCurve.SemilinearAut.smul_toValuationSubring AlgebraicCurve.SemilinearAut.baseAut_inv AlgebraicCurve.SemilinearAut.baseAut_ofAlgAut AlgebraicCurve.SemilinearAut.toRingAut_ofAlgAut AlgebraicCurve.SemilinearAut.torsionRep_apply AlgebraicCurve.SemilinearAut.toRingAut_one AlgebraicCurve.SemilinearAut.deg_smul AlgebraicCurve.SemilinearAut.degree_smul AlgebraicCurve.SemilinearAut.coe_degZeroSMulHom AlgebraicCurve.SemilinearAut.baseAut_mul AlgebraicCurve.SemilinearAut.coe_smulValuationSubringEquiv_apply AlgebraicCurve.SemilinearAut.baseAut_one AlgebraicCurve.SemilinearAut.ofAlgAut_smul"
p2m_attr_erase "simp" "AlgebraicCurve.SemilinearAut.coe_torsion_smul AlgebraicCurve.SemilinearAut.toRingAut_mul AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.jqNModC_one ModularCurve.qExpand_coeff_mul ModularCurve.qExpandₐ_apply ModularCurve.jqN_one ModularCurve.qExpand_single ModularCurve.dedekindPsi_one ModularCurve.ModularPolynomialData.mk.sizeOf_spec ModularCurve.evalAtJ_X ModularCurve.ModularPolynomialData.mk.injEq ModularCurve.constantCoeff_jNum ModularCurve.constantCoeff_eisenstein4 ModularCurve.qExpand_C ModularCurve.coeff_jq_neg_one ModularCurve.constantCoeff_jNumQ ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply"

noncomputable section
open IntermediateField

namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "HasPrincipalDivisors hasPrincipalDivisors_of_transcendental"
p2m_open "AlgebraicCurve"
namespace W2

variable (K : Type*) [Field K] [CharZero K] {LF : Type*} [Field LF] [Algebra K LF]

theorem hasPrincipalDivisors_adjoin (x : LF) (hx : Transcendental K x) (T : Finset LF)
    (hT : ∀ t ∈ T, IsIntegral (IntermediateField.adjoin K ({x} : Set LF)) t) :
    HasPrincipalDivisors K (IntermediateField.adjoin K (insert x (T : Set LF))) := by
  set F : IntermediateField K LF := IntermediateField.adjoin K (insert x (T : Set LF)) with hF
  have hxF : x ∈ F := subset_adjoin K _ (Set.mem_insert x _)
  have hTF : ∀ t ∈ T, t ∈ F := fun t ht => subset_adjoin K _ (Set.mem_insert_of_mem x ht)
  set x' : F := ⟨x, hxF⟩ with hx'

  have hx't : Transcendental K x' :=
    (transcendental_algebraMap_iff (R := K) (S := F) (A := LF) Subtype.val_injective).mp hx

  set A : IntermediateField K F := IntermediateField.adjoin K ({x'} : Set F) with hA
  have hliftA : lift A = IntermediateField.adjoin K ({x} : Set LF) := by
    rw [hA, lift_adjoin_simple]

  let e : A ≃ₐ[K] IntermediateField.adjoin K ({x} : Set LF) :=
    (liftAlgEquiv A).trans (equivOfEq hliftA)
  have he : ∀ a : A, ((e a : IntermediateField.adjoin K ({x} : Set LF)) : LF) = ((a : F) : LF) := by
    intro a; rfl

  have hint : ∀ t (ht : t ∈ T), IsIntegral A (⟨t, hTF t ht⟩ : F) := by
    intro t ht

    have h1 : IsIntegral A (t : LF) := by
      refine (hT t ht).map_of_comp_eq (R := IntermediateField.adjoin K ({x} : Set LF)) (S := LF) (T := A) (U := LF)
        (e.symm : IntermediateField.adjoin K ({x} : Set LF) →+* A) (RingHom.id LF) ?_
      ext b
      change (((e.symm b : A) : F) : LF) = ((b : IntermediateField.adjoin K ({x} : Set LF)) : LF)
      rw [← he (e.symm b), AlgEquiv.apply_symm_apply]
    exact (isIntegral_algHom_iff (IsScalarTower.toAlgHom A F LF) Subtype.val_injective).mp h1

  haveI : FiniteDimensional A F := by
    set T' : Set F := (fun t : T => (⟨(t : LF), hTF t t.2⟩ : F)) '' Set.univ with hT'
    haveI : Finite T' := Set.Finite.to_subtype ((Set.finite_univ).image _)
    have hT'int : ∀ y ∈ T', IsIntegral A y := by
      rintro _ ⟨t, -, rfl⟩; exact hint t t.2
    haveI : FiniteDimensional A (IntermediateField.adjoin A T') := finiteDimensional_adjoin hT'int

    have htop : IntermediateField.adjoin A T' = ⊤ := by
      apply restrictScalars_injective K
      rw [restrictScalars_adjoin, restrictScalars_top]
      apply lift_injective
      rw [lift_top, lift_adjoin]
      apply le_antisymm (adjoin_le_iff.mpr ?_) ?_
      · rintro _ ⟨y, hy, rfl⟩; exact y.2
      · show IntermediateField.adjoin K (insert x (T : Set LF)) ≤ _
        apply adjoin.mono
        intro z hz
        rcases hz with rfl | hz
        · exact ⟨x', Or.inl (subset_adjoin K _ (Set.mem_singleton _)), rfl⟩
        · exact ⟨⟨z, hTF z hz⟩, Or.inr ⟨⟨z, hz⟩, Set.mem_univ _, rfl⟩, rfl⟩
    rw [htop] at this
    exact LinearEquiv.finiteDimensional (IntermediateField.topEquiv (F := A) (E := F)).toLinearEquiv
  exact hasPrincipalDivisors_of_transcendental K x' hx't

end W2
end AlgebraicCurve

p2m_open "AlgebraicCurve P2MW.S_AlgebraicCurve_hasPrincipalDivisors_adjoin_of_transcendental.AlgebraicCurve"

theorem solution (K : Type*) [Field K] [CharZero K] {LF : Type*} [Field LF] [Algebra K LF]
    (x : LF) (hx : Transcendental K x) (T : Finset LF)
    (hT : ∀ t ∈ T, IsIntegral (IntermediateField.adjoin K ({x} : Set LF)) t) :
    HasPrincipalDivisors K (IntermediateField.adjoin K (insert x (T : Set LF))) :=
  AlgebraicCurve.W2.hasPrincipalDivisors_adjoin K x hx T hT

end

end S_AlgebraicCurve_hasPrincipalDivisors_adjoin_of_transcendental
end P2MW
export P2MW.S_AlgebraicCurve_hasPrincipalDivisors_adjoin_of_transcendental (solution)
