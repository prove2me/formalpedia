-- Prove2me | solution 1 for AlgebraicCurve.exists_mem_lSpaceOn_adicValuation_eq_of_riemannGenusReachedAt
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.4153+00:00
-- url     : https://prove2.me/submissions/a0f4f896-6846-5370-a669-3b9b4c2adca7

import Mathlib
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Definitions.Def_AlgebraicCurve_Repartitions
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_AdelicIndex
import Definitions.Def_AlgebraicCurve_CechSectionsOfDivisor
import Theorems.Thm_AlgebraicCurve_exists_forall_adicValuation_sub_le_of_riemannGenusReachedAt
import Theorems.Thm_AlgebraicCurve_Place_exists_forall_adicValuation_sub_eq
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_exists_mem_lSpaceOn_adicValuation_eq_of_riemannGenusReachedAt
p2m_attr_erase "instance" "AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupDivisor AlgebraicCurve.Pic0.instModuleZModTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instDistribMulActionTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instSMulTorsion AlgebraicCurve.SemilinearAut.instMulActionSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instSMulCommClassZModTorsion AlgebraicCurve.SemilinearAut.instMulSemiringActionSubtypeProdRingAutMemSubgroup instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt"
p2m_attr_erase "simp" "AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.SemilinearAut.toRingAut_inv AlgebraicCurve.SemilinearAut.smul_def AlgebraicCurve.SemilinearAut.smul_single AlgebraicCurve.SemilinearAut.smul_toValuationSubring AlgebraicCurve.SemilinearAut.baseAut_inv AlgebraicCurve.SemilinearAut.baseAut_ofAlgAut AlgebraicCurve.SemilinearAut.toRingAut_ofAlgAut"
p2m_attr_erase "simp" "AlgebraicCurve.SemilinearAut.torsionRep_apply AlgebraicCurve.SemilinearAut.toRingAut_one AlgebraicCurve.SemilinearAut.deg_smul AlgebraicCurve.SemilinearAut.degree_smul AlgebraicCurve.SemilinearAut.coe_degZeroSMulHom AlgebraicCurve.SemilinearAut.baseAut_mul AlgebraicCurve.SemilinearAut.coe_smulValuationSubringEquiv_apply AlgebraicCurve.SemilinearAut.baseAut_one AlgebraicCurve.SemilinearAut.ofAlgAut_smul AlgebraicCurve.SemilinearAut.coe_torsion_smul AlgebraicCurve.SemilinearAut.toRingAut_mul AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.jqNModC_one ModularCurve.qExpand_coeff_mul ModularCurve.qExpandₐ_apply ModularCurve.jqN_one ModularCurve.qExpand_single ModularCurve.dedekindPsi_one ModularCurve.ModularPolynomialData.mk.sizeOf_spec ModularCurve.evalAtJ_X ModularCurve.ModularPolynomialData.mk.injEq ModularCurve.constantCoeff_jNum ModularCurve.constantCoeff_eisenstein4 ModularCurve.qExpand_C ModularCurve.coeff_jq_neg_one ModularCurve.constantCoeff_jNumQ ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal"

set_option autoImplicit false

namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "Place Divisor IsCurveOver LSpace RiemannGenusReachedAt lSpaceOn exists_forall_adicValuation_sub_le_of_riemannGenusReachedAt Place.exists_forall_adicValuation_sub_eq"
p2m_open "AlgebraicCurve"
open WithZero

theorem exists_mem_lSpaceOn_adicValuation_eq' {K F : Type*} [Field K] [Field F] [Algebra K F] [IsCurveOver K F]
    [FiniteDimensional K ↥(LSpace (0 : Divisor K F))]
    {γ : ℤ} {D₀ : Divisor K F} (h : RiemannGenusReachedAt γ D₀)
    (S : Set (Place K F)) {v₀ : Place K F} (hv₀ : v₀ ∉ S) (D : Divisor K F) (v : Place K F) (hv : v ∈ S) :
    ∃ f : F, f ∈ lSpaceOn S D ∧ v.adicValuation f = exp (D v) := by
  classical

  obtain ⟨a, ha⟩ := Place.exists_forall_adicValuation_sub_eq ({v} : Finset (Place K F)) (fun _ => (0 : F)) (fun _ => D v)
  have hav : v.adicValuation a = exp (D v) := by
    have := ha v (Finset.mem_singleton_self v)
    rwa [sub_zero] at this

  let α : Place K F → F := fun w => if w = v then a else 0
  let E : Divisor K F := D - Finsupp.single v 1
  have hα : {w | w ∈ S ∧ ¬ w.adicValuation (α w) ≤ exp (E w)}.Finite := by
    apply (Set.finite_singleton v).subset
    rintro w ⟨-, hw⟩
    by_contra hwv
    apply hw
    have hαw : α w = 0 := if_neg hwv
    rw [hαw, Valuation.map_zero]
    exact zero_le'
  obtain ⟨f, hf⟩ := exists_forall_adicValuation_sub_le_of_riemannGenusReachedAt h S hv₀ E α hα
  have hEv : E v = D v - 1 := by simp [E]
  have hEw : ∀ w, w ≠ v → E w = D w := fun w hw => by
    rw [show E w = D w - Finsupp.single v (1 : ℤ) w from rfl, Finsupp.single_apply, if_neg (fun h => hw h.symm),
      sub_zero]
  have hfv : v.adicValuation (a - f) < v.adicValuation a := by
    have := hf v hv
    simp only [α, if_pos rfl, hEv] at this
    rw [hav]
    exact lt_of_le_of_lt this (exp_lt_exp.mpr (by omega))
  have hfval : v.adicValuation f = exp (D v) := by
    rw [← hav, show f = a - (a - f) by ring]
    exact Valuation.map_sub_eq_of_lt_left _ hfv
  refine ⟨f, ?_, hfval⟩
  intro w hwS
  by_cases hwv : w = v
  · subst hwv
    exact hfval.le
  · have := hf w hwS
    simp only [α, if_neg hwv, hEw w hwv, zero_sub, Valuation.map_neg] at this
    exact this

end AlgebraicCurve

open _root_.AlgebraicCurve _root_.P2MW.S_AlgebraicCurve_exists_mem_lSpaceOn_adicValuation_eq_of_riemannGenusReachedAt.AlgebraicCurve in
theorem solution
    {K F : Type*} [Field K] [Field F] [Algebra K F] [AlgebraicCurve.IsCurveOver K F]
    [FiniteDimensional K ↥(AlgebraicCurve.LSpace (0 : AlgebraicCurve.Divisor K F))]
    {γ : ℤ} {D₀ : AlgebraicCurve.Divisor K F} (h : AlgebraicCurve.RiemannGenusReachedAt γ D₀)
    (S : Set (AlgebraicCurve.Place K F)) {v₀ : AlgebraicCurve.Place K F} (hv₀ : v₀ ∉ S)
    (D : AlgebraicCurve.Divisor K F) (v : AlgebraicCurve.Place K F) (hv : v ∈ S) :
    ∃ f : F, f ∈ AlgebraicCurve.lSpaceOn S D ∧ v.adicValuation f = WithZero.exp (D v) :=
  exists_mem_lSpaceOn_adicValuation_eq' h S hv₀ D v hv

end S_AlgebraicCurve_exists_mem_lSpaceOn_adicValuation_eq_of_riemannGenusReachedAt
end P2MW
export P2MW.S_AlgebraicCurve_exists_mem_lSpaceOn_adicValuation_eq_of_riemannGenusReachedAt (solution)
