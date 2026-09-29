-- Prove2me | solution 1 for AlgebraicCurve.finiteDimensional_lSpace_zero_and_ell_zero_eq_one_of_isAlgClosed_of_transcendental
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.4153+00:00
-- url     : https://prove2.me/submissions/4638416f-1593-55b1-b506-fffe0cb928c7

import Mathlib
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Definitions.Def_AlgebraicCurve_Repartitions
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_AdelicIndex
import Theorems.Thm_AlgebraicCurve_isCurveOver_of_isAlgClosed_of_transcendental
import Theorems.Thm_AlgebraicCurve_exists_finset_sum_neg_ord_eq_finrank_of_isAlgClosed
import Theorems.Thm_AlgebraicCurve_finiteDimensional_lSpace_zero
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_finiteDimensional_lSpace_zero_and_ell_zero_eq_one_of_isAlgClosed_of_transcendental
p2m_attr_erase "instance" "AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupDivisor AlgebraicCurve.Pic0.instModuleZModTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instDistribMulActionTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instSMulTorsion AlgebraicCurve.SemilinearAut.instMulActionSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instSMulCommClassZModTorsion AlgebraicCurve.SemilinearAut.instMulSemiringActionSubtypeProdRingAutMemSubgroup instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions"
p2m_attr_erase "simp" "AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.SemilinearAut.toRingAut_inv AlgebraicCurve.SemilinearAut.smul_def"
p2m_attr_erase "simp" "AlgebraicCurve.SemilinearAut.smul_single AlgebraicCurve.SemilinearAut.smul_toValuationSubring AlgebraicCurve.SemilinearAut.baseAut_inv AlgebraicCurve.SemilinearAut.baseAut_ofAlgAut AlgebraicCurve.SemilinearAut.toRingAut_ofAlgAut AlgebraicCurve.SemilinearAut.torsionRep_apply AlgebraicCurve.SemilinearAut.toRingAut_one AlgebraicCurve.SemilinearAut.deg_smul AlgebraicCurve.SemilinearAut.degree_smul AlgebraicCurve.SemilinearAut.coe_degZeroSMulHom AlgebraicCurve.SemilinearAut.baseAut_mul AlgebraicCurve.SemilinearAut.coe_smulValuationSubringEquiv_apply AlgebraicCurve.SemilinearAut.baseAut_one AlgebraicCurve.SemilinearAut.ofAlgAut_smul AlgebraicCurve.SemilinearAut.coe_torsion_smul AlgebraicCurve.SemilinearAut.toRingAut_mul AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.jqNModC_one ModularCurve.qExpand_coeff_mul ModularCurve.qExpandₐ_apply ModularCurve.jqN_one ModularCurve.qExpand_single ModularCurve.dedekindPsi_one ModularCurve.ModularPolynomialData.mk.sizeOf_spec ModularCurve.evalAtJ_X ModularCurve.ModularPolynomialData.mk.injEq ModularCurve.constantCoeff_jNum ModularCurve.constantCoeff_eisenstein4 ModularCurve.qExpand_C ModularCurve.coeff_jq_neg_one ModularCurve.constantCoeff_jNumQ ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen"
p2m_attr_erase "simp" "ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq"

set_option autoImplicit false

open AlgebraicCurve
open scoped IntermediateField

namespace E97cEllZero

theorem main (k : Type*) [Field k] [IsAlgClosed k] {F : Type*} [Field F] [Algebra k F]
    (x : F) (hx : Transcendental k x)
    (hfin : FiniteDimensional (IntermediateField.adjoin k ({x} : Set F)) F) :
    FiniteDimensional k ↥(LSpace (0 : Divisor k F)) ∧ ell (0 : Divisor k F) = 1 := by
  classical
  haveI := hfin
  haveI : IsCurveOver k F := AlgebraicCurve.isCurveOver_of_isAlgClosed_of_transcendental x hx

  let e := RatFunc.algEquivOfTranscendental x hx
  letI : Algebra (RatFunc k) k⟮x⟯ := e.toAlgHom.toRingHom.toAlgebra
  letI : Algebra (RatFunc k) F := ((algebraMap k⟮x⟯ F).comp e.toAlgHom.toRingHom).toAlgebra
  haveI : IsScalarTower (RatFunc k) k⟮x⟯ F := IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI : IsScalarTower k (RatFunc k) F :=
    IsScalarTower.of_algebraMap_eq fun r => by
      show algebraMap k F r = algebraMap k⟮x⟯ F (e (algebraMap k (RatFunc k) r))
      rw [AlgEquiv.commutes]
      exact IsScalarTower.algebraMap_apply k k⟮x⟯ F r
  haveI : Module.Finite (RatFunc k) k⟮x⟯ :=
    Module.Finite.of_surjective (Algebra.linearMap (RatFunc k) k⟮x⟯) e.surjective
  haveI : Module.Finite (RatFunc k) F := Module.Finite.trans k⟮x⟯ F
  haveI : Algebra.EssFiniteType (Polynomial k) (RatFunc k) :=
    Algebra.EssFiniteType.of_isLocalization (RatFunc k) (nonZeroDivisors (Polynomial k))
  haveI : Algebra.EssFiniteType k (RatFunc k) := Algebra.EssFiniteType.comp k (Polynomial k) (RatFunc k)
  haveI : Algebra.EssFiniteType (RatFunc k) F := inferInstance
  haveI : Algebra.EssFiniteType k F := Algebra.EssFiniteType.comp k (RatFunc k) F

  haveI : Nonempty (Place k F) := by
    obtain ⟨S, -, hsum⟩ := AlgebraicCurve.exists_finset_sum_neg_ord_eq_finrank_of_isAlgClosed k x hx hfin
    by_contra h
    have hS : S = ∅ := Finset.eq_empty_of_forall_notMem fun v _ => h ⟨v⟩
    rw [hS, Finset.sum_empty] at hsum
    have hpos : 0 < Module.finrank (IntermediateField.adjoin k ({x} : Set F)) F := Module.finrank_pos
    omega
  have hfd : FiniteDimensional k ↥(LSpace (0 : Divisor k F)) := AlgebraicCurve.finiteDimensional_lSpace_zero k F
  refine ⟨hfd, ?_⟩

  have hmem0 : ∀ {y : F}, y ∈ LSpace (0 : Divisor k F) ↔ y = 0 ∨ ∀ v : Place k F, 0 ≤ v.ord y := by
    intro y
    rw [mem_lSpace_iff_ord]
    simp
  let L0 : Subalgebra k F :=
    { carrier := LSpace (0 : Divisor k F)
      mul_mem' := fun {a b} ha hb => by
        rcases eq_or_ne a 0 with rfl | ha0
        · simp
        rcases eq_or_ne b 0 with rfl | hb0
        · simp
        have ha' := (hmem0.mp ha).resolve_left ha0
        have hb' := (hmem0.mp hb).resolve_left hb0
        exact hmem0.mpr (Or.inr fun v => by rw [Place.ord_mul v ha0 hb0]; exact add_nonneg (ha' v) (hb' v))
      add_mem' := fun ha hb => (LSpace (0 : Divisor k F)).add_mem ha hb
      algebraMap_mem' := fun c => algebraMap_mem_lSpace_zero c }
  have hL0 : L0.toSubmodule = LSpace (0 : Divisor k F) := rfl
  have hfg : L0.toSubmodule.FG := by
    rw [hL0]
    exact Module.Finite.iff_fg.mp hfd

  have hconst : ∀ y ∈ LSpace (0 : Divisor k F), y ∈ (algebraMap k F).range := by
    intro y hy
    have hint : IsIntegral k y := IsIntegral.of_mem_of_fg L0 hfg y hy
    exact minpoly.mem_range_of_degree_eq_one k y (IsAlgClosed.degree_eq_one_of_irreducible k (minpoly.irreducible hint))
  have hC : ConstantsAreBase k F := by
    apply le_antisymm
    · intro y hy
      obtain ⟨c, rfl⟩ := hconst y hy
      exact ⟨c, rfl⟩
    · rintro _ ⟨c, rfl⟩
      exact algebraMap_mem_lSpace_zero c
  exact ell_zero_eq_one_of_constantsAreBase hC

end E97cEllZero

theorem solution
    (k : Type*) [Field k] [IsAlgClosed k] {F : Type*} [Field F] [Algebra k F]
    (x : F) (hx : Transcendental k x)
    (hfin : FiniteDimensional (IntermediateField.adjoin k ({x} : Set F)) F) :
    FiniteDimensional k ↥(LSpace (0 : Divisor k F)) ∧ ell (0 : Divisor k F) = 1 :=
  E97cEllZero.main k x hx hfin

end S_AlgebraicCurve_finiteDimensional_lSpace_zero_and_ell_zero_eq_one_of_isAlgClosed_of_transcendental
end P2MW
export P2MW.S_AlgebraicCurve_finiteDimensional_lSpace_zero_and_ell_zero_eq_one_of_isAlgClosed_of_transcendental (solution)
