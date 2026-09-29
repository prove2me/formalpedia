-- Prove2me | solution 1 for AlgebraicCurve.exists_int_forall_degree_add_one_sub_le_ell
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.4153+00:00
-- url     : https://prove2.me/submissions/6dd1ee16-7c0e-598f-bf82-8c5a21bffd7d

import Definitions.Def_AlgebraicCurve_AdelicIndex
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Theorems.Thm_AlgebraicCurve_exists_transcendental_isSeparable_of_finrank_kaehlerDifferential_eq_one
import Theorems.Thm_AlgebraicCurve_finiteDimensional_lSpace_zero
import Theorems.Thm_AlgebraicCurve_RationalFunctionField_stichtenothGenusExists_of_ratFunc_tower
import Theorems.Thm_AlgebraicCurve_exists_genus_riemannIndex_of_stichtenothGenusExists
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_exists_int_forall_degree_add_one_sub_le_ell
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupDivisor AlgebraicCurve.Pic0.instModuleZModTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instDistribMulActionTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instSMulTorsion AlgebraicCurve.SemilinearAut.instMulActionSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instSMulCommClassZModTorsion AlgebraicCurve.SemilinearAut.instMulSemiringActionSubtypeProdRingAutMemSubgroup instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt"
p2m_attr_erase "simp" "AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.SemilinearAut.toRingAut_inv AlgebraicCurve.SemilinearAut.smul_def AlgebraicCurve.SemilinearAut.smul_single AlgebraicCurve.SemilinearAut.smul_toValuationSubring AlgebraicCurve.SemilinearAut.baseAut_inv AlgebraicCurve.SemilinearAut.baseAut_ofAlgAut AlgebraicCurve.SemilinearAut.toRingAut_ofAlgAut AlgebraicCurve.SemilinearAut.torsionRep_apply AlgebraicCurve.SemilinearAut.toRingAut_one AlgebraicCurve.SemilinearAut.deg_smul AlgebraicCurve.SemilinearAut.degree_smul AlgebraicCurve.SemilinearAut.coe_degZeroSMulHom AlgebraicCurve.SemilinearAut.baseAut_mul AlgebraicCurve.SemilinearAut.coe_smulValuationSubringEquiv_apply AlgebraicCurve.SemilinearAut.baseAut_one"
p2m_attr_erase "simp" "AlgebraicCurve.SemilinearAut.ofAlgAut_smul AlgebraicCurve.SemilinearAut.coe_torsion_smul AlgebraicCurve.SemilinearAut.toRingAut_mul AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.jqNModC_one ModularCurve.qExpand_coeff_mul ModularCurve.qExpandₐ_apply ModularCurve.jqN_one ModularCurve.qExpand_single ModularCurve.dedekindPsi_one ModularCurve.ModularPolynomialData.mk.sizeOf_spec ModularCurve.evalAtJ_X ModularCurve.ModularPolynomialData.mk.injEq ModularCurve.constantCoeff_jNum ModularCurve.constantCoeff_eisenstein4 ModularCurve.qExpand_C ModularCurve.coeff_jq_neg_one ModularCurve.constantCoeff_jNumQ ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Place.placeOfPrime_toValuationSubring"
p2m_attr_erase "simp" "AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal"

set_option autoImplicit false

universe u v

open IntermediateField

namespace HRIgenSol

private theorem Place_algebraTranscendental {K : Type u} {F : Type v} [Field K] [Field F] [Algebra K F]
    (v : AlgebraicCurve.Place K F) : Algebra.Transcendental K F := by
  rw [Algebra.transcendental_iff_not_isAlgebraic]
  intro halg
  apply v.ne_top'
  have hv := Valuation.integer.integers v.toValuationSubring.valuation
  let φ : K →+* v.toValuationSubring.valuation.integer :=
    (algebraMap K F).codRestrict _ fun a => by
      rw [ValuationSubring.integer_valuation]; exact v.algebraMap_mem' a
  have hcomp : (algebraMap v.toValuationSubring.valuation.integer F).comp φ = algebraMap K F :=
    RingHom.ext fun _ => rfl
  refine ValuationSubring.ext _ _ fun x => ⟨fun _ => ValuationSubring.mem_top x, fun _ => ?_⟩
  obtain ⟨p, hp, hpx⟩ := (Algebra.IsAlgebraic.isAlgebraic (R := K) x).isIntegral
  have hx : IsIntegral v.toValuationSubring.valuation.integer x :=
    ⟨p.map φ, hp.map φ, by rw [Polynomial.eval₂_map, hcomp]; exact hpx⟩
  have hmem := hv.mem_of_integral hx
  rw [ValuationSubring.integer_valuation] at hmem
  exact hmem

private theorem algebraTranscendental_of_nonempty_place {K : Type u} {F : Type v} [Field K] [Field F]
    [Algebra K F] [h : Nonempty (AlgebraicCurve.Place K F)] : Algebra.Transcendental K F :=
  h.elim fun v => Place_algebraTranscendental v

section Tower

variable {K : Type u} {F : Type v} [Field K] [Field F] [Algebra K F]

@[reducible] private noncomputable def ratFuncAlgebra (t : F) (htr : Transcendental K t) : Algebra (RatFunc K) F :=
  ((algebraMap K⟮t⟯ F).comp (RatFunc.algEquivOfTranscendental t htr).toAlgHom.toRingHom).toAlgebra

@[reducible] private noncomputable def ratFuncAlgebraAdjoin (t : F) (htr : Transcendental K t) :
    Algebra (RatFunc K) K⟮t⟯ :=
  (RatFunc.algEquivOfTranscendental t htr).toAlgHom.toRingHom.toAlgebra

private theorem isScalarTower (t : F) (htr : Transcendental K t) :
    letI := ratFuncAlgebra t htr
    IsScalarTower K (RatFunc K) F := by
  letI := ratFuncAlgebra t htr
  refine IsScalarTower.of_algebraMap_eq fun k => ?_
  show algebraMap K F k =
    algebraMap K⟮t⟯ F (RatFunc.algEquivOfTranscendental t htr (algebraMap K (RatFunc K) k))
  rw [AlgEquiv.commutes, ← IsScalarTower.algebraMap_apply]

private theorem isScalarTower_adjoin (t : F) (htr : Transcendental K t) :
    letI := ratFuncAlgebra t htr
    letI := ratFuncAlgebraAdjoin t htr
    IsScalarTower (RatFunc K) K⟮t⟯ F := by
  letI := ratFuncAlgebra t htr
  letI := ratFuncAlgebraAdjoin t htr
  exact IsScalarTower.of_algebraMap_eq fun _ => rfl

private theorem finite_adjoin (t : F) (htr : Transcendental K t) :
    letI := ratFuncAlgebraAdjoin t htr
    Module.Finite (RatFunc K) K⟮t⟯ := by
  letI := ratFuncAlgebraAdjoin t htr
  exact Module.Finite.of_surjective (Algebra.linearMap (RatFunc K) K⟮t⟯)
    (RatFunc.algEquivOfTranscendental t htr).surjective

private theorem isSeparable_adjoin (t : F) (htr : Transcendental K t) :
    letI := ratFuncAlgebraAdjoin t htr
    Algebra.IsSeparable (RatFunc K) K⟮t⟯ := by
  letI := ratFuncAlgebraAdjoin t htr
  refine ⟨fun y => ?_⟩
  obtain ⟨x, rfl⟩ := (RatFunc.algEquivOfTranscendental t htr).surjective y
  exact isSeparable_algebraMap x

private theorem finite (t : F) (htr : Transcendental K t) [FiniteDimensional K⟮t⟯ F] :
    letI := ratFuncAlgebra t htr
    FiniteDimensional (RatFunc K) F := by
  letI := ratFuncAlgebra t htr
  letI := ratFuncAlgebraAdjoin t htr
  haveI := isScalarTower_adjoin t htr
  haveI := finite_adjoin t htr
  exact Module.Finite.trans K⟮t⟯ F

private theorem isSeparable (t : F) (htr : Transcendental K t) [Algebra.IsSeparable K⟮t⟯ F] :
    letI := ratFuncAlgebra t htr
    Algebra.IsSeparable (RatFunc K) F := by
  letI := ratFuncAlgebra t htr
  letI := ratFuncAlgebraAdjoin t htr
  haveI := isScalarTower_adjoin t htr
  haveI := isSeparable_adjoin t htr
  exact Algebra.IsSeparable.trans (F := RatFunc K) (E := K⟮t⟯) (K := F)

end Tower

end HRIgenSol

open AlgebraicCurve in
theorem solution
    (K : Type u) (F : Type v) [Field K] [Field F] [Algebra K F]
    [IsCurveOver K F] [Algebra.EssFiniteType K F] :
    ∃ γ : ℤ, ∀ D : Divisor K F, Divisor.degree D + 1 - γ ≤ (ell D : ℤ) := by
  classical
  by_cases hP : Nonempty (Place K F)
  ·
    haveI : Algebra.Transcendental K F := HRIgenSol.algebraTranscendental_of_nonempty_place
    obtain ⟨t, htr, hfd, hsep⟩ :=
      AlgebraicCurve.exists_transcendental_isSeparable_of_finrank_kaehlerDifferential_eq_one (K := K) (F := F)
        IsCurveOver.kaehler_free_rank_one.2
    letI := HRIgenSol.ratFuncAlgebra t htr
    haveI := HRIgenSol.isScalarTower t htr
    haveI := HRIgenSol.finite t htr
    haveI := HRIgenSol.isSeparable t htr
    haveI : FiniteDimensional K (LSpace (0 : Divisor K F)) := finiteDimensional_lSpace_zero K F
    have hSGE : StichtenothGenusExists K F :=
      RationalFunctionField.stichtenothGenusExists_of_ratFunc_tower K F
    obtain ⟨γ, hγ⟩ := exists_genus_riemannIndex_of_stichtenothGenusExists hSGE
    refine ⟨γ, fun D => ?_⟩
    obtain ⟨-, hD⟩ := hγ D
    have h0 : (0 : ℤ) ≤ (indexOfSpecialty D : ℤ) := Int.natCast_nonneg _
    omega
  ·
    haveI : IsEmpty (Place K F) := not_nonempty_iff.mp hP
    refine ⟨1, fun D => ?_⟩
    rw [Subsingleton.elim D 0, map_zero]
    have h0 : (0 : ℤ) ≤ (ell (0 : Divisor K F) : ℤ) := Int.natCast_nonneg _
    omega

end S_AlgebraicCurve_exists_int_forall_degree_add_one_sub_le_ell
end P2MW
export P2MW.S_AlgebraicCurve_exists_int_forall_degree_add_one_sub_le_ell (solution)
