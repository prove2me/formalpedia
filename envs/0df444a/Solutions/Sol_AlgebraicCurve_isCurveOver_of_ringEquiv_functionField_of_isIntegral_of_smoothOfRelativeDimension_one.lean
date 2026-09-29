-- Prove2me | solution 1 for AlgebraicCurve.isCurveOver_of_ringEquiv_functionField_of_isIntegral_of_smoothOfRelativeDimension_one
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.4153+00:00
-- url     : https://prove2.me/submissions/1b81eace-f351-59b3-98b8-51e4889a70cc

import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_CurveModel
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.FieldTheory.IntermediateField.Adjoin.Algebra
import Mathlib.RingTheory.Etale.Field
import Mathlib.RingTheory.Etale.Kaehler
import Mathlib.RingTheory.Smooth.StandardSmoothCotangent
import Mathlib.RingTheory.Smooth.Flat
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.RingHom.StandardSmooth
import Mathlib.RingTheory.Algebraic.MvPolynomial
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
import Theorems.Thm_AlgebraicCurve_isCurveOver_of_transcendental
import Theorems.Thm_AlgebraicCurve_exists_transcendental_isSeparable_of_finrank_kaehlerDifferential_eq_one
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_isCurveOver_of_ringEquiv_functionField_of_isIntegral_of_smoothOfRelativeDimension_one
p2m_attr_erase "instance" "AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupDivisor AlgebraicCurve.Pic0.instModuleZModTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instDistribMulActionTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instSMulTorsion AlgebraicCurve.SemilinearAut.instMulActionSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instSMulCommClassZModTorsion AlgebraicCurve.SemilinearAut.instMulSemiringActionSubtypeProdRingAutMemSubgroup instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions"
p2m_attr_erase "simp" "AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.SemilinearAut.toRingAut_inv AlgebraicCurve.SemilinearAut.smul_def"
p2m_attr_erase "simp" "AlgebraicCurve.SemilinearAut.smul_single AlgebraicCurve.SemilinearAut.smul_toValuationSubring AlgebraicCurve.SemilinearAut.baseAut_inv AlgebraicCurve.SemilinearAut.baseAut_ofAlgAut AlgebraicCurve.SemilinearAut.toRingAut_ofAlgAut AlgebraicCurve.SemilinearAut.torsionRep_apply AlgebraicCurve.SemilinearAut.toRingAut_one AlgebraicCurve.SemilinearAut.deg_smul AlgebraicCurve.SemilinearAut.degree_smul AlgebraicCurve.SemilinearAut.coe_degZeroSMulHom AlgebraicCurve.SemilinearAut.baseAut_mul AlgebraicCurve.SemilinearAut.coe_smulValuationSubringEquiv_apply AlgebraicCurve.SemilinearAut.baseAut_one AlgebraicCurve.SemilinearAut.ofAlgAut_smul AlgebraicCurve.SemilinearAut.coe_torsion_smul AlgebraicCurve.SemilinearAut.toRingAut_mul AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.jqNModC_one ModularCurve.qExpand_coeff_mul ModularCurve.qExpandₐ_apply ModularCurve.jqN_one ModularCurve.qExpand_single ModularCurve.dedekindPsi_one ModularCurve.ModularPolynomialData.mk.sizeOf_spec ModularCurve.evalAtJ_X ModularCurve.ModularPolynomialData.mk.injEq ModularCurve.constantCoeff_jNum ModularCurve.constantCoeff_eisenstein4 ModularCurve.qExpand_C ModularCurve.coeff_jq_neg_one ModularCurve.constantCoeff_jNumQ ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen"
p2m_attr_erase "simp" "ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one"

open scoped TensorProduct
open CategoryTheory AlgebraicGeometry AlgebraicCurve Opposite

universe u v

namespace SmoothModelFunctionFieldGen

private theorem stageA3 {K : Type u} [Field K] {C : Scheme.{u}} (c : C ⟶ Spec (.of K)) [IsIntegral C]
    [SmoothOfRelativeDimension 1 c] :
    letI := (baseToFunctionField c).toAlgebra
    Algebra.EssFiniteType K C.functionField ∧
      Module.rank C.functionField Ω[C.functionField⁄K] = 1 ∧
      Algebra.Transcendental K C.functionField := by
  letI algKF : Algebra K C.functionField := (baseToFunctionField c).toAlgebra
  obtain ⟨x⟩ := (inferInstance : Nonempty C)
  obtain ⟨U, hU, V, hV, hxV, e, hstd⟩ :=
    SmoothOfRelativeDimension.exists_isStandardSmoothOfRelativeDimension (n := 1) (f := c) x
  haveI : Nonempty V := ⟨⟨x, hxV⟩⟩

  obtain rfl : U = ⊤ := by
    ext y
    simp only [TopologicalSpace.Opens.coe_top, Set.mem_univ, iff_true]
    have : y = c.base x := Subsingleton.elim _ _
    rw [this]; exact e hxV

  let eK : Γ(Spec (CommRingCat.of K), ⊤) ≃+* K := (Scheme.ΓSpecIso (.of K)).commRingCatIsoToRingEquiv
  letI algRA : Algebra Γ(Spec (CommRingCat.of K), ⊤) Γ(C, V) := (c.appLE ⊤ V e).hom.toAlgebra
  have hstdA : Algebra.IsStandardSmoothOfRelativeDimension 1 Γ(Spec (CommRingCat.of K), ⊤) Γ(C, V) :=
    hstd
  letI algKR : Algebra K Γ(Spec (CommRingCat.of K), ⊤) := eK.symm.toRingHom.toAlgebra
  haveI : Algebra.IsStandardSmoothOfRelativeDimension 0 K Γ(Spec (CommRingCat.of K), ⊤) :=
    .of_algebraMap_bijective eK.symm.bijective
  letI algKA : Algebra K Γ(C, V) :=
    ((algebraMap Γ(Spec (CommRingCat.of K), ⊤) Γ(C, V)).comp
      (algebraMap K Γ(Spec (CommRingCat.of K), ⊤))).toAlgebra
  haveI : IsScalarTower K Γ(Spec (CommRingCat.of K), ⊤) Γ(C, V) :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI hKA : Algebra.IsStandardSmoothOfRelativeDimension (1 + 0) K Γ(C, V) :=
    Algebra.IsStandardSmoothOfRelativeDimension.trans 0 1 K Γ(Spec (CommRingCat.of K), ⊤) Γ(C, V)

  haveI : IsFractionRing Γ(C, V) C.functionField :=
    functionField_isFractionRing_of_isAffineOpen C V hV
  haveI : IsScalarTower K Γ(C, V) C.functionField := by
    refine IsScalarTower.of_algebraMap_eq fun k => ?_
    change baseToFunctionField c k =
      (C.germToFunctionField V).hom ((c.appLE ⊤ V e).hom (eK.symm k))
    simp only [baseToFunctionField, RingHom.coe_comp, Function.comp_apply, Scheme.Hom.appLE,
      Scheme.germToFunctionField, CommRingCat.hom_comp]
    rw [TopCat.Presheaf.germ_res_apply]
    rfl

  haveI := Algebra.IsStandardSmoothOfRelativeDimension.isStandardSmooth (n := 1 + 0) (R := K)
    (S := Γ(C, V))
  haveI : Algebra.EssFiniteType Γ(C, V) C.functionField :=
    Algebra.EssFiniteType.of_isLocalization C.functionField (nonZeroDivisors Γ(C, V))

  have hT : Algebra.Transcendental K C.functionField := by
    obtain ⟨g, hg⟩ := Algebra.IsStandardSmoothOfRelativeDimension.exists_etale_mvPolynomial
      (1 + 0) K Γ(C, V)
    letI algPA : Algebra (MvPolynomial (Fin (1 + 0)) K) Γ(C, V) := g.toRingHom.toAlgebra
    haveI : Algebra.Etale (MvPolynomial (Fin (1 + 0)) K) Γ(C, V) := hg.toAlgebra
    haveI : IsScalarTower K (MvPolynomial (Fin (1 + 0)) K) Γ(C, V) :=
      IsScalarTower.of_algebraMap_eq fun k => (g.commutes k).symm
    have hinj : Function.Injective (algebraMap (MvPolynomial (Fin (1 + 0)) K) Γ(C, V)) := by
      rw [injective_iff_map_eq_zero]
      intro p hp
      by_contra hp0
      have hreg : IsSMulRegular Γ(C, V) p :=
        Module.Flat.isSMulRegular_of_nonZeroDivisors (mem_nonZeroDivisors_of_ne_zero hp0)
      have h1 : p • (1 : Γ(C, V)) = p • (0 : Γ(C, V)) := by
        rw [Algebra.smul_def, mul_one, hp, smul_zero]
      exact one_ne_zero (hreg h1)
    have hX : Transcendental K
        (algebraMap (MvPolynomial (Fin (1 + 0)) K) Γ(C, V) (MvPolynomial.X 0)) :=
      (transcendental_algebraMap_iff hinj).mpr (MvPolynomial.transcendental_X K 0)
    exact ⟨⟨algebraMap Γ(C, V) C.functionField _,
      (transcendental_algebraMap_iff (IsFractionRing.injective Γ(C, V) C.functionField)).mpr hX⟩⟩
  refine ⟨Algebra.EssFiniteType.comp K Γ(C, V) C.functionField, ?_, hT⟩

  haveI : Algebra.FormallyEtale Γ(C, V) C.functionField :=
    Algebra.FormallyEtale.of_isLocalization (nonZeroDivisors Γ(C, V))
  have h := (KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale K Γ(C, V)
    C.functionField).lift_rank_eq
  rw [Module.rank_baseChange,
    Algebra.IsStandardSmoothOfRelativeDimension.rank_kaehlerDifferential (1 + 0)] at h
  simpa using h.symm

private theorem rank_kaehler_eq_one_of_algEquiv {K : Type u} [Field K] {F : Type v} [Field F]
    [Algebra K F] {L : Type u} [Field L] [Algebra K L] (e : F ≃ₐ[K] L)
    (h : Module.rank L Ω[L⁄K] = 1) : Module.rank F Ω[F⁄K] = 1 := by
  letI : Algebra L F := (e.symm : L →ₐ[K] F).toRingHom.toAlgebra
  haveI : IsScalarTower K L F :=
    IsScalarTower.of_algebraMap_eq fun k => by simp [RingHom.algebraMap_toAlgebra]
  have e' : L ≃ₐ[L] F := { e.symm.toRingEquiv with commutes' := fun l => rfl }
  haveI : Algebra.FormallyEtale L L := Algebra.FormallyEtale.of_formallyUnramified_and_formallySmooth
  haveI : Algebra.FormallyEtale L F := Algebra.FormallyEtale.of_equiv e'
  have h1 := (KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale K L F).lift_rank_eq
  rw [Module.rank_baseChange, h] at h1
  simpa using h1.symm

private theorem isCurveOver_of_rank_eq_one {K : Type u} [Field K] {F : Type v} [Field F] [Algebra K F]
    [Algebra.EssFiniteType K F] [Algebra.Transcendental K F] (hΩ : Module.rank F Ω[F⁄K] = 1) :
    IsCurveOver K F := by
  have hfin : Module.finrank F Ω[F⁄K] = 1 := Module.finrank_eq_of_rank_eq (by exact_mod_cast hΩ)
  obtain ⟨t, htr, hfd, hsep⟩ :=
    AlgebraicCurve.exists_transcendental_isSeparable_of_finrank_kaehlerDifferential_eq_one hfin
  exact AlgebraicCurve.isCurveOver_of_transcendental htr hfd hsep

private theorem assembly {K : Type u} [Field K] {F : Type v} [Field F] [Algebra K F]
    {C : AlgebraicGeometry.Scheme.{u}} (c : C ⟶ AlgebraicGeometry.Spec (.of K))
    [AlgebraicGeometry.IsIntegral C]
    (φ : F ≃+* C.functionField) (hφ : ∀ a : K, φ (algebraMap K F a) = baseToFunctionField c a)
    (hA1 : letI := (baseToFunctionField c).toAlgebra; Algebra.EssFiniteType K C.functionField)
    (hA2 : letI := (baseToFunctionField c).toAlgebra;
      Module.rank C.functionField Ω[C.functionField⁄K] = 1)
    (hA3 : letI := (baseToFunctionField c).toAlgebra; Algebra.Transcendental K C.functionField) :
    IsCurveOver K F := by
  letI := (baseToFunctionField c).toAlgebra
  let e : F ≃ₐ[K] C.functionField := AlgEquiv.ofRingEquiv (f := φ) hφ
  haveI : Algebra.EssFiniteType K F := (Algebra.EssFiniteType.iff_of_algEquiv e).mpr hA1
  haveI : Algebra.Transcendental K F := by
    rw [Algebra.transcendental_iff_not_isAlgebraic] at hA3 ⊢
    exact fun h => hA3 (e.isAlgebraic_iff.mp h)
  exact isCurveOver_of_rank_eq_one (rank_kaehler_eq_one_of_algEquiv e hA2)

end SmoothModelFunctionFieldGen

theorem solution
    {K : Type u} [Field K] {F : Type v} [Field F] [Algebra K F]
    {C : Scheme.{u}} (c : C ⟶ Spec (.of K)) [IsIntegral C]
    [SmoothOfRelativeDimension 1 c] (φ : F ≃+* C.functionField)
    (hφ : ∀ a : K, φ (algebraMap K F a) = baseToFunctionField c a) :
    IsCurveOver K F :=
  SmoothModelFunctionFieldGen.assembly c φ hφ (SmoothModelFunctionFieldGen.stageA3 c).1
    (SmoothModelFunctionFieldGen.stageA3 c).2.1 (SmoothModelFunctionFieldGen.stageA3 c).2.2

end S_AlgebraicCurve_isCurveOver_of_ringEquiv_functionField_of_isIntegral_of_smoothOfRelativeDimension_one
end P2MW
export P2MW.S_AlgebraicCurve_isCurveOver_of_ringEquiv_functionField_of_isIntegral_of_smoothOfRelativeDimension_one (solution)
