-- Prove2me | solution 1 for AlgebraicCurve.exists_centre_and_finite_setOf_centre_of_isClosed_singleton
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.4153+00:00
-- url     : https://prove2.me/submissions/700f18df-886d-5466-aa4b-42498b922722

import Mathlib
import Definitions.Def_AlgebraicCurve_CurveModel
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_CechSectionsOfDivisor
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import Theorems.Thm_AlgebraicCurve_not_isAffine_of_isProper_of_isCurveOver
import Theorems.Thm_AlgebraicCurve_isCurveOver_iff_exists_transcendental_finiteDimensional
import Theorems.Thm_ValuationSubring_isPrincipalIdealRing_of_finiteDimensional_adjoin
import Theorems.Thm_AlgebraicCurve_essFiniteType_functionField
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_exists_centre_and_finite_setOf_centre_of_isClosed_singleton
p2m_attr_erase "instance" "AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupDivisor AlgebraicCurve.Pic0.instModuleZModTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instDistribMulActionTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instSMulTorsion AlgebraicCurve.SemilinearAut.instMulActionSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instSMulCommClassZModTorsion AlgebraicCurve.SemilinearAut.instMulSemiringActionSubtypeProdRingAutMemSubgroup instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions"
p2m_attr_erase "simp" "AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.SemilinearAut.toRingAut_inv AlgebraicCurve.SemilinearAut.smul_def"
p2m_attr_erase "simp" "AlgebraicCurve.SemilinearAut.smul_single AlgebraicCurve.SemilinearAut.smul_toValuationSubring AlgebraicCurve.SemilinearAut.baseAut_inv AlgebraicCurve.SemilinearAut.baseAut_ofAlgAut AlgebraicCurve.SemilinearAut.toRingAut_ofAlgAut AlgebraicCurve.SemilinearAut.torsionRep_apply AlgebraicCurve.SemilinearAut.toRingAut_one AlgebraicCurve.SemilinearAut.deg_smul AlgebraicCurve.SemilinearAut.degree_smul AlgebraicCurve.SemilinearAut.coe_degZeroSMulHom AlgebraicCurve.SemilinearAut.baseAut_mul AlgebraicCurve.SemilinearAut.coe_smulValuationSubringEquiv_apply AlgebraicCurve.SemilinearAut.baseAut_one AlgebraicCurve.SemilinearAut.ofAlgAut_smul AlgebraicCurve.SemilinearAut.coe_torsion_smul AlgebraicCurve.SemilinearAut.toRingAut_mul AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.jqNModC_one ModularCurve.qExpand_coeff_mul ModularCurve.qExpandₐ_apply ModularCurve.jqN_one ModularCurve.qExpand_single ModularCurve.dedekindPsi_one ModularCurve.ModularPolynomialData.mk.sizeOf_spec ModularCurve.evalAtJ_X ModularCurve.ModularPolynomialData.mk.injEq ModularCurve.constantCoeff_jNum ModularCurve.constantCoeff_eisenstein4 ModularCurve.qExpand_C ModularCurve.coeff_jq_neg_one ModularCurve.constantCoeff_jNumQ ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen"
p2m_attr_erase "simp" "ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one"

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry AlgebraicCurve

namespace CentreL2b

theorem eq_genericPoint_of_isField {C : Scheme.{u}} [IsIntegral C] (x : C)
    (hfield : IsField (C.presheaf.stalk x)) : x = genericPoint C := by
  obtain ⟨U, hU, hxU, -⟩ := exists_isAffineOpen_mem_and_subset (X := C) (x := x) (U := ⊤) trivial
  haveI : Nonempty U := ⟨⟨_, hxU⟩⟩
  letI := C.presheaf.algebra_section_stalk (⟨_, hxU⟩ : U)
  haveI := hU.isLocalization_stalk ⟨_, hxU⟩
  have hbot : (hU.primeIdealOf ⟨_, hxU⟩).asIdeal = ⊥ := by
    rw [← Ideal.map_eq_bot_iff_of_injective (IsLocalization.injective (C.presheaf.stalk x)
      (hU.primeIdealOf ⟨_, hxU⟩).asIdeal.primeCompl_le_nonZeroDivisors),
      IsLocalization.AtPrime.map_eq_maximalIdeal (hU.primeIdealOf ⟨_, hxU⟩).asIdeal,
      ← IsLocalRing.isField_iff_maximalIdeal_eq]
    exact hfield
  have h1 : hU.primeIdealOf ⟨_, hxU⟩ = hU.primeIdealOf ⟨genericPoint C,
      ((genericPoint_spec C).mem_open_set_iff U.isOpen).mpr (by simpa using (inferInstance : Nonempty U))⟩ := by
    rw [hU.primeIdealOf_genericPoint, genericPoint_eq_bot_of_affine]
    ext1
    exact hbot
  have h2 := congr(hU.fromSpec $h1)
  rwa [hU.fromSpec_primeIdealOf, hU.fromSpec_primeIdealOf] at h2

theorem ne_genericPoint_of_isClosed
    (k : Type u) [Field k] [IsAlgClosed k] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of k))
    [IsIntegral C] [IsProper c]
    (hK : letI := (AlgebraicCurve.baseToFunctionField c).toAlgebra; IsCurveOver k C.functionField)
    (z : C) (hz : IsClosed ({z} : Set C)) : z ≠ genericPoint C := by
  rintro rfl
  apply AlgebraicCurve.not_isAffine_of_isProper_of_isCurveOver k c hK
  have huniv : ∀ y : C, y = genericPoint C := by
    intro y
    have hy : y ∈ closure ({genericPoint C} : Set C) := by
      rw [(genericPoint_spec C).def]; trivial
    rw [hz.closure_eq] at hy
    exact hy
  obtain ⟨U, hU, hηU, -⟩ := exists_isAffineOpen_mem_and_subset (X := C) (x := genericPoint C) (U := ⊤) trivial
  have hUtop : U = ⊤ := by
    ext y
    simp only [TopologicalSpace.Opens.coe_top, Set.mem_univ, iff_true]
    rw [huniv y]; exact hηU
  rw [hUtop] at hU
  haveI : IsAffine (⊤ : C.Opens) := hU
  exact IsAffine.of_isIso C.topIso.inv

end CentreL2b

theorem solution
    (k : Type u) [Field k] [IsAlgClosed k] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of k))
    [IsIntegral C] [IsProper c]
    (hK : letI := (AlgebraicCurve.baseToFunctionField c).toAlgebra; IsCurveOver k C.functionField)
    (z : C) (hz : IsClosed ({z} : Set C)) :
    letI := (AlgebraicCurve.baseToFunctionField c).toAlgebra
    (∃ v : Place k C.functionField, (∀ s : C.presheaf.stalk z,
          v.adicValuation (algebraMap (C.presheaf.stalk z) C.functionField s) ≤ 1 ∧
          (s ∈ IsLocalRing.maximalIdeal (C.presheaf.stalk z) →
            v.adicValuation (algebraMap (C.presheaf.stalk z) C.functionField s) < 1))) ∧
      {v : Place k C.functionField | (∀ s : C.presheaf.stalk z,
          v.adicValuation (algebraMap (C.presheaf.stalk z) C.functionField s) ≤ 1 ∧
          (s ∈ IsLocalRing.maximalIdeal (C.presheaf.stalk z) →
            v.adicValuation (algebraMap (C.presheaf.stalk z) C.functionField s) < 1))}.Finite := by
  classical
  letI := (AlgebraicCurve.baseToFunctionField c).toAlgebra
  let φ : C.presheaf.stalk z →+* C.functionField := algebraMap (C.presheaf.stalk z) C.functionField
  have hφinj : Function.Injective φ := IsFractionRing.injective (C.presheaf.stalk z) C.functionField
  have hzη : z ≠ genericPoint C := CentreL2b.ne_genericPoint_of_isClosed k c hK z hz
  have hnf : ¬ IsField (C.presheaf.stalk z) := fun h => hzη (CentreL2b.eq_genericPoint_of_isField z h)

  have key : ∀ t : Γ(C, ⊤), (C.presheaf.germ ⊤ (genericPoint C) trivial).hom t = φ ((C.presheaf.germ ⊤ z trivial).hom t) := by
    intro t
    change _ = (C.presheaf.germ ⊤ z trivial ≫ C.presheaf.stalkSpecializes ((genericPoint_spec C).specializes trivial)).hom t
    rw [TopCat.Presheaf.germ_stalkSpecializes]
  have hbase : ∀ a : k, ∃ t : C.presheaf.stalk z, algebraMap k C.functionField a = φ t := fun a =>
    ⟨(C.presheaf.germ ⊤ z trivial).hom (c.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom a)), key _⟩

  obtain ⟨A, hA, hloc⟩ := IsLocalRing.exists_factor_valuationRing φ
  have hAtop : A ≠ ⊤ := by
    intro hA'
    apply hnf
    rw [IsLocalRing.isField_iff_maximalIdeal_eq, eq_bot_iff]
    intro s hs
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at hs
    rw [Ideal.mem_bot]
    by_contra hs0
    apply hs
    apply hloc.map_nonunit
    have hne : φ s ≠ 0 := fun h => hs0 (hφinj (by rw [h, map_zero]))
    refine isUnit_iff_exists_inv.mpr ⟨⟨(φ s)⁻¹, ?_⟩, ?_⟩
    · rw [ValuationSubring.mem_toSubring, hA']; exact ValuationSubring.mem_top _
    · exact Subtype.ext (mul_inv_cancel₀ hne)

  haveI : PerfectField k := inferInstance
  haveI := AlgebraicCurve.essFiniteType_functionField c
  obtain ⟨t, -, hfd, -⟩ := (AlgebraicCurve.isCurveOver_iff_exists_transcendental_finiteDimensional).mp hK
  haveI := hfd
  have hkA : ∀ a : k, algebraMap k C.functionField a ∈ A := fun a => by
    obtain ⟨t, ht⟩ := hbase a
    rw [ht]; exact hA t
  have hPIR : IsPrincipalIdealRing A := ValuationSubring.isPrincipalIdealRing_of_finiteDimensional_adjoin t A hkA hAtop
  let v : Place k C.functionField :=
    { toValuationSubring := A, algebraMap_mem' := hkA, ne_top' := hAtop, isPrincipalIdealRing' := hPIR }

  have hdom : ∀ s : C.presheaf.stalk z, v.adicValuation (φ s) ≤ 1 ∧
      (s ∈ IsLocalRing.maximalIdeal (C.presheaf.stalk z) → v.adicValuation (φ s) < 1) := by
    intro s
    have hmem : φ s ∈ v.toValuationSubring := hA s
    have hcoe : φ s = ((⟨φ s, hmem⟩ : v.toValuationSubring) : C.functionField) := rfl
    constructor
    · rw [hcoe, v.adicValuation_coe]
      exact IsDedekindDomain.HeightOneSpectrum.intValuation_le_one _ _
    · intro hs
      have hnu : ¬ IsUnit (⟨φ s, hmem⟩ : v.toValuationSubring) := by
        intro hu
        rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at hs
        exact hs (hloc.map_nonunit s hu)
      rw [hcoe, v.adicValuation_coe, IsDedekindDomain.HeightOneSpectrum.intValuation_lt_one_iff_mem,
        Place.heightOneSpectrum_asIdeal, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
      exact hnu
  refine ⟨⟨v, hdom⟩, ?_⟩

  obtain ⟨s, hs𝔪, hs0⟩ : ∃ s ∈ IsLocalRing.maximalIdeal (C.presheaf.stalk z), s ≠ 0 := by
    by_contra! h
    apply hnf
    rw [IsLocalRing.isField_iff_maximalIdeal_eq, eq_bot_iff]
    intro s hs
    rw [h s hs]; exact Ideal.zero_mem _
  have hf0 : φ s ≠ 0 := fun h => hs0 (hφinj (by rw [h, map_zero]))
  haveI : IsCurveOver k C.functionField := hK
  obtain ⟨D, hD, -⟩ := HasPrincipalDivisors.exists_divisor (K := k) (F := C.functionField) (φ s) hf0
  refine Set.Finite.subset D.support.finite_toSet ?_
  intro w hw
  have hlt : w.adicValuation (φ s) < 1 := (hw s).2 hs𝔪
  rw [Finset.mem_coe, Finsupp.mem_support_iff, hD w]
  have hne0 := w.adicValuation_ne_zero hf0
  have hlog : WithZero.log (w.adicValuation (φ s)) < 0 :=
    (WithZero.log_lt_iff_lt_exp hne0).mpr (by rwa [WithZero.exp_zero])
  show -(WithZero.log (w.adicValuation (φ s))) ≠ 0
  omega

end S_AlgebraicCurve_exists_centre_and_finite_setOf_centre_of_isClosed_singleton
end P2MW
export P2MW.S_AlgebraicCurve_exists_centre_and_finite_setOf_centre_of_isClosed_singleton (solution)
