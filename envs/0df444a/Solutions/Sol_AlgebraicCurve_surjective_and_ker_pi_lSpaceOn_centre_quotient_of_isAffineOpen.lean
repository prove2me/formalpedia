-- Prove2me | solution 1 for AlgebraicCurve.surjective_and_ker_pi_lSpaceOn_centre_quotient_of_isAffineOpen
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.935278+00:00
-- url     : https://prove2.me/submissions/dd990db5-5790-51b5-a96b-bf859f9ad85e

import Mathlib
import Definitions.Def_AlgebraicCurve_CurveModel
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_CechSectionsOfDivisor
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import Theorems.Thm_AlgebraicCurve_CurveModel_finite_integralClosure_sections_of_isIso_stalkMap
import Theorems.Thm_AlgebraicCurve_CurveModel_surjective_and_eq_genericPoint_or_isClosed_singleton_of_isIso_stalkMap
import Theorems.Thm_AlgebraicCurve_surjective_and_ker_pi_span_mul_quotient_of_finite
import Theorems.Thm_AlgebraicCurve_lSpaceOn_setOf_exists_centre_eq_span_integralClosure
import Theorems.Thm_AlgebraicCurve_lSpaceOn_setOf_centre_eq_span_integralClosure_mul
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_surjective_and_ker_pi_lSpaceOn_centre_quotient_of_isAffineOpen
p2m_attr_erase "instance" "AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupDivisor AlgebraicCurve.Pic0.instModuleZModTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instDistribMulActionTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instSMulTorsion AlgebraicCurve.SemilinearAut.instMulActionSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instSMulCommClassZModTorsion AlgebraicCurve.SemilinearAut.instMulSemiringActionSubtypeProdRingAutMemSubgroup instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions"
p2m_attr_erase "simp" "AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong"
p2m_attr_erase "simp" "AlgebraicCurve.SemilinearAut.toRingAut_inv AlgebraicCurve.SemilinearAut.smul_def AlgebraicCurve.SemilinearAut.smul_single AlgebraicCurve.SemilinearAut.smul_toValuationSubring AlgebraicCurve.SemilinearAut.baseAut_inv AlgebraicCurve.SemilinearAut.baseAut_ofAlgAut AlgebraicCurve.SemilinearAut.toRingAut_ofAlgAut AlgebraicCurve.SemilinearAut.torsionRep_apply AlgebraicCurve.SemilinearAut.toRingAut_one AlgebraicCurve.SemilinearAut.deg_smul AlgebraicCurve.SemilinearAut.degree_smul AlgebraicCurve.SemilinearAut.coe_degZeroSMulHom AlgebraicCurve.SemilinearAut.baseAut_mul AlgebraicCurve.SemilinearAut.coe_smulValuationSubringEquiv_apply AlgebraicCurve.SemilinearAut.baseAut_one AlgebraicCurve.SemilinearAut.ofAlgAut_smul AlgebraicCurve.SemilinearAut.coe_torsion_smul AlgebraicCurve.SemilinearAut.toRingAut_mul AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.jqNModC_one ModularCurve.qExpand_coeff_mul ModularCurve.qExpandₐ_apply ModularCurve.jqN_one ModularCurve.qExpand_single ModularCurve.dedekindPsi_one ModularCurve.ModularPolynomialData.mk.sizeOf_spec ModularCurve.evalAtJ_X ModularCurve.ModularPolynomialData.mk.injEq ModularCurve.constantCoeff_jNum ModularCurve.constantCoeff_eisenstein4 ModularCurve.qExpand_C ModularCurve.coeff_jq_neg_one ModularCurve.constantCoeff_jNumQ ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X"
p2m_attr_erase "simp" "ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one"

set_option autoImplicit false

universe u v

open CategoryTheory AlgebraicGeometry AlgebraicCurve
open scoped Pointwise

noncomputable section

namespace PGL5K12

section Gen
variable {k : Type u} [Field k] {K : Type u} [AddCommGroup K] [Module k K] {ι : Type u}

def Concl (T : Submodule k K) (Tz : ι → Submodule k K) (O : ι → Submodule k K) (A0 : Submodule k K)
    (hle : ∀ i, T ≤ Tz i) : Prop :=
  Function.Surjective (LinearMap.pi fun i => ((O i).comap (Tz i).subtype).mkQ ∘ₗ Submodule.inclusion (hle i) :
      ↥T →ₗ[k] ((i : ι) → ↥(Tz i) ⧸ (O i).comap (Tz i).subtype)) ∧
    LinearMap.ker (LinearMap.pi fun i => ((O i).comap (Tz i).subtype).mkQ ∘ₗ Submodule.inclusion (hle i) :
      ↥T →ₗ[k] ((i : ι) → ↥(Tz i) ⧸ (O i).comap (Tz i).subtype)) = A0.comap T.subtype ∧
    {i : ι | Nontrivial (↥(Tz i) ⧸ (O i).comap (Tz i).subtype)}.Finite ∧
    ∀ i : ι, FiniteDimensional k (↥(Tz i) ⧸ (O i).comap (Tz i).subtype)

theorem concl_congr {T T' : Submodule k K} {Tz Tz' : ι → Submodule k K} (O : ι → Submodule k K) (A0 : Submodule k K)
    (hle : ∀ i, T ≤ Tz i) (hle' : ∀ i, T' ≤ Tz' i) (hT : T = T') (hTz : Tz = Tz')
    (h : Concl T Tz O A0 hle) : Concl T' Tz' O A0 hle' := by
  subst hT hTz
  exact h

end Gen

end PGL5K12

open PGL5K12

set_option maxHeartbeats 3200000 in
set_option synthInstance.maxHeartbeats 1600000 in

theorem solution
    (k : Type u) [Field k] [IsAlgClosed k] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of k))
    [IsIntegral C] [IsProper c]
    (hK : letI := (AlgebraicCurve.baseToFunctionField c).toAlgebra; IsCurveOver k C.functionField)
    {F : Type v} [Field F] [Algebra k F] (M : AlgebraicCurve.CurveModel k F)
    (ν : M.C ⟶ C) (hν : ν ≫ c = M.toBase) (hbir : IsIso (ν.stalkMap (genericPoint M.C)))
    (U : C.Opens) (hUaff : IsAffineOpen U) (hU : genericPoint C ∈ U) :
    letI := (AlgebraicCurve.baseToFunctionField c).toAlgebra

    let Q : C → Type u := fun z =>
      ↥(lSpaceOn {v : Place k C.functionField | (∀ s : C.presheaf.stalk z,
          v.adicValuation (algebraMap (C.presheaf.stalk z) C.functionField s) ≤ 1 ∧
          (s ∈ IsLocalRing.maximalIdeal (C.presheaf.stalk z) →
            v.adicValuation (algebraMap (C.presheaf.stalk z) C.functionField s) < 1))} (0 : Divisor k C.functionField)) ⧸
        (Submodule.span k (Set.range (algebraMap (C.presheaf.stalk z) C.functionField))).comap
          (lSpaceOn {v : Place k C.functionField | (∀ s : C.presheaf.stalk z,
          v.adicValuation (algebraMap (C.presheaf.stalk z) C.functionField s) ≤ 1 ∧
          (s ∈ IsLocalRing.maximalIdeal (C.presheaf.stalk z) →
            v.adicValuation (algebraMap (C.presheaf.stalk z) C.functionField s) < 1))} (0 : Divisor k C.functionField)).subtype

    let φ : ↥(lSpaceOn {v : Place k C.functionField | ∃ z : C, z ∈ U ∧ (∀ s : C.presheaf.stalk z,
          v.adicValuation (algebraMap (C.presheaf.stalk z) C.functionField s) ≤ 1 ∧
          (s ∈ IsLocalRing.maximalIdeal (C.presheaf.stalk z) →
            v.adicValuation (algebraMap (C.presheaf.stalk z) C.functionField s) < 1))} (0 : Divisor k C.functionField)) →ₗ[k]
        ((z : {z : C // z ∈ U ∧ IsClosed ({z} : Set C)}) → Q z.1) :=
      LinearMap.pi fun z => (Submodule.mkQ _).comp
        (Submodule.inclusion (lSpaceOn_anti (S₀ := {v : Place k C.functionField | (∀ s : C.presheaf.stalk z.1,
          v.adicValuation (algebraMap (C.presheaf.stalk z.1) C.functionField s) ≤ 1 ∧
          (s ∈ IsLocalRing.maximalIdeal (C.presheaf.stalk z.1) →
            v.adicValuation (algebraMap (C.presheaf.stalk z.1) C.functionField s) < 1))})
          (S₁ := {v : Place k C.functionField | ∃ z : C, z ∈ U ∧ (∀ s : C.presheaf.stalk z,
          v.adicValuation (algebraMap (C.presheaf.stalk z) C.functionField s) ≤ 1 ∧
          (s ∈ IsLocalRing.maximalIdeal (C.presheaf.stalk z) →
            v.adicValuation (algebraMap (C.presheaf.stalk z) C.functionField s) < 1))})
          (fun v hv => ⟨z.1, z.2.1, hv⟩) 0))
    Function.Surjective φ ∧
      LinearMap.ker φ = (Submodule.span k (Set.range (C.presheaf.germ U (genericPoint C) hU).hom)).comap
        (lSpaceOn {v : Place k C.functionField | ∃ z : C, z ∈ U ∧ (∀ s : C.presheaf.stalk z,
          v.adicValuation (algebraMap (C.presheaf.stalk z) C.functionField s) ≤ 1 ∧
          (s ∈ IsLocalRing.maximalIdeal (C.presheaf.stalk z) →
            v.adicValuation (algebraMap (C.presheaf.stalk z) C.functionField s) < 1))} (0 : Divisor k C.functionField)).subtype ∧
      {z : {z : C // z ∈ U ∧ IsClosed ({z} : Set C)} | Nontrivial (Q z.1)}.Finite ∧
      ∀ z : {z : C // z ∈ U ∧ IsClosed ({z} : Set C)}, FiniteDimensional k (Q z.1) := by
  letI := (AlgebraicCurve.baseToFunctionField c).toAlgebra
  haveI : Nonempty U := ⟨⟨genericPoint C, hU⟩⟩

  have hpts : ∀ z : C, z = genericPoint C ∨ IsClosed ({z} : Set C) :=
    (AlgebraicCurve.CurveModel.surjective_and_eq_genericPoint_or_isClosed_singleton_of_isIso_stalkMap k c M ν hν hbir).2

  have hB : Module.Finite Γ(C, U) ↥(integralClosure Γ(C, U) C.functionField) :=
    AlgebraicCurve.CurveModel.finite_integralClosure_sections_of_isIso_stalkMap k c M ν hν hbir U hUaff

  have hGLG := AlgebraicCurve.surjective_and_ker_pi_span_mul_quotient_of_finite k c hpts U hUaff hU
    (integralClosure Γ(C, U) C.functionField) hB

  have hT : Submodule.span k (integralClosure Γ(C, U) C.functionField : Set C.functionField) =
      lSpaceOn {v : Place k C.functionField | ∃ z : C, z ∈ U ∧ (∀ s : C.presheaf.stalk z,
          v.adicValuation (algebraMap (C.presheaf.stalk z) C.functionField s) ≤ 1 ∧
          (s ∈ IsLocalRing.maximalIdeal (C.presheaf.stalk z) →
            v.adicValuation (algebraMap (C.presheaf.stalk z) C.functionField s) < 1))} (0 : Divisor k C.functionField) :=
    (AlgebraicCurve.lSpaceOn_setOf_exists_centre_eq_span_integralClosure k c hK U hUaff).symm
  have hTz : (fun z : {z : C // z ∈ U ∧ IsClosed ({z} : Set C)} =>
        Submodule.span k ((integralClosure Γ(C, U) C.functionField : Set C.functionField) *
          Set.range (algebraMap (C.presheaf.stalk z.1) C.functionField))) =
      (fun z : {z : C // z ∈ U ∧ IsClosed ({z} : Set C)} =>
        lSpaceOn {v : Place k C.functionField | (∀ s : C.presheaf.stalk z.1,
          v.adicValuation (algebraMap (C.presheaf.stalk z.1) C.functionField s) ≤ 1 ∧
          (s ∈ IsLocalRing.maximalIdeal (C.presheaf.stalk z.1) →
            v.adicValuation (algebraMap (C.presheaf.stalk z.1) C.functionField s) < 1))} (0 : Divisor k C.functionField)) :=
    funext fun z => (AlgebraicCurve.lSpaceOn_setOf_centre_eq_span_integralClosure_mul k c hK hpts U hUaff z.1 z.2.1 z.2.2).symm

  exact concl_congr (ι := {z : C // z ∈ U ∧ IsClosed ({z} : Set C)})
    (fun z => Submodule.span k (Set.range (algebraMap (C.presheaf.stalk z.1) C.functionField)))
    (Submodule.span k (Set.range (C.presheaf.germ U (genericPoint C) hU).hom))
    _ _ hT hTz hGLG

end

#print axioms solution

end S_AlgebraicCurve_surjective_and_ker_pi_lSpaceOn_centre_quotient_of_isAffineOpen
end P2MW
export P2MW.S_AlgebraicCurve_surjective_and_ker_pi_lSpaceOn_centre_quotient_of_isAffineOpen (solution)
