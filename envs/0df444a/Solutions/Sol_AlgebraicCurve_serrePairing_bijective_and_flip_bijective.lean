-- Prove2me | solution 1 for AlgebraicCurve.serrePairing_bijective_and_flip_bijective
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.935278+00:00
-- url     : https://prove2.me/submissions/5d137321-8550-5527-82b8-40a021c4203d

import Mathlib
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Definitions.Def_AlgebraicCurve_Repartitions
import Definitions.Def_AlgebraicCurve_AdelicIndex
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_ModularCurve_CanonicalDivisor
import Definitions.Def_AlgebraicCurve_CanonicalDivisor
import Definitions.Def_AlgebraicCurve_LocalResidue
import Definitions.Def_AlgebraicCurve_WeilOfKaehler
import Definitions.Def_AlgebraicCurve_RegularDifferentials
import Definitions.Def_AlgebraicCurve_CechSectionsOfDivisor
import Definitions.Def_AlgebraicCurve_SerrePairing
import Theorems.Thm_AlgebraicCurve_finite_H1_and_exists_linearEquiv_dual_H1_omegaSpace
import Theorems.Thm_AlgebraicCurve_exists_linearEquiv_regularDifferentials_omegaSpace_zero
import Theorems.Thm_AlgebraicCurve_cechH1ToH1_bijective
import Theorems.Thm_AlgebraicCurve_exists_genus_riemannIndex_of_isCurveOver
import Theorems.Thm_AlgebraicCurve_exists_riemannGenusReachedAt_of_bounded
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_serrePairing_bijective_and_flip_bijective
p2m_attr_erase "instance" "AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupDivisor AlgebraicCurve.Pic0.instModuleZModTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instDistribMulActionTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instSMulTorsion AlgebraicCurve.SemilinearAut.instMulActionSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instSMulCommClassZModTorsion AlgebraicCurve.SemilinearAut.instMulSemiringActionSubtypeProdRingAutMemSubgroup instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt"
p2m_attr_erase "simp" "AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.SemilinearAut.toRingAut_inv AlgebraicCurve.SemilinearAut.smul_def AlgebraicCurve.SemilinearAut.smul_single AlgebraicCurve.SemilinearAut.smul_toValuationSubring AlgebraicCurve.SemilinearAut.baseAut_inv AlgebraicCurve.SemilinearAut.baseAut_ofAlgAut AlgebraicCurve.SemilinearAut.toRingAut_ofAlgAut AlgebraicCurve.SemilinearAut.torsionRep_apply AlgebraicCurve.SemilinearAut.toRingAut_one AlgebraicCurve.SemilinearAut.deg_smul AlgebraicCurve.SemilinearAut.degree_smul AlgebraicCurve.SemilinearAut.coe_degZeroSMulHom AlgebraicCurve.SemilinearAut.baseAut_mul AlgebraicCurve.SemilinearAut.coe_smulValuationSubringEquiv_apply AlgebraicCurve.SemilinearAut.baseAut_one AlgebraicCurve.SemilinearAut.ofAlgAut_smul"
p2m_attr_erase "simp" "AlgebraicCurve.SemilinearAut.coe_torsion_smul AlgebraicCurve.SemilinearAut.toRingAut_mul AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.jqNModC_one ModularCurve.qExpand_coeff_mul ModularCurve.qExpandₐ_apply ModularCurve.jqN_one ModularCurve.qExpand_single ModularCurve.dedekindPsi_one ModularCurve.ModularPolynomialData.mk.sizeOf_spec ModularCurve.evalAtJ_X ModularCurve.ModularPolynomialData.mk.injEq ModularCurve.constantCoeff_jNum ModularCurve.constantCoeff_eisenstein4 ModularCurve.qExpand_C ModularCurve.coeff_jq_neg_one ModularCurve.constantCoeff_jNumQ ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver"
p2m_attr_erase "simp" "AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal"

set_option autoImplicit false
set_option maxHeartbeats 800000

open KaehlerDifferential

namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "Place Divisor HasPrincipalDivisors repartitions H1 LSpace ConstantsAreBase adeleSpace indexOfSpecialty RiemannGenusReachedAt IsCurveOver HasCanonicalDivisor genus HasCanonicalLocalResidueKStar weilOfKaehler weilOfKaehler_apply ResidueTheorem regularDifferentials lSpaceOn cechH1 extendOffChart cechH1ToH1 cechH1ToH1_mk coe_extendOffChart_mem_adeleSpace residueSumOffChart_def serrePairing serrePairing_apply_mk finite_H1_and_exists_linearEquiv_dual_H1_omegaSpace exists_linearEquiv_regularDifferentials_omegaSpace_zero cechH1ToH1_bijective exists_genus_riemannIndex_of_isCurveOver exists_riemannGenusReachedAt_of_bounded"
p2m_open "AlgebraicCurve"

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

theorem finiteDimensional_lSpace_zero_of_constantsAreBase (hC : ConstantsAreBase K F) :
    FiniteDimensional K ↥(LSpace (0 : Divisor K F)) := by
  have h : LSpace (0 : Divisor K F) = LinearMap.range (Algebra.linearMap K F) := hC
  rw [h]
  infer_instance

theorem exists_riemannGenusReachedAt_of_constantsAreBase [PerfectField K] [Algebra.EssFiniteType K F]
    [IsCurveOver K F] (hC : ConstantsAreBase K F) :
    ∃ (γ : ℤ) (D₀ : Divisor K F), RiemannGenusReachedAt γ D₀ := by
  haveI := finiteDimensional_lSpace_zero_of_constantsAreBase hC
  obtain ⟨γ, hγ⟩ := exists_genus_riemannIndex_of_isCurveOver (K := K) (F := F) hC
  refine exists_riemannGenusReachedAt_of_bounded ⟨γ - 1, fun D => ?_⟩
  have h := (hγ D).2
  have hi : (0 : ℤ) ≤ (indexOfSpecialty D : ℤ) := Int.natCast_nonneg _
  linarith

section Generic

variable [HasCanonicalLocalResidueKStar K F] [∀ v : Place K F, v.DCoordGenerates] [Nontrivial Ω[F⁄K]]
  [HasCanonicalDivisor (K := K) (F := F)] [HasPrincipalDivisors K F]

theorem serrePairing_apply_mk_eq_weilOfKaehler (hRT : ResidueTheorem K F) {S₀ S₁ : Set (Place K F)}
    (hcover : S₀ ∪ S₁ = Set.univ) (ω : ↥(regularDifferentials K F)) (hω : (ω : Ω[F⁄K]) ≠ 0)
    (f : ↥(lSpaceOn (S₀ ∩ S₁) (0 : Divisor K F))) :
    serrePairing hRT hcover ω (Submodule.Quotient.mk f)
      = weilOfKaehler K F hω ⟨((extendOffChart K S₀ (f : F) : ↥(repartitions K F)) : Place K F → F),
          coe_extendOffChart_mem_adeleSpace S₀ (f : F)⟩ := by
  rw [serrePairing_apply_mk, residueSumOffChart_def, weilOfKaehler_apply]

theorem serrePairing_zero_left_apply (hRT : ResidueTheorem K F) {S₀ S₁ : Set (Place K F)}
    (hcover : S₀ ∪ S₁ = Set.univ) (x : cechH1 S₀ S₁ (0 : Divisor K F)) :
    serrePairing hRT hcover 0 x = 0 := by
  rw [map_zero, LinearMap.zero_apply]

end Generic

theorem serrePairing_bijective_and_flip_bijective' {K : Type*} {F : Type*} [Field K] [Field F] [Algebra K F]
    [PerfectField K] [Algebra.EssFiniteType K F] [IsCurveOver K F]
    [HasCanonicalDivisor (K := K) (F := F)] [∀ v : Place K F, v.DCoordGenerates]
    [HasCanonicalLocalResidueKStar K F]
    (hC : ConstantsAreBase K F) (hRT : ResidueTheorem K F)
    {S₀ S₁ : Set (Place K F)} (hcover : S₀ ∪ S₁ = Set.univ) (h₀ : ∃ v, v ∉ S₀) (h₁ : ∃ v, v ∉ S₁) :
    Function.Bijective (serrePairing hRT hcover) ∧
      Function.Bijective (serrePairing hRT hcover).flip := by
  classical

  haveI := finiteDimensional_lSpace_zero_of_constantsAreBase hC
  obtain ⟨γ, D₀, hγ⟩ := exists_riemannGenusReachedAt_of_constantsAreBase (K := K) (F := F) hC
  have hι : Function.Bijective (cechH1ToH1 hcover (0 : Divisor K F)) :=
    cechH1ToH1_bijective hγ hcover h₀ h₁ 0
  let ιe : cechH1 S₀ S₁ (0 : Divisor K F) ≃ₗ[K] H1 (0 : Divisor K F) :=
    LinearEquiv.ofBijective _ hι
  obtain ⟨hfin, e₀, he₀⟩ := finite_H1_and_exists_linearEquiv_dual_H1_omegaSpace (K := K) (F := F) hC 0
  obtain ⟨e₂, he₂⟩ := exists_linearEquiv_regularDifferentials_omegaSpace_zero (K := K) (F := F) hC hRT

  let E : ↥(regularDifferentials K F) ≃ₗ[K] Module.Dual K (cechH1 S₀ S₁ (0 : Divisor K F)) :=
    e₂.trans (e₀.symm.trans ιe.dualMap)
  have key : ∀ (ω : ↥(regularDifferentials K F)) (x : cechH1 S₀ S₁ (0 : Divisor K F)),
      serrePairing hRT hcover ω x = E ω x := by
    intro ω x
    obtain ⟨f, rfl⟩ := Submodule.Quotient.mk_surjective _ x

    have hR : E ω (Submodule.Quotient.mk f)
        = (e₂ ω : Module.Dual K ↥(adeleSpace K F))
            ⟨((extendOffChart K S₀ (f : F) : ↥(repartitions K F)) : Place K F → F),
              coe_extendOffChart_mem_adeleSpace S₀ (f : F)⟩ := by
      show (ιe.dualMap (e₀.symm (e₂ ω))) (Submodule.Quotient.mk f) = _
      rw [LinearEquiv.dualMap_apply, LinearEquiv.ofBijective_apply, cechH1ToH1_mk]
      have h := he₀ (e₀.symm (e₂ ω))
        ⟨((extendOffChart K S₀ (f : F) : ↥(repartitions K F)) : Place K F → F),
          coe_extendOffChart_mem_adeleSpace S₀ (f : F)⟩ (extendOffChart K S₀ (f : F)).2
      rw [LinearEquiv.apply_symm_apply] at h
      rw [h]
    rw [hR]
    rcases eq_or_ne (ω : Ω[F⁄K]) 0 with hω | hω
    · have hω' : ω = 0 := Subtype.ext hω
      rw [hω', serrePairing_zero_left_apply, map_zero, Submodule.coe_zero, LinearMap.zero_apply]
    · rw [serrePairing_apply_mk_eq_weilOfKaehler hRT hcover ω hω, he₂ ω hω]
  have hfun : ⇑(serrePairing hRT hcover) = ⇑E :=
    funext fun ω => LinearMap.ext fun x => key ω x
  have hleft : Function.Bijective (serrePairing hRT hcover) := by
    rw [hfun]
    exact E.bijective
  refine ⟨hleft, ?_⟩

  haveI : Module.Finite K (H1 (0 : Divisor K F)) := hfin
  haveI : Module.Finite K (cechH1 S₀ S₁ (0 : Divisor K F)) := Module.Finite.equiv ιe.symm
  haveI : Module.Finite K ↥(regularDifferentials K F) := Module.Finite.equiv E.symm

  have hinj : Function.Injective (serrePairing hRT hcover).flip := by
    rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
    intro x hx
    rw [LinearMap.mem_ker] at hx
    have hall : ∀ φ : Module.Dual K (H1 (0 : Divisor K F)), φ (ιe x) = 0 := by
      intro φ
      let ω := (e₂.trans e₀.symm).symm φ
      have h1 : serrePairing hRT hcover ω x = 0 := by
        rw [← LinearMap.flip_apply, hx, LinearMap.zero_apply]
      rw [key ω x] at h1
      have h2 : E ω x = φ (ιe x) := by
        show (ιe.dualMap (e₀.symm (e₂ ((e₂.trans e₀.symm).symm φ)))) x = φ (ιe x)
        rw [LinearEquiv.dualMap_apply]
        congr 1
        show (e₂.trans e₀.symm) ((e₂.trans e₀.symm).symm φ) = φ
        exact LinearEquiv.apply_symm_apply _ φ
      rw [← h2]
      exact h1
    have hx0 : ιe x = 0 := (Module.forall_dual_apply_eq_zero_iff K (ιe x)).mp hall
    exact ιe.injective (by rw [hx0, map_zero])
  refine (LinearMap.injective_iff_surjective_of_finrank_eq_finrank ?_).mp hinj |> fun hsurj => ⟨hinj, hsurj⟩
  rw [Subspace.dual_finrank_eq, E.finrank_eq, Subspace.dual_finrank_eq]

end AlgebraicCurve

open _root_.AlgebraicCurve _root_.P2MW.S_AlgebraicCurve_serrePairing_bijective_and_flip_bijective.AlgebraicCurve in
theorem solution {K : Type*} {F : Type*} [Field K] [Field F] [Algebra K F]
    [PerfectField K] [Algebra.EssFiniteType K F] [IsCurveOver K F]
    [HasCanonicalDivisor (K := K) (F := F)] [∀ v : Place K F, v.DCoordGenerates]
    [HasCanonicalLocalResidueKStar K F]
    (hC : ConstantsAreBase K F) (hRT : ResidueTheorem K F)
    {S₀ S₁ : Set (Place K F)} (hcover : S₀ ∪ S₁ = Set.univ) (h₀ : ∃ v, v ∉ S₀) (h₁ : ∃ v, v ∉ S₁) :
    Function.Bijective (serrePairing hRT hcover) ∧
      Function.Bijective (serrePairing hRT hcover).flip :=
  serrePairing_bijective_and_flip_bijective' hC hRT hcover h₀ h₁

end S_AlgebraicCurve_serrePairing_bijective_and_flip_bijective
end P2MW
export P2MW.S_AlgebraicCurve_serrePairing_bijective_and_flip_bijective (solution)
