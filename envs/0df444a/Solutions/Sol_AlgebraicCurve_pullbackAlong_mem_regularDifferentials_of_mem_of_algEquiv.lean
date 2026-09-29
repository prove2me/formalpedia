-- Prove2me | solution 1 for AlgebraicCurve.pullbackAlong_mem_regularDifferentials_of_mem_of_algEquiv
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.4153+00:00
-- url     : https://prove2.me/submissions/004292c3-d880-5fed-be18-0bcec63e6644

import Mathlib
import Definitions.Def_AlgebraicCurve_RegularDifferentials
import Definitions.Def_AlgebraicCurve_DifferentialPushPull
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_RatFuncPlaces
import Theorems.Thm_P2M_Dup_AlgebraicCurve_Place_mem_iff_ord_nonneg
import Theorems.Thm_AlgebraicCurve_localUnitDerivativeRegular_of_isCurveOver
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_pullbackAlong_mem_regularDifferentials_of_mem_of_algEquiv
p2m_attr_erase "instance" "instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt"
p2m_attr_erase "simp" "AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.jqNModC_one ModularCurve.qExpand_coeff_mul ModularCurve.qExpandₐ_apply ModularCurve.jqN_one ModularCurve.qExpand_single ModularCurve.dedekindPsi_one ModularCurve.ModularPolynomialData.mk.sizeOf_spec ModularCurve.evalAtJ_X ModularCurve.ModularPolynomialData.mk.injEq ModularCurve.constantCoeff_jNum ModularCurve.constantCoeff_eisenstein4 ModularCurve.qExpand_C ModularCurve.coeff_jq_neg_one ModularCurve.constantCoeff_jNumQ ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply"
p2m_attr_erase "simp" "ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal"

set_option autoImplicit false

open AlgebraicCurve

namespace RegPullIso

variable {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F']

theorem mem_of_ord_nonneg {L : Type*} [Field L] [Algebra K L] (v : Place K L) {f : L} (h : 0 ≤ v.ord f) :
    f ∈ v.toValuationSubring := by
  rcases eq_or_ne f 0 with rfl | hf
  · exact zero_mem _
  · exact (v.mem_iff_ord_nonneg hf).mpr h

noncomputable def pullPlace (Φ : F ≃ₐ[K] F') (w : Place K F') : Place K F :=
  Place.congrRingEquiv (Φ.symm : F' ≃+* F) (fun a => by
    show Φ.symm (algebraMap K F' a) = algebraMap K F a
    exact Φ.symm.commutes a) w

theorem mem_pullPlace_iff (Φ : F ≃ₐ[K] F') (w : Place K F') (f : F) :
    f ∈ (pullPlace Φ w).toValuationSubring ↔ Φ f ∈ w.toValuationSubring := by
  rw [pullPlace, Place.congrRingEquiv_toValuationSubring, ValuationSubring.mem_comap]
  exact Iff.rfl

theorem exists_mem_D_eq_smul_dCoord [PerfectField K] [Algebra.EssFiniteType K F'] [IsCurveOver K F']
    [∀ w : Place K F', w.DCoordGenerates] (v : Place K F') {g : F'} (hg : g ∈ v.toValuationSubring) :
    ∃ c ∈ v.toValuationSubring, KaehlerDifferential.D K F' g = c • v.dCoord := by
  have key : ∀ u : F', u ≠ 0 → v.ord u = 0 →
      ∃ c ∈ v.toValuationSubring, KaehlerDifferential.D K F' u = c • v.dCoord := by
    intro u hu0 hu
    refine ⟨v.differentialCoeff (KaehlerDifferential.D K F' u), ?_, (v.differentialCoeff_smul_dCoord _).symm⟩
    rcases localUnitDerivativeRegular_of_isCurveOver v u hu0 hu with h | h
    · rw [h]; exact zero_mem _
    · exact mem_of_ord_nonneg v h
  set a : v.toValuationSubring := ⟨g, hg⟩ with ha
  by_cases hunit : IsUnit a
  · have hord : v.ord g = 0 := by
      have := v.ord_coe_unit hunit.unit
      rwa [IsUnit.unit_spec] at this
    have hg0 : g ≠ 0 := by
      intro h0
      apply hunit.ne_zero
      exact Subtype.ext h0
    exact key g hg0 hord
  · have h1 : IsUnit (1 + a) := by
      rcases IsLocalRing.isUnit_or_isUnit_one_sub_self (-a) with h | h
      · exact absurd (IsUnit.neg_iff _ |>.mp h) hunit
      · simpa using h
    have hord : v.ord (1 + g) = 0 := by
      have := v.ord_coe_unit h1.unit
      rwa [IsUnit.unit_spec] at this
    have hne : (1 + g) ≠ 0 := by
      intro h0
      apply h1.ne_zero
      exact Subtype.ext h0
    obtain ⟨c, hc, hcD⟩ := key (1 + g) hne hord
    refine ⟨c, hc, ?_⟩
    rw [← hcD, map_add, Derivation.map_one_eq_zero, zero_add]

theorem main [PerfectField K] [Algebra.EssFiniteType K F'] [IsCurveOver K F']
    [∀ w : Place K F', w.DCoordGenerates]
    (Φ : F ≃ₐ[K] F') {η : Ω[F⁄K]} (hη : η ∈ regularDifferentials K F) :
    Differential.pullbackAlong (Φ : F →ₐ[K] F') η ∈ regularDifferentials K F' := by
  rw [mem_regularDifferentials_iff] at hη ⊢
  intro w
  obtain ⟨f, hf, hηf⟩ := hη (pullPlace Φ w)
  obtain ⟨π, hπ1, hπd⟩ := (pullPlace Φ w).exists_ord_eq_one_and_dCoord_eq
  have hwf : Φ f ∈ w.toValuationSubring := (mem_pullPlace_iff Φ w f).mp hf
  have hπmem : π ∈ (pullPlace Φ w).toValuationSubring :=
    mem_of_ord_nonneg (pullPlace Φ w) (by rw [hπ1]; exact zero_le_one)
  have hwπ : Φ π ∈ w.toValuationSubring := (mem_pullPlace_iff Φ w π).mp hπmem
  obtain ⟨c, hc, hcD⟩ := exists_mem_D_eq_smul_dCoord w hwπ
  refine ⟨Φ f * c, mul_mem hwf hc, ?_⟩
  rw [hηf, hπd, Differential.pullbackAlong_smul, Differential.pullbackAlong_D, AlgEquiv.coe_algHom, hcD,
    mul_smul]

end RegPullIso

theorem solution
    {K : Type*} [Field K] [PerfectField K] {F F' : Type*} [Field F] [Field F'] [Algebra K F] [Algebra K F']
    [Algebra.EssFiniteType K F'] [IsCurveOver K F']
    [∀ v : Place K F, v.DCoordGenerates] [∀ w : Place K F', w.DCoordGenerates]
    (Φ : F ≃ₐ[K] F') (η : Ω[F⁄K]) (hη : η ∈ regularDifferentials K F) :
    Differential.pullbackAlong (Φ : F →ₐ[K] F') η ∈ regularDifferentials K F' :=
  RegPullIso.main Φ hη

end S_AlgebraicCurve_pullbackAlong_mem_regularDifferentials_of_mem_of_algEquiv
end P2MW
export P2MW.S_AlgebraicCurve_pullbackAlong_mem_regularDifferentials_of_mem_of_algEquiv (solution)
