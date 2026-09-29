-- Prove2me | solution 1 for AlgebraicCurve.exists_forall_mem_span_pow_mul_of_forall_ord_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.4153+00:00
-- url     : https://prove2.me/submissions/c0ea5fcd-268d-5f6b-a0e9-a35032304489

import Mathlib
import Definitions.Def_AlgebraicCurve_Repartitions
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_AdelicIndex
import Theorems.Thm_AlgebraicCurve_lSpace_nsmul_succ_poleDivisor_le_sup_map_mulLeft_of_ell_eq
import Theorems.Thm_AlgebraicCurve_exists_ell_nsmul_eq_of_isAlgClosed_of_transcendental
import Theorems.Thm_AlgebraicCurve_finiteDimensional_lSpace
import Theorems.Thm_AlgebraicCurve_isCurveOver_of_isAlgClosed_of_transcendental
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_exists_forall_mem_span_pow_mul_of_forall_ord_nonneg
p2m_attr_erase "instance" "AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupDivisor AlgebraicCurve.Pic0.instModuleZModTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instDistribMulActionTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instSMulTorsion AlgebraicCurve.SemilinearAut.instMulActionSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instSMulCommClassZModTorsion AlgebraicCurve.SemilinearAut.instMulSemiringActionSubtypeProdRingAutMemSubgroup instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions"
p2m_attr_erase "simp" "AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.SemilinearAut.toRingAut_inv AlgebraicCurve.SemilinearAut.smul_def"
p2m_attr_erase "simp" "AlgebraicCurve.SemilinearAut.smul_single AlgebraicCurve.SemilinearAut.smul_toValuationSubring AlgebraicCurve.SemilinearAut.baseAut_inv AlgebraicCurve.SemilinearAut.baseAut_ofAlgAut AlgebraicCurve.SemilinearAut.toRingAut_ofAlgAut AlgebraicCurve.SemilinearAut.torsionRep_apply AlgebraicCurve.SemilinearAut.toRingAut_one AlgebraicCurve.SemilinearAut.deg_smul AlgebraicCurve.SemilinearAut.degree_smul AlgebraicCurve.SemilinearAut.coe_degZeroSMulHom AlgebraicCurve.SemilinearAut.baseAut_mul AlgebraicCurve.SemilinearAut.coe_smulValuationSubringEquiv_apply AlgebraicCurve.SemilinearAut.baseAut_one AlgebraicCurve.SemilinearAut.ofAlgAut_smul AlgebraicCurve.SemilinearAut.coe_torsion_smul AlgebraicCurve.SemilinearAut.toRingAut_mul AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.jqNModC_one ModularCurve.qExpand_coeff_mul ModularCurve.qExpandₐ_apply ModularCurve.jqN_one ModularCurve.qExpand_single ModularCurve.dedekindPsi_one ModularCurve.ModularPolynomialData.mk.sizeOf_spec ModularCurve.evalAtJ_X ModularCurve.ModularPolynomialData.mk.injEq ModularCurve.constantCoeff_jNum ModularCurve.constantCoeff_eisenstein4 ModularCurve.qExpand_C ModularCurve.coeff_jq_neg_one ModularCurve.constantCoeff_jNumQ ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen"
p2m_attr_erase "simp" "ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq"

set_option autoImplicit false
set_option maxHeartbeats 8000000

open AlgebraicCurve

noncomputable section

theorem fd_lSpace_nsmul_poleDivisor
    {K F : Type*} [Field K] [IsAlgClosed K] [Field F] [Algebra K F]
    (x : F) (hx : Transcendental K x)
    [FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F]
    (D : Divisor K F) (hD : ∀ v : Place K F, D v = max 0 (-v.ord x)) :
    ∀ M : ℕ, FiniteDimensional K ↥(LSpace (M • D)) := by
  haveI : IsCurveOver K F :=
    AlgebraicCurve.isCurveOver_of_isAlgClosed_of_transcendental x hx
  have hell0 : ell (0 : Divisor K F) = 1 :=
    (AlgebraicCurve.exists_ell_nsmul_eq_of_isAlgClosed_of_transcendental x hx D hD).1
  haveI : FiniteDimensional K ↥(LSpace (0 : Divisor K F)) :=
    FiniteDimensional.of_finrank_eq_succ (n := 0) hell0
  exact fun M => AlgebraicCurve.finiteDimensional_lSpace (M • D)

theorem exists_mem_lSpace_nsmul_of_forall_ord_nonneg
    {K F : Type*} [Field K] [Field F] [Algebra K F]
    (x : F) (D : Divisor K F) (hD : ∀ v : Place K F, D v = max 0 (-v.ord x))
    (h : F) (hh : ∀ v : Place K F, 0 ≤ v.ord x → 0 ≤ v.ord h) :
    ∃ M : ℕ, h ∈ LSpace (M • D) := by
  rcases eq_or_ne h 0 with rfl | hh0
  · exact ⟨0, (LSpace _).zero_mem⟩
  refine ⟨D.support.sup (fun v => (-(v.ord h)).toNat), mem_lSpace_iff_ord.mpr (Or.inr fun v => ?_)⟩
  set M := D.support.sup (fun v => (-(v.ord h)).toNat) with hM
  simp only [Finsupp.coe_smul, Pi.smul_apply, nsmul_eq_mul, neg_le]

  by_cases hv : v ∈ D.support
  · have hDv1 : (1:ℤ) ≤ D v := by
      have hne := Finsupp.mem_support_iff.mp hv
      have := hD v; omega
    have hMv : ((-(v.ord h)).toNat : ℤ) ≤ (M:ℤ) := by
      have h' := Finset.le_sup (f := fun w => (-(w.ord h)).toNat) hv
      exact_mod_cast h'
    calc -(v.ord h) ≤ ((-(v.ord h)).toNat : ℤ) := Int.self_le_toNat _
      _ ≤ (M:ℤ) := hMv
      _ = (M:ℤ) * 1 := (mul_one _).symm
      _ ≤ (M:ℤ) * D v := mul_le_mul_of_nonneg_left hDv1 (Nat.cast_nonneg M)
  · have hDv0 : D v = 0 := Finsupp.notMem_support_iff.mp hv
    rw [hDv0, mul_zero]
    have hox : 0 ≤ v.ord x := by
      have := hD v; rw [hDv0] at this; omega
    exact neg_nonpos_of_nonneg (hh v hox)

theorem solution
    {K F : Type*} [Field K] [IsAlgClosed K] [Field F] [Algebra K F]
    (x : F) (hx : Transcendental K x)
    [FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F]
    (D : Divisor K F) (hD : ∀ v : Place K F, D v = max 0 (-v.ord x)) :
    ∃ M₁ : ℕ, ∀ h : F, (∀ v : Place K F, 0 ≤ v.ord x → 0 ≤ v.ord h) →
      h ∈ Submodule.span K {g : F | ∃ j : ℕ, ∃ y ∈ LSpace (M₁ • D), g = x ^ j * y} := by
  classical
  obtain ⟨_, M₀, hM₀1, hell⟩ :=
    AlgebraicCurve.exists_ell_nsmul_eq_of_isAlgClosed_of_transcendental x hx D hD
  have hFD : ∀ M : ℕ, FiniteDimensional K ↥(LSpace (M • D)) :=
    fd_lSpace_nsmul_poleDivisor x hx D hD
  set M₁ := M₀ + 1
  refine ⟨M₁, fun h hh => ?_⟩
  set SP := Submodule.span K {g : F | ∃ j : ℕ, ∃ y ∈ LSpace (M₁ • D), g = x ^ j * y} with hSP

  have hD0 : (0 : Divisor K F) ≤ D := fun v => by rw [hD]; exact le_max_left _ _

  have hbase : (LSpace (M₁ • D) : Submodule K F) ≤ SP := fun y hy =>
    Submodule.subset_span ⟨0, y, hy, by rw [pow_zero, one_mul]⟩

  have hxSP : (SP.map (LinearMap.mulLeft K x) : Submodule K F) ≤ SP := by
    rw [Submodule.map_span, Submodule.span_le]
    rintro _ ⟨_, ⟨j, y, hy, rfl⟩, rfl⟩
    refine Submodule.subset_span ⟨j+1, y, hy, ?_⟩
    rw [LinearMap.mulLeft_apply]; ring

  have hup : ∀ k, (LSpace ((M₁ + k) • D) : Submodule K F) ≤ SP := by
    intro k
    induction k with
    | zero => simpa using hbase
    | succ n ih =>
      have hdegD : (0:ℤ) ≤ Divisor.degree D := by
        simp only [Divisor.degree, Finsupp.liftAddHom_apply, AddMonoidHom.coe_mulRight,
          Finsupp.sum]
        exact Finset.sum_nonneg fun v _ => mul_nonneg (by simpa using hD0 v) (Nat.cast_nonneg _)
      have hstep := AlgebraicCurve.lSpace_nsmul_succ_poleDivisor_le_sup_map_mulLeft_of_ell_eq
        x D hD hFD M₀ (Divisor.degree D).toNat (genusFF K F)
        (fun N hN => by rw [hell N hN, Int.toNat_of_nonneg hdegD])
        (M₁ + n) (by omega)
      refine hstep.trans (sup_le ih ?_)
      exact (Submodule.map_mono ih).trans hxSP

  have hall : ∀ m, (LSpace (m • D) : Submodule K F) ≤ SP := fun m => by
    refine (lSpace_mono ?_).trans (hup m)

    intro v
    have hDv : (0:ℤ) ≤ D v := by simpa using hD0 v
    simp only [Finsupp.coe_smul, Pi.smul_apply, nsmul_eq_mul]
    have hmle : (m:ℤ) ≤ ((M₁+m:ℕ):ℤ) := by exact_mod_cast Nat.le_add_left m M₁
    exact mul_le_mul_of_nonneg_right hmle hDv

  obtain ⟨M, hMmem⟩ := exists_mem_lSpace_nsmul_of_forall_ord_nonneg x D hD h hh
  exact hall M hMmem

end
end S_AlgebraicCurve_exists_forall_mem_span_pow_mul_of_forall_ord_nonneg
end P2MW
export P2MW.S_AlgebraicCurve_exists_forall_mem_span_pow_mul_of_forall_ord_nonneg (solution)
