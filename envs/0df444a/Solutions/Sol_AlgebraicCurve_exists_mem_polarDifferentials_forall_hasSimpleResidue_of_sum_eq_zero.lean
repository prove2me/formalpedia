-- Prove2me | solution 1 for AlgebraicCurve.exists_mem_polarDifferentials_forall_hasSimpleResidue_of_sum_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.4153+00:00
-- url     : https://prove2.me/submissions/411caaec-2fac-558e-a286-68c9d8a9a6c3

import Mathlib
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_CanonicalDivisor
import Definitions.Def_AlgebraicCurve_PolarDifferentials
import Theorems.Thm_AlgebraicCurve_existsUnique_hasSimpleResidue_of_hasSimplePoleAt
import Theorems.Thm_AlgebraicCurve_sum_eq_zero_of_forall_hasSimpleResidue_of_mem_polarDifferentials
import Theorems.Thm_AlgebraicCurve_finite_and_finrank_polarDifferentials_eq
import Theorems.Thm_AlgebraicCurve_finite_and_finrank_regularDifferentials_eq_genus
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_exists_mem_polarDifferentials_forall_hasSimpleResidue_of_sum_eq_zero
p2m_attr_erase "instance" "AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupDivisor AlgebraicCurve.Pic0.instModuleZModTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instDistribMulActionTorsion"
p2m_attr_erase "instance" "AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instSMulTorsion AlgebraicCurve.SemilinearAut.instMulActionSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instSMulCommClassZModTorsion AlgebraicCurve.SemilinearAut.instMulSemiringActionSubtypeProdRingAutMemSubgroup instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy"
p2m_attr_erase "simp" "AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint"
p2m_attr_erase "simp" "AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.SemilinearAut.toRingAut_inv AlgebraicCurve.SemilinearAut.smul_def AlgebraicCurve.SemilinearAut.smul_single AlgebraicCurve.SemilinearAut.smul_toValuationSubring AlgebraicCurve.SemilinearAut.baseAut_inv AlgebraicCurve.SemilinearAut.baseAut_ofAlgAut AlgebraicCurve.SemilinearAut.toRingAut_ofAlgAut AlgebraicCurve.SemilinearAut.torsionRep_apply AlgebraicCurve.SemilinearAut.toRingAut_one AlgebraicCurve.SemilinearAut.deg_smul"
p2m_attr_erase "simp" "AlgebraicCurve.SemilinearAut.degree_smul AlgebraicCurve.SemilinearAut.coe_degZeroSMulHom AlgebraicCurve.SemilinearAut.baseAut_mul AlgebraicCurve.SemilinearAut.coe_smulValuationSubringEquiv_apply AlgebraicCurve.SemilinearAut.baseAut_one AlgebraicCurve.SemilinearAut.ofAlgAut_smul AlgebraicCurve.SemilinearAut.coe_torsion_smul AlgebraicCurve.SemilinearAut.toRingAut_mul AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.jqNModC_one ModularCurve.qExpand_coeff_mul ModularCurve.qExpandₐ_apply ModularCurve.jqN_one ModularCurve.qExpand_single ModularCurve.dedekindPsi_one ModularCurve.ModularPolynomialData.mk.sizeOf_spec ModularCurve.evalAtJ_X ModularCurve.ModularPolynomialData.mk.injEq ModularCurve.constantCoeff_jNum ModularCurve.constantCoeff_eisenstein4 ModularCurve.qExpand_C ModularCurve.coeff_jq_neg_one ModularCurve.constantCoeff_jNumQ ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply"

set_option autoImplicit false

p2m_open "AlgebraicCurve P2MW.S_AlgebraicCurve_exists_mem_polarDifferentials_forall_hasSimpleResidue_of_sum_eq_zero.AlgebraicCurve"

namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "IsCurveOver Place HasCanonicalDivisor genus polarDifferentials regularDifferentials mem_regularDifferentials_iff existsUnique_hasSimpleResidue_of_hasSimplePoleAt sum_eq_zero_of_forall_hasSimpleResidue_of_mem_polarDifferentials finite_and_finrank_polarDifferentials_eq finite_and_finrank_regularDifferentials_eq_genus"
namespace ResSurjSol
p2m_open "AlgebraicCurve"

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

theorem hasValue_add {v : Place K F} {g g' : F} {a a' : K} (h : v.HasValue g a) (h' : v.HasValue g' a') :
    v.HasValue (g + g') (a + a') := by
  obtain ⟨hg, hr⟩ := h
  obtain ⟨hg', hr'⟩ := h'
  refine ⟨add_mem hg hg', ?_⟩
  have hx : (⟨g + g', add_mem hg hg'⟩ : v.toValuationSubring) = ⟨g, hg⟩ + ⟨g', hg'⟩ := rfl
  rw [hx, map_add, hr, hr', map_add]

theorem hasSimpleResidue_add {v : Place K F} {ω η : Ω[F⁄K]} {a b : K}
    (hω : v.HasSimpleResidue ω a) (hη : v.HasSimpleResidue η b) : v.HasSimpleResidue (ω + η) (a + b) := by
  obtain ⟨f, rfl, hf⟩ := hω
  obtain ⟨g, rfl, hg⟩ := hη
  refine ⟨f + g, by rw [add_smul], ?_⟩
  rw [mul_add]
  exact hasValue_add hf hg

theorem hasSimpleResidue_smul {v : Place K F} {ω : Ω[F⁄K]} {a : K} (c : K)
    (hω : v.HasSimpleResidue ω a) : v.HasSimpleResidue (c • ω) (c * a) := by
  obtain ⟨f, rfl, hf⟩ := hω
  refine ⟨algebraMap K F c * f, by rw [mul_smul, algebraMap_smul], ?_⟩
  rw [mul_left_comm]
  exact (v.hasValue_algebraMap c).mul hf

theorem isRegularAt_of_hasSimpleResidue_zero {v : Place K F} {ω : Ω[F⁄K]} (hω : v.HasSimpleResidue ω 0) :
    v.IsRegularAt ω := by
  obtain ⟨f, rfl, hmem, hres⟩ := hω
  rw [map_zero, IsLocalRing.residue_eq_zero_iff, v.irreducible_mk_uniformizer.maximalIdeal_eq,
    Ideal.mem_span_singleton] at hres
  obtain ⟨g, hg⟩ := hres
  have hfg : f = (g : F) := by
    have h1 : v.uniformizer * f = v.uniformizer * (g : F) := congrArg Subtype.val hg
    have hπ : v.uniformizer ≠ 0 := fun h0 => v.irreducible_mk_uniformizer.ne_zero (Subtype.ext h0)
    exact mul_left_cancel₀ hπ h1
  exact ⟨f, hfg ▸ g.2, rfl⟩

end AlgebraicCurve.ResSurjSol

open AlgebraicCurve.ResSurjSol in
theorem solution
    {K F : Type*} [Field K] [Field F] [Algebra K F] [IsAlgClosed K] [Algebra.EssFiniteType K F]
    [AlgebraicCurve.IsCurveOver K F] [AlgebraicCurve.HasCanonicalDivisor (K := K) (F := F)]
    (S : Finset (AlgebraicCurve.Place K F))
    (r : AlgebraicCurve.Place K F → K) (hr : ∑ v ∈ S, r v = 0) :
    ∃ ω ∈ AlgebraicCurve.polarDifferentials K F (S : Set (AlgebraicCurve.Place K F)),
      ∀ v ∈ S, v.HasSimpleResidue ω (r v) := by
  classical

  rcases S.eq_empty_or_nonempty with hS | hS
  · subst hS
    exact ⟨0, Submodule.zero_mem _, fun v hv => (Finset.notMem_empty v hv).elim⟩

  set P : Submodule K Ω[F⁄K] := AlgebraicCurve.polarDifferentials K F (S : Set (AlgebraicCurve.Place K F)) with hP
  have hPfin : Module.Finite K P := (AlgebraicCurve.finite_and_finrank_polarDifferentials_eq S hS).1
  have hPrk : Module.finrank K P = AlgebraicCurve.genus K F + S.card - 1 :=
    (AlgebraicCurve.finite_and_finrank_polarDifferentials_eq S hS).2
  have hRfin : Module.Finite K ↥(AlgebraicCurve.regularDifferentials K F) :=
    AlgebraicCurve.finite_and_finrank_regularDifferentials_eq_genus.1
  have hRrk : Module.finrank K ↥(AlgebraicCurve.regularDifferentials K F) = AlgebraicCurve.genus K F :=
    AlgebraicCurve.finite_and_finrank_regularDifferentials_eq_genus.2

  have hpole : ∀ (ω : P) (v : ↥S), (v : AlgebraicCurve.Place K F).HasSimplePoleAt (ω : Ω[F⁄K]) :=
    fun ω v => (ω.2 v).2 (Finset.mem_coe.mpr v.2)
  let res : P → ↥S → K := fun ω v =>
    (AlgebraicCurve.existsUnique_hasSimpleResidue_of_hasSimplePoleAt (v : AlgebraicCurve.Place K F) (ω : Ω[F⁄K])
      (hpole ω v)).exists.choose
  have hres : ∀ (ω : P) (v : ↥S), (v : AlgebraicCurve.Place K F).HasSimpleResidue (ω : Ω[F⁄K]) (res ω v) :=
    fun ω v => (AlgebraicCurve.existsUnique_hasSimpleResidue_of_hasSimplePoleAt (v : AlgebraicCurve.Place K F)
      (ω : Ω[F⁄K]) (hpole ω v)).exists.choose_spec
  have huniq : ∀ (ω : P) (v : ↥S) (a : K), (v : AlgebraicCurve.Place K F).HasSimpleResidue (ω : Ω[F⁄K]) a →
      a = res ω v :=
    fun ω v a ha => (AlgebraicCurve.existsUnique_hasSimpleResidue_of_hasSimplePoleAt
      (v : AlgebraicCurve.Place K F) (ω : Ω[F⁄K]) (hpole ω v)).unique ha (hres ω v)

  let Res : P →ₗ[K] (↥S → K) :=
    { toFun := res
      map_add' := fun ω η => funext fun v =>
        (huniq (ω + η) v _ (hasSimpleResidue_add (hres ω v) (hres η v))).symm
      map_smul' := fun c ω => funext fun v =>
        (huniq (c • ω) v _ (hasSimpleResidue_smul c (hres ω v))).symm }

  have hker : ∀ ω : P, Res ω = 0 → (ω : Ω[F⁄K]) ∈ AlgebraicCurve.regularDifferentials K F := by
    intro ω h0
    rw [AlgebraicCurve.mem_regularDifferentials_iff]
    intro v
    by_cases hv : v ∈ S
    · have h1 : res ω ⟨v, hv⟩ = 0 := congrFun h0 ⟨v, hv⟩
      exact isRegularAt_of_hasSimpleResidue_zero (h1 ▸ hres ω ⟨v, hv⟩)
    · exact (ω.2 v).1 (fun h => hv (Finset.mem_coe.mp h))

  have hkerle : Module.finrank K ↥(LinearMap.ker Res) ≤ AlgebraicCurve.genus K F := by
    let ι : ↥(LinearMap.ker Res) →ₗ[K] ↥(AlgebraicCurve.regularDifferentials K F) :=
      { toFun := fun x => ⟨(x.1 : Ω[F⁄K]), hker x.1 x.2⟩
        map_add' := fun x y => rfl
        map_smul' := fun c x => rfl }
    have hι : Function.Injective ι := by
      intro x y h
      apply Subtype.ext
      apply Subtype.ext
      exact congrArg (fun z : ↥(AlgebraicCurve.regularDifferentials K F) => (z : Ω[F⁄K])) h
    rw [← hRrk]
    exact LinearMap.finrank_le_finrank_of_injective hι

  let σ : (↥S → K) →ₗ[K] K :=
    { toFun := fun x => ∑ v : ↥S, x v
      map_add' := fun x y => by simp only [Pi.add_apply, Finset.sum_add_distrib]
      map_smul' := fun c x => by simp only [Pi.smul_apply, smul_eq_mul, Finset.mul_sum, RingHom.id_apply] }
  have hσsurj : Function.Surjective σ := by
    obtain ⟨v₀, hv₀⟩ := hS
    intro c
    refine ⟨Pi.single ⟨v₀, hv₀⟩ c, ?_⟩
    show ∑ v : ↥S, Pi.single (⟨v₀, hv₀⟩ : ↥S) c v = c
    rw [Finset.sum_pi_single']
    simp
  have hHrk : Module.finrank K ↥(LinearMap.ker σ) + 1 = S.card := by
    have h1 := LinearMap.finrank_range_add_finrank_ker σ
    rw [LinearMap.range_eq_top.mpr hσsurj, finrank_top, Module.finrank_self, Module.finrank_fintype_fun_eq_card,
      Fintype.card_coe] at h1
    omega

  have hrange : LinearMap.range Res ≤ LinearMap.ker σ := by
    rintro _ ⟨ω, rfl⟩
    rw [LinearMap.mem_ker]
    show ∑ v : ↥S, res ω v = 0
    have h := AlgebraicCurve.sum_eq_zero_of_forall_hasSimpleResidue_of_mem_polarDifferentials S (ω : Ω[F⁄K]) ω.2
      (fun v => if h : v ∈ S then res ω ⟨v, h⟩ else 0) (fun v hv => by simp only [dif_pos hv]; exact hres ω ⟨v, hv⟩)
    rw [← Finset.sum_coe_sort] at h
    simpa using h

  have hrange_eq : LinearMap.range Res = LinearMap.ker σ := by
    apply Submodule.eq_of_le_of_finrank_le hrange
    have h1 := LinearMap.finrank_range_add_finrank_ker Res
    rw [hPrk] at h1
    have hcard : 1 ≤ S.card := Finset.card_pos.mpr hS
    omega

  have hmem : (fun v : ↥S => r v) ∈ LinearMap.ker σ := by
    rw [LinearMap.mem_ker]
    show ∑ v : ↥S, r v = 0
    rw [Finset.sum_coe_sort S r]
    exact hr
  rw [← hrange_eq] at hmem
  obtain ⟨ω, hω⟩ := hmem
  refine ⟨ω, ω.2, fun v hv => ?_⟩
  have h1 : res ω ⟨v, hv⟩ = r v := congrFun hω ⟨v, hv⟩
  exact h1 ▸ hres ω ⟨v, hv⟩

end S_AlgebraicCurve_exists_mem_polarDifferentials_forall_hasSimpleResidue_of_sum_eq_zero
end P2MW
export P2MW.S_AlgebraicCurve_exists_mem_polarDifferentials_forall_hasSimpleResidue_of_sum_eq_zero (solution)
