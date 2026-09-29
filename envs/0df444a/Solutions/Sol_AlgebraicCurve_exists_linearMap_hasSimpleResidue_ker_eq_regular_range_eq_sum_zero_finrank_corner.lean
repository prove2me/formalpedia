-- Prove2me | solution 1 for AlgebraicCurve.exists_linearMap_hasSimpleResidue_ker_eq_regular_range_eq_sum_zero_finrank_corner
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.4153+00:00
-- url     : https://prove2.me/submissions/c59eaf7a-0c09-5f29-b175-bdb6318133c7

import Mathlib
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_CanonicalDivisor
import Definitions.Def_AlgebraicCurve_PolarDifferentials
import Theorems.Thm_AlgebraicCurve_existsUnique_hasSimpleResidue_of_hasSimplePoleAt
import Theorems.Thm_AlgebraicCurve_sum_eq_zero_of_forall_hasSimpleResidue_of_mem_polarDifferentials
import Theorems.Thm_AlgebraicCurve_exists_mem_polarDifferentials_forall_hasSimpleResidue_of_sum_eq_zero
import Theorems.Thm_AlgebraicCurve_finite_and_finrank_polarDifferentials_eq
import Theorems.Thm_AlgebraicCurve_finite_and_finrank_regularDifferentials_eq_genus
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_exists_linearMap_hasSimpleResidue_ker_eq_regular_range_eq_sum_zero_finrank_corner
p2m_attr_erase "instance" "AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupDivisor AlgebraicCurve.Pic0.instModuleZModTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instDistribMulActionTorsion"
p2m_attr_erase "instance" "AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instSMulTorsion AlgebraicCurve.SemilinearAut.instMulActionSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instSMulCommClassZModTorsion AlgebraicCurve.SemilinearAut.instMulSemiringActionSubtypeProdRingAutMemSubgroup instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy"
p2m_attr_erase "simp" "AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint"
p2m_attr_erase "simp" "AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.SemilinearAut.toRingAut_inv AlgebraicCurve.SemilinearAut.smul_def AlgebraicCurve.SemilinearAut.smul_single AlgebraicCurve.SemilinearAut.smul_toValuationSubring AlgebraicCurve.SemilinearAut.baseAut_inv AlgebraicCurve.SemilinearAut.baseAut_ofAlgAut AlgebraicCurve.SemilinearAut.toRingAut_ofAlgAut AlgebraicCurve.SemilinearAut.torsionRep_apply AlgebraicCurve.SemilinearAut.toRingAut_one AlgebraicCurve.SemilinearAut.deg_smul"
p2m_attr_erase "simp" "AlgebraicCurve.SemilinearAut.degree_smul AlgebraicCurve.SemilinearAut.coe_degZeroSMulHom AlgebraicCurve.SemilinearAut.baseAut_mul AlgebraicCurve.SemilinearAut.coe_smulValuationSubringEquiv_apply AlgebraicCurve.SemilinearAut.baseAut_one AlgebraicCurve.SemilinearAut.ofAlgAut_smul AlgebraicCurve.SemilinearAut.coe_torsion_smul AlgebraicCurve.SemilinearAut.toRingAut_mul AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.jqNModC_one ModularCurve.qExpand_coeff_mul ModularCurve.qExpandₐ_apply ModularCurve.jqN_one ModularCurve.qExpand_single ModularCurve.dedekindPsi_one ModularCurve.ModularPolynomialData.mk.sizeOf_spec ModularCurve.evalAtJ_X ModularCurve.ModularPolynomialData.mk.injEq ModularCurve.constantCoeff_jNum ModularCurve.constantCoeff_eisenstein4 ModularCurve.qExpand_C ModularCurve.coeff_jq_neg_one ModularCurve.constantCoeff_jNumQ ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply"

set_option autoImplicit false

p2m_open "AlgebraicCurve P2MW.S_AlgebraicCurve_exists_linearMap_hasSimpleResidue_ker_eq_regular_range_eq_sum_zero_finrank_corner.AlgebraicCurve"

namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "IsCurveOver Place HasCanonicalDivisor Place.HasSimpleResidue Place.hasSimpleResidue_zero_of_mem polarDifferentials polarDifferentials_empty regularDifferentials existsUnique_hasSimpleResidue_of_hasSimplePoleAt sum_eq_zero_of_forall_hasSimpleResidue_of_mem_polarDifferentials exists_mem_polarDifferentials_forall_hasSimpleResidue_of_sum_eq_zero finite_and_finrank_polarDifferentials_eq finite_and_finrank_regularDifferentials_eq_genus"
namespace ResidueCorner
p2m_open "AlgebraicCurve"

open scoped Classical

variable {K F : Type*} [Field K] [Field F] [Algebra K F] [IsAlgClosed K] [Algebra.EssFiniteType K F]
  [AlgebraicCurve.IsCurveOver K F] [AlgebraicCurve.HasCanonicalDivisor (K := K) (F := F)]

open IsLocalRing

theorem hasValue_add {v : Place K F} {g g' : F} {a a' : K} (h : v.HasValue g a) (h' : v.HasValue g' a') :
    v.HasValue (g + g') (a + a') := by
  refine ⟨add_mem h.mem h'.mem, ?_⟩
  have : (⟨g + g', add_mem h.mem h'.mem⟩ : v.toValuationSubring) = ⟨g, h.mem⟩ + ⟨g', h'.mem⟩ := rfl
  rw [this, map_add, h.residue_eq, h'.residue_eq, map_add]

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

theorem hasSimpleResidue_unique {v : Place K F} {ω : Ω[F⁄K]} {a b : K}
    (ha : v.HasSimpleResidue ω a) (hb : v.HasSimpleResidue ω b) : a = b :=
  (AlgebraicCurve.existsUnique_hasSimpleResidue_of_hasSimplePoleAt v ω ha.hasSimplePoleAt).unique ha hb

theorem isRegularAt_of_hasSimpleResidue_zero {v : Place K F} {ω : Ω[F⁄K]} (h : v.HasSimpleResidue ω 0) :
    v.IsRegularAt ω := by
  obtain ⟨f, rfl, hmem, hres⟩ := h
  rw [map_zero, IsLocalRing.residue_eq_zero_iff, v.irreducible_mk_uniformizer.maximalIdeal_eq,
    Ideal.mem_span_singleton] at hres
  obtain ⟨g, hg⟩ := hres
  have hg' : v.uniformizer * f = v.uniformizer * (g : F) := by
    have := congrArg (fun x : v.toValuationSubring => (x : F)) hg
    simpa using this
  have hπ : v.uniformizer ≠ 0 := fun h0 => v.irreducible_mk_uniformizer.ne_zero (Subtype.ext h0)
  have hfg : f = (g : F) := mul_left_cancel₀ hπ hg'
  exact ⟨f, hfg ▸ g.2, rfl⟩

variable (S : Finset (Place K F))

noncomputable def resAt (ω : ↥(polarDifferentials K F (S : Set (Place K F)))) (v : Place K F) : K :=
  if hv : v ∈ S then
    Classical.choose (AlgebraicCurve.existsUnique_hasSimpleResidue_of_hasSimplePoleAt v (ω : Ω[F⁄K])
      ((ω.2 v).2 hv)).exists
  else 0

theorem hasSimpleResidue_resAt (ω : ↥(polarDifferentials K F (S : Set (Place K F)))) {v : Place K F} (hv : v ∈ S) :
    v.HasSimpleResidue (ω : Ω[F⁄K]) (resAt S ω v) := by
  rw [resAt, dif_pos hv]
  exact Classical.choose_spec (AlgebraicCurve.existsUnique_hasSimpleResidue_of_hasSimplePoleAt v (ω : Ω[F⁄K])
      ((ω.2 v).2 hv)).exists

theorem resAt_of_not_mem (ω : ↥(polarDifferentials K F (S : Set (Place K F)))) {v : Place K F} (hv : v ∉ S) :
    resAt S ω v = 0 := by
  rw [resAt, dif_neg hv]

theorem resAt_eq_of_hasSimpleResidue (ω : ↥(polarDifferentials K F (S : Set (Place K F)))) {v : Place K F}
    (hv : v ∈ S) {a : K} (ha : v.HasSimpleResidue (ω : Ω[F⁄K]) a) : resAt S ω v = a :=
  hasSimpleResidue_unique (hasSimpleResidue_resAt S ω hv) ha

noncomputable def res : ↥(polarDifferentials K F (S : Set (Place K F))) →ₗ[K] (Place K F → K) where
  toFun ω := resAt S ω
  map_add' ω η := by
    funext v
    by_cases hv : v ∈ S
    · rw [Pi.add_apply]
      exact resAt_eq_of_hasSimpleResidue S (ω + η) hv
        (hasSimpleResidue_add (hasSimpleResidue_resAt S ω hv) (hasSimpleResidue_resAt S η hv))
    · rw [Pi.add_apply, resAt_of_not_mem S _ hv, resAt_of_not_mem S _ hv, resAt_of_not_mem S _ hv, add_zero]
  map_smul' c ω := by
    funext v
    by_cases hv : v ∈ S
    · rw [RingHom.id_apply, Pi.smul_apply, smul_eq_mul]
      exact resAt_eq_of_hasSimpleResidue S (c • ω) hv (hasSimpleResidue_smul c (hasSimpleResidue_resAt S ω hv))
    · rw [RingHom.id_apply, Pi.smul_apply, resAt_of_not_mem S _ hv, resAt_of_not_mem S _ hv, smul_zero]

theorem res_apply (ω : ↥(polarDifferentials K F (S : Set (Place K F)))) (v : Place K F) : res S ω v = resAt S ω v := rfl

theorem res_eq_zero_iff (ω : ↥(polarDifferentials K F (S : Set (Place K F)))) :
    res S ω = 0 ↔ (ω : Ω[F⁄K]) ∈ regularDifferentials K F := by
  constructor
  · intro h v
    by_cases hv : v ∈ S
    · have h0 : resAt S ω v = 0 := by rw [← res_apply, h, Pi.zero_apply]
      exact isRegularAt_of_hasSimpleResidue_zero (h0 ▸ hasSimpleResidue_resAt S ω hv)
    · exact (ω.2 v).1 hv
  · intro h
    funext v
    by_cases hv : v ∈ S
    · obtain ⟨f, hf, hω⟩ := h v
      rw [Pi.zero_apply, res_apply]
      refine resAt_eq_of_hasSimpleResidue S ω hv ?_
      rw [hω]
      exact Place.hasSimpleResidue_zero_of_mem hf
    · rw [Pi.zero_apply, res_apply, resAt_of_not_mem S ω hv]

theorem mem_range_res_iff (r : Place K F → K) :
    r ∈ LinearMap.range (res S) ↔ (∀ v : Place K F, v ∉ S → r v = 0) ∧ ∑ v ∈ S, r v = 0 := by
  constructor
  · rintro ⟨ω, rfl⟩
    refine ⟨fun v hv => resAt_of_not_mem S ω hv, ?_⟩
    exact AlgebraicCurve.sum_eq_zero_of_forall_hasSimpleResidue_of_mem_polarDifferentials S (ω : Ω[F⁄K]) ω.2
      (res S ω) (fun v hv => hasSimpleResidue_resAt S ω hv)
  · rintro ⟨hsupp, hsum⟩
    obtain ⟨ω, hω, hres⟩ := AlgebraicCurve.exists_mem_polarDifferentials_forall_hasSimpleResidue_of_sum_eq_zero S r hsum
    refine ⟨⟨ω, hω⟩, funext fun v => ?_⟩
    by_cases hv : v ∈ S
    · exact resAt_eq_of_hasSimpleResidue S ⟨ω, hω⟩ hv (hres v hv)
    · rw [res_apply, resAt_of_not_mem S _ hv, hsupp v hv]

theorem finite_polarDifferentials : Module.Finite K ↥(polarDifferentials K F (S : Set (Place K F))) := by
  rcases S.eq_empty_or_nonempty with h | h
  · subst h
    rw [Finset.coe_empty, polarDifferentials_empty]
    exact AlgebraicCurve.finite_and_finrank_regularDifferentials_eq_genus.1
  · exact (AlgebraicCurve.finite_and_finrank_polarDifferentials_eq S h).1

theorem finrank_corner {V U : Type*} [AddCommGroup V] [Module K V] [AddCommGroup U] [Module K U]
    [Module.Finite K V] (f : V →ₗ[K] U) (E : V →ₗ[K] V) (ē : U →ₗ[K] U)
    (hE : E ∘ₗ E = E) (hf : f ∘ₗ E = ē ∘ₗ f) :
    Module.finrank K ↥(LinearMap.range E) =
      Module.finrank K ↥((LinearMap.ker f).map E) + Module.finrank K ↥((LinearMap.range f).map ē) := by

  set g : ↥(LinearMap.range E) →ₗ[K] U := f ∘ₗ (LinearMap.range E).subtype with hg
  have h1 := LinearMap.finrank_range_add_finrank_ker g

  have hrange : LinearMap.range g = (LinearMap.range f).map ē := by
    apply le_antisymm
    · rintro _ ⟨⟨y, x, rfl⟩, rfl⟩
      refine ⟨f x, ⟨x, rfl⟩, ?_⟩
      have := LinearMap.congr_fun hf x
      simp only [LinearMap.comp_apply] at this
      simpa [hg] using this.symm
    · rintro _ ⟨_, ⟨x, rfl⟩, rfl⟩
      refine ⟨⟨E x, x, rfl⟩, ?_⟩
      have := LinearMap.congr_fun hf x
      simp only [LinearMap.comp_apply] at this
      simpa [hg] using this

  have hEE : ∀ x, E (E x) = E x := fun x => by
    have := LinearMap.congr_fun hE x
    simpa only [LinearMap.comp_apply] using this
  have hker_mem : ∀ y : ↥(LinearMap.range E), y ∈ LinearMap.ker g ↔ (y : V) ∈ (LinearMap.ker f).map E := by
    intro y
    obtain ⟨y, x, rfl⟩ := y
    rw [LinearMap.mem_ker]
    show f (E x) = 0 ↔ E x ∈ (LinearMap.ker f).map E
    constructor
    · intro h0
      exact ⟨E x, LinearMap.mem_ker.2 h0, hEE x⟩
    · rintro ⟨w, hw, hwx⟩
      rw [← hwx]
      have := LinearMap.congr_fun hf w
      simp only [LinearMap.comp_apply] at this
      rw [this, LinearMap.mem_ker.1 hw, map_zero]
  let eqv : ↥(LinearMap.ker g) ≃ₗ[K] ↥((LinearMap.ker f).map E) :=
    { toFun := fun y => ⟨(y : ↥(LinearMap.range E)), (hker_mem _).1 y.2⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl
      invFun := fun z => ⟨⟨z, by obtain ⟨w, -, hw⟩ := z.2; exact ⟨w, hw⟩⟩, (hker_mem _).2 (by exact z.2)⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [← h1, hrange, eqv.finrank_eq, add_comm]

end AlgebraicCurve.ResidueCorner

theorem solution
    {K F : Type*} [Field K] [Field F] [Algebra K F] [IsAlgClosed K] [Algebra.EssFiniteType K F]
    [AlgebraicCurve.IsCurveOver K F] [AlgebraicCurve.HasCanonicalDivisor (K := K) (F := F)]
    (S : Finset (AlgebraicCurve.Place K F)) :
    ∃ res : ↥(AlgebraicCurve.polarDifferentials K F (S : Set (AlgebraicCurve.Place K F))) →ₗ[K]
        (AlgebraicCurve.Place K F → K),

      (∀ (ω : ↥(AlgebraicCurve.polarDifferentials K F (S : Set (AlgebraicCurve.Place K F))))
          (v : AlgebraicCurve.Place K F), v ∈ S → v.HasSimpleResidue (ω : Ω[F⁄K]) (res ω v)) ∧
      (∀ (ω : ↥(AlgebraicCurve.polarDifferentials K F (S : Set (AlgebraicCurve.Place K F))))
          (v : AlgebraicCurve.Place K F), v ∉ S → res ω v = 0) ∧

      (∀ ω : ↥(AlgebraicCurve.polarDifferentials K F (S : Set (AlgebraicCurve.Place K F))),
          res ω = 0 ↔ (ω : Ω[F⁄K]) ∈ AlgebraicCurve.regularDifferentials K F) ∧

      (∀ r : AlgebraicCurve.Place K F → K,
          r ∈ LinearMap.range res ↔ (∀ v : AlgebraicCurve.Place K F, v ∉ S → r v = 0) ∧ ∑ v ∈ S, r v = 0) ∧

      Module.Finite K ↥(AlgebraicCurve.polarDifferentials K F (S : Set (AlgebraicCurve.Place K F))) ∧

      (∀ (E : ↥(AlgebraicCurve.polarDifferentials K F (S : Set (AlgebraicCurve.Place K F))) →ₗ[K]
            ↥(AlgebraicCurve.polarDifferentials K F (S : Set (AlgebraicCurve.Place K F))))
          (ē : (AlgebraicCurve.Place K F → K) →ₗ[K] (AlgebraicCurve.Place K F → K)),
          E ∘ₗ E = E → res ∘ₗ E = ē ∘ₗ res →
          Module.finrank K ↥(LinearMap.range E) =
            Module.finrank K ↥((LinearMap.ker res).map E) + Module.finrank K ↥((LinearMap.range res).map ē)) := by
  haveI := AlgebraicCurve.ResidueCorner.finite_polarDifferentials (K := K) (F := F) S
  refine ⟨AlgebraicCurve.ResidueCorner.res S, fun ω v hv => AlgebraicCurve.ResidueCorner.hasSimpleResidue_resAt S ω hv,
    fun ω v hv => AlgebraicCurve.ResidueCorner.resAt_of_not_mem S ω hv,
    fun ω => AlgebraicCurve.ResidueCorner.res_eq_zero_iff S ω,
    fun r => AlgebraicCurve.ResidueCorner.mem_range_res_iff S r, inferInstance,
    fun E ē hE hf => AlgebraicCurve.ResidueCorner.finrank_corner _ E ē hE hf⟩

end S_AlgebraicCurve_exists_linearMap_hasSimpleResidue_ker_eq_regular_range_eq_sum_zero_finrank_corner
end P2MW
export P2MW.S_AlgebraicCurve_exists_linearMap_hasSimpleResidue_ker_eq_regular_range_eq_sum_zero_finrank_corner (solution)
