-- Prove2me | solution 1 for AlgebraicCurve.finite_and_finrank_regularDifferentials_eq_genus
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.4153+00:00
-- url     : https://prove2.me/submissions/bb555221-8820-54f1-ab35-84e866a49dee

import Mathlib
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_CanonicalDivisor
import Definitions.Def_AlgebraicCurve_RegularDifferentials
import Definitions.Def_AlgebraicCurve_RiemannRochRows
import Theorems.Thm_AlgebraicCurve_dCoordGenerates_of_isCurveOver
import Theorems.Thm_AlgebraicCurve_IsCurveOver_exists_separating_transcendental
import Theorems.Thm_AlgebraicCurve_isCurveOver_ratFunc
import Theorems.Thm_AlgebraicCurve_essFiniteType_of_transcendental_of_finiteDimensional
import Theorems.Thm_AlgebraicCurve_functionFieldRiemannRoch_of_isAlgClosed_of_isCurveOver
import Theorems.Thm_AlgebraicCurve_constantsAreBase_of_isAlgClosed
import Theorems.Thm_AlgebraicCurve_finiteDimensional_lSpace
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_finite_and_finrank_regularDifferentials_eq_genus
p2m_attr_erase "instance" "AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupDivisor AlgebraicCurve.Pic0.instModuleZModTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instDistribMulActionTorsion"
p2m_attr_erase "instance" "AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instSMulTorsion AlgebraicCurve.SemilinearAut.instMulActionSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instSMulCommClassZModTorsion AlgebraicCurve.SemilinearAut.instMulSemiringActionSubtypeProdRingAutMemSubgroup instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy"
p2m_attr_erase "simp" "AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply"
p2m_attr_erase "simp" "AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.SemilinearAut.toRingAut_inv AlgebraicCurve.SemilinearAut.smul_def AlgebraicCurve.SemilinearAut.smul_single AlgebraicCurve.SemilinearAut.smul_toValuationSubring AlgebraicCurve.SemilinearAut.baseAut_inv AlgebraicCurve.SemilinearAut.baseAut_ofAlgAut AlgebraicCurve.SemilinearAut.toRingAut_ofAlgAut AlgebraicCurve.SemilinearAut.torsionRep_apply AlgebraicCurve.SemilinearAut.toRingAut_one AlgebraicCurve.SemilinearAut.deg_smul AlgebraicCurve.SemilinearAut.degree_smul AlgebraicCurve.SemilinearAut.coe_degZeroSMulHom AlgebraicCurve.SemilinearAut.baseAut_mul AlgebraicCurve.SemilinearAut.coe_smulValuationSubringEquiv_apply AlgebraicCurve.SemilinearAut.baseAut_one AlgebraicCurve.SemilinearAut.ofAlgAut_smul AlgebraicCurve.SemilinearAut.coe_torsion_smul AlgebraicCurve.SemilinearAut.toRingAut_mul"
p2m_attr_erase "simp" "AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.jqNModC_one ModularCurve.qExpand_coeff_mul ModularCurve.qExpandₐ_apply ModularCurve.jqN_one ModularCurve.qExpand_single ModularCurve.dedekindPsi_one ModularCurve.ModularPolynomialData.mk.sizeOf_spec ModularCurve.evalAtJ_X ModularCurve.ModularPolynomialData.mk.injEq ModularCurve.constantCoeff_jNum ModularCurve.constantCoeff_eisenstein4 ModularCurve.qExpand_C ModularCurve.coeff_jq_neg_one ModularCurve.constantCoeff_jNumQ ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply"

set_option autoImplicit false

noncomputable section

p2m_open "AlgebraicCurve P2MW.S_AlgebraicCurve_finite_and_finrank_regularDifferentials_eq_genus.AlgebraicCurve KaehlerDifferential IntermediateField"

namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "IsCurveOver IsCurveOver.finrank_kaehler Place Divisor HasCanonicalDivisor canonicalDivisorOf canonicalDivisorOf_apply genus Place.ordDifferential regularDifferentials mem_regularDifferentials_iff FunctionFieldRiemannRoch LSpace ell mem_lSpace_iff_ord ConstantsAreBase ell_zero_eq_one_of_constantsAreBase dCoordGenerates_of_isCurveOver IsCurveOver.exists_separating_transcendental isCurveOver_ratFunc essFiniteType_of_transcendental_of_finiteDimensional functionFieldRiemannRoch_of_isAlgClosed_of_isCurveOver constantsAreBase_of_isAlgClosed finiteDimensional_lSpace"
p2m_open "AlgebraicCurve"

namespace RegularDifferentialsFinrank

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

theorem ord_nonneg_of_mem_valuationSubring (v : Place K F) {f : F}
    (hf : f ∈ v.toValuationSubring) : 0 ≤ v.ord f := by
  rcases eq_or_ne f 0 with rfl | hf0
  · simp
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible v.toValuationSubring
  obtain ⟨n, u, hu⟩ :=
    IsDiscreteValuationRing.eq_unit_mul_pow_irreducible
      (x := (⟨f, hf⟩ : v.toValuationSubring)) (by simpa [Subtype.ext_iff] using hf0) hπ
  have hcoe : f = ((u : v.toValuationSubring) : F) * ((π : F) ^ (n : ℤ)) := by
    have h := congrArg Subtype.val hu
    push_cast at h
    rw [zpow_natCast]
    exact h
  rw [hcoe, v.ord_unit_smul_zpow u hπ (n : ℤ)]
  exact Int.natCast_nonneg n

theorem mem_valuationSubring_of_ord_nonneg (v : Place K F) {f : F} (hf : f ≠ 0)
    (h : 0 ≤ v.ord f) : f ∈ v.toValuationSubring := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible v.toValuationSubring
  obtain ⟨u, hu⟩ := v.exists_unit_mul_zpow hf hπ
  rw [hu, show v.ord f = (((v.ord f).toNat : ℕ) : ℤ) from (Int.toNat_of_nonneg h).symm,
    zpow_natCast]
  exact mul_mem (u : v.toValuationSubring).2 (pow_mem (π : v.toValuationSubring).2 _)

theorem differentialCoeff_ne_zero {ω : Ω[F⁄K]} (hω : ω ≠ 0) (v : Place K F) [v.DCoordGenerates] :
    v.differentialCoeff ω ≠ 0 := by
  intro h
  apply hω
  rw [← v.differentialCoeff_smul_dCoord ω, h, zero_smul]

theorem exists_smul_eq [IsCurveOver K F] {ω₀ : Ω[F⁄K]} (hω₀ : ω₀ ≠ 0) (ω : Ω[F⁄K]) :
    ∃ h : F, h • ω₀ = ω :=
  (finrank_eq_one_iff_of_nonzero' ω₀ hω₀).mp IsCurveOver.finrank_kaehler ω

section Comparison

variable [IsCurveOver K F] [HasCanonicalDivisor (K := K) (F := F)]
  [∀ v : Place K F, v.DCoordGenerates]

theorem smul_mem_regularDifferentials_iff {ω₀ : Ω[F⁄K]} (hω₀ : ω₀ ≠ 0) (h : F) :
    h • ω₀ ∈ regularDifferentials K F ↔ h ∈ LSpace (canonicalDivisorOf hω₀) := by
  rcases eq_or_ne h 0 with rfl | hh
  · simp only [zero_smul, Submodule.zero_mem]
  rw [mem_regularDifferentials_iff, mem_lSpace_iff_ord, or_iff_right hh]
  refine forall_congr' fun v => ?_
  have hc : v.differentialCoeff ω₀ ≠ 0 := differentialCoeff_ne_zero hω₀ v

  have hdec : h • ω₀ = (h * v.differentialCoeff ω₀) • v.dCoord := by
    rw [mul_smul, v.differentialCoeff_smul_dCoord]
  have hprod : h * v.differentialCoeff ω₀ ≠ 0 := mul_ne_zero hh hc
  rw [canonicalDivisorOf_apply, Place.ordDifferential]
  constructor
  · rintro ⟨g, hg, hEq⟩

    have hgu : g = h * v.differentialCoeff ω₀ := by
      rw [← v.differentialCoeff_unique hEq, v.differentialCoeff_unique hdec]
    have h0 : 0 ≤ v.ord (h * v.differentialCoeff ω₀) :=
      hgu ▸ ord_nonneg_of_mem_valuationSubring v hg
    rw [v.ord_mul hh hc] at h0
    linarith
  · intro hle
    refine ⟨h * v.differentialCoeff ω₀, ?_, hdec⟩
    refine mem_valuationSubring_of_ord_nonneg v hprod ?_
    rw [v.ord_mul hh hc]
    linarith

def toRegular {ω₀ : Ω[F⁄K]} (hω₀ : ω₀ ≠ 0) :
    LSpace (canonicalDivisorOf hω₀) →ₗ[K] regularDifferentials K F where
  toFun h := ⟨(h : F) • ω₀, (smul_mem_regularDifferentials_iff hω₀ (h : F)).mpr h.2⟩
  map_add' h₁ h₂ := by
    ext
    simp [add_smul]
  map_smul' c h := by
    ext
    simp [smul_assoc]

theorem toRegular_apply {ω₀ : Ω[F⁄K]} (hω₀ : ω₀ ≠ 0) (h : LSpace (canonicalDivisorOf hω₀)) :
    ((toRegular hω₀ h : regularDifferentials K F) : Ω[F⁄K]) = (h : F) • ω₀ := rfl

theorem toRegular_bijective {ω₀ : Ω[F⁄K]} (hω₀ : ω₀ ≠ 0) :
    Function.Bijective (toRegular (K := K) (F := F) hω₀) := by
  constructor
  · intro h₁ h₂ hEq
    have hEq' : ((h₁ : F) - (h₂ : F)) • ω₀ = 0 := by
      have := congrArg (fun x : regularDifferentials K F => (x : Ω[F⁄K])) hEq
      simp only [toRegular_apply] at this
      rw [sub_smul, this, sub_self]
    rcases smul_eq_zero.mp hEq' with h0 | h0
    · exact Subtype.ext (sub_eq_zero.mp h0)
    · exact absurd h0 hω₀
  · rintro ⟨ω, hω⟩
    obtain ⟨h, rfl⟩ := exists_smul_eq hω₀ ω
    exact ⟨⟨h, (smul_mem_regularDifferentials_iff hω₀ h).mp hω⟩, rfl⟩

def lSpaceCanonicalEquivRegular {ω₀ : Ω[F⁄K]} (hω₀ : ω₀ ≠ 0) :
    LSpace (canonicalDivisorOf hω₀) ≃ₗ[K] regularDifferentials K F :=
  LinearEquiv.ofBijective (toRegular hω₀) (toRegular_bijective hω₀)

theorem ell_canonical_eq_genus (hRR : FunctionFieldRiemannRoch K F) (hC : ConstantsAreBase K F)
    {ω₀ : Ω[F⁄K]} (hω₀ : ω₀ ≠ 0) :
    ell (canonicalDivisorOf hω₀) = genus K F := by
  have h := hRR hω₀ 0
  rw [sub_zero, ell_zero_eq_one_of_constantsAreBase hC] at h
  simp only [map_zero, Nat.cast_one, zero_add] at h
  exact_mod_cast (by linarith : (ell (canonicalDivisorOf hω₀) : ℤ) = genus K F)

end Comparison

theorem riemannRoch_and_constantsAreBase [IsAlgClosed K] [Algebra.EssFiniteType K F]
    [IsCurveOver K F] [HasCanonicalDivisor (K := K) (F := F)]
    [∀ v : Place K F, v.DCoordGenerates] :
    FunctionFieldRiemannRoch K F ∧ ConstantsAreBase K F := by
  classical

  obtain ⟨t, ht, htfd, htsep⟩ :=
    IsCurveOver.exists_separating_transcendental (K := K) (F := F)
  haveI := htfd
  haveI := htsep

  set e : RatFunc K ≃ₐ[K] K⟮t⟯ := RatFunc.algEquivOfTranscendental t ht with he
  letI : Algebra (RatFunc K) F :=
    ((algebraMap K⟮t⟯ F).comp e.toAlgHom.toRingHom).toAlgebra
  have hsq : RingHom.comp (algebraMap (RatFunc K) F)
        (e.symm.toRingEquiv : K⟮t⟯ →+* RatFunc K)
      = RingHom.comp (RingEquiv.refl F : F →+* F) (algebraMap K⟮t⟯ F) := by
    refine RingHom.ext fun a => ?_
    show algebraMap K⟮t⟯ F (e (e.symm a)) = algebraMap K⟮t⟯ F a
    rw [e.apply_symm_apply]
  haveI : IsScalarTower K (RatFunc K) F :=
    IsScalarTower.of_algebraMap_eq fun a => by
      show algebraMap K F a = algebraMap K⟮t⟯ F (e (algebraMap K (RatFunc K) a))
      rw [e.commutes, ← IsScalarTower.algebraMap_apply]
  haveI : FiniteDimensional (RatFunc K) F :=
    Module.Finite.of_equiv_equiv e.symm.toRingEquiv (RingEquiv.refl F) hsq
  haveI : Algebra.IsSeparable (RatFunc K) F :=
    Algebra.IsSeparable.of_equiv_equiv e.symm.toRingEquiv (RingEquiv.refl F) hsq
  haveI : Algebra.IsIntegral (RatFunc K) F := Algebra.IsIntegral.of_finite (RatFunc K) F

  haveI : IsCurveOver K (RatFunc K) := isCurveOver_ratFunc K
  haveI : FiniteDimensional (IntermediateField.adjoin K ({RatFunc.X} : Set (RatFunc K)))
      (RatFunc K) := by
    refine Module.Finite.of_surjective
      (Algebra.linearMap (IntermediateField.adjoin K ({RatFunc.X} : Set (RatFunc K)))
        (RatFunc K)) fun y => ?_
    refine ⟨⟨y, ?_⟩, rfl⟩
    rw [RatFunc.adjoin_X]
    exact IntermediateField.mem_top
  haveI : Algebra.EssFiniteType K (RatFunc K) :=
    essFiniteType_of_transcendental_of_finiteDimensional
      (RatFunc.transcendental_X (K := K)) inferInstance
  haveI : ∀ v : Place K (RatFunc K), v.DCoordGenerates := dCoordGenerates_of_isCurveOver
  refine ⟨?_, constantsAreBase_of_isAlgClosed K F⟩
  intro _ _ _ ω hω D
  exact functionFieldRiemannRoch_of_isAlgClosed_of_isCurveOver (K := K) (F := F) hω D

end RegularDifferentialsFinrank

end AlgebraicCurve

end

open _root_.AlgebraicCurve _root_.P2MW.S_AlgebraicCurve_finite_and_finrank_regularDifferentials_eq_genus.AlgebraicCurve AlgebraicCurve.RegularDifferentialsFinrank KaehlerDifferential in
theorem solution {K F : Type*} [Field K]
    [Field F] [Algebra K F] [IsAlgClosed K] [Algebra.EssFiniteType K F]
    [AlgebraicCurve.IsCurveOver K F] [AlgebraicCurve.HasCanonicalDivisor (K := K) (F := F)] :
    Module.Finite K ↥(AlgebraicCurve.regularDifferentials K F) ∧
      Module.finrank K ↥(AlgebraicCurve.regularDifferentials K F) =
        AlgebraicCurve.genus K F := by
  classical

  haveI : ∀ v : Place K F, v.DCoordGenerates := dCoordGenerates_of_isCurveOver

  obtain ⟨hRR, hC⟩ := riemannRoch_and_constantsAreBase (K := K) (F := F)

  obtain ⟨ω₀, hω₀⟩ := exists_ne (0 : Ω[F⁄K])

  haveI : FiniteDimensional K ↥(LSpace (0 : Divisor K F)) := by
    rw [show LSpace (0 : Divisor K F) = _ from hC]
    infer_instance
  haveI : FiniteDimensional K ↥(LSpace (canonicalDivisorOf hω₀)) :=
    finiteDimensional_lSpace _

  set e := lSpaceCanonicalEquivRegular (K := K) (F := F) hω₀
  refine ⟨Module.Finite.equiv e, ?_⟩
  rw [← e.finrank_eq]
  exact ell_canonical_eq_genus hRR hC hω₀

end S_AlgebraicCurve_finite_and_finrank_regularDifferentials_eq_genus
end P2MW
export P2MW.S_AlgebraicCurve_finite_and_finrank_regularDifferentials_eq_genus (solution)
