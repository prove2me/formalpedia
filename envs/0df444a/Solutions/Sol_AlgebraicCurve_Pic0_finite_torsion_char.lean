-- Prove2me | solution 1 for AlgebraicCurve.Pic0.finite_torsion_char
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:01.734404+00:00
-- url     : https://prove2.me/submissions/e705776c-9c71-5a11-ba67-29bdd719c4a2

import Mathlib
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_CanonicalDivisor
import Definitions.Def_AlgebraicCurve_RegularDifferentials
import Definitions.Def_AlgebraicGeometry_KwCartierDlogFixednessEngine
import Definitions.Def_AlgebraicGeometry_KwFrobSemilinearFixedPointFiniteEngine
import Theorems.Thm_AlgebraicCurve_finite_and_finrank_regularDifferentials_eq_genus
import Theorems.Thm_AlgebraicCurve_KwPke_kw_pke_hsep_of_isSeparable_adjoin
import Theorems.Thm_KaehlerDifferential_D_ne_zero_of_transcendental
import Theorems.Thm_AlgebraicCurve_dCoordGenerates_of_isCurveOver
import Theorems.Thm_AlgebraicCurve_dlog_mem_regularDifferentials_of_forall_dvd_ord
import Theorems.Thm_AlgebraicCurve_Pic0_exists_injective_addMonoidHom_torsion_dlog
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_Pic0_finite_torsion_char
p2m_attr_erase "instance" "AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupDivisor AlgebraicCurve.Pic0.instModuleZModTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instDistribMulActionTorsion"
p2m_attr_erase "instance" "AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instSMulTorsion AlgebraicCurve.SemilinearAut.instMulActionSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instSMulCommClassZModTorsion AlgebraicCurve.SemilinearAut.instMulSemiringActionSubtypeProdRingAutMemSubgroup instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy"
p2m_attr_erase "simp" "AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq"
p2m_attr_erase "simp" "AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.SemilinearAut.toRingAut_inv AlgebraicCurve.SemilinearAut.smul_def AlgebraicCurve.SemilinearAut.smul_single AlgebraicCurve.SemilinearAut.smul_toValuationSubring AlgebraicCurve.SemilinearAut.baseAut_inv AlgebraicCurve.SemilinearAut.baseAut_ofAlgAut AlgebraicCurve.SemilinearAut.toRingAut_ofAlgAut AlgebraicCurve.SemilinearAut.torsionRep_apply AlgebraicCurve.SemilinearAut.toRingAut_one AlgebraicCurve.SemilinearAut.deg_smul"
p2m_attr_erase "simp" "AlgebraicCurve.SemilinearAut.degree_smul AlgebraicCurve.SemilinearAut.coe_degZeroSMulHom AlgebraicCurve.SemilinearAut.baseAut_mul AlgebraicCurve.SemilinearAut.coe_smulValuationSubringEquiv_apply AlgebraicCurve.SemilinearAut.baseAut_one AlgebraicCurve.SemilinearAut.ofAlgAut_smul AlgebraicCurve.SemilinearAut.coe_torsion_smul AlgebraicCurve.SemilinearAut.toRingAut_mul AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.jqNModC_one ModularCurve.qExpand_coeff_mul ModularCurve.qExpandₐ_apply ModularCurve.jqN_one ModularCurve.qExpand_single ModularCurve.dedekindPsi_one ModularCurve.ModularPolynomialData.mk.sizeOf_spec ModularCurve.evalAtJ_X ModularCurve.ModularPolynomialData.mk.injEq ModularCurve.constantCoeff_jNum ModularCurve.constantCoeff_eisenstein4 ModularCurve.qExpand_C ModularCurve.coeff_jq_neg_one ModularCurve.constantCoeff_jNumQ ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply"

set_option maxHeartbeats 1600000
set_option autoImplicit false

p2m_open "AlgebraicCurve P2MW.S_AlgebraicCurve_Pic0_finite_torsion_char.AlgebraicCurve AlgebraicCurve.KwPke AlgebraicCurve.KwCart AlgebraicCurve.KwCfx AlgebraicCurve.KwFsfp"

noncomputable section

namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "Place Pic0 Pic0.torsion IsCurveOver HasCanonicalDivisor regularDifferentials kw_hwcd_dlog finite_and_finrank_regularDifferentials_eq_genus dCoordGenerates_of_isCurveOver dlog_mem_regularDifferentials_of_forall_dvd_ord Pic0.exists_injective_addMonoidHom_torsion_dlog"
namespace CharlAsm
p2m_open "AlgebraicCurve"

variable {K F : Type*} [Field K] [Field F] [Algebra K F]
variable {ℓ : ℕ} [hℓ : Fact ℓ.Prime] [CharP F ℓ]

theorem C_smul_K (t : F) (hdt : KaehlerDifferential.D K F t ≠ 0)
    (hspan : Submodule.span F {KaehlerDifferential.D K F t} = ⊤)
    (hsep : ∀ x : F, IsSeparable (kw_pke_expansionField (ℓ := ℓ) t).toSubfield x)
    (hdeg : (minpoly (kw_pke_pthPowers F ℓ) t).natDegree = ℓ)
    (a : K) (ω : Ω[F⁄K]) :
    kw_cart_C (K := K) t hdt hspan hsep hdeg (a ^ ℓ • ω)
      = a • kw_cart_C (K := K) t hdt hspan hsep hdeg ω := by
  have h1 : (a ^ ℓ) • ω = (algebraMap K F (a ^ ℓ)) • ω := (algebraMap_smul F _ ω).symm
  rw [h1, map_pow, kw_cart_C_semilinear, algebraMap_smul]

theorem mapsTo_span_fixed [CharP K ℓ] [PerfectRing K ℓ]
    (t : F) (hdt : KaehlerDifferential.D K F t ≠ 0)
    (hspan : Submodule.span F {KaehlerDifferential.D K F t} = ⊤)
    (hsep : ∀ x : F, IsSeparable (kw_pke_expansionField (ℓ := ℓ) t).toSubfield x)
    (hdeg : (minpoly (kw_pke_pthPowers F ℓ) t).natDegree = ℓ)
    (S : Set Ω[F⁄K]) (hS : ∀ ω ∈ S, kw_cart_C (K := K) t hdt hspan hsep hdeg ω = ω) :
    Set.MapsTo (kw_cart_C (K := K) t hdt hspan hsep hdeg)
      (Submodule.span K S) (Submodule.span K S) := by
  have hC0 : kw_cart_C (K := K) t hdt hspan hsep hdeg 0 = 0 := by
    have h := kw_cart_C_add (K := K) t hdt hspan hsep hdeg 0 0
    rw [add_zero] at h
    exact (add_left_cancel (h.symm.trans (add_zero _).symm).symm).symm
  intro ω hω
  rw [SetLike.mem_coe] at hω ⊢
  induction hω using Submodule.span_induction with
  | mem x hx =>
      rw [hS x hx]
      exact Submodule.subset_span hx
  | zero =>
      rw [hC0]
      exact Submodule.zero_mem _
  | add x y hx hy ihx ihy =>
      rw [kw_cart_C_add]
      exact Submodule.add_mem _ ihx ihy
  | smul a x hx ih =>
      obtain ⟨b, hb⟩ : ∃ b : K, b ^ ℓ = a :=
        ⟨(frobeniusEquiv K ℓ).symm a, by
          have h := (frobeniusEquiv K ℓ).apply_symm_apply a
          rwa [frobeniusEquiv_def] at h⟩
      rw [← hb, C_smul_K t hdt hspan hsep hdeg b x]
      exact Submodule.smul_mem _ b ih

theorem fixed_regular_finite [CharP K ℓ] [PerfectRing K ℓ]
    (t : F) (hdt : KaehlerDifferential.D K F t ≠ 0)
    (hspan : Submodule.span F {KaehlerDifferential.D K F t} = ⊤)
    (hsep : ∀ x : F, IsSeparable (kw_pke_expansionField (ℓ := ℓ) t).toSubfield x)
    (hdeg : (minpoly (kw_pke_pthPowers F ℓ) t).natDegree = ℓ)
    [FiniteDimensional K (regularDifferentials K F)] :
    {ω : Ω[F⁄K] | ω ∈ regularDifferentials K F
      ∧ kw_cart_C (K := K) t hdt hspan hsep hdeg ω = ω}.Finite := by
  set S : Set Ω[F⁄K] := {ω : Ω[F⁄K] | ω ∈ regularDifferentials K F
      ∧ kw_cart_C (K := K) t hdt hspan hsep hdeg ω = ω} with hSdef
  have hle : Submodule.span K S ≤ regularDifferentials K F :=
    Submodule.span_le.mpr fun ω hω => hω.1
  haveI : FiniteDimensional K (Submodule.span K S) := Submodule.finiteDimensional_of_le hle
  have hseam := kw_fsfp_fixedPoints_inter_finite_of_mapsTo (ℓ := ℓ)
    (Submodule.span K S)
    (kw_cart_C (K := K) t hdt hspan hsep hdeg)
    (kw_cart_C_add (K := K) t hdt hspan hsep hdeg)
    (C_smul_K (K := K) t hdt hspan hsep hdeg)
    (mapsTo_span_fixed (K := K) t hdt hspan hsep hdeg S fun ω hω => hω.2)
  refine hseam.subset ?_
  rintro ω ⟨hreg, hfix⟩
  exact ⟨Submodule.subset_span ⟨hreg, hfix⟩, hfix⟩

end AlgebraicCurve.CharlAsm

open AlgebraicCurve.CharlAsm in
theorem solution (K F : Type*) [Field K] [Field F] [Algebra K F]
    [IsAlgClosed K] (p : ℕ) [Fact p.Prime] [CharP K p]
    (hfg : ∃ x : F, Transcendental K x ∧ FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F
      ∧ Algebra.IsSeparable (IntermediateField.adjoin K ({x} : Set F)) F)
    [AlgebraicCurve.IsCurveOver K F] [Algebra.EssFiniteType K F]
    [AlgebraicCurve.HasCanonicalDivisor (K := K) (F := F)] :
    Finite (AlgebraicCurve.Pic0.torsion K F p) := by
  obtain ⟨x, hx, hfd, hsepK⟩ := hfg
  haveI := hfd
  haveI := hsepK

  haveI : CharP F p := charP_of_injective_algebraMap (algebraMap K F).injective p
  haveI : ExpChar K p := ExpChar.prime (Fact.out : p.Prime)
  haveI : PerfectField K := IsAlgClosed.perfectField K
  haveI : PerfectRing K p := PerfectField.toPerfectRing p
  haveI : ∀ w : Place K F, w.DCoordGenerates := AlgebraicCurve.dCoordGenerates_of_isCurveOver

  have hdt : KaehlerDifferential.D K F x ≠ 0 :=
    KaehlerDifferential.D_ne_zero_of_transcendental K x hx
  have hspan := kw_cart_hspan_of_isCurveOver (K := K) hdt
  have hdeg := kw_cart_minpoly_natDegree_eq (K := K) (ℓ := p) hdt
  have hsep := kw_pke_hsep_of_isSeparable_adjoin (K := K) (ℓ := p) x hsepK

  haveI : FiniteDimensional K (regularDifferentials K F) :=
    (AlgebraicCurve.finite_and_finrank_regularDifferentials_eq_genus (K := K) (F := F)).1

  have hS := fixed_regular_finite (K := K) (ℓ := p) x hdt hspan hsep hdeg

  obtain ⟨φ, hinj, hφ⟩ := AlgebraicCurve.Pic0.exists_injective_addMonoidHom_torsion_dlog K F p x hx hsepK hdt
  have hrange : Set.range φ ⊆ {ω : Ω[F⁄K] | ω ∈ regularDifferentials K F
      ∧ kw_cart_C (K := K) x hdt hspan hsep hdeg ω = ω} := by
    rintro _ ⟨c, rfl⟩
    obtain ⟨f, hf, hdvd, hc⟩ := hφ c
    rw [hc]
    refine ⟨AlgebraicCurve.dlog_mem_regularDifferentials_of_forall_dvd_ord K F p hf hdvd, ?_⟩
    have hfix := kw_cfx_C_dlog_fixed (K := K) x hdt hspan hsep hdeg hf
    simpa only [kw_hwcd_dlog] using hfix
  haveI := ((hS.subset hrange).to_subtype : Finite (Set.range φ))
  exact Finite.of_injective (Set.rangeFactorization φ)
    (fun a b hab => hinj (congrArg Subtype.val hab))

end

end S_AlgebraicCurve_Pic0_finite_torsion_char
end P2MW
export P2MW.S_AlgebraicCurve_Pic0_finite_torsion_char (solution)
