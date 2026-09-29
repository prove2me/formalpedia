-- Prove2me | solution 1 for AlgebraicGeometry.RelPicard.exists_finite_etale_hasChartSections_of_finiteMapData
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:03.589526+00:00
-- url     : https://prove2.me/submissions/a4f66255-8622-561b-99ac-c7da5b131f18

import Mathlib
import Definitions.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier
import Definitions.Def_AlgebraicGeometry_RelPicardChartSections
import Definitions.Def_AlgebraicGeometry_SmoothProperCurveBase
import Definitions.Def_AlgebraicCurve_CurveModel
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Definitions.Def_AlgebraicCurve_Repartitions
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_AdelicIndex
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import Definitions.Def_AlgebraicGeometry_SmoothProperCurveFiniteMapData
import Theorems.Thm_Algebra_Etale_exists_finite_etale_faithfullyFlat_tensorProduct_algEquiv_pi
import Theorems.Thm_AlgebraicCurve_exists_canonicalDivisor_genus_riemannRoch
import Theorems.Thm_AlgebraicCurve_RROpens_exists_injective_ell_sub_sum_single_eq_one_of_le_card
import Theorems.Thm_AlgebraicGeometry_SmoothProperCurve_exists_curveModel_iso_pullback_of_isAlgClosed
import Theorems.Thm_AlgebraicGeometry_SmoothProperCurve_exists_genus_forall_geometricFibre_riemannRoch_imp_eq_of_finiteMapData
import Theorems.Thm_AlgebraicGeometry_SmoothProperCurve_exists_finite_etale_isClosedImmersion_le_finrank_of_finiteMapData
import Theorems.Thm_AlgebraicGeometry_SmoothProperCurve_exists_sections_injective_of_tensorProduct_algEquiv_pi
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_RelPicard_exists_finite_etale_hasChartSections_of_finiteMapData
p2m_attr_erase "instance" "AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupDivisor AlgebraicCurve.Pic0.instModuleZModTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instDistribMulActionTorsion"
p2m_attr_erase "instance" "AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instSMulTorsion AlgebraicCurve.SemilinearAut.instMulActionSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instSMulCommClassZModTorsion AlgebraicCurve.SemilinearAut.instMulSemiringActionSubtypeProdRingAutMemSubgroup instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy"
p2m_attr_erase "simp" "AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring"
p2m_attr_erase "simp" "AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.SemilinearAut.toRingAut_inv AlgebraicCurve.SemilinearAut.smul_def AlgebraicCurve.SemilinearAut.smul_single AlgebraicCurve.SemilinearAut.smul_toValuationSubring AlgebraicCurve.SemilinearAut.baseAut_inv AlgebraicCurve.SemilinearAut.baseAut_ofAlgAut AlgebraicCurve.SemilinearAut.toRingAut_ofAlgAut AlgebraicCurve.SemilinearAut.torsionRep_apply AlgebraicCurve.SemilinearAut.toRingAut_one AlgebraicCurve.SemilinearAut.deg_smul AlgebraicCurve.SemilinearAut.degree_smul AlgebraicCurve.SemilinearAut.coe_degZeroSMulHom AlgebraicCurve.SemilinearAut.baseAut_mul AlgebraicCurve.SemilinearAut.coe_smulValuationSubringEquiv_apply AlgebraicCurve.SemilinearAut.baseAut_one AlgebraicCurve.SemilinearAut.ofAlgAut_smul"
p2m_attr_erase "simp" "AlgebraicCurve.SemilinearAut.coe_torsion_smul AlgebraicCurve.SemilinearAut.toRingAut_mul AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.jqNModC_one ModularCurve.qExpand_coeff_mul ModularCurve.qExpandₐ_apply ModularCurve.jqN_one ModularCurve.qExpand_single ModularCurve.dedekindPsi_one ModularCurve.ModularPolynomialData.mk.sizeOf_spec ModularCurve.evalAtJ_X ModularCurve.ModularPolynomialData.mk.injEq ModularCurve.constantCoeff_jNum ModularCurve.constantCoeff_eisenstein4 ModularCurve.qExpand_C ModularCurve.coeff_jq_neg_one ModularCurve.constantCoeff_jNumQ ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq AlgebraicCurve.coe_cechH0Equiv_apply AlgebraicCurve.cechH1ToH1_mk"
p2m_attr_erase "simp" "AlgebraicCurve.lSpaceOn_univ AlgebraicCurve.lSpaceOn_empty"

set_option autoImplicit false

universe u

open scoped TensorProduct
p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.RelPicard AlgebraicGeometry.SmoothProperCurve NeronModelInfra AlgebraicCurve~genus"

theorem solution
    (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R)) [IsProper c]
    [SmoothOfRelativeDimension 1 c] [GeometricallyIntegral c]
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c)
    (h𝔉 : ∀ m₀ : ℕ, ∃ 𝔉 : SmoothProperCurve.FiniteMapData c ε, m₀ ≤ 𝔉.m ∧ 𝔉.LevelSetsGenericallyEtale) :
    ∃ (R' : Type u) (_ : CommRing R') (_ : Algebra R R') (_ : Module.Finite R R')
      (_ : Algebra.Etale R R') (_ : Module.FaithfullyFlat R R') (_ : IsNoetherianRing R')
      (n g r : ℕ) (_ : 2 * g < r)
      (γ : Fin n → Fin (r - g) → SchemeHomOver (𝟙 (Spec (CommRingCat.of R'))) (baseChange R c R')),
      HasChartSections (baseChange R c R') γ := by
  classical

  obtain ⟨𝔉₀, -⟩ := h𝔉 0
  obtain ⟨g, hg⟩ := exists_genus_forall_geometricFibre_riemannRoch_imp_eq_of_finiteMapData R c ε 𝔉₀

  obtain ⟨R₀, _, _, _, _, _, _, _, B, _, _, _, _, ι, hιci, hι, hN⟩ :=
    exists_finite_etale_isClosedImmersion_le_finrank_of_finiteMapData R c ε h𝔉 (2 * g + 2)

  obtain ⟨R', _, _, _, _, _, _, ⟨φ⟩⟩ :=
    Algebra.Etale.exists_finite_etale_faithfullyFlat_tensorProduct_algEquiv_pi R₀ B

  letI : Algebra R R' := Algebra.compHom R' (algebraMap R R₀)
  haveI : IsScalarTower R R₀ R' := IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI : Module.Finite R R' := Module.Finite.trans R₀ R'
  haveI : Algebra.Etale R R' := Algebra.Etale.comp R R₀ R'
  haveI : Module.FaithfullyFlat R R' := Module.FaithfullyFlat.trans R R₀ R'
  haveI : IsClosedImmersion ι := hιci

  obtain ⟨σ, hσ⟩ := exists_sections_injective_of_tensorProduct_algEquiv_pi R c R₀ B ι hι R'
    (Module.finrank R₀ B) φ

  let E := Fintype.equivFin (Fin (2 * g + 1 - g) → Fin (Module.finrank R₀ B))
  refine ⟨R', inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    Fintype.card (Fin (2 * g + 1 - g) → Fin (Module.finrank R₀ B)), g, 2 * g + 1, by omega,
    fun i j => σ (E.symm i j), ?_⟩
  intro k _ _ s

  obtain ⟨L, _, _, _, _, M, e, he⟩ := exists_curveModel_iso_pullback_of_isAlgClosed R' (baseChange R c R') k s
  refine ⟨L, inferInstance, inferInstance, M, e, he, ?_⟩

  obtain ⟨Kc, g', hRR⟩ := AlgebraicCurve.exists_canonicalDivisor_genus_riemannRoch k L
  have hgg : g' = g := by
    refine hg k (s ≫ specMap R R') L M (e ≪≫ pullbackLeftPullbackSndIso c (specMap R R') s) ?_ Kc g' hRR
    rw [Iso.trans_hom, Category.assoc, pullbackLeftPullbackSndIso_hom_snd, he]
  rw [hgg] at hRR
  refine ⟨⟨Kc, hRR⟩, ?_⟩
  intro D _ hdegD

  let P : {p : Spec (CommRingCat.of k) ⟶ pullback (baseChange R c R') s //
      p ≫ pullback.snd (baseChange R c R') s = 𝟙 _} → Place k L :=
    fun q => M.pointEquivPlace ⟨q.1 ≫ e.inv, by rw [Category.assoc, ← he, e.inv_hom_id_assoc]; exact q.2⟩
  have hPinj : Function.Injective P := by
    intro q q' h
    have h1 := congrArg Subtype.val (M.pointEquivPlace.injective h)
    exact Subtype.ext ((cancel_mono e.inv).mp h1)
  let pl : Fin (Module.finrank R₀ B) → Place k L := fun m => P (sectionFibrePoint (σ m) s)
  have key : ∀ m, (sectionFibrePoint (σ m) s).1 ≫ pullback.fst (baseChange R c R') s = s ≫ (σ m).1 :=
    fun m => pullback.lift_fst _ _ _
  have hplinj : Function.Injective pl := by
    intro m m' h
    have h1 := congrArg (fun q => q.1 ≫ pullback.fst (baseChange R c R') s) (hPinj h)
    rw [key, key] at h1
    exact hσ k s h1
  let S : Finset (Place k L) := Finset.univ.image pl
  have hScard : 2 * g + 1 + 1 ≤ S.card := by
    have : S.card = Module.finrank R₀ B := by
      rw [Finset.card_image_of_injective _ hplinj, Finset.card_univ, Fintype.card_fin]
    omega
  have hS1 : ∀ v ∈ S, v.deg = 1 := fun v _ => IsCurveOver.deg_eq_one_of_isAlgClosed v

  obtain ⟨f, -, hfS, hf⟩ :=
    AlgebraicCurve.RROpens.exists_injective_ell_sub_sum_single_eq_one_of_le_card hRR (by omega) S hS1
      hScard D hdegD
  have hch : ∀ j, ∃ m, pl m = f j := fun j => by
    simpa [S, Finset.mem_image] using hfS j
  choose μ hμ using hch
  refine ⟨E μ, ?_⟩
  show ell (D - ∑ j, Finsupp.single (P (sectionFibrePoint (σ (E.symm (E μ) j)) s)) 1) = 1
  simp only [Equiv.symm_apply_apply]
  have hsum : ∑ j, Finsupp.single (P (sectionFibrePoint (σ (μ j)) s)) (1 : ℤ)
      = ∑ j, Finsupp.single (f j) 1 :=
    Finset.sum_congr rfl fun j _ => by rw [← hμ j]
  rw [hsum]
  exact hf

end S_AlgebraicGeometry_RelPicard_exists_finite_etale_hasChartSections_of_finiteMapData
end P2MW
export P2MW.S_AlgebraicGeometry_RelPicard_exists_finite_etale_hasChartSections_of_finiteMapData (solution)
