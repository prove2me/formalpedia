-- Prove2me | solution 1 for AlgebraicCurve.mem_span_image_polarDifferentials_of_constantFieldExtension_of_isAlgClosed
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.4153+00:00
-- url     : https://prove2.me/submissions/27fb82bd-ff52-59ab-b963-d2fc92b2f2c7

import Mathlib
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_PolarDifferentials
import Definitions.Def_AlgebraicCurve_CanonicalDivisor
import Definitions.Def_AlgebraicCurve_RiemannRochRows
import Theorems.Thm_AlgebraicCurve_map_mem_polarDifferentials_of_constantFieldExtension_of_isAlgClosed
import Theorems.Thm_AlgebraicCurve_finite_and_finrank_polarDifferentials_eq
import Theorems.Thm_AlgebraicCurve_finite_and_finrank_regularDifferentials_eq_genus
import Theorems.Thm_AlgebraicCurve_Place_exists_comap_algebraMap_eq_of_constantFieldExtension_of_isAlgClosed
import Theorems.Thm_AlgebraicCurve_linearIndependent_of_constantFieldExtension_of_isAlgClosed
import Theorems.Thm_AlgebraicCurve_hasCanonicalDivisor_of_isCurveOver
import Theorems.Thm_AlgebraicCurve_genus_eq_genusFF
import Theorems.Thm_AlgebraicCurve_functionFieldRiemannRoch_of_isAlgClosed_of_transcendental
import Theorems.Thm_AlgebraicCurve_constantsAreBase_of_isAlgClosed_of_transcendental
import Theorems.Thm_AlgebraicCurve_stichtenothGenusExists_of_isCurveOver
import Theorems.Thm_AlgebraicCurve_weilDualityAdelic_of_functionFieldRiemannRoch_of_stichtenothGenusExists
import Theorems.Thm_AlgebraicCurve_genusFF_eq_of_constantFieldExtension_of_isAlgClosed
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_mem_span_image_polarDifferentials_of_constantFieldExtension_of_isAlgClosed
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupDivisor AlgebraicCurve.Pic0.instModuleZModTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instDistribMulActionTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instSMulTorsion AlgebraicCurve.SemilinearAut.instMulActionSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instSMulCommClassZModTorsion AlgebraicCurve.SemilinearAut.instMulSemiringActionSubtypeProdRingAutMemSubgroup instDecEqAlgebraicClosureRat"
p2m_attr_erase "instance" "WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy"
p2m_attr_erase "simp" "AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk"
p2m_attr_erase "simp" "ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.SemilinearAut.toRingAut_inv AlgebraicCurve.SemilinearAut.smul_def AlgebraicCurve.SemilinearAut.smul_single AlgebraicCurve.SemilinearAut.smul_toValuationSubring AlgebraicCurve.SemilinearAut.baseAut_inv AlgebraicCurve.SemilinearAut.baseAut_ofAlgAut AlgebraicCurve.SemilinearAut.toRingAut_ofAlgAut AlgebraicCurve.SemilinearAut.torsionRep_apply AlgebraicCurve.SemilinearAut.toRingAut_one AlgebraicCurve.SemilinearAut.deg_smul AlgebraicCurve.SemilinearAut.degree_smul AlgebraicCurve.SemilinearAut.coe_degZeroSMulHom AlgebraicCurve.SemilinearAut.baseAut_mul AlgebraicCurve.SemilinearAut.coe_smulValuationSubringEquiv_apply AlgebraicCurve.SemilinearAut.baseAut_one AlgebraicCurve.SemilinearAut.ofAlgAut_smul AlgebraicCurve.SemilinearAut.coe_torsion_smul AlgebraicCurve.SemilinearAut.toRingAut_mul AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.jqNModC_one ModularCurve.qExpand_coeff_mul ModularCurve.qExpandₐ_apply ModularCurve.jqN_one ModularCurve.qExpand_single ModularCurve.dedekindPsi_one ModularCurve.ModularPolynomialData.mk.sizeOf_spec ModularCurve.evalAtJ_X ModularCurve.ModularPolynomialData.mk.injEq ModularCurve.constantCoeff_jNum ModularCurve.constantCoeff_eisenstein4 ModularCurve.qExpand_C ModularCurve.coeff_jq_neg_one ModularCurve.constantCoeff_jNumQ"
p2m_attr_erase "simp" "ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq"

set_option autoImplicit false

p2m_open "AlgebraicCurve P2MW.S_AlgebraicCurve_mem_span_image_polarDifferentials_of_constantFieldExtension_of_isAlgClosed.AlgebraicCurve KaehlerDifferential"

namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "IsCurveOver IsCurveOver.finrank_kaehler Place Place.ext polarDifferentials polarDifferentials_mono polarDifferentials_empty regularDifferentials Place.ordDifferential HasCanonicalDivisor genus HasCanonicalDivisor.exists_divisor WeilDualityAdelic FunctionFieldRiemannRoch ConstantsAreBase StichtenothGenusExists genusFF map_mem_polarDifferentials_of_constantFieldExtension_of_isAlgClosed finite_and_finrank_polarDifferentials_eq finite_and_finrank_regularDifferentials_eq_genus Place.exists_comap_algebraMap_eq_of_constantFieldExtension_of_isAlgClosed linearIndependent_of_constantFieldExtension_of_isAlgClosed hasCanonicalDivisor_of_isCurveOver genus_eq_genusFF functionFieldRiemannRoch_of_isAlgClosed_of_transcendental constantsAreBase_of_isAlgClosed_of_transcendental stichtenothGenusExists_of_isCurveOver weilDualityAdelic_of_functionFieldRiemannRoch_of_stichtenothGenusExists genusFF_eq_of_constantFieldExtension_of_isAlgClosed"
namespace A2SupBody
p2m_open "AlgebraicCurve"

section Basic

variable {k L : Type*} [Field k] [Field L] [Algebra k L] (w : Place k L)

theorem ord_nonneg_of_mem {f : L} (hf : f ∈ w.toValuationSubring) : 0 ≤ w.ord f := by
  rcases eq_or_ne f 0 with rfl | hf0
  · simp
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible w.toValuationSubring
  obtain ⟨n, u, hu⟩ :=
    IsDiscreteValuationRing.eq_unit_mul_pow_irreducible
      (x := (⟨f, hf⟩ : w.toValuationSubring)) (by simpa [Subtype.ext_iff] using hf0) hπ
  have hf' : f = ((u : w.toValuationSubring) : L) * ((π : L) ^ (n : ℤ)) := by
    have := congrArg (fun z : w.toValuationSubring => (z : L)) hu
    simpa [zpow_natCast] using this
  rw [hf', w.ord_unit_smul_zpow u hπ]
  exact Int.natCast_nonneg n

theorem mem_of_ord_nonneg {f : L} (hf : f ≠ 0) (h : 0 ≤ w.ord f) : f ∈ w.toValuationSubring := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible w.toValuationSubring
  obtain ⟨u, hu⟩ := w.exists_unit_mul_zpow hf hπ
  rw [hu, ← Int.toNat_of_nonneg h, zpow_natCast]
  exact mul_mem (u : w.toValuationSubring).2 (pow_mem (π : w.toValuationSubring).2 _)

end Basic

section Curve

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

theorem isRegularAt_iff_differentialCoeff_mem [Nontrivial Ω[F⁄K]] (v : Place K F) [v.DCoordGenerates]
    (ω : Ω[F⁄K]) : v.IsRegularAt ω ↔ v.differentialCoeff ω ∈ v.toValuationSubring := by
  constructor
  · rintro ⟨f, hf, h⟩
    rw [v.differentialCoeff_unique h]
    exact hf
  · intro h
    exact ⟨v.differentialCoeff ω, h, (v.differentialCoeff_smul_dCoord ω).symm⟩

theorem finite_setOf_not_isRegularAt [Nontrivial Ω[F⁄K]] [HasCanonicalDivisor (K := K) (F := F)]
    [∀ v : Place K F, v.DCoordGenerates] (ω : Ω[F⁄K]) :
    {v : Place K F | ¬ v.IsRegularAt ω}.Finite := by
  rcases eq_or_ne ω 0 with rfl | hω
  · have : {v : Place K F | ¬ v.IsRegularAt (0 : Ω[F⁄K])} = ∅ := by
      ext v
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_not]
      exact v.isRegularAt_zero
    rw [this]
    exact Set.finite_empty
  obtain ⟨D, hD⟩ := HasCanonicalDivisor.exists_divisor ω hω
  refine D.finite_support.subset ?_
  intro v hv
  rw [Set.mem_setOf_eq, isRegularAt_iff_differentialCoeff_mem] at hv
  rw [Function.mem_support, hD v, Place.ordDifferential]
  intro h0
  have hc0 : v.differentialCoeff ω ≠ 0 := by
    intro hc
    exact hv (hc ▸ zero_mem _)
  exact hv (mem_of_ord_nonneg v hc0 (le_of_eq h0.symm))

theorem genus_eq_genusFF_of_isAlgClosed [IsAlgClosed K] [Algebra.EssFiniteType K F] [IsCurveOver K F]
    [HasCanonicalDivisor (K := K) (F := F)] [∀ v : Place K F, v.DCoordGenerates]
    (hfg : ∃ x : F, Transcendental K x ∧ FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F) :
    genus K F = genusFF K F := by
  obtain ⟨x, hx, hfd⟩ := hfg
  haveI := hfd
  have hC : ConstantsAreBase K F := constantsAreBase_of_isAlgClosed_of_transcendental x hx
  have hRR : FunctionFieldRiemannRoch K F := functionFieldRiemannRoch_of_isAlgClosed_of_transcendental hx hfd
  have hSG : StichtenothGenusExists K F := stichtenothGenusExists_of_isCurveOver hC
  have hWDA : WeilDualityAdelic K F :=
    weilDualityAdelic_of_functionFieldRiemannRoch_of_stichtenothGenusExists hRR hSG
  exact genus_eq_genusFF hRR hWDA hC

theorem exists_smul_eq [IsCurveOver K F] {ω₀ : Ω[F⁄K]} (hω₀ : ω₀ ≠ 0) (ω : Ω[F⁄K]) :
    ∃ f : F, f • ω₀ = ω :=
  (finrank_eq_one_iff_of_nonzero' ω₀ hω₀).mp IsCurveOver.finrank_kaehler ω

theorem kaehler_eq_zero_of_forall_D_eq_zero (h : ∀ x : F, D K F x = 0) (ω : Ω[F⁄K]) : ω = 0 := by
  have hω : ω ∈ Submodule.span F (Set.range (D K F)) := by
    rw [KaehlerDifferential.span_range_derivation]; exact Submodule.mem_top
  have hr : Set.range (D K F) ⊆ {0} := by
    rintro _ ⟨x, rfl⟩; exact h x
  have := Submodule.span_mono hr hω
  rw [Submodule.span_singleton_eq_bot.mpr rfl] at this
  exact (Submodule.mem_bot F).mp this

end Curve

section CFE

variable {K F K' F' : Type*}
  [Field K] [Field F] [Field K'] [Field F'] [Algebra K F] [Algebra K' F']
  [Algebra K K'] [Algebra F F'] [Algebra K F'] [IsScalarTower K K' F'] [IsScalarTower K F F'] [SMulCommClass K' F F']

noncomputable def kerD (K' F' : Type*) [Field K'] [Field F'] [Algebra K' F'] : IntermediateField K' F' where
  carrier := {y : F' | D K' F' y = 0}
  mul_mem' {a b} ha hb := by
    simp only [Set.mem_setOf_eq] at ha hb ⊢
    rw [Derivation.leibniz, ha, hb, smul_zero, smul_zero, add_zero]
  one_mem' := by
    simp only [Set.mem_setOf_eq]
    exact Derivation.map_one_eq_zero _
  add_mem' {a b} ha hb := by
    simp only [Set.mem_setOf_eq] at ha hb ⊢
    rw [map_add, ha, hb, add_zero]
  zero_mem' := by
    simp only [Set.mem_setOf_eq]
    exact map_zero _
  algebraMap_mem' r := by
    simp only [Set.mem_setOf_eq]
    exact Derivation.map_algebraMap _ r
  inv_mem' y hy := by
    simp only [Set.mem_setOf_eq] at hy ⊢
    rcases eq_or_ne y 0 with rfl | hy0
    · rw [inv_zero]; exact map_zero _
    have h1 : D K' F' (y * y⁻¹) = 0 := by
      rw [mul_inv_cancel₀ hy0]; exact Derivation.map_one_eq_zero _
    rw [Derivation.leibniz, hy, smul_zero, add_zero] at h1
    exact (smul_eq_zero.mp h1).resolve_left hy0

theorem mem_kerD_iff (y : F') : y ∈ kerD K' F' ↔ D K' F' y = 0 := Iff.rfl

omit [SMulCommClass K' F F'] in

theorem exists_D_algebraMap_ne_zero [IsCurveOver K' F']
    (hgen : IntermediateField.adjoin K' (Set.range (algebraMap F F')) = ⊤) :
    ∃ x : F, D K' F' (algebraMap F F' x) ≠ 0 := by
  rcases forall_or_exists_not (fun x : F => D K' F' (algebraMap F F' x) = 0) with h | ⟨x, hx⟩
  swap
  · exact ⟨x, hx⟩
  exfalso
  have hle : IntermediateField.adjoin K' (Set.range (algebraMap F F')) ≤ kerD K' F' := by
    rw [IntermediateField.adjoin_le_iff]
    rintro _ ⟨x, rfl⟩
    exact h x
  rw [hgen, top_le_iff] at hle
  have hall : ∀ y : F', D K' F' y = 0 := fun y => by
    have : y ∈ kerD K' F' := hle ▸ IntermediateField.mem_top
    exact this
  obtain ⟨ω, hω⟩ := exists_ne (0 : Ω[F'⁄K'])
  exact hω (kaehler_eq_zero_of_forall_D_eq_zero hall ω)

theorem map_smul_base (c : K) (ω : Ω[F⁄K]) :
    KaehlerDifferential.map K K' F F' (c • ω) = algebraMap K K' c • KaehlerDifferential.map K K' F F' ω := by
  rw [← algebraMap_smul F c ω, LinearMap.map_smul, ← algebraMap_smul F' (algebraMap K F c),
    ← algebraMap_smul F' (algebraMap K K' c)]
  congr 1
  rw [← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply]

theorem map_smul_F (f : F) (ω : Ω[F⁄K]) :
    KaehlerDifferential.map K K' F F' (f • ω) = algebraMap F F' f • KaehlerDifferential.map K K' F F' ω := by
  rw [LinearMap.map_smul, algebraMap_smul]

variable [IsAlgClosed K] [IsCurveOver K F] [IsCurveOver K' F']

theorem finrank_span_image_map
    (hfg : ∃ x : F, Transcendental K x ∧ FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F)
    (hfg' : ∃ x : F', Transcendental K' x ∧
      FiniteDimensional (IntermediateField.adjoin K' ({x} : Set F')) F')
    (hgen : IntermediateField.adjoin K' (Set.range (algebraMap F F')) = ⊤)
    (P : Submodule K Ω[F⁄K]) [Module.Finite K P] :
    Module.finrank K' (Submodule.span K' (KaehlerDifferential.map K K' F F' '' (P : Set Ω[F⁄K]))) =
      Module.finrank K P := by
  classical

  obtain ⟨x₀, hx₀⟩ := exists_D_algebraMap_ne_zero (F := F) (K' := K') (F' := F') hgen
  set ω₀ : Ω[F⁄K] := D K F x₀ with hω₀def
  have hmapω₀ : KaehlerDifferential.map K K' F F' ω₀ = D K' F' (algebraMap F F' x₀) := KaehlerDifferential.map_D _ _ _ _ _
  have hω₀ : ω₀ ≠ 0 := by
    intro h
    apply hx₀
    rw [← hmapω₀, h, map_zero]

  set n := Module.finrank K P
  let b := Module.finBasis K P
  choose f hf using fun i : Fin n => exists_smul_eq (K := K) hω₀ ((b i : P) : Ω[F⁄K])

  let e : Fin n → Ω[F'⁄K'] := fun i => KaehlerDifferential.map K K' F F' ((b i : P) : Ω[F⁄K])
  have he : ∀ i, e i = algebraMap F F' (f i) • D K' F' (algebraMap F F' x₀) := by
    intro i
    show KaehlerDifferential.map K K' F F' ((b i : P) : Ω[F⁄K]) = _
    rw [← hf i, map_smul_F, hmapω₀]

  have hfli : LinearIndependent K f := by
    rw [linearIndependent_iff']
    intro s g hsum i hi
    have hb := b.linearIndependent
    rw [linearIndependent_iff'] at hb
    refine hb s g ?_ i hi
    apply Subtype.ext
    rw [Submodule.coe_sum, Submodule.coe_zero]
    have : ∑ j ∈ s, ((g j • b j : P) : Ω[F⁄K]) = (∑ j ∈ s, g j • f j) • ω₀ := by
      rw [Finset.sum_smul]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Submodule.coe_smul, ← hf j, smul_assoc]
    rw [this, hsum, zero_smul]
  have hfli' : LinearIndependent K' (fun i => algebraMap F F' (f i)) :=
    AlgebraicCurve.linearIndependent_of_constantFieldExtension_of_isAlgClosed K F K' F' hfg hfg' hgen hfli

  have heli : LinearIndependent K' e := by
    rw [linearIndependent_iff']
    intro s g hsum i hi
    rw [linearIndependent_iff'] at hfli'
    refine hfli' s g ?_ i hi
    have h1 : ∑ j ∈ s, g j • e j = (∑ j ∈ s, g j • algebraMap F F' (f j)) • D K' F' (algebraMap F F' x₀) := by
      rw [Finset.sum_smul]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [he j, smul_assoc]
    rw [h1] at hsum
    exact (smul_eq_zero.mp hsum).resolve_right hx₀

  have hspan : Submodule.span K' (KaehlerDifferential.map K K' F F' '' (P : Set Ω[F⁄K])) =
      Submodule.span K' (Set.range e) := by
    apply le_antisymm
    · rw [Submodule.span_le]
      rintro _ ⟨ω, hω, rfl⟩
      have hrepr := b.sum_repr ⟨ω, hω⟩
      have hω' : ω = ∑ i, (b.repr ⟨ω, hω⟩ i) • ((b i : P) : Ω[F⁄K]) := by
        have := congrArg (fun z : P => (z : Ω[F⁄K])) hrepr
        simp only [Submodule.coe_sum, Submodule.coe_smul] at this
        exact this.symm
      rw [hω', map_sum]
      refine Submodule.sum_mem _ fun i _ => ?_
      rw [map_smul_base]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
    · rw [Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      exact Submodule.subset_span ⟨_, (b i).2, rfl⟩
  rw [hspan, finrank_span_eq_card heli, Fintype.card_fin]

end CFE

section Key

variable {K F K' F' : Type*}
  [Field K] [Field F] [Field K'] [Field F'] [Algebra K F] [Algebra K' F']
  [Algebra K K'] [Algebra F F'] [Algebra K F'] [IsScalarTower K K' F'] [IsScalarTower K F F'] [SMulCommClass K' F F']
  [IsAlgClosed K] [IsAlgClosed K'] [IsCurveOver K F] [IsCurveOver K' F']
  [Algebra.EssFiniteType K F] [Algebra.EssFiniteType K' F']

theorem polarDifferentials_le_span_map_of_finset
    (hfg : ∃ x : F, Transcendental K x ∧ FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F)
    (hfg' : ∃ x : F', Transcendental K' x ∧
      FiniteDimensional (IntermediateField.adjoin K' ({x} : Set F')) F')
    (hgen : IntermediateField.adjoin K' (Set.range (algebraMap F F')) = ⊤)
    (hdK : ∀ v : Place K F, v.DCoordGenerates) (hdK' : ∀ w : Place K' F', w.DCoordGenerates)
    (lift : Place K F → Place K' F')
    (hlift : ∀ v : Place K F, (lift v).toValuationSubring.comap (algebraMap F F') = v.toValuationSubring)
    (huniq : ∀ (v : Place K F) (w : Place K' F'),
      w.toValuationSubring.comap (algebraMap F F') = v.toValuationSubring → w = lift v)
    (T : Finset (Place K F)) :
    polarDifferentials K' F'
        {w : Place K' F' | ∃ v ∈ (T : Set (Place K F)), w.toValuationSubring.comap (algebraMap F F') = v.toValuationSubring} ≤
      Submodule.span K'
        (KaehlerDifferential.map K K' F F' '' (polarDifferentials K F (T : Set (Place K F)) : Set (Ω[F⁄K]))) := by
  classical
  haveI : ∀ v : Place K F, v.DCoordGenerates := hdK
  haveI : ∀ w : Place K' F', w.DCoordGenerates := hdK'
  haveI : HasCanonicalDivisor (K := K) (F := F) := hasCanonicalDivisor_of_isCurveOver
  haveI : HasCanonicalDivisor (K := K') (F := F') := hasCanonicalDivisor_of_isCurveOver

  have hgenus : genus K' F' = genus K F := by
    rw [genus_eq_genusFF_of_isAlgClosed hfg, genus_eq_genusFF_of_isAlgClosed hfg',
      AlgebraicCurve.genusFF_eq_of_constantFieldExtension_of_isAlgClosed K F K' F' hfg hfg' hgen]
  have hlift_inj : Function.Injective lift := by
    intro v₁ v₂ h
    apply Place.ext
    rw [← hlift v₁, ← hlift v₂, h]

  have hset : {w : Place K' F' | ∃ v ∈ (T : Set (Place K F)),
      w.toValuationSubring.comap (algebraMap F F') = v.toValuationSubring} = ((T.image lift : Finset (Place K' F')) : Set (Place K' F')) := by
    ext w
    simp only [Set.mem_setOf_eq, Finset.coe_image, Set.mem_image, Finset.mem_coe]
    constructor
    · rintro ⟨v, hv, h⟩
      exact ⟨v, hv, (huniq v w h).symm⟩
    · rintro ⟨v, hv, rfl⟩
      exact ⟨v, hv, hlift v⟩

  set P : Submodule K Ω[F⁄K] := polarDifferentials K F (T : Set (Place K F)) with hPdef
  set P' : Submodule K' Ω[F'⁄K'] := polarDifferentials K' F'
    {w : Place K' F' | ∃ v ∈ (T : Set (Place K F)), w.toValuationSubring.comap (algebraMap F F') = v.toValuationSubring}
    with hP'def
  set V : Submodule K' Ω[F'⁄K'] := Submodule.span K' (KaehlerDifferential.map K K' F F' '' (P : Set (Ω[F⁄K]))) with hVdef
  have hVle : V ≤ P' := by
    rw [hVdef, Submodule.span_le]
    rintro _ ⟨ω, hω, rfl⟩
    exact AlgebraicCurve.map_mem_polarDifferentials_of_constantFieldExtension_of_isAlgClosed K F K' F'
      hfg hfg' hgen hdK hdK' (T : Set (Place K F)) ω hω

  have hdims : Module.Finite K P ∧ Module.Finite K' P' ∧ Module.finrank K' P' = Module.finrank K P := by
    rcases T.eq_empty_or_nonempty with hT | hT
    ·
      have hP : P = regularDifferentials K F := by
        rw [hPdef, hT, Finset.coe_empty, polarDifferentials_empty]
      have hP' : P' = regularDifferentials K' F' := by
        rw [hP'def, hset, hT, Finset.image_empty, Finset.coe_empty, polarDifferentials_empty]
      obtain ⟨h1, h2⟩ := AlgebraicCurve.finite_and_finrank_regularDifferentials_eq_genus (K := K) (F := F)
      obtain ⟨h1', h2'⟩ := AlgebraicCurve.finite_and_finrank_regularDifferentials_eq_genus (K := K') (F := F')
      rw [hP, hP']
      exact ⟨h1, h1', by rw [h2, h2', hgenus]⟩
    · obtain ⟨h1, h2⟩ := AlgebraicCurve.finite_and_finrank_polarDifferentials_eq (K := K) (F := F) T hT
      have hT' : (T.image lift).Nonempty := hT.image lift
      obtain ⟨h1', h2'⟩ := AlgebraicCurve.finite_and_finrank_polarDifferentials_eq (K := K') (F := F') (T.image lift) hT'
      have hP' : P' = polarDifferentials K' F' ((T.image lift : Finset (Place K' F')) : Set (Place K' F')) := by
        rw [hP'def, hset]
      rw [hP']
      refine ⟨h1, h1', ?_⟩
      rw [h2', h2, hgenus, Finset.card_image_of_injective T hlift_inj]
  obtain ⟨hfinP, hfinP', hdim⟩ := hdims
  haveI := hfinP
  haveI := hfinP'
  have hVdim : Module.finrank K' V = Module.finrank K P :=
    finrank_span_image_map (K := K) (F := F) (K' := K') (F' := F') hfg hfg' hgen P
  have hVeq : V = P' := Submodule.eq_of_le_of_finrank_eq hVle (by rw [hVdim, hdim])
  exact hVeq.symm.le

end Key

end AlgebraicCurve.A2SupBody

open AlgebraicCurve.A2SupBody in
theorem solution
    (K F K' F' : Type*)
    [Field K] [Field F] [Field K'] [Field F'] [Algebra K F] [Algebra K' F']
    [Algebra K K'] [Algebra F F'] [Algebra K F'] [IsScalarTower K K' F'] [IsScalarTower K F F'] [SMulCommClass K' F F']
    [IsAlgClosed K] [IsAlgClosed K'] [IsCurveOver K F] [IsCurveOver K' F']
    [Algebra.EssFiniteType K F] [Algebra.EssFiniteType K' F']
    (hfg : ∃ x : F, Transcendental K x ∧ FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F)
    (hfg' : ∃ x : F', Transcendental K' x ∧
      FiniteDimensional (IntermediateField.adjoin K' ({x} : Set F')) F')
    (hgen : IntermediateField.adjoin K' (Set.range (algebraMap F F')) = ⊤)
    (hdK : ∀ v : Place K F, v.DCoordGenerates) (hdK' : ∀ w : Place K' F', w.DCoordGenerates)
    (S : Set (Place K F)) :
    ∀ η ∈ polarDifferentials K' F'
          {w : Place K' F' | ∃ v ∈ S, w.toValuationSubring.comap (algebraMap F F') = v.toValuationSubring},
        η ∈ Submodule.span K'
          (KaehlerDifferential.map K K' F F' '' (polarDifferentials K F S : Set (Ω[F⁄K]))) := by
  intro η hη
  classical
  haveI : ∀ v : Place K F, v.DCoordGenerates := hdK
  haveI : ∀ w : Place K' F', w.DCoordGenerates := hdK'
  haveI : HasCanonicalDivisor (K := K') (F := F') := hasCanonicalDivisor_of_isCurveOver

  choose lift hlift hlift_ord huniq' using fun P : Place K F =>
    AlgebraicCurve.Place.exists_comap_algebraMap_eq_of_constantFieldExtension_of_isAlgClosed K F K' F' hfg hfg' hgen P
  have huniq : ∀ (v : Place K F) (w : Place K' F'),
      w.toValuationSubring.comap (algebraMap F F') = v.toValuationSubring → w = lift v :=
    fun v w h => huniq' v w h
  have hlift_inj : Function.Injective lift := by
    intro v₁ v₂ h
    apply Place.ext
    rw [← hlift v₁, ← hlift v₂, h]

  have hN : {w : Place K' F' | ¬ w.IsRegularAt η}.Finite := finite_setOf_not_isRegularAt η
  have hTfin : {v : Place K F | v ∈ S ∧ ¬ (lift v).IsRegularAt η}.Finite := by
    apply Set.Finite.subset (hN.preimage hlift_inj.injOn)
    intro v hv
    exact hv.2
  set T : Finset (Place K F) := hTfin.toFinset with hTdef
  have hTS : (T : Set (Place K F)) ⊆ S := by
    intro v hv
    rw [hTdef, Set.Finite.coe_toFinset] at hv
    exact hv.1

  have hηT : η ∈ polarDifferentials K' F'
      {w : Place K' F' | ∃ v ∈ (T : Set (Place K F)), w.toValuationSubring.comap (algebraMap F F') = v.toValuationSubring} := by
    intro w
    constructor
    · intro hw
      by_contra hreg
      apply hw
      have hwS : w ∈ {w : Place K' F' | ∃ v ∈ S, w.toValuationSubring.comap (algebraMap F F') = v.toValuationSubring} := by
        by_contra hwS
        exact hreg ((hη w).1 hwS)
      obtain ⟨v, hvS, hv⟩ := hwS
      have hwv : w = lift v := huniq v w hv
      refine ⟨v, ?_, hv⟩
      rw [hTdef, Set.Finite.coe_toFinset]
      exact ⟨hvS, hwv ▸ hreg⟩
    · rintro ⟨v, hvT, hv⟩
      exact (hη w).2 ⟨v, hTS hvT, hv⟩

  have hmem := polarDifferentials_le_span_map_of_finset (K := K) (F := F) (K' := K') (F' := F')
    hfg hfg' hgen hdK hdK' lift hlift huniq T hηT
  refine Submodule.span_mono ?_ hmem
  exact Set.image_mono (polarDifferentials_mono hTS)

#print axioms solution

end S_AlgebraicCurve_mem_span_image_polarDifferentials_of_constantFieldExtension_of_isAlgClosed
end P2MW
export P2MW.S_AlgebraicCurve_mem_span_image_polarDifferentials_of_constantFieldExtension_of_isAlgClosed (solution)
