-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.TwoAffineOpenCover.serrePairingInt_bijective_and_flip_bijective_of_isSectional_of_isCompletionAlong_of_perfectField
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.122355+00:00
-- url     : https://prove2.me/submissions/e02eb2e3-4412-530c-8448-b9f1f61356aa

import Mathlib
import Definitions.Def_AlgebraicGeometry_TwoChartCechSerrePairingInt
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCoverSectional
import Definitions.Def_AlgebraicCurve_KaehlerToFunctionField
import Definitions.Def_AlgebraicCurve_SerrePairing
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_CanonicalDivisor
import Definitions.Def_AlgebraicCurve_CanonicalLocalResidueInstanceV2
import Definitions.Def_AlgebraicCurve_PlacesOf
import Theorems.Thm_AlgebraicCurve_serrePairing_bijective_and_flip_bijective
import Theorems.Thm_AlgebraicGeometry_Scheme_TwoAffineOpenCover_exists_serrePairingInt_eq_serrePairing_of_isCompletionAlong
import Theorems.Thm_AlgebraicGeometry_Scheme_TwoAffineOpenCover_exists_linearEquiv_kaehlerSectionsH0_regularDifferentials_apply_eq_kaehlerToFunctionField
import Theorems.Thm_AlgebraicCurve_exists_linearEquiv_structureSheafH1_cechH1
import Theorems.Thm_AlgebraicCurve_exists_linearEquiv_cechH1_swap
import Theorems.Thm_AlgebraicCurve_exists_embedding_place_range_eq_compl_placesOf_of_isSectional
import Theorems.Thm_AlgebraicCurve_isCurveOver_of_ringEquiv_functionField_of_isIntegral_of_smoothOfRelativeDimension_one
import Theorems.Thm_AlgebraicCurve_essFiniteType_functionField
import Theorems.Thm_AlgebraicCurve_hasCanonicalDivisor_of_isCurveOver
import Theorems.Thm_AlgebraicCurve_dCoordGenerates_of_isCurveOver
import Theorems.Thm_AlgebraicCurve_constantsAreBase_of_exists_isRational
import Theorems.Thm_AlgebraicCurve_Place_isRational_iff_deg_eq_one
import Theorems.Thm_AlgebraicGeometry_not_isAffine_of_isProper_of_smoothOfRelativeDimension_one
import Theorems.Thm_AlgebraicCurve_placesOf_union_eq_univ_of_sup_eq_top
import Theorems.Thm_AlgebraicCurve_Place_isRational_of_range_stalk_section_eq
import Theorems.Thm_AlgebraicCurve_residueTheorem_functionField_of_smoothOfRelativeDimension_one
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_serrePairingInt_bijective_and_flip_bijective_of_isSectional_of_isCompletionAlong_of_perfectField
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupDivisor AlgebraicCurve.Pic0.instModuleZModTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instDistribMulActionTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instSMulTorsion AlgebraicCurve.SemilinearAut.instMulActionSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instSMulCommClassZModTorsion AlgebraicCurve.SemilinearAut.instMulSemiringActionSubtypeProdRingAutMemSubgroup instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt"
p2m_attr_erase "simp" "AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.SemilinearAut.toRingAut_inv AlgebraicCurve.SemilinearAut.smul_def AlgebraicCurve.SemilinearAut.smul_single AlgebraicCurve.SemilinearAut.smul_toValuationSubring AlgebraicCurve.SemilinearAut.baseAut_inv AlgebraicCurve.SemilinearAut.baseAut_ofAlgAut AlgebraicCurve.SemilinearAut.toRingAut_ofAlgAut AlgebraicCurve.SemilinearAut.torsionRep_apply AlgebraicCurve.SemilinearAut.toRingAut_one"
p2m_attr_erase "simp" "AlgebraicCurve.SemilinearAut.deg_smul AlgebraicCurve.SemilinearAut.degree_smul AlgebraicCurve.SemilinearAut.coe_degZeroSMulHom AlgebraicCurve.SemilinearAut.baseAut_mul AlgebraicCurve.SemilinearAut.coe_smulValuationSubringEquiv_apply AlgebraicCurve.SemilinearAut.baseAut_one AlgebraicCurve.SemilinearAut.ofAlgAut_smul AlgebraicCurve.SemilinearAut.coe_torsion_smul AlgebraicCurve.SemilinearAut.toRingAut_mul AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.jqNModC_one ModularCurve.qExpand_coeff_mul ModularCurve.qExpandₐ_apply ModularCurve.jqN_one ModularCurve.qExpand_single ModularCurve.dedekindPsi_one ModularCurve.ModularPolynomialData.mk.sizeOf_spec ModularCurve.evalAtJ_X ModularCurve.ModularPolynomialData.mk.injEq ModularCurve.constantCoeff_jNum ModularCurve.constantCoeff_eisenstein4 ModularCurve.qExpand_C ModularCurve.coeff_jq_neg_one ModularCurve.constantCoeff_jNumQ ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty"
p2m_attr_erase "simp" "AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal"

set_option autoImplicit false
set_option linter.unusedSectionVars false

universe u v

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace C4Skel

variable {k : Type u} [Field k] [PerfectField k] {X : Scheme.{u}} [IsIntegral X]
  (𝒱 : X.TwoAffineOpenCover) (c : X ⟶ Spec (.of k)) [IsProper c] [SmoothOfRelativeDimension 1 c]

theorem isAffine_of_isAffineOpen_top {Y : Scheme.{u}} (h : IsAffineOpen (⊤ : Y.Opens)) : IsAffine Y :=
  haveI : IsAffine (⊤ : Y.Opens) := h
  IsAffine.of_isIso Y.topIso.inv

theorem U0_ne_top (c : X ⟶ Spec (.of k)) [IsProper c] [SmoothOfRelativeDimension 1 c] : 𝒱.U0 ≠ ⊤ := fun h =>
  not_isAffine_of_isProper_of_smoothOfRelativeDimension_one c (isAffine_of_isAffineOpen_top (h ▸ 𝒱.isAffineOpen_U0))

theorem U1_ne_top (c : X ⟶ Spec (.of k)) [IsProper c] [SmoothOfRelativeDimension 1 c] : 𝒱.U1 ≠ ⊤ := fun h =>
  not_isAffine_of_isProper_of_smoothOfRelativeDimension_one c (isAffine_of_isAffineOpen_top (h ▸ 𝒱.isAffineOpen_U1))

theorem nonempty_U1 (c : X ⟶ Spec (.of k)) [IsProper c] [SmoothOfRelativeDimension 1 c] : Nonempty 𝒱.U1 := by
  by_contra h
  have hbot : 𝒱.U1 = ⊥ := by
    ext x; simp only [TopologicalSpace.Opens.coe_bot, Set.mem_empty_iff_false, iff_false]
    exact fun hx => h ⟨⟨x, hx⟩⟩
  have := 𝒱.sup_eq_top
  rw [hbot, sup_bot_eq] at this
  exact U0_ne_top 𝒱 c this

theorem bijective_and_flip_of_eq {K : Type*} [Field K] {V W V' W' : Type*}
    [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W] [AddCommGroup V'] [Module K V'] [AddCommGroup W'] [Module K W']
    (B : V →ₗ[K] W →ₗ[K] K) (B' : V' →ₗ[K] W' →ₗ[K] K) (eV : V ≃ₗ[K] V') (eW : W ≃ₗ[K] W')
    (h : ∀ v w, B v w = B' (eV v) (eW w)) (hB' : Function.Bijective B' ∧ Function.Bijective B'.flip) :
    Function.Bijective B ∧ Function.Bijective B.flip := by

  have hB : (B : V → (W →ₗ[K] K)) = (fun φ : W' →ₗ[K] K => φ.comp eW.toLinearMap) ∘ B' ∘ eV := by
    funext v; apply LinearMap.ext; intro w; exact h v w
  have hBf : (B.flip : W → (V →ₗ[K] K)) = (fun φ : V' →ₗ[K] K => φ.comp eV.toLinearMap) ∘ B'.flip ∘ eW := by
    funext w; apply LinearMap.ext; intro v; exact h v w
  have hpreW : Function.Bijective (fun φ : W' →ₗ[K] K => φ.comp eW.toLinearMap) :=
    (LinearEquiv.congrLeft K K eW.symm).bijective
  have hpreV : Function.Bijective (fun φ : V' →ₗ[K] K => φ.comp eV.toLinearMap) :=
    (LinearEquiv.congrLeft K K eV.symm).bijective
  refine ⟨?_, ?_⟩
  · rw [hB]; exact hpreW.comp (hB'.1.comp eV.bijective)
  · rw [hBf]; exact hpreV.comp (hB'.2.comp eW.bijective)

theorem linearMap_eq_of_forall_mk {K : Type*} [Field K] {M N : Type*} [AddCommGroup M] [Module K M] [AddCommGroup N] [Module K N]
    (p : Submodule K M) (f g : (M ⧸ p) →ₗ[K] N) (h : ∀ m : M, f (Submodule.Quotient.mk m) = g (Submodule.Quotient.mk m)) :
    f = g :=
  LinearMap.ext fun x => by obtain ⟨m, rfl⟩ := Submodule.Quotient.mk_surjective p x; exact h m

theorem nonempty_index {ι : Type v} (σ : ι → (Spec (.of k) ⟶ X)) (hσ : 𝒱.IsSectional c σ) : Nonempty ι := by
  by_contra hι
  rw [not_nonempty_iff] at hι
  have hU1 : (𝒱.U1 : Set X) = Set.univ := by
    have := hσ.compl_eq_iUnion
    rw [Set.iUnion_of_empty, Set.compl_empty_iff] at this
    exact this
  exact U1_ne_top 𝒱 c (TopologicalSpace.Opens.ext hU1)

theorem assembly
    {ι : Type v} [Fintype ι] (σ : ι → (Spec (.of k) ⟶ X)) (hσ : 𝒱.IsSectional c σ)
    (Λ : ι → (𝒱.cover c).LaurentChart)
    (hΛ : ∀ i, (Λ i).IsCompletionAlong (𝒱.cover c).ρ0
      (Scheme.TwoAffineOpenCover.sectionAlgHom (σ i) (hσ.comp_eq i) (hσ.range_subset i)))
    (hΛt : ∀ i, (Λ i).HasParameter (𝒱.cover c).ρ0)
    (hv : (𝒱.cover c).ResiduesVanishOnCoboundaries Λ) :
    Function.Bijective ((𝒱.cover c).serrePairingInt Λ hv) ∧
      Function.Bijective ((𝒱.cover c).serrePairingInt Λ hv).flip := by
  classical
  letI := (AlgebraicCurve.baseToFunctionField c).toAlgebra

  haveI : AlgebraicCurve.IsCurveOver k X.functionField :=
    AlgebraicCurve.isCurveOver_of_ringEquiv_functionField_of_isIntegral_of_smoothOfRelativeDimension_one c
      (RingEquiv.refl _) (fun _ => rfl)
  haveI : Algebra.EssFiniteType k X.functionField := AlgebraicCurve.essFiniteType_functionField c
  haveI : AlgebraicCurve.HasCanonicalDivisor (K := k) (F := X.functionField) :=
    AlgebraicCurve.hasCanonicalDivisor_of_isCurveOver
  haveI : ∀ v : AlgebraicCurve.Place k X.functionField, v.DCoordGenerates := AlgebraicCurve.dCoordGenerates_of_isCurveOver
  have hRT : AlgebraicCurve.ResidueTheorem k X.functionField :=
    @AlgebraicCurve.residueTheorem_functionField_of_smoothOfRelativeDimension_one k _ _ X c _ _ _ _ _

  obtain ⟨_, hW, hgerm, e1, he1, eΩ, _, heΩ, hpair⟩ :=
    Scheme.TwoAffineOpenCover.exists_serrePairingInt_eq_serrePairing_of_isCompletionAlong 𝒱 c σ hσ Λ hv hΛ hΛt hRT

  haveI hι : Nonempty ι := nonempty_index 𝒱 c σ hσ
  obtain ⟨i₀⟩ := hι
  haveI : Nonempty 𝒱.U0 := ⟨⟨(σ i₀).base (IsLocalRing.closedPoint k), hσ.range_subset i₀ ⟨_, rfl⟩⟩⟩
  haveI : Nonempty 𝒱.U1 := nonempty_U1 𝒱 c

  obtain ⟨eΩ', heΩ'⟩ :=
    Scheme.TwoAffineOpenCover.exists_linearEquiv_kaehlerSectionsH0_regularDifferentials_apply_eq_kaehlerToFunctionField 𝒱 c
  have heq : (eΩ : _ → _) = eΩ' := funext fun ω => Subtype.ext ((heΩ ω).trans (heΩ' ω).symm)

  obtain ⟨hmem, e, he⟩ := AlgebraicCurve.exists_linearEquiv_structureSheafH1_cechH1 𝒱 c ‹Nonempty 𝒱.U0› ‹Nonempty 𝒱.U1›
  obtain ⟨sw, hsw⟩ := AlgebraicCurve.exists_linearEquiv_cechH1_swap
    (AlgebraicCurve.placesOf c 𝒱.U0) (AlgebraicCurve.placesOf c 𝒱.U1) (0 : AlgebraicCurve.Divisor k X.functionField)
  have he1eq : e1 = (e.trans sw).toLinearMap := by
    refine linearMap_eq_of_forall_mk _ _ _ fun s => ?_
    rw [he1 s, LinearEquiv.coe_coe, LinearEquiv.trans_apply, he s (hmem s), hsw]

  obtain ⟨p, hp, hstalk⟩ := AlgebraicCurve.exists_embedding_place_range_eq_compl_placesOf_of_isSectional 𝒱 c σ hσ
  have hrat : (p i₀).IsRational :=
    AlgebraicCurve.Place.isRational_of_range_stalk_section_eq c (σ i₀) (hσ.comp_eq i₀) (p i₀) (hstalk i₀)
  have hC : AlgebraicCurve.ConstantsAreBase k X.functionField :=
    AlgebraicCurve.constantsAreBase_of_exists_isRational (p i₀) hrat
      (by rw [(AlgebraicCurve.Place.isRational_iff_deg_eq_one _).mp hrat]; exact one_ne_zero)
  have h₀ : ∃ v : AlgebraicCurve.Place k X.functionField, v ∉ AlgebraicCurve.placesOf c 𝒱.U1 :=
    ⟨p i₀, by rw [← Set.mem_compl_iff, ← hp]; exact ⟨i₀, rfl⟩⟩
  have h₁ : ∃ v : AlgebraicCurve.Place k X.functionField, v ∉ AlgebraicCurve.placesOf c 𝒱.U0 :=
    (AlgebraicCurve.placesOf_union_eq_univ_of_sup_eq_top c 𝒱.U1 𝒱.U0
      (by rw [sup_comm]; exact 𝒱.sup_eq_top) (U1_ne_top 𝒱 c) (U0_ne_top 𝒱 c)).2.2

  have hS1 := AlgebraicCurve.serrePairing_bijective_and_flip_bijective hC hRT hW h₀ h₁
  exact bijective_and_flip_of_eq _ _ (LinearEquiv.ofBijective eΩ (by rw [heq]; exact eΩ'.bijective))
    (LinearEquiv.ofBijective e1 (by rw [he1eq]; exact (e.trans sw).bijective)) (fun ω x => hpair ω x) hS1

end C4Skel

theorem solution
    {k : Type u} [Field k] [PerfectField k] {X : Scheme.{u}} [IsIntegral X]
    (𝒱 : X.TwoAffineOpenCover) (c : X ⟶ Spec (.of k)) [IsProper c] [SmoothOfRelativeDimension 1 c]
    {ι : Type v} [Fintype ι] (σ : ι → (Spec (.of k) ⟶ X)) (hσ : 𝒱.IsSectional c σ)
    (Λ : ι → (𝒱.cover c).LaurentChart)
    (hΛ : ∀ i, (Λ i).IsCompletionAlong (𝒱.cover c).ρ0
      (Scheme.TwoAffineOpenCover.sectionAlgHom (σ i) (hσ.comp_eq i) (hσ.range_subset i)))
    (hΛt : ∀ i, (Λ i).HasParameter (𝒱.cover c).ρ0)
    (hv : (𝒱.cover c).ResiduesVanishOnCoboundaries Λ) :
    Function.Bijective ((𝒱.cover c).serrePairingInt Λ hv) ∧
      Function.Bijective ((𝒱.cover c).serrePairingInt Λ hv).flip := by
  exact C4Skel.assembly 𝒱 c σ hσ Λ hΛ hΛt hv

end S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_serrePairingInt_bijective_and_flip_bijective_of_isSectional_of_isCompletionAlong_of_perfectField
end P2MW
export P2MW.S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_serrePairingInt_bijective_and_flip_bijective_of_isSectional_of_isCompletionAlong_of_perfectField (solution)
