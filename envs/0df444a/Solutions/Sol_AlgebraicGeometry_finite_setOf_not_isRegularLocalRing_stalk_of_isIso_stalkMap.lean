-- Prove2me | solution 1 for AlgebraicGeometry.finite_setOf_not_isRegularLocalRing_stalk_of_isIso_stalkMap
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.553648+00:00
-- url     : https://prove2.me/submissions/285c77b6-4e66-5d45-b5db-4e71ae51b3a2

import Mathlib
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import Definitions.Def_AlgebraicGeometry_TwoChartCechSectionsOf
import Definitions.Def_AlgebraicCurve_CurveModel
import Definitions.Def_AlgebraicCurve_Repartitions
import Theorems.Thm_AlgebraicGeometry_IsClosedImmersion_isIso_stalkMap_of_mem_interior_range
import Theorems.Thm_AlgebraicGeometry_finite_setOf_not_isRegularLocalRing_stalk_of_isIso_stalkMap_of_isIntegral
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_finite_setOf_not_isRegularLocalRing_stalk_of_isIso_stalkMap
p2m_attr_erase "instance" "AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupDivisor AlgebraicCurve.Pic0.instModuleZModTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instDistribMulActionTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instSMulTorsion AlgebraicCurve.SemilinearAut.instMulActionSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instSMulCommClassZModTorsion AlgebraicCurve.SemilinearAut.instMulSemiringActionSubtypeProdRingAutMemSubgroup instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions"
p2m_attr_erase "simp" "AlgebraicCurve.coe_cechH0Equiv_apply AlgebraicCurve.cechH1ToH1_mk AlgebraicCurve.lSpaceOn_univ AlgebraicCurve.lSpaceOn_empty AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.Divisor.degree_pushforwardAlong"
p2m_attr_erase "simp" "AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.SemilinearAut.toRingAut_inv AlgebraicCurve.SemilinearAut.smul_def AlgebraicCurve.SemilinearAut.smul_single AlgebraicCurve.SemilinearAut.smul_toValuationSubring AlgebraicCurve.SemilinearAut.baseAut_inv AlgebraicCurve.SemilinearAut.baseAut_ofAlgAut AlgebraicCurve.SemilinearAut.toRingAut_ofAlgAut AlgebraicCurve.SemilinearAut.torsionRep_apply AlgebraicCurve.SemilinearAut.toRingAut_one AlgebraicCurve.SemilinearAut.deg_smul AlgebraicCurve.SemilinearAut.degree_smul AlgebraicCurve.SemilinearAut.coe_degZeroSMulHom AlgebraicCurve.SemilinearAut.baseAut_mul AlgebraicCurve.SemilinearAut.coe_smulValuationSubringEquiv_apply AlgebraicCurve.SemilinearAut.baseAut_one AlgebraicCurve.SemilinearAut.ofAlgAut_smul AlgebraicCurve.SemilinearAut.coe_torsion_smul AlgebraicCurve.SemilinearAut.toRingAut_mul AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.jqNModC_one ModularCurve.qExpand_coeff_mul ModularCurve.qExpandₐ_apply ModularCurve.jqN_one ModularCurve.qExpand_single ModularCurve.dedekindPsi_one ModularCurve.ModularPolynomialData.mk.sizeOf_spec ModularCurve.evalAtJ_X ModularCurve.ModularPolynomialData.mk.injEq ModularCurve.constantCoeff_jNum ModularCurve.constantCoeff_eisenstein4 ModularCurve.qExpand_C ModularCurve.coeff_jq_neg_one ModularCurve.constantCoeff_jNumQ ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single"
p2m_attr_erase "simp" "ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord"

set_option autoImplicit false

universe u v

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace

namespace SingFinAux

theorem isReduced_image {Y X : Scheme.{u}} (f : Y ⟶ X) [QuasiCompact f] [IsReduced Y] : IsReduced f.image := by
  let V : X.affineOpens → f.image.Opens := fun U => f.imageι ⁻¹ᵁ (U : X.Opens)
  have hV : TopologicalSpace.IsOpenCover V := by
    show (⨆ U : X.affineOpens, f.imageι ⁻¹ᵁ (U : X.Opens)) = ⊤
    rw [← Scheme.Hom.preimage_iSup, iSup_affineOpens_eq_top]; rfl
  haveI : ∀ U : X.affineOpens, IsReduced ((f.image.openCoverOfIsOpenCover V hV).X U) := fun U => by
    have hVa : IsAffineOpen (V U) := U.2.preimage f.imageι
    haveI : IsAffine ((f.image.openCoverOfIsOpenCover V hV).X U) := hVa
    haveI : _root_.IsReduced Γ((f.image.openCoverOfIsOpenCover V hV).X U, ⊤) :=
      isReduced_of_injective ((V U).topIso.hom ≫ f.toImage.app (V U)).hom
        ((f.toImage_app_injective U).comp (V U).topIso.commRingCatIsoToRingEquiv.injective)
    exact isReduced_of_isAffine_isReduced _
  exact IsReduced.of_openCover f.image (f.image.openCoverOfIsOpenCover V hV)

theorem isRegularLocalRing_stalk_iff_of_mem_interior_range {C X : Scheme.{u}} (i : C ⟶ X) [IsClosedImmersion i]
    [IsReduced X] (c : C) (hc : i c ∈ interior (Set.range i)) :
    IsRegularLocalRing (X.presheaf.stalk (i c)) ↔ IsRegularLocalRing (C.presheaf.stalk c) := by
  haveI := AlgebraicGeometry.IsClosedImmersion.isIso_stalkMap_of_mem_interior_range i c hc
  let e : X.presheaf.stalk (i c) ≃+* C.presheaf.stalk c := (asIso (i.stalkMap c)).commRingCatIsoToRingEquiv
  exact ⟨fun h => IsRegularLocalRing.of_ringEquiv e, fun h => IsRegularLocalRing.of_ringEquiv e.symm⟩

theorem isIso_stalkMap_of_comp {C X Y : Scheme.{u}} (f : Y ⟶ C) (g : C ⟶ X) [IsClosedImmersion g] (y : Y)
    (hc : IsIso ((f ≫ g).stalkMap y)) : IsIso (f.stalkMap y) := by
  haveI := hc
  have hbij : Function.Bijective ((f ≫ g).stalkMap y) := ConcreteCategory.bijective_of_isIso _
  rw [Scheme.Hom.stalkMap_comp] at hbij
  have hsurj : Function.Surjective (g.stalkMap (f y)) := g.stalkMap_surjective (f y)
  have hinj : Function.Injective (g.stalkMap (f y)) := by
    apply Function.Injective.of_comp (f := (f.stalkMap y))
    exact hbij.1
  haveI : IsIso (g.stalkMap (f y)) := (ConcreteCategory.isIso_iff_bijective _).mpr ⟨hinj, hsurj⟩
  haveI : IsIso (g.stalkMap (f y) ≫ f.stalkMap y) := by
    rw [← Scheme.Hom.stalkMap_comp]; exact hc
  exact IsIso.of_isIso_comp_left (g.stalkMap (f y)) (f.stalkMap y)

theorem setOf_not_isRegularLocalRing_subset {X C₁ C₂ : Scheme.{u}} [IsReduced X] (i₁ : C₁ ⟶ X) (i₂ : C₂ ⟶ X)
    [IsClosedImmersion i₁] [IsClosedImmersion i₂]
    (hcov : ∀ z : X, z ∈ Set.range i₁ ∨ z ∈ Set.range i₂) :
    {z : X | ¬ IsRegularLocalRing (X.presheaf.stalk z)} ⊆
      i₁ '' {c : C₁ | ¬ IsRegularLocalRing (C₁.presheaf.stalk c)} ∪
        i₂ '' {c : C₂ | ¬ IsRegularLocalRing (C₂.presheaf.stalk c)} ∪ (Set.range i₁ ∩ Set.range i₂) := by
  have hint₁ : ∀ z : X, z ∉ Set.range i₂ → z ∈ interior (Set.range i₁) := by
    intro z hz
    refine mem_interior.mpr ⟨(Set.range i₂)ᶜ, fun y hy => (hcov y).resolve_right hy,
      i₂.isClosedEmbedding.isClosed_range.isOpen_compl, hz⟩
  have hint₂ : ∀ z : X, z ∉ Set.range i₁ → z ∈ interior (Set.range i₂) := by
    intro z hz
    refine mem_interior.mpr ⟨(Set.range i₁)ᶜ, fun y hy => (hcov y).resolve_left hy,
      i₁.isClosedEmbedding.isClosed_range.isOpen_compl, hz⟩
  intro z hz
  by_cases h₁ : z ∈ Set.range i₁ <;> by_cases h₂ : z ∈ Set.range i₂
  · exact Or.inr ⟨h₁, h₂⟩
  · obtain ⟨c, rfl⟩ := h₁
    exact Or.inl (Or.inl ⟨c, fun hreg => hz ((isRegularLocalRing_stalk_iff_of_mem_interior_range i₁ c (hint₁ _ h₂)).mpr hreg), rfl⟩)
  · obtain ⟨c, rfl⟩ := h₂
    exact Or.inl (Or.inr ⟨c, fun hreg => hz ((isRegularLocalRing_stalk_iff_of_mem_interior_range i₂ c (hint₂ _ h₁)).mpr hreg), rfl⟩)
  · exact absurd (hcov z) (not_or.mpr ⟨h₁, h₂⟩)

end SingFinAux

theorem solution
    (k : Type u) [Field k] [IsAlgClosed k]
    {X : Scheme.{u}} (x : X ⟶ Spec (CommRingCat.of k)) [IsProper x] [IsReduced X]
    {F₁ F₂ : Type v} [Field F₁] [Algebra k F₁] [Field F₂] [Algebra k F₂]
    (M₁ : AlgebraicCurve.CurveModel k F₁) (M₂ : AlgebraicCurve.CurveModel k F₂)
    (ν₁ : M₁.C ⟶ X) (ν₂ : M₂.C ⟶ X) (hν₁ : ν₁ ≫ x = M₁.toBase) (hν₂ : ν₂ ≫ x = M₂.toBase)
    (hcover : Set.range ν₁.base ∪ Set.range ν₂.base = Set.univ)
    (hfin : (Set.range ν₁.base ∩ Set.range ν₂.base).Finite)
    (hbir₁ : IsIso (ν₁.stalkMap (genericPoint M₁.C)))
    (hbir₂ : IsIso (ν₂.stalkMap (genericPoint M₂.C)))
    :
    {z : X | ¬ IsRegularLocalRing (X.presheaf.stalk z)}.Finite := by
  classical

  haveI : IsProper ν₁ := by
    have : IsProper (ν₁ ≫ x) := hν₁ ▸ inferInstance
    exact IsProper.of_comp ν₁ x
  haveI : IsProper ν₂ := by
    have : IsProper (ν₂ ≫ x) := hν₂ ▸ inferInstance
    exact IsProper.of_comp ν₂ x

  let C₁ : Scheme.{u} := ν₁.image
  let C₂ : Scheme.{u} := ν₂.image
  let i₁ : C₁ ⟶ X := ν₁.imageι
  let i₂ : C₂ ⟶ X := ν₂.imageι
  let c₁ : C₁ ⟶ Spec (CommRingCat.of k) := i₁ ≫ x
  let c₂ : C₂ ⟶ Spec (CommRingCat.of k) := i₂ ≫ x
  let ν₁' : M₁.C ⟶ C₁ := ν₁.toImage
  let ν₂' : M₂.C ⟶ C₂ := ν₂.toImage
  have hfac₁ : ν₁' ≫ i₁ = ν₁ := ν₁.toImage_imageι
  have hfac₂ : ν₂' ≫ i₂ = ν₂ := ν₂.toImage_imageι
  haveI : Surjective ν₁' := inferInstance
  haveI : Surjective ν₂' := inferInstance
  haveI : IrreducibleSpace C₁ := ν₁'.surjective.irreducibleSpace ν₁'.continuous
  haveI : IrreducibleSpace C₂ := ν₂'.surjective.irreducibleSpace ν₂'.continuous
  haveI : IsReduced C₁ := SingFinAux.isReduced_image ν₁
  haveI : IsReduced C₂ := SingFinAux.isReduced_image ν₂
  haveI : IsIntegral C₁ := isIntegral_of_irreducibleSpace_of_isReduced C₁
  haveI : IsIntegral C₂ := isIntegral_of_irreducibleSpace_of_isReduced C₂
  haveI : IsProper c₁ := inferInstance
  haveI : IsProper c₂ := inferInstance
  have hbir₁' : IsIso (ν₁'.stalkMap (genericPoint M₁.C)) :=
    SingFinAux.isIso_stalkMap_of_comp ν₁' i₁ _ (by rw [hfac₁]; exact hbir₁)
  have hbir₂' : IsIso (ν₂'.stalkMap (genericPoint M₂.C)) :=
    SingFinAux.isIso_stalkMap_of_comp ν₂' i₂ _ (by rw [hfac₂]; exact hbir₂)

  have hF₁ := AlgebraicGeometry.finite_setOf_not_isRegularLocalRing_stalk_of_isIso_stalkMap_of_isIntegral k c₁ M₁ ν₁'
    (by rw [← Category.assoc, hfac₁, hν₁]) hbir₁'
  have hF₂ := AlgebraicGeometry.finite_setOf_not_isRegularLocalRing_stalk_of_isIso_stalkMap_of_isIntegral k c₂ M₂ ν₂'
    (by rw [← Category.assoc, hfac₂, hν₂]) hbir₂'

  have hrange : ∀ {C : Scheme.{u}} {Y : Scheme.{u}} (f : Y ⟶ C) (g : C ⟶ X), Function.Surjective f.base →
      Set.range (f ≫ g).base = Set.range g.base := by
    intro C Y f g hf
    ext z; constructor
    · rintro ⟨y, rfl⟩; exact ⟨f.base y, by rw [Scheme.Hom.comp_apply]⟩
    · rintro ⟨c, rfl⟩; obtain ⟨y, rfl⟩ := hf c; exact ⟨y, by rw [Scheme.Hom.comp_apply]⟩
  have hr₁ : Set.range ν₁.base = Set.range i₁.base := by
    rw [← hrange ν₁' i₁ ν₁'.surjective, hfac₁]
  have hr₂ : Set.range ν₂.base = Set.range i₂.base := by
    rw [← hrange ν₂' i₂ ν₂'.surjective, hfac₂]
  have hcov : ∀ z : X, z ∈ Set.range i₁.base ∨ z ∈ Set.range i₂.base := by
    intro z
    have hz : z ∈ Set.range ν₁.base ∪ Set.range ν₂.base := hcover ▸ Set.mem_univ z
    rcases hz with h | h
    · exact Or.inl (hr₁ ▸ h)
    · exact Or.inr (hr₂ ▸ h)

  have hsub := SingFinAux.setOf_not_isRegularLocalRing_subset i₁ i₂ hcov
  refine Set.Finite.subset ?_ hsub
  refine ((hF₁.image _).union (hF₂.image _)).union ?_
  rw [← hr₁, ← hr₂]
  exact hfin

end S_AlgebraicGeometry_finite_setOf_not_isRegularLocalRing_stalk_of_isIso_stalkMap
end P2MW
export P2MW.S_AlgebraicGeometry_finite_setOf_not_isRegularLocalRing_stalk_of_isIso_stalkMap (solution)
