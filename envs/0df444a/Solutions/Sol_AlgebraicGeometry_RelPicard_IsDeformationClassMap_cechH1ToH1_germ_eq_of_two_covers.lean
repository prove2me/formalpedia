-- Prove2me | solution 1 for AlgebraicGeometry.RelPicard.IsDeformationClassMap.cechH1ToH1_germ_eq_of_two_covers
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:03.589526+00:00
-- url     : https://prove2.me/submissions/6381a8d1-4723-5bd5-b069-c6e4b3da694c

import Mathlib
import Definitions.Def_AlgebraicGeometry_RigKerDualNumber
import Definitions.Def_AlgebraicGeometry_PicDualNumberDeformationClassSpec
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCoverH1BaseChange
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import Definitions.Def_AlgebraicGeometry_TwoChartCech
import Definitions.Def_AlgebraicCurve_CechSectionsOfDivisor
import Definitions.Def_AlgebraicCurve_PlacesOf
import Theorems.Thm_AlgebraicGeometry_RelPicard_IsDeformationClassMap_exists_crossSections
import Theorems.Thm_AlgebraicCurve_cechH1ToH1_mk_eq_cechH1ToH1_mk_of_crossSections
import Theorems.Thm_AlgebraicCurve_germToFunctionField_inf_mem_lSpaceOn_inter_placesOf
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_RelPicard_IsDeformationClassMap_cechH1ToH1_germ_eq_of_two_covers
p2m_attr_erase "instance" "AlgebraicGeometry.SmoothOfRelativeDimension.fiberToSpecResidueField AlgebraicGeometry.SmoothOfRelativeDimension.pullback_snd AlgebraicGeometry.SmoothOfRelativeDimension.pullback_fst AlgebraicGeometry.SmoothOfRelativeDimension.smooth_one AlgebraicGeometry.SmoothProperCurve.isIntegral_pullback_Spec_field AlgebraicGeometry.IsProper.fiberToSpecResidueField SheafOfModules.isIso_ihomModelToIhom AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation"
p2m_attr_erase "simp" "AlgebraicGeometry.RelPicard.BaseChange.relSubPicPresheafRestrictIso_hom_app_coe AlgebraicGeometry.RelPicard.BaseChange.relSubPicPresheafRestrictIso_inv_app_coe AlgebraicGeometry.RelPicard.BaseChange.restrict_P AlgebraicGeometry.SmoothProperCurve.sectionBaseChange_coe_snd AlgebraicGeometry.SmoothProperCurve.sectionBaseChange_coe_fst PresheafOfModules.InternalHom.IsSheafAux.appAt_toPresheafHom SheafOfModules.ihomSectionsEquivFamily_unit AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_apply SheafOfModules.ihomEval_unit_app AlgebraicGeometry.Scheme.Modules.ihomEval_zero_right AlgebraicGeometry.Scheme.Modules.ihomEval_zero_left AlgebraicGeometry.Scheme.Modules.homOfFamily_app_apply SheafOfModules.unit_ihomSectionsEquivFamily AlgebraicGeometry.Scheme.Modules.familyOfHom_app AlgebraicGeometry.Scheme.Modules.restrictUnitIso_hom_app_apply AlgebraicGeometry.Scheme.Modules.restrictUnitIso_inv_app_apply AlgebraicGeometry.Scheme.Modules.restrictHomOfFamily_app_apply AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_symm_apply AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_neg AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_zero AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_sub AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_add AlgebraicGeometry.tilde.functorCompPullbackSpecIso_app AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint"

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.RelPicard NeronModelInfra AlgebraicGeometry.Scheme.TwoAffineOpenCover

namespace CoverGlue

theorem nonempty_inf {X : Scheme.{u}} [IrreducibleSpace X] (U V : X.Opens) [hU : Nonempty U] [hV : Nonempty V] :
    Nonempty (U ⊓ V : X.Opens) :=
  (nonempty_preirreducible_inter U.isOpen V.isOpen (Set.nonempty_coe_sort.mp hU)
    (Set.nonempty_coe_sort.mp hV)).to_subtype

theorem nonempty_of_nonempty_inf_left {X : Scheme.{u}} (U V : X.Opens) [h : Nonempty (U ⊓ V : X.Opens)] :
    Nonempty U := by
  obtain ⟨⟨x, hx⟩⟩ := h
  exact ⟨⟨x, hx.1⟩⟩

theorem nonempty_of_nonempty_inf_right {X : Scheme.{u}} (U V : X.Opens) [h : Nonempty (U ⊓ V : X.Opens)] :
    Nonempty V := by
  obtain ⟨⟨x, hx⟩⟩ := h
  exact ⟨⟨x, hx.2⟩⟩

theorem germToFunctionField_map {X : Scheme.{u}} [IrreducibleSpace X] {U V : X.Opens} [Nonempty U] [Nonempty V]
    (h : V ≤ U) (s : Γ(X, U)) :
    (X.germToFunctionField V).hom ((X.presheaf.map (homOfLE h).op).hom s)
      = (X.germToFunctionField U).hom s := by
  rw [← CategoryTheory.ConcreteCategory.comp_apply]
  erw [TopCat.Presheaf.germ_res]
  try rfl

end CoverGlue

open CoverGlue in
theorem solution
    {R : Type u} [CommRing R] {C : Scheme.{u}} (c : C ⟶ Spec (.of R)) (ε : SchemeHomOver (𝟙 (Spec (.of R))) c)
    (K : Type u) [Field K] [Algebra R K]
    [IsIntegral (Limits.pullback c (Scheme.TwoAffineOpenCover.specMap R K))]
    [IsSeparated (pullback.snd c (Scheme.TwoAffineOpenCover.specMap R K))]
    [SmoothOfRelativeDimension 1 (pullback.snd c (Scheme.TwoAffineOpenCover.specMap R K))]
    (𝒲 𝒲' : C.TwoAffineOpenCover)
    {δ  : RigKerDualNumber c ε K → H1StructureSheaf c K 𝒲}
    {δ' : RigKerDualNumber c ε K → H1StructureSheaf c K 𝒲'}
    (hδ : IsDeformationClassMap c ε K 𝒲 δ) (hδ' : IsDeformationClassMap c ε K 𝒲' δ')
    (x : RigKerDualNumber c ε K)
    (s  : ((𝒲.pullback c K).cover  (pullback.snd c (Scheme.TwoAffineOpenCover.specMap R K))).A01)
    (s' : ((𝒲'.pullback c K).cover (pullback.snd c (Scheme.TwoAffineOpenCover.specMap R K))).A01)
    (hs : δ x = Submodule.Quotient.mk s) (hs' : δ' x = Submodule.Quotient.mk s') :
    letI X' := Limits.pullback c (Scheme.TwoAffineOpenCover.specMap R K)
    letI c' : X' ⟶ Spec (.of K) := pullback.snd c (Scheme.TwoAffineOpenCover.specMap R K)
    letI := (AlgebraicCurve.baseToFunctionField c').toAlgebra
    letI W := 𝒲.pullback c K; letI W' := 𝒲'.pullback c K
    ∀ [Nonempty (W.U0 ⊓ W.U1 : X'.Opens)] [Nonempty (W'.U0 ⊓ W'.U1 : X'.Opens)]
      (hW  : AlgebraicCurve.placesOf c' W.U0  ∪ AlgebraicCurve.placesOf c' W.U1  = Set.univ)
      (hW' : AlgebraicCurve.placesOf c' W'.U0 ∪ AlgebraicCurve.placesOf c' W'.U1 = Set.univ)
      (hsr  : (X'.germToFunctionField (W.U0 ⊓ W.U1)).hom s ∈
        AlgebraicCurve.lSpaceOn (AlgebraicCurve.placesOf c' W.U0 ∩ AlgebraicCurve.placesOf c' W.U1)
          (0 : AlgebraicCurve.Divisor K X'.functionField))
      (hsr' : (X'.germToFunctionField (W'.U0 ⊓ W'.U1)).hom s' ∈
        AlgebraicCurve.lSpaceOn (AlgebraicCurve.placesOf c' W'.U0 ∩ AlgebraicCurve.placesOf c' W'.U1)
          (0 : AlgebraicCurve.Divisor K X'.functionField)),
      AlgebraicCurve.cechH1ToH1 hW 0
          (Submodule.Quotient.mk ⟨(X'.germToFunctionField (W.U0 ⊓ W.U1)).hom s, hsr⟩) =
        AlgebraicCurve.cechH1ToH1 hW' 0
          (Submodule.Quotient.mk ⟨(X'.germToFunctionField (W'.U0 ⊓ W'.U1)).hom s', hsr'⟩) := by
  intro hne hne' hW hW' hsr hsr'
  letI := (AlgebraicCurve.baseToFunctionField (pullback.snd c (Scheme.TwoAffineOpenCover.specMap R K))).toAlgebra

  haveI : Nonempty ((𝒲.pullback c K).U0 : (Limits.pullback c (Scheme.TwoAffineOpenCover.specMap R K)).Opens) :=
    nonempty_of_nonempty_inf_left _ (𝒲.pullback c K).U1
  haveI : Nonempty ((𝒲.pullback c K).U1 : (Limits.pullback c (Scheme.TwoAffineOpenCover.specMap R K)).Opens) :=
    nonempty_of_nonempty_inf_right (𝒲.pullback c K).U0 _
  haveI : Nonempty ((𝒲'.pullback c K).U0 : (Limits.pullback c (Scheme.TwoAffineOpenCover.specMap R K)).Opens) :=
    nonempty_of_nonempty_inf_left _ (𝒲'.pullback c K).U1
  haveI : Nonempty ((𝒲'.pullback c K).U1 : (Limits.pullback c (Scheme.TwoAffineOpenCover.specMap R K)).Opens) :=
    nonempty_of_nonempty_inf_right (𝒲'.pullback c K).U0 _
  haveI : Nonempty ((𝒲.pullback c K).U0 ⊓ (𝒲'.pullback c K).U0 :
      (Limits.pullback c (Scheme.TwoAffineOpenCover.specMap R K)).Opens) := nonempty_inf _ _
  haveI : Nonempty ((𝒲.pullback c K).U0 ⊓ (𝒲'.pullback c K).U1 :
      (Limits.pullback c (Scheme.TwoAffineOpenCover.specMap R K)).Opens) := nonempty_inf _ _
  haveI : Nonempty ((𝒲.pullback c K).U1 ⊓ (𝒲'.pullback c K).U0 :
      (Limits.pullback c (Scheme.TwoAffineOpenCover.specMap R K)).Opens) := nonempty_inf _ _
  haveI : Nonempty ((𝒲.pullback c K).U1 ⊓ (𝒲'.pullback c K).U1 :
      (Limits.pullback c (Scheme.TwoAffineOpenCover.specMap R K)).Opens) := nonempty_inf _ _
  haveI : Nonempty (((𝒲.pullback c K).U0 ⊓ (𝒲.pullback c K).U1) ⊓ (𝒲'.pullback c K).U0 :
      (Limits.pullback c (Scheme.TwoAffineOpenCover.specMap R K)).Opens) := nonempty_inf _ _
  haveI : Nonempty (((𝒲.pullback c K).U0 ⊓ (𝒲.pullback c K).U1) ⊓ (𝒲'.pullback c K).U1 :
      (Limits.pullback c (Scheme.TwoAffineOpenCover.specMap R K)).Opens) := nonempty_inf _ _
  haveI : Nonempty ((𝒲.pullback c K).U0 ⊓ ((𝒲'.pullback c K).U0 ⊓ (𝒲'.pullback c K).U1) :
      (Limits.pullback c (Scheme.TwoAffineOpenCover.specMap R K)).Opens) := nonempty_inf _ _
  haveI : Nonempty ((𝒲.pullback c K).U1 ⊓ ((𝒲'.pullback c K).U0 ⊓ (𝒲'.pullback c K).U1) :
      (Limits.pullback c (Scheme.TwoAffineOpenCover.specMap R K)).Opens) := nonempty_inf _ _

  obtain ⟨g00, g01, g10, g11, h1, h2, h3, -⟩ :=
    IsDeformationClassMap.exists_crossSections c ε K 𝒲 𝒲' hδ hδ' x s s' hs hs'

  have m00 := AlgebraicCurve.germToFunctionField_inf_mem_lSpaceOn_inter_placesOf
    (pullback.snd c (Scheme.TwoAffineOpenCover.specMap R K)) (𝒲.pullback c K).U0 (𝒲'.pullback c K).U0 g00
  have m01 := AlgebraicCurve.germToFunctionField_inf_mem_lSpaceOn_inter_placesOf
    (pullback.snd c (Scheme.TwoAffineOpenCover.specMap R K)) (𝒲.pullback c K).U0 (𝒲'.pullback c K).U1 g01
  have m10 := AlgebraicCurve.germToFunctionField_inf_mem_lSpaceOn_inter_placesOf
    (pullback.snd c (Scheme.TwoAffineOpenCover.specMap R K)) (𝒲.pullback c K).U1 (𝒲'.pullback c K).U0 g10
  have m11 := AlgebraicCurve.germToFunctionField_inf_mem_lSpaceOn_inter_placesOf
    (pullback.snd c (Scheme.TwoAffineOpenCover.specMap R K)) (𝒲.pullback c K).U1 (𝒲'.pullback c K).U1 g11

  have e1 := congrArg ((Limits.pullback c (Scheme.TwoAffineOpenCover.specMap R K)).germToFunctionField
    (((𝒲.pullback c K).U0 ⊓ (𝒲.pullback c K).U1) ⊓ (𝒲'.pullback c K).U0)).hom h1
  have e2 := congrArg ((Limits.pullback c (Scheme.TwoAffineOpenCover.specMap R K)).germToFunctionField
    (((𝒲.pullback c K).U0 ⊓ (𝒲.pullback c K).U1) ⊓ (𝒲'.pullback c K).U1)).hom h2
  have e3 := congrArg ((Limits.pullback c (Scheme.TwoAffineOpenCover.specMap R K)).germToFunctionField
    ((𝒲.pullback c K).U0 ⊓ ((𝒲'.pullback c K).U0 ⊓ (𝒲'.pullback c K).U1))).hom h3
  simp only [map_add, germToFunctionField_map] at e1 e2 e3
  exact AlgebraicCurve.cechH1ToH1_mk_eq_cechH1ToH1_mk_of_crossSections hW hW' ⟨_, hsr⟩ ⟨_, hsr'⟩ _ _ _ _
    m00 m01 m10 m11 e1 e2 e3

end S_AlgebraicGeometry_RelPicard_IsDeformationClassMap_cechH1ToH1_germ_eq_of_two_covers
end P2MW
export P2MW.S_AlgebraicGeometry_RelPicard_IsDeformationClassMap_cechH1ToH1_germ_eq_of_two_covers (solution)
