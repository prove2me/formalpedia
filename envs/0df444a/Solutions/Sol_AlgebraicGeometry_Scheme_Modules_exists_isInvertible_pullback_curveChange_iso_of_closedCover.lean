-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.Modules.exists_isInvertible_pullback_curveChange_iso_of_closedCover
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:03.589526+00:00
-- url     : https://prove2.me/submissions/df09d25c-6952-5253-9449-0d40e406ec23

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RelPicardPullback
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_exists_isInvertible_pullback_iso_of_milnorSquare
import Theorems.Thm_AlgebraicGeometry_IsClosedImmersion_app_curveChange_injective_and_exists_of_app_eq_of_isReduced
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_isInvertible_pullback_curveChange_iso_of_closedCover
p2m_attr_erase "instance" "PresheafOfModules.instMonoidalClosed PresheafOfModules.InternalHom.instModuleCarrierObjOppositeCommRingCatSubtypePiFamilyMemAddSubgroupNaturalFamilies PresheafOfModules.InternalHom.instModuleCarrierObjOppositeRingCatCompCommRingCatForget₂RingHomCarrierCarrierAbPresheaf PresheafOfModules.InternalHom.instSMulCarrierObjOppositeCommRingCatSubtypePiFamilyMemAddSubgroupNaturalFamilies AlgebraicGeometry.Scheme.PresheafOfModules.symmetricCategory SheafOfModules.instFaithfulRingSheafPModToPMod SheafOfModules.symmetricCategory AlgebraicGeometry.Scheme.PresheafOfModules.monoidalCategory AlgebraicGeometry.Scheme.PresheafOfModules.monoidalClosed SheafOfModules.instFullRingSheafPModToPMod SheafOfModules.monoidalCategory AlgebraicGeometry.Scheme.Modules.symmetricCategory SheafOfModules.monoidalClosed SheafOfModules.instIsLocalizationPModRingSheafSheafifyFunctorPresheafW SheafOfModules.sheafifyFunctor_monoidal AlgebraicGeometry.Scheme.Modules.monoidalClosed AlgebraicGeometry.instMonoidalPresheafOfModulesModulesSheafify AlgebraicGeometry.Scheme.Modules.monoidalCategory PresheafOfModules.PullbackMonoidal.pullback_monoidal PresheafOfModules.PullbackMonoidal.isIso_δ PresheafOfModules.pushforward_laxMonoidal PresheafOfModules.PullbackMonoidal.isIso_η PresheafOfModules.free_monoidal PresheafOfModules.restrictScalars_laxMonoidal PresheafOfModules.PullbackMonoidal.isIso_δ_gS PresheafOfModules.pullback_oplaxMonoidal PresheafOfModules.PullbackMonoidal.instPreservesColimitsOfSizeCompOppositeCommRingCatRingCatForget₂RingHomCarrierCarrierPb PresheafOfModules.pullback_monoidal' AlgebraicGeometry.Scheme.Modules.preservesBinaryProducts_opensMap AlgebraicGeometry.Scheme.Modules.pullback_monoidal AlgebraicGeometry.Scheme.Modules.sheafify_isLocalization' AlgebraicGeometry.Scheme.Modules.preservesTerminal_opensMap AlgebraicGeometry.Scheme.Modules.pullback₀_monoidal AlgebraicGeometry.Scheme.Modules.preservesFiniteProducts_opensMap AlgebraicGeometry.Scheme.Modules.instLiftingPresheafOfModulesSheafifyPresheafWOpensCarrierCarrierCommRingCatGrothendieckTopologyObjFunctorOppositeIsSheafSheafCompPullback₀Pullback"
p2m_attr_erase "simp" "AlgebraicGeometry.Scheme.Modules.tensorSections_zero_right AlgebraicGeometry.Scheme.Modules.map_unitSection AlgebraicGeometry.Scheme.Modules.tensorSectionsBilin_apply AlgebraicGeometry.Scheme.Modules.tensorPowSection_zero AlgebraicGeometry.Scheme.Modules.tensorSections_zero_left PresheafOfModules.InternalHom.presheaf_map_apply PresheafOfModules.InternalHom.curryFamily_app PresheafOfModules.InternalHom.add_app PresheafOfModules.InternalHom.smul_app PresheafOfModules.InternalHom.zero_app PresheafOfModules.ihomObj_map_val PresheafOfModules.ihomFunctor_map PresheafOfModules.InternalHom.restrict_app PresheafOfModules.InternalHom.postcomp_app PresheafOfModules.InternalHom.neg_app PresheafOfModules.curry'_app_val PresheafOfModules.InternalHom.presheaf_obj PresheafOfModules.ihomFunctor_obj PresheafOfModules.ihomObj_obj PresheafOfModules.InternalHom.sub_app PresheafOfModules.ihomMap_app_val SheafOfModules.tensorUnit_eq AlgebraicGeometry.Scheme.Modules.tensorUnit_eq AlgebraicGeometry.Scheme.Modules.tensorPow_zero AlgebraicGeometry.Scheme.Modules.tensorPow_succ AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_neg AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_zero AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_sub AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_add PresheafOfModules.freeεIso_hom_app PresheafOfModules.freeμIso_hom_app"
set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian AlgebraicGeometry.RelPicard

namespace GTExists

theorem isClosedImmersion_curveChange {R : Type u} [CommRing R] {C C' T : Scheme.{u}}
    {c : C ⟶ Spec (CommRingCat.of R)} {c' : C' ⟶ Spec (CommRingCat.of R)} (f : C' ⟶ C) (hf : f ≫ c = c')
    (t : T ⟶ Spec (CommRingCat.of R)) [IsClosedImmersion f] : IsClosedImmersion (curveChange f hf t) := by
  have big : IsPullback (curveChange f hf t ≫ pullback.snd c t) (pullback.fst c' t) t (f ≫ c) := by
    rw [curveChange_snd, hf]
    exact (IsPullback.of_hasPullback c' t).flip
  have hcomm : curveChange f hf t ≫ pullback.fst c t = pullback.fst c' t ≫ f := by
    simp only [curveChange, pullback.lift_fst]
  have sq : IsPullback (curveChange f hf t) (pullback.fst c' t) (pullback.fst c t) f :=
    IsPullback.of_right big hcomm (IsPullback.of_hasPullback c t).flip
  exact MorphismProperty.of_isPullback (P := @IsClosedImmersion) sq.flip inferInstance

end GTExists

theorem solution
    {k : Type u} [Field k] {X Y₁ Y₂ Z : Scheme.{u}} (x : X ⟶ Spec (CommRingCat.of k)) (hXred : IsReduced X)
    (y₁ : Y₁ ⟶ Spec (CommRingCat.of k)) (y₂ : Y₂ ⟶ Spec (CommRingCat.of k)) (z : Z ⟶ Spec (CommRingCat.of k))
    (i₁ : SchemeHomOver y₁ x) (i₂ : SchemeHomOver y₂ x) [IsClosedImmersion i₁.1] [IsClosedImmersion i₂.1]
    (hjs : ∀ p : X, p ∈ Set.range i₁.1.base ∨ p ∈ Set.range i₂.1.base)
    (j₁ : SchemeHomOver z y₁) (j₂ : SchemeHomOver z y₂) (hZ : IsPullback j₁.1 j₂.1 i₁.1 i₂.1)
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k))
    (hsq : curveChange j₁.1 j₁.2 t ≫ curveChange i₁.1 i₁.2 t = curveChange j₂.1 j₂.2 t ≫ curveChange i₂.1 i₂.2 t)
    (L₁ : (Limits.pullback y₁ t).Modules) (hL₁ : Scheme.Modules.IsInvertible L₁)
    (L₂ : (Limits.pullback y₂ t).Modules) (hL₂ : Scheme.Modules.IsInvertible L₂)
    (φ : (Scheme.Modules.pullback (curveChange j₁.1 j₁.2 t)).obj L₁ ≅
      (Scheme.Modules.pullback (curveChange j₂.1 j₂.2 t)).obj L₂) :
    ∃ (L : (Limits.pullback x t).Modules), Scheme.Modules.IsInvertible L ∧
      ∃ (α₁ : (Scheme.Modules.pullback (curveChange i₁.1 i₁.2 t)).obj L ≅ L₁)
        (α₂ : (Scheme.Modules.pullback (curveChange i₂.1 i₂.2 t)).obj L ≅ L₂),
        (Scheme.Modules.pullback (curveChange j₁.1 j₁.2 t)).map α₁.hom ≫ φ.hom =
          ((Scheme.Modules.pullbackComp (curveChange j₁.1 j₁.2 t) (curveChange i₁.1 i₁.2 t)).app L).hom ≫
            ((Scheme.Modules.pullbackCongr hsq).app L).hom ≫
            ((Scheme.Modules.pullbackComp (curveChange j₂.1 j₂.2 t) (curveChange i₂.1 i₂.2 t)).app L).inv ≫
            (Scheme.Modules.pullback (curveChange j₂.1 j₂.2 t)).map α₂.hom := by
  haveI := GTExists.isClosedImmersion_curveChange i₁.1 i₁.2 t
  haveI := GTExists.isClosedImmersion_curveChange i₂.1 i₂.2 t
  haveI : IsClosedImmersion j₂.1 := MorphismProperty.of_isPullback (P := @IsClosedImmersion) hZ inferInstance
  haveI := GTExists.isClosedImmersion_curveChange (c := y₂) j₂.1 j₂.2 t
  exact AlgebraicGeometry.Scheme.Modules.exists_isInvertible_pullback_iso_of_milnorSquare
    (curveChange i₁.1 i₁.2 t) (curveChange i₂.1 i₂.2 t) (curveChange j₁.1 j₁.2 t) (curveChange j₂.1 j₂.2 t) hsq
    (fun U => AlgebraicGeometry.IsClosedImmersion.app_curveChange_injective_and_exists_of_app_eq_of_isReduced x hXred y₁ y₂ z i₁ i₂ hjs j₁ j₂ hZ t hsq U)
    L₁ hL₁ L₂ hL₂ φ

end S_AlgebraicGeometry_Scheme_Modules_exists_isInvertible_pullback_curveChange_iso_of_closedCover
end P2MW
export P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_isInvertible_pullback_curveChange_iso_of_closedCover (solution)
