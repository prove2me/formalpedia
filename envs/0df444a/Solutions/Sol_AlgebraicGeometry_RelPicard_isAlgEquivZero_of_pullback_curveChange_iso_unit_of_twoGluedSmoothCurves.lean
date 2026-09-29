-- Prove2me | solution 1 for AlgebraicGeometry.RelPicard.isAlgEquivZero_of_pullback_curveChange_iso_unit_of_twoGluedSmoothCurves
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:03.589526+00:00
-- url     : https://prove2.me/submissions/f593dd42-5380-5910-b011-8206ebf91555

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RepresentsRelSubPic
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_AlgebraicGeometry_RelPicardPullback
import Definitions.Def_AlgebraicGeometry_TwoGluedCurvesNodeUnitModule
import Theorems.Thm_AlgebraicGeometry_exists_rationalPoint_enumeration_of_natCard_pullback_eq
import Theorems.Thm_AlgebraicGeometry_TwoGluedCurves_exists_isNodeUnitModule_of_pullback_curveChange_iso_unit
import Theorems.Thm_AlgebraicGeometry_TwoGluedCurves_IsNodeUnitModule_fibrewiseAlgEquivZero
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_RelPicard_isAlgEquivZero_of_pullback_curveChange_iso_unit_of_twoGluedSmoothCurves
p2m_attr_erase "instance" "PresheafOfModules.instMonoidalClosed PresheafOfModules.InternalHom.instModuleCarrierObjOppositeCommRingCatSubtypePiFamilyMemAddSubgroupNaturalFamilies PresheafOfModules.InternalHom.instModuleCarrierObjOppositeRingCatCompCommRingCatForget₂RingHomCarrierCarrierAbPresheaf PresheafOfModules.InternalHom.instSMulCarrierObjOppositeCommRingCatSubtypePiFamilyMemAddSubgroupNaturalFamilies AlgebraicGeometry.Scheme.PresheafOfModules.symmetricCategory SheafOfModules.instFaithfulRingSheafPModToPMod SheafOfModules.symmetricCategory AlgebraicGeometry.Scheme.PresheafOfModules.monoidalCategory AlgebraicGeometry.Scheme.PresheafOfModules.monoidalClosed SheafOfModules.instFullRingSheafPModToPMod SheafOfModules.monoidalCategory AlgebraicGeometry.Scheme.Modules.symmetricCategory SheafOfModules.monoidalClosed SheafOfModules.instIsLocalizationPModRingSheafSheafifyFunctorPresheafW SheafOfModules.sheafifyFunctor_monoidal AlgebraicGeometry.Scheme.Modules.monoidalClosed AlgebraicGeometry.instMonoidalPresheafOfModulesModulesSheafify AlgebraicGeometry.Scheme.Modules.monoidalCategory PresheafOfModules.PullbackMonoidal.pullback_monoidal PresheafOfModules.PullbackMonoidal.isIso_δ PresheafOfModules.pushforward_laxMonoidal PresheafOfModules.PullbackMonoidal.isIso_η PresheafOfModules.free_monoidal PresheafOfModules.restrictScalars_laxMonoidal PresheafOfModules.PullbackMonoidal.isIso_δ_gS PresheafOfModules.pullback_oplaxMonoidal PresheafOfModules.PullbackMonoidal.instPreservesColimitsOfSizeCompOppositeCommRingCatRingCatForget₂RingHomCarrierCarrierPb PresheafOfModules.pullback_monoidal' AlgebraicGeometry.Scheme.Modules.preservesBinaryProducts_opensMap AlgebraicGeometry.Scheme.Modules.pullback_monoidal AlgebraicGeometry.Scheme.Modules.sheafify_isLocalization' AlgebraicGeometry.Scheme.Modules.preservesTerminal_opensMap AlgebraicGeometry.Scheme.Modules.pullback₀_monoidal AlgebraicGeometry.Scheme.Modules.preservesFiniteProducts_opensMap AlgebraicGeometry.Scheme.Modules.instLiftingPresheafOfModulesSheafifyPresheafWOpensCarrierCarrierCommRingCatGrothendieckTopologyObjFunctorOppositeIsSheafSheafCompPullback₀Pullback"
p2m_attr_erase "simp" "AlgebraicGeometry.Scheme.Modules.tensorSections_zero_right AlgebraicGeometry.Scheme.Modules.map_unitSection AlgebraicGeometry.Scheme.Modules.tensorSectionsBilin_apply AlgebraicGeometry.Scheme.Modules.tensorPowSection_zero AlgebraicGeometry.Scheme.Modules.tensorSections_zero_left PresheafOfModules.InternalHom.presheaf_map_apply PresheafOfModules.InternalHom.curryFamily_app PresheafOfModules.InternalHom.add_app PresheafOfModules.InternalHom.smul_app PresheafOfModules.InternalHom.zero_app PresheafOfModules.ihomObj_map_val PresheafOfModules.ihomFunctor_map PresheafOfModules.InternalHom.restrict_app PresheafOfModules.InternalHom.postcomp_app PresheafOfModules.InternalHom.neg_app PresheafOfModules.curry'_app_val PresheafOfModules.InternalHom.presheaf_obj PresheafOfModules.ihomFunctor_obj PresheafOfModules.ihomObj_obj PresheafOfModules.InternalHom.sub_app PresheafOfModules.ihomMap_app_val SheafOfModules.tensorUnit_eq AlgebraicGeometry.Scheme.Modules.tensorUnit_eq AlgebraicGeometry.Scheme.Modules.tensorPow_zero AlgebraicGeometry.Scheme.Modules.tensorPow_succ AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_neg AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_zero AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_sub AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_add PresheafOfModules.freeεIso_hom_app PresheafOfModules.freeμIso_hom_app"
set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian AlgebraicGeometry.RelPicard AlgebraicGeometry.TwoGluedCurves

theorem solution
    {k : Type u} [Field k] [IsAlgClosed k]
    {X C₁ C₂ : Scheme.{u}} (x : X ⟶ Spec (CommRingCat.of k)) [IsProper x] (hXred : IsReduced X)
    (c₁ : C₁ ⟶ Spec (CommRingCat.of k)) (c₂ : C₂ ⟶ Spec (CommRingCat.of k))
    [IsProper c₁] [SmoothOfRelativeDimension 1 c₁] [GeometricallyIntegral c₁]
    [IsProper c₂] [SmoothOfRelativeDimension 1 c₂] [GeometricallyIntegral c₂]
    (i₁ : SchemeHomOver c₁ x) (i₂ : SchemeHomOver c₂ x) [IsClosedImmersion i₁.1] [IsClosedImmersion i₂.1]
    (hjs : ∀ z : X, z ∈ Set.range i₁.1.base ∨ z ∈ Set.range i₂.1.base)
    (hcr : IsReduced (pullback i₁.1 i₂.1)) (s : ℕ) (hs : Nat.card ↥(pullback i₁.1 i₂.1) = s) (hs0 : 0 < s)
    (K : Type u) [Field K] [IsAlgClosed K] (κ : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of k))
    (N : (pullback x κ).Modules) (hN : Scheme.Modules.IsInvertible N)
    (h₁ : Nonempty ((Scheme.Modules.pullback (curveChange i₁.1 i₁.2 κ)).obj N ≅
      SheafOfModules.unit (pullback c₁ κ).ringCatSheaf))
    (h₂ : Nonempty ((Scheme.Modules.pullback (curveChange i₂.1 i₂.2 κ)).obj N ≅
      SheafOfModules.unit (pullback c₂ κ).ringCatSheaf)) :
    IsAlgEquivZero (pullback.snd x κ) N := by
  haveI : IsReduced X := hXred
  haveI : LocallyOfFiniteType c₁ := by
    haveI := SmoothOfRelativeDimension.smooth 1 c₁; infer_instance
  haveI : LocallyOfFiniteType c₂ := by
    haveI := SmoothOfRelativeDimension.smooth 1 c₂; infer_instance

  obtain ⟨p₁, p₂, hinj, hnode, hinter⟩ :=
    AlgebraicGeometry.exists_rationalPoint_enumeration_of_natCard_pullback_eq k x i₁ i₂ s hs hs0

  obtain ⟨u, hu⟩ := AlgebraicGeometry.TwoGluedCurves.exists_isNodeUnitModule_of_pullback_curveChange_iso_unit
    k x i₁ i₂ hjs p₁ p₂ hinj hnode hinter hcr κ N hN h₁ h₂

  obtain ⟨j₀⟩ : Nonempty (Fin s) := ⟨⟨0, hs0⟩⟩
  let ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) x :=
    ⟨(p₁ j₀).1 ≫ i₁.1, by rw [Category.assoc, i₁.2, (p₁ j₀).2]⟩
  have hε : (p₁ j₀).1 ≫ i₁.1 = ε.1 := rfl
  have hrig : Nonempty ((Scheme.Modules.pullback (rigSection x κ ε)).obj N ≅
      SheafOfModules.unit (Spec (CommRingCat.of K)).ringCatSheaf) :=
    ⟨(Scheme.Modules.pullbackCongr (rigSection_curveChange i₁.1 i₁.2 hε κ).symm).app N ≪≫
      ((Scheme.Modules.pullbackComp _ _).app N).symm ≪≫
      (Scheme.Modules.pullback _).mapIso h₁.some ≪≫ Scheme.Modules.pullbackUnitIso _⟩
  let M : RigidifiedLineBundle x ε κ := ⟨N, hN, hrig⟩

  have hfib : FibrewiseAlgEquivZero M :=
    AlgebraicGeometry.TwoGluedCurves.IsNodeUnitModule.fibrewiseAlgEquivZero
      k x i₁ i₂ hjs p₁ p₂ hinj hnode hinter hcr ε M hu

  have h1 := hfib K (𝟙 _)
  let e : pullback x κ ⟶ pullback (pullback.snd x κ) (𝟙 (Spec (CommRingCat.of K))) :=
    pullback.lift (𝟙 _) (pullback.snd x κ) (by simp)
  have he : e ≫ fibreAt x κ (𝟙 _) = pullback.snd x κ := by
    simp only [e, fibreAt, pullback.lift_snd]
  have hefst : e ≫ pullback.fst (pullback.snd x κ) (𝟙 _) = 𝟙 _ := by
    simp only [e, pullback.lift_fst]
  exact (h1.pullback e he).of_iso ((Scheme.Modules.pullbackComp _ _).app N ≪≫
    (Scheme.Modules.pullbackCongr hefst).app N ≪≫ (Scheme.Modules.pullbackId _).app N)

end S_AlgebraicGeometry_RelPicard_isAlgEquivZero_of_pullback_curveChange_iso_unit_of_twoGluedSmoothCurves
end P2MW
export P2MW.S_AlgebraicGeometry_RelPicard_isAlgEquivZero_of_pullback_curveChange_iso_unit_of_twoGluedSmoothCurves (solution)
