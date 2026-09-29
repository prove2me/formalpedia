-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.Modules.geomFibreH0Finrank_id_eq_finrank_sections
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.122355+00:00
-- url     : https://prove2.me/submissions/07706c72-7a9a-5d01-ae3f-3e05f429515a

import Mathlib
import Definitions.Def_AlgebraicGeometry_PolarisedAbelianScheme
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_TwoChartCechSectionsOf
import Definitions.Def_AlgebraicGeometry_OModulePresheafOfModules
import Definitions.Def_AlgebraicGeometry_OModulePresheafEulerChar
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCech
import Theorems.Thm_AlgebraicGeometry_OModulePresheaf_nonempty_sections_top_equiv_H0_ofModules
import Theorems.Thm_AlgebraicGeometry_OModulePresheaf_cechFinrank_ofModules_pullback_eq_of_isIso
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Scheme_Modules_geomFibreH0Finrank_id_eq_finrank_sections
p2m_attr_erase "instance" "AlgebraicGeometry.OModulePresheaf.instSubsingletonObjZero AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instDecidableEqIdx AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintype AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instLinearOrder AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintypeIdx PresheafOfModules.instMonoidalClosed PresheafOfModules.InternalHom.instModuleCarrierObjOppositeCommRingCatSubtypePiFamilyMemAddSubgroupNaturalFamilies PresheafOfModules.InternalHom.instModuleCarrierObjOppositeRingCatCompCommRingCatForget₂RingHomCarrierCarrierAbPresheaf PresheafOfModules.InternalHom.instSMulCarrierObjOppositeCommRingCatSubtypePiFamilyMemAddSubgroupNaturalFamilies AlgebraicGeometry.Scheme.PresheafOfModules.symmetricCategory SheafOfModules.instFaithfulRingSheafPModToPMod SheafOfModules.symmetricCategory AlgebraicGeometry.Scheme.PresheafOfModules.monoidalCategory AlgebraicGeometry.Scheme.PresheafOfModules.monoidalClosed SheafOfModules.instFullRingSheafPModToPMod SheafOfModules.monoidalCategory AlgebraicGeometry.Scheme.Modules.symmetricCategory SheafOfModules.monoidalClosed SheafOfModules.instIsLocalizationPModRingSheafSheafifyFunctorPresheafW SheafOfModules.sheafifyFunctor_monoidal AlgebraicGeometry.Scheme.Modules.monoidalClosed AlgebraicGeometry.instMonoidalPresheafOfModulesModulesSheafify AlgebraicGeometry.Scheme.Modules.monoidalCategory"
p2m_attr_erase "simp" "AlgebraicGeometry.OModulePresheaf.prod_obj AlgebraicGeometry.OModulePresheaf.restrOpen_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.injEq AlgebraicGeometry.OModulePresheaf.pushforward_obj AlgebraicGeometry.OModulePresheaf.im_obj AlgebraicGeometry.OModulePresheaf.pow_obj AlgebraicGeometry.OModulePresheaf.fstHom_app AlgebraicGeometry.OModulePresheaf.ker_obj AlgebraicGeometry.OModulePresheaf.coker_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.preimage_U AlgebraicGeometry.OModulePresheaf.sndHom_app AlgebraicGeometry.OModulePresheaf.Hom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.id_app AlgebraicGeometry.OModulePresheaf.AffHom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffHom.comp_app AlgebraicGeometry.OModulePresheaf.AffSES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.kerMap_coe AlgebraicGeometry.OModulePresheaf.AffHom.id_app AlgebraicGeometry.OModulePresheaf.Hom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.toAffHom_app AlgebraicGeometry.OModulePresheaf.SES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.comp_app AlgebraicGeometry.OModulePresheaf.SES.mk.injEq AlgebraicGeometry.OModulePresheaf.AffHom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffSES.mk.injEq AlgebraicGeometry.Scheme.OrderedAffineCover.toCoverOf_U AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.injEq AlgebraicGeometry.Scheme.OrderedAffineCover.restrict_U AlgebraicGeometry.Scheme.Modules.tensorSections_zero_right AlgebraicGeometry.Scheme.Modules.map_unitSection AlgebraicGeometry.Scheme.Modules.tensorSectionsBilin_apply AlgebraicGeometry.Scheme.Modules.tensorPowSection_zero AlgebraicGeometry.Scheme.Modules.tensorSections_zero_left PresheafOfModules.InternalHom.presheaf_map_apply PresheafOfModules.InternalHom.curryFamily_app PresheafOfModules.InternalHom.add_app"
p2m_attr_erase "simp" "PresheafOfModules.InternalHom.smul_app PresheafOfModules.InternalHom.zero_app PresheafOfModules.ihomObj_map_val PresheafOfModules.ihomFunctor_map PresheafOfModules.InternalHom.restrict_app PresheafOfModules.InternalHom.postcomp_app PresheafOfModules.InternalHom.neg_app PresheafOfModules.curry'_app_val PresheafOfModules.InternalHom.presheaf_obj PresheafOfModules.ihomFunctor_obj PresheafOfModules.ihomObj_obj PresheafOfModules.InternalHom.sub_app PresheafOfModules.ihomMap_app_val SheafOfModules.tensorUnit_eq AlgebraicGeometry.Scheme.Modules.tensorUnit_eq AlgebraicGeometry.Scheme.Modules.tensorPow_zero AlgebraicGeometry.Scheme.Modules.tensorPow_succ"

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace L4B5

theorem nonempty_orderedAffineCover (X : Scheme.{u}) [CompactSpace X] : Nonempty X.OrderedAffineCover := by
  classical
  let 𝒱 := X.affineCover.finiteSubcover
  letI : LinearOrder 𝒱.I₀ := LinearOrder.lift' (Fintype.equivFin 𝒱.I₀) (Fintype.equivFin 𝒱.I₀).injective
  exact ⟨Scheme.OrderedAffineCover.mk (ι := 𝒱.I₀) (U := fun j => (𝒱.f j).opensRange)
    (isAffineOpen := fun j => isAffineOpen_opensRange (𝒱.f j)) (iSup_eq_top := 𝒱.iSup_opensRange)⟩

end L4B5

open L4B5 _root_.AlgebraicGeometry.Scheme.TwoAffineOpenCover in
theorem solution
    (k : Type u) [Field k] {A : Scheme.{u}} (f : A ⟶ Spec (CommRingCat.of k)) [IsProper f]
    (M : A.Modules) (hM : Scheme.Modules.IsInvertible M) :
    Scheme.Modules.geomFibreH0Finrank f M k (RingHom.id k) =
      (letI := Scheme.TwoAffineOpenCover.moduleSectionsOfHom f M ⊤; Module.finrank k Γ(M, ⊤)) := by
  have hι : Spec.map (CommRingCat.ofHom (RingHom.id k)) = 𝟙 (Spec (CommRingCat.of k)) := by
    rw [CommRingCat.ofHom_id]; exact Spec.map_id _
  haveI : IsIso (Spec.map (CommRingCat.ofHom (RingHom.id k))) := by rw [hι]; infer_instance
  haveI : IsIso (pullback.fst f (Spec.map (CommRingCat.ofHom (RingHom.id k)))) := inferInstance
  have hpf : pullback.fst f (Spec.map (CommRingCat.ofHom (RingHom.id k))) ≫ f =
      pullback.snd f (Spec.map (CommRingCat.ofHom (RingHom.id k))) := by
    rw [pullback.condition, hι, Category.comp_id]
  haveI : CompactSpace ↑A := QuasiCompact.compactSpace_of_compactSpace f
  haveI : CompactSpace ↑(pullback f (Spec.map (CommRingCat.ofHom (RingHom.id k)))) :=
    QuasiCompact.compactSpace_of_compactSpace (pullback.snd f (Spec.map (CommRingCat.ofHom (RingHom.id k))))
  obtain ⟨𝒰⟩ := nonempty_orderedAffineCover A
  obtain ⟨𝒰₀⟩ := nonempty_orderedAffineCover (pullback f (Spec.map (CommRingCat.ofHom (RingHom.id k))))
  change (letI := (moduleSectionsOfHom (pullback.snd f (Spec.map (CommRingCat.ofHom (RingHom.id k))))
      ((Scheme.Modules.pullback (pullback.fst f (Spec.map (CommRingCat.ofHom (RingHom.id k))))).obj M) ⊤);
    Module.finrank k Γ((Scheme.Modules.pullback (pullback.fst f (Spec.map (CommRingCat.ofHom (RingHom.id k))))).obj M, ⊤)) = _
  letI i0 := moduleSectionsOfHom (pullback.snd f (Spec.map (CommRingCat.ofHom (RingHom.id k))))
      ((Scheme.Modules.pullback (pullback.fst f (Spec.map (CommRingCat.ofHom (RingHom.id k))))).obj M) ⊤
  letI i1 := moduleSectionsOfHom f M ⊤
  obtain ⟨e₀⟩ := OModulePresheaf.nonempty_sections_top_equiv_H0_ofModules
    (pullback.snd f (Spec.map (CommRingCat.ofHom (RingHom.id k))))
    ((Scheme.Modules.pullback (pullback.fst f (Spec.map (CommRingCat.ofHom (RingHom.id k))))).obj M) 𝒰₀
  obtain ⟨e₁⟩ := OModulePresheaf.nonempty_sections_top_equiv_H0_ofModules f M 𝒰
  have h := OModulePresheaf.cechFinrank_ofModules_pullback_eq_of_isIso f
    (pullback.fst f (Spec.map (CommRingCat.ofHom (RingHom.id k)))) M hM 𝒰₀ 𝒰 0
  rw [hpf, OModulePresheaf.cechFinrank_zero, OModulePresheaf.cechFinrank_zero] at h
  exact e₀.finrank_eq.trans (h.trans e₁.finrank_eq.symm)

end S_AlgebraicGeometry_Scheme_Modules_geomFibreH0Finrank_id_eq_finrank_sections
end P2MW
export P2MW.S_AlgebraicGeometry_Scheme_Modules_geomFibreH0Finrank_id_eq_finrank_sections (solution)
