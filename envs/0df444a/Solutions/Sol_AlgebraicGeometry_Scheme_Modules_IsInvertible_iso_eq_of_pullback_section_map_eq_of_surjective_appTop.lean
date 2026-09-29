-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.Modules.IsInvertible.iso_eq_of_pullback_section_map_eq_of_surjective_appTop
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:03.589526+00:00
-- url     : https://prove2.me/submissions/2095ca32-8d3a-5398-a75b-28d0268005b7

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_forall_app_eq_smul
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_pullback_map_app_eq_smul_of_forall_app_eq_smul
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_eq_one_of_forall_smul_eq
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_iso_eq_of_pullback_section_map_eq_of_surjective_appTop
p2m_attr_erase "instance" "AlgebraicGeometry.Scheme.PresheafOfModules.symmetricCategory SheafOfModules.instFaithfulRingSheafPModToPMod SheafOfModules.symmetricCategory AlgebraicGeometry.Scheme.PresheafOfModules.monoidalCategory AlgebraicGeometry.Scheme.PresheafOfModules.monoidalClosed SheafOfModules.instFullRingSheafPModToPMod SheafOfModules.monoidalCategory AlgebraicGeometry.Scheme.Modules.symmetricCategory SheafOfModules.monoidalClosed SheafOfModules.instIsLocalizationPModRingSheafSheafifyFunctorPresheafW SheafOfModules.sheafifyFunctor_monoidal AlgebraicGeometry.Scheme.Modules.monoidalClosed AlgebraicGeometry.instMonoidalPresheafOfModulesModulesSheafify AlgebraicGeometry.Scheme.Modules.monoidalCategory PresheafOfModules.instMonoidalClosed PresheafOfModules.InternalHom.instModuleCarrierObjOppositeCommRingCatSubtypePiFamilyMemAddSubgroupNaturalFamilies PresheafOfModules.InternalHom.instModuleCarrierObjOppositeRingCatCompCommRingCatForget₂RingHomCarrierCarrierAbPresheaf PresheafOfModules.InternalHom.instSMulCarrierObjOppositeCommRingCatSubtypePiFamilyMemAddSubgroupNaturalFamilies"
p2m_attr_erase "simp" "AlgebraicGeometry.Scheme.Modules.toUnitSection_ofUnitSection AlgebraicGeometry.Scheme.Modules.pullbackSection_def AlgebraicGeometry.Scheme.Modules.ofUnitSection_toUnitSection SheafOfModules.tensorUnit_eq AlgebraicGeometry.Scheme.Modules.tensorUnit_eq PresheafOfModules.InternalHom.presheaf_map_apply PresheafOfModules.InternalHom.curryFamily_app PresheafOfModules.InternalHom.add_app PresheafOfModules.InternalHom.smul_app PresheafOfModules.InternalHom.zero_app PresheafOfModules.ihomObj_map_val PresheafOfModules.ihomFunctor_map PresheafOfModules.InternalHom.restrict_app PresheafOfModules.InternalHom.postcomp_app PresheafOfModules.InternalHom.neg_app PresheafOfModules.curry'_app_val PresheafOfModules.InternalHom.presheaf_obj PresheafOfModules.ihomFunctor_obj PresheafOfModules.ihomObj_obj PresheafOfModules.InternalHom.sub_app PresheafOfModules.ihomMap_app_val AlgebraicGeometry.RelEffCartierDiv.toRelEffDivisor_ofRelEffDivisor AlgebraicGeometry.RelEffCartierDiv.toRelEffDivisor_I AlgebraicGeometry.mapOnProdOver_fst_assoc AlgebraicGeometry.RelEffCartierDiv.mk.sizeOf_spec AlgebraicGeometry.RelEffCartierDiv.mk.injEq AlgebraicGeometry.mapOnProdOver_snd AlgebraicGeometry.mapOnProdOver_fst AlgebraicGeometry.mapOnProdOver_snd_assoc AlgebraicGeometry.mapOnProdOver_id AlgebraicCurve.RelEffDivisor.mk.sizeOf_spec AlgebraicCurve.mapOnProd_fst AlgebraicCurve.mapOnProd_fst_assoc AlgebraicCurve.mapOnProd_snd AlgebraicCurve.UnivDivisorPack.mk.injEq AlgebraicCurve.RelEffDivisor.mk.injEq AlgebraicCurve.UnivDivisorPack.mk.sizeOf_spec AlgebraicCurve.mapOnProd_snd_assoc"

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem solution
    {S : Type u} [CommRing S] {A : Scheme.{u}} (f : A ⟶ Spec (CommRingCat.of S))
    (e : Spec (CommRingCat.of S) ⟶ A) (he : e ≫ f = 𝟙 _)
    (hΓ : Function.Surjective (f.appTop).hom)
    (L M : A.Modules) (hL : Scheme.Modules.IsInvertible L)
    (α β : L ≅ M)
    (h : (Scheme.Modules.pullback e).map α.hom = (Scheme.Modules.pullback e).map β.hom) :
    α = β := by

  set γ : L ⟶ L := α.hom ≫ β.inv with hγdef
  obtain ⟨u, hu⟩ := AlgebraicGeometry.Scheme.Modules.IsInvertible.exists_forall_app_eq_smul hL γ
  obtain ⟨s₀, hs₀⟩ := hΓ u

  have heγ : (Scheme.Modules.pullback e).map γ = 𝟙 _ := by
    rw [hγdef, CategoryTheory.Functor.map_comp, h, ← CategoryTheory.Functor.map_comp, Iso.hom_inv_id, CategoryTheory.Functor.map_id]
  have hes : e.appTop (f.appTop s₀) = s₀ := by
    rw [← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop, he, Scheme.Hom.id_appTop]
    rfl
  have hs1 : s₀ = 1 := by
    have h1 := AlgebraicGeometry.Scheme.Modules.IsInvertible.eq_one_of_forall_smul_eq (hL.pullback e) (e.appTop u)
      (fun V t => by
        rw [← AlgebraicGeometry.Scheme.Modules.pullback_map_app_eq_smul_of_forall_app_eq_smul e L u γ hu V t, heγ,
          Scheme.Modules.Hom.id_app]
        rfl)
    rwa [← hs₀, hes] at h1

  have hu1 : u = 1 := by rw [← hs₀, hs1, map_one]
  have hγ1 : γ = 𝟙 L := by
    apply Scheme.Modules.hom_ext
    intro U
    ext s
    rw [hu U s, hu1, map_one, one_smul, Scheme.Modules.Hom.id_app]
    rfl
  ext
  rw [← Category.comp_id α.hom, ← β.inv_hom_id, ← Category.assoc, ← hγdef, hγ1, Category.id_comp]

end S_AlgebraicGeometry_Scheme_Modules_IsInvertible_iso_eq_of_pullback_section_map_eq_of_surjective_appTop
end P2MW
export P2MW.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_iso_eq_of_pullback_section_map_eq_of_surjective_appTop (solution)
