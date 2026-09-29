-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.Modules.ProjPresentation.exists_unit_appTop_smul_eq_of_toProj_eq_of_bijective
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:03.589526+00:00
-- url     : https://prove2.me/submissions/7ee06770-672c-5e05-b4d6-c2cc6fc6c75c

import Definitions.Def_AlgebraicGeometry_ModulesProjPresentation
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_ProjPresentation_exists_unit_smul_eq_of_toProj_eq
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Scheme_Modules_ProjPresentation_exists_unit_appTop_smul_eq_of_toProj_eq_of_bijective
p2m_attr_erase "instance" "PresheafOfModules.instMonoidalClosed PresheafOfModules.InternalHom.instModuleCarrierObjOppositeCommRingCatSubtypePiFamilyMemAddSubgroupNaturalFamilies PresheafOfModules.InternalHom.instModuleCarrierObjOppositeRingCatCompCommRingCatForget₂RingHomCarrierCarrierAbPresheaf PresheafOfModules.InternalHom.instSMulCarrierObjOppositeCommRingCatSubtypePiFamilyMemAddSubgroupNaturalFamilies AlgebraicGeometry.Scheme.PresheafOfModules.symmetricCategory SheafOfModules.instFaithfulRingSheafPModToPMod SheafOfModules.symmetricCategory AlgebraicGeometry.Scheme.PresheafOfModules.monoidalCategory AlgebraicGeometry.Scheme.PresheafOfModules.monoidalClosed SheafOfModules.instFullRingSheafPModToPMod SheafOfModules.monoidalCategory AlgebraicGeometry.Scheme.Modules.symmetricCategory SheafOfModules.monoidalClosed SheafOfModules.instIsLocalizationPModRingSheafSheafifyFunctorPresheafW SheafOfModules.sheafifyFunctor_monoidal AlgebraicGeometry.Scheme.Modules.monoidalClosed AlgebraicGeometry.instMonoidalPresheafOfModulesModulesSheafify AlgebraicGeometry.Scheme.Modules.monoidalCategory"
p2m_attr_erase "simp" "PresheafOfModules.InternalHom.presheaf_map_apply PresheafOfModules.InternalHom.curryFamily_app PresheafOfModules.InternalHom.add_app PresheafOfModules.InternalHom.smul_app PresheafOfModules.InternalHom.zero_app PresheafOfModules.ihomObj_map_val PresheafOfModules.ihomFunctor_map PresheafOfModules.InternalHom.restrict_app PresheafOfModules.InternalHom.postcomp_app PresheafOfModules.InternalHom.neg_app PresheafOfModules.curry'_app_val PresheafOfModules.InternalHom.presheaf_obj PresheafOfModules.ihomFunctor_obj PresheafOfModules.ihomObj_obj PresheafOfModules.InternalHom.sub_app PresheafOfModules.ihomMap_app_val SheafOfModules.tensorUnit_eq AlgebraicGeometry.Scheme.Modules.tensorUnit_eq AlgebraicGeometry.Scheme.Modules.tensorPow_zero AlgebraicGeometry.Scheme.Modules.tensorPow_succ AlgebraicGeometry.Scheme.Modules.tensorSections_zero_right AlgebraicGeometry.Scheme.Modules.map_unitSection AlgebraicGeometry.Scheme.Modules.tensorSectionsBilin_apply AlgebraicGeometry.Scheme.Modules.tensorPowSection_zero AlgebraicGeometry.Scheme.Modules.tensorSections_zero_left"

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem solution
    {R : Type u} [CommRing R] {X : Scheme.{u}} {M : X.Modules} {f : X ⟶ Spec (.of R)} {N : ℕ}
    (P P' : M.ProjPresentation f N) (h : P.toProj = P'.toProj)
    (hΓ : Function.Bijective fun r : R => f.appTop ((Scheme.ΓSpecIso (.of R)).inv r)) :
    ∃ c : Rˣ, ∀ i : Fin (N + 1), P'.σ i = (f.appTop ((Scheme.ΓSpecIso (.of R)).inv (c : R))) • P.σ i := by
  obtain ⟨u, hu⟩ := AlgebraicGeometry.Scheme.Modules.ProjPresentation.exists_unit_smul_eq_of_toProj_eq P P' h
  let φ : R →+* Γ(X, ⊤) := f.appTop.hom.comp (Scheme.ΓSpecIso (.of R)).inv.hom
  have hφ : Function.Bijective φ := hΓ
  let e : R ≃+* Γ(X, ⊤) := RingEquiv.ofBijective φ hφ
  refine ⟨Units.map (e.symm : Γ(X, ⊤) ≃+* R).toRingHom.toMonoidHom u, fun i => ?_⟩
  rw [hu i]
  congr 1
  show (u : Γ(X, ⊤)) = φ (e.symm (u : Γ(X, ⊤)))
  exact (e.apply_symm_apply (u : Γ(X, ⊤))).symm

end S_AlgebraicGeometry_Scheme_Modules_ProjPresentation_exists_unit_appTop_smul_eq_of_toProj_eq_of_bijective
end P2MW
export P2MW.S_AlgebraicGeometry_Scheme_Modules_ProjPresentation_exists_unit_appTop_smul_eq_of_toProj_eq_of_bijective (solution)
