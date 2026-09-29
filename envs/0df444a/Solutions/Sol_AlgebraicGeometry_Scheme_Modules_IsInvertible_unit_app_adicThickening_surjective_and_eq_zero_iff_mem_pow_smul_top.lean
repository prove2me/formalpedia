-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.Modules.IsInvertible.unit_app_adicThickening_surjective_and_eq_zero_iff_mem_pow_smul_top
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:03.589526+00:00
-- url     : https://prove2.me/submissions/39cf3d38-6db3-5d0f-94f6-327a518a028f

import Mathlib
import Definitions.Def_AlgebraicGeometry_OModulePresheafOfModules
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_AdicThickening
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_tensorProduct_linearEquiv_sections_pullback_preimage_of_isAffineOpen
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_unit_app_adicThickening_surjective_and_eq_zero_iff_mem_pow_smul_top
p2m_attr_erase "instance" "PresheafOfModules.instMonoidalClosed PresheafOfModules.InternalHom.instModuleCarrierObjOppositeCommRingCatSubtypePiFamilyMemAddSubgroupNaturalFamilies PresheafOfModules.InternalHom.instModuleCarrierObjOppositeRingCatCompCommRingCatForget₂RingHomCarrierCarrierAbPresheaf PresheafOfModules.InternalHom.instSMulCarrierObjOppositeCommRingCatSubtypePiFamilyMemAddSubgroupNaturalFamilies AlgebraicGeometry.Scheme.PresheafOfModules.symmetricCategory SheafOfModules.instFaithfulRingSheafPModToPMod SheafOfModules.symmetricCategory AlgebraicGeometry.Scheme.PresheafOfModules.monoidalCategory AlgebraicGeometry.Scheme.PresheafOfModules.monoidalClosed SheafOfModules.instFullRingSheafPModToPMod SheafOfModules.monoidalCategory AlgebraicGeometry.Scheme.Modules.symmetricCategory SheafOfModules.monoidalClosed SheafOfModules.instIsLocalizationPModRingSheafSheafifyFunctorPresheafW SheafOfModules.sheafifyFunctor_monoidal AlgebraicGeometry.Scheme.Modules.monoidalClosed AlgebraicGeometry.instMonoidalPresheafOfModulesModulesSheafify AlgebraicGeometry.Scheme.Modules.monoidalCategory PresheafOfModules.ExteriorPower.instModulePresheafAb"
p2m_attr_erase "simp" "AlgebraicGeometry.Scheme.Modules.tensorSections_zero_right AlgebraicGeometry.Scheme.Modules.map_unitSection AlgebraicGeometry.Scheme.Modules.tensorSectionsBilin_apply AlgebraicGeometry.Scheme.Modules.tensorPowSection_zero AlgebraicGeometry.Scheme.Modules.tensorSections_zero_left PresheafOfModules.InternalHom.presheaf_map_apply PresheafOfModules.InternalHom.curryFamily_app PresheafOfModules.InternalHom.add_app PresheafOfModules.InternalHom.smul_app PresheafOfModules.InternalHom.zero_app PresheafOfModules.ihomObj_map_val PresheafOfModules.ihomFunctor_map PresheafOfModules.InternalHom.restrict_app PresheafOfModules.InternalHom.postcomp_app PresheafOfModules.InternalHom.neg_app PresheafOfModules.curry'_app_val PresheafOfModules.InternalHom.presheaf_obj PresheafOfModules.ihomFunctor_obj PresheafOfModules.ihomObj_obj PresheafOfModules.InternalHom.sub_app PresheafOfModules.ihomMap_app_val SheafOfModules.tensorUnit_eq AlgebraicGeometry.Scheme.Modules.tensorUnit_eq AlgebraicGeometry.Scheme.Modules.tensorPow_zero AlgebraicGeometry.Scheme.Modules.tensorPow_succ AlgebraicGeometry.Scheme.Hom.kaehlerPresheaf_obj PresheafOfModules.exteriorPower_map_ιMulti PresheafOfModules.ExteriorPower.appₗ_apply AlgebraicGeometry.Scheme.Modules.exteriorPower_obj"

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped TensorProduct

universe u

theorem solution
    {R : Type u} [CommRing R] (I : Ideal R) {X : Scheme.{u}} (f : X ⟶ Spec (.of R))
    (N : X.Modules) (hN : Scheme.Modules.IsInvertible N) (n : ℕ) (U : X.affineOpens) :
    Function.Surjective
        (((Scheme.Modules.pullbackPushforwardAdjunction (adicThickeningι f I n)).unit.app N).app U.1) ∧
      ∀ s : (OModulePresheaf.ofModules f N).obj U.1,
        ((Scheme.Modules.pullbackPushforwardAdjunction (adicThickeningι f I n)).unit.app N).app U.1 s = 0 ↔
          s ∈ I ^ (n + 1) • (⊤ : Submodule R ((OModulePresheaf.ofModules f N).obj U.1)) := by

  letI algU : Algebra R Γ(X, U.1) := ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ f.appLE ⊤ U.1 le_top).hom.toAlgebra
  letI modU : Module R Γ(N, U.1) := Module.compHom _ (algebraMap R Γ(X, U.1))

  have hc : IsPullback (adicThickeningι f I n) (adicThickeningToBase f I n) f
      (Spec.map (CommRingCat.ofHom (algebraMap R (R ⧸ I ^ (n + 1))))) := by
    rw [Ideal.Quotient.algebraMap_eq]
    exact IsPullback.of_hasPullback _ _
  obtain ⟨β, hβ⟩ :=
    AlgebraicGeometry.Scheme.Modules.IsInvertible.exists_tensorProduct_linearEquiv_sections_pullback_preimage_of_isAffineOpen
      (R ⧸ I ^ (n + 1)) f (adicThickeningToBase f I n) (adicThickeningι f I n) hc N hN U.1 U.2

  have h1 : ∀ x : (R ⧸ I ^ (n + 1)) ⊗[R] Γ(N, U.1), ∃ m : Γ(N, U.1), x = 1 ⊗ₜ m := by
    intro x
    obtain ⟨m, hm⟩ := Submodule.Quotient.mk_surjective _ (TensorProduct.quotTensorEquivQuotSMul Γ(N, U.1) (I ^ (n + 1)) x)
    refine ⟨m, ?_⟩
    rw [← TensorProduct.quotTensorEquivQuotSMul_symm_mk (I ^ (n + 1)) m, hm, LinearEquiv.symm_apply_apply]
  refine ⟨fun y => ?_, ?_⟩
  · obtain ⟨x, rfl⟩ := β.surjective y
    obtain ⟨m, rfl⟩ := h1 x
    exact ⟨m, (hβ m).symm⟩
  · show ∀ s : Γ(N, U.1),
      (((Scheme.Modules.pullbackPushforwardAdjunction (adicThickeningι f I n)).unit.app N).app U.1) s = 0 ↔
        s ∈ I ^ (n + 1) • (⊤ : Submodule R Γ(N, U.1))
    intro s
    have key : β (1 ⊗ₜ[R] s) = 0 ↔ s ∈ I ^ (n + 1) • (⊤ : Submodule R Γ(N, U.1)) := by
      rw [LinearEquiv.map_eq_zero_iff, ← TensorProduct.quotTensorEquivQuotSMul_symm_mk (I ^ (n + 1)) s,
        LinearEquiv.map_eq_zero_iff, Submodule.Quotient.mk_eq_zero]
    refine Iff.trans ?_ (Iff.trans key Iff.rfl)
    rw [← hβ s]
    exact Iff.rfl

end S_AlgebraicGeometry_Scheme_Modules_IsInvertible_unit_app_adicThickening_surjective_and_eq_zero_iff_mem_pow_smul_top
end P2MW
export P2MW.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_unit_app_adicThickening_surjective_and_eq_zero_iff_mem_pow_smul_top (solution)
