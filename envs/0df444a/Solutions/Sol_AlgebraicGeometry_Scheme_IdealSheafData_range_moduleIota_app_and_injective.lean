-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.IdealSheafData.range_moduleIota_app_and_injective
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:03.589526+00:00
-- url     : https://prove2.me/submissions/c1ce4c02-26f4-5b4a-9dcb-b0a3f60c0f96

import Definitions.Def_AlgebraicGeometry_IdealSheafModule
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Scheme_IdealSheafData_range_moduleIota_app_and_injective

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

set_option maxHeartbeats 4000000 in
set_option synthInstance.maxHeartbeats 800000 in
open AlgebraicGeometry Opposite in

theorem solution {X : Scheme.{u}} (I : X.IdealSheafData) (U : X.affineOpens) :
    Set.range (I.moduleι.app U) = (I.ideal U : Set Γ(X, U)) ∧
      Function.Injective (I.moduleι.app U) := by

  let R := X.ringCatSheaf
  let F := I.subschemeι.unitToPushforwardUnit

  let G : SheafOfModules R ⥤ ModuleCat (R.obj.obj (op (U : X.Opens))) :=
    SheafOfModules.forget R ⋙ PresheafOfModules.evaluation R.obj (op (U : X.Opens))
  haveI : G.Additive := inferInstance
  haveI : PreservesLimit (parallelPair F 0) G := inferInstance
  let e₁ : G.obj (kernel F) ≅ kernel (G.map F) := PreservesKernel.iso G F
  let e₂ : kernel (G.map F) ≅ ModuleCat.of _ (LinearMap.ker (G.map F).hom) :=
    ModuleCat.kernelIsoKer (G.map F)
  have key : G.map (kernel.ι F) =
      e₁.hom ≫ e₂.hom ≫ ModuleCat.ofHom (LinearMap.ker (G.map F).hom).subtype := by
    rw [ModuleCat.kernelIsoKer_hom_ker_subtype, PreservesKernel.iso_hom, kernelComparison_comp_ι]

  have hfun : ⇑(I.moduleι.app U) = Subtype.val ∘ ⇑(e₁ ≪≫ e₂).toLinearEquiv := by
    funext m
    change (G.map (kernel.ι F)).hom m = _
    rw [key]
    rfl
  have hbij : Function.Bijective ⇑(e₁ ≪≫ e₂).toLinearEquiv := (e₁ ≪≫ e₂).toLinearEquiv.bijective

  have hker : ∀ s, s ∈ LinearMap.ker (G.map F).hom ↔ s ∈ (I.ideal U : Set Γ(X, U)) := fun s ↦ by
    have h1 : s ∈ LinearMap.ker (G.map F).hom ↔ (I.subschemeι.app U).hom s = 0 :=
      LinearMap.mem_ker.trans Iff.rfl
    have h2 : s ∈ (I.ideal U : Set Γ(X, U)) ↔ (I.subschemeι.app U).hom s = 0 := by
      rw [← I.ker_subschemeι_app U]
      exact RingHom.mem_ker
    exact h1.trans h2.symm
  refine ⟨?_, ?_⟩
  · rw [hfun]
    ext s
    constructor
    · rintro ⟨m, rfl⟩
      exact (hker _).mp ((e₁ ≪≫ e₂).toLinearEquiv m).2
    · intro hs
      obtain ⟨m, hm⟩ := hbij.surjective ⟨s, (hker s).mpr hs⟩
      exact ⟨m, by simp [hm]⟩
  · rw [hfun]
    exact Subtype.val_injective.comp hbij.injective

end S_AlgebraicGeometry_Scheme_IdealSheafData_range_moduleIota_app_and_injective
end P2MW
export P2MW.S_AlgebraicGeometry_Scheme_IdealSheafData_range_moduleIota_app_and_injective (solution)
