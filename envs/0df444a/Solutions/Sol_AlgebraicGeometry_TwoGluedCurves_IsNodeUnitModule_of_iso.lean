-- Prove2me | solution 1 for AlgebraicGeometry.TwoGluedCurves.IsNodeUnitModule.of_iso
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.122355+00:00
-- url     : https://prove2.me/submissions/552f65d5-b806-52af-aa0a-46fb1907d7f8

import Mathlib
import Definitions.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RelPicardPullback
import Definitions.Def_AlgebraicGeometry_TwoGluedCurvesNodeUnitModule
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_TwoGluedCurves_IsNodeUnitModule_of_iso

set_option autoImplicit false

universe u v

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.RelPicard NeronModelInfra AlgebraicGeometry.TwoGluedCurves

theorem solution
    {κ : Type u} [Field κ]
    {X C₁ C₂ : Scheme.{u}} {x : X ⟶ Spec (.of κ)}
    {c₁ : C₁ ⟶ Spec (.of κ)} {c₂ : C₂ ⟶ Spec (.of κ)}
    {i₁ : SchemeHomOver c₁ x} {i₂ : SchemeHomOver c₂ x}
    {ι : Type v} {p₁ : ι → SchemeHomOver (𝟙 (Spec (.of κ))) c₁} {p₂ : ι → SchemeHomOver (𝟙 (Spec (.of κ))) c₂}
    {T : Scheme.{u}} {h : T ⟶ Spec (.of κ)} {u : ι → Γ(T, ⊤)ˣ} {M M' : (pullback x h).Modules}
    (e : M ≅ M') (hM : IsNodeUnitModule x i₁ i₂ p₁ p₂ h u M) :
    IsNodeUnitModule x i₁ i₂ p₁ p₂ h u M' := by
  obtain ⟨j₁, j₂, hj⟩ := hM
  refine ⟨e.inv ≫ j₁, e.inv ≫ j₂, fun W => ?_⟩
  have hsurj : Function.Surjective (e.inv.app W) := fun m => ⟨e.hom.app W m, by
    change (e.hom ≫ e.inv).app W m = m
    rw [e.hom_inv_id]; rfl⟩
  have hinjE : Function.Injective (e.inv.app W) := fun m n hmn => by
    have h2 : (e.inv ≫ e.hom).app W m = (e.inv ≫ e.hom).app W n := by
      change e.hom.app W (e.inv.app W m) = e.hom.app W (e.inv.app W n)
      rw [hmn]
    rw [e.inv_hom_id] at h2
    exact h2
  have hcomp : (fun m : Γ(M', W) => ((e.inv ≫ j₁).app W m, (e.inv ≫ j₂).app W m)) =
      (fun m : Γ(M, W) => (j₁.app W m, j₂.app W m)) ∘ (e.inv.app W) := rfl
  rw [hcomp, Set.range_comp, hsurj.range_eq, Set.image_univ]
  exact ⟨(hj W).1.comp hinjE, (hj W).2⟩

end S_AlgebraicGeometry_TwoGluedCurves_IsNodeUnitModule_of_iso
end P2MW
export P2MW.S_AlgebraicGeometry_TwoGluedCurves_IsNodeUnitModule_of_iso (solution)
