-- Prove2me | solution 1 for AlgebraicGeometry.flat_image_comp_of_isDedekindDomain
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.553648+00:00
-- url     : https://prove2.me/submissions/3dbab1de-d677-514c-b0a3-6cb164bded6e

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_flat_image_comp_of_isDedekindDomain

set_option autoImplicit false

universe u

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry P2MW.S_AlgebraicGeometry_flat_image_comp_of_isDedekindDomain.AlgebraicGeometry TopologicalSpace Opposite"

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "Scheme.Hom Scheme.Hom.appLE_comp_appLE QuasiCompact Scheme.Hom.toImage_imageι_assoc Spec Scheme Flat isAffineOpen_top Scheme.Hom.appLE_map Scheme.Hom.app_eq_appLE HasRingHomProperty.of_iSup_eq_top HasRingHomProperty Scheme.ΓSpecIso"
namespace FlatImage
p2m_open "AlgebraicGeometry"

theorem isTorsionFree_sections {R : Type u} [CommRing R] {X : Scheme.{u}} (g : X ⟶ Spec (CommRingCat.of R)) [Flat g]
    (W : X.Opens) :
    letI := ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ g.appLE ⊤ W le_top).hom.toAlgebra
    Module.IsTorsionFree R Γ(X, W) := by
  letI algW := ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ g.appLE ⊤ W le_top).hom.toAlgebra

  let ι := {V : X.affineOpens // V.1 ≤ W}
  let U : ι → X.Opens := fun V => V.1.1
  have hcover : W ≤ iSup U := by
    intro x hx
    obtain ⟨_, ⟨V, hV, rfl⟩, hxV, hVW⟩ := X.isBasis_affineOpens.exists_subset_of_mem_open hx W.isOpen
    exact Opens.mem_iSup.mpr ⟨⟨⟨V, hV⟩, hVW⟩, hxV⟩

  letI algV : ∀ V : ι, Algebra R Γ(X, U V) := fun V =>
    ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ g.appLE ⊤ (U V) le_top).hom.toAlgebra
  haveI : ∀ V : ι, Module.Flat R Γ(X, U V) := fun V => by
    have h := g.flat_appLE (isAffineOpen_top _) V.1.2 (le_top : U V ≤ g ⁻¹ᵁ ⊤)
    have h' : ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ g.appLE ⊤ (U V) le_top).hom.Flat :=
      (RingHom.Flat.respectsIso.cancel_left_isIso (Scheme.ΓSpecIso (CommRingCat.of R)).inv (g.appLE ⊤ (U V) le_top)).mpr h
    exact h'

  let ρ : Γ(X, W) → ∀ V : ι, Γ(X, U V) := fun s V => X.presheaf.map (homOfLE V.2).op s
  have hρ : Function.Injective ρ := fun s t h =>
    X.sheaf.eq_of_locally_eq' U W (fun V => homOfLE V.2) hcover s t (fun V => congrFun h V)
  refine hρ.moduleIsTorsionFree ρ ?_
  intro r s
  funext V
  change X.presheaf.map (homOfLE V.2).op (((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ g.appLE ⊤ W le_top) r * s) =
    ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ g.appLE ⊤ (U V) le_top) r * X.presheaf.map (homOfLE V.2).op s
  rw [map_mul, ← CommRingCat.comp_apply, Category.assoc, Scheme.Hom.appLE_map]

end AlgebraicGeometry.FlatImage

open AlgebraicGeometry.FlatImage in

theorem solution {R : Type u} [CommRing R] [IsDomain R] [IsDedekindDomain R]
    {X J : Scheme.{u}} (σ : X ⟶ J) [QuasiCompact σ] (f : J ⟶ Spec (CommRingCat.of R)) [Flat (σ ≫ f)] :
    Flat (σ.imageι ≫ f) := by
  let U : J.affineOpens → σ.image.affineOpens := fun V => ⟨σ.imageι ⁻¹ᵁ V.1, V.2.preimage σ.imageι⟩
  refine HasRingHomProperty.of_iSup_eq_top (P := @Flat) U ?_ ?_
  · rw [← top_le_iff]
    intro b _
    obtain ⟨_, ⟨V, hV, rfl⟩, hbV, -⟩ := J.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (σ.imageι b)) isOpen_univ
    exact Opens.mem_iSup.mpr ⟨⟨V, hV⟩, hbV⟩
  · intro V

    rw [← RingHom.Flat.respectsIso.cancel_left_isIso (Scheme.ΓSpecIso (CommRingCat.of R)).inv]
    let ψ := (Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ (σ.imageι ≫ f).appLE ⊤ (U V).1 le_top
    letI algB := ψ.hom.toAlgebra
    change Module.Flat R Γ(σ.image, (U V).1)

    have hflat : Flat (σ.toImage ≫ σ.imageι ≫ f) := by rw [Scheme.Hom.toImage_imageι_assoc]; infer_instance
    let W : X.Opens := σ.toImage ⁻¹ᵁ (U V).1
    letI algW := ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ (σ.toImage ≫ σ.imageι ≫ f).appLE ⊤ W le_top).hom.toAlgebra
    haveI : Module.IsTorsionFree R Γ(X, W) := isTorsionFree_sections (σ.toImage ≫ σ.imageι ≫ f) W
    have hinj : Function.Injective (σ.toImage.app (U V).1) := σ.toImage_app_injective V
    haveI : Module.IsTorsionFree R Γ(σ.image, (U V).1) := by
      refine hinj.moduleIsTorsionFree (σ.toImage.app (U V).1) ?_
      intro r s
      change σ.toImage.app (U V).1 (ψ r * s) =
        ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ (σ.toImage ≫ σ.imageι ≫ f).appLE ⊤ W le_top) r * σ.toImage.app (U V).1 s
      rw [map_mul, ← CommRingCat.comp_apply]
      have hc : ψ ≫ σ.toImage.app (U V).1 =
          (Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ (σ.toImage ≫ σ.imageι ≫ f).appLE ⊤ W le_top := by
        change ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ (σ.imageι ≫ f).appLE ⊤ (U V).1 le_top) ≫ σ.toImage.app (U V).1 = _
        rw [Category.assoc, Scheme.Hom.app_eq_appLE, Scheme.Hom.appLE_comp_appLE]
      rw [hc]
    infer_instance

end S_AlgebraicGeometry_flat_image_comp_of_isDedekindDomain
end P2MW
export P2MW.S_AlgebraicGeometry_flat_image_comp_of_isDedekindDomain (solution)
