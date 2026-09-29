-- Prove2me | solution 1 for AlgebraicGeometry.exists_iso_hom_comp_eq_comp_hom_of_comp_hom_eq_of_isClosedImmersion_of_forall_mem_range_or
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.122355+00:00
-- url     : https://prove2.me/submissions/7c566c97-c752-5772-af90-b69a6b722705

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_exists_iso_hom_comp_eq_comp_hom_of_comp_hom_eq_of_isClosedImmersion_of_forall_mem_range_or

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry

universe u

namespace C2StabAux

theorem ker_eq_vanishingIdeal {X Y : Scheme.{u}} [IsReduced X] (f : X ⟶ Y) :
    f.ker = Scheme.IdealSheafData.vanishingIdeal (TopologicalSpace.Closeds.closure (Set.range f.base)) := by
  rw [← Scheme.IdealSheafData.map_bot, ← Scheme.nilradical_eq_bot (X := X),
    ← Scheme.IdealSheafData.vanishingIdeal_top, Scheme.IdealSheafData.map_vanishingIdeal]
  congr 1
  ext1
  simp [Set.image_univ]

theorem image_eq_of_forall_mem_or {α : Type u} [TopologicalSpace α] (e : α ≃ₜ α) (Z₁ Z₂ : Set α)
    (hZ₁ : IsClosed Z₁) (hZ₂ : IsClosed Z₂) (hirr : IsPreirreducible Z₂)
    (hcover : ∀ z, z ∈ Z₁ ∨ z ∈ Z₂) (hfix : ∀ z ∈ Z₁, e z = z) : e '' Z₂ = Z₂ := by
  have key : ∀ (g : α ≃ₜ α), (∀ z ∈ Z₁, g z = z) → g '' Z₂ ⊆ Z₂ ∨ (∀ z ∈ Z₂, g z = z) := by
    intro g hg
    have hirr' : IsPreirreducible (g '' Z₂) := hirr.image g g.continuous.continuousOn
    rcases (isPreirreducible_iff_isClosed_union_isClosed.mp hirr') Z₁ Z₂ hZ₁ hZ₂
        (by rintro _ ⟨z, hz, rfl⟩; exact hcover _) with h | h
    · right
      intro z hz
      have h1 : g z ∈ Z₁ := h ⟨z, hz, rfl⟩
      have h2 : g (g z) = g z := hg _ h1
      exact g.injective h2
    · left; exact h
  rcases key e hfix with h | h
  · refine subset_antisymm h ?_
    have hfix' : ∀ z ∈ Z₁, e.symm z = z := fun z hz => by
      rw [Homeomorph.symm_apply_eq]; exact (hfix z hz).symm
    rcases key e.symm hfix' with h' | h'
    · intro z hz
      exact ⟨e.symm z, h' ⟨z, hz, rfl⟩, e.apply_symm_apply z⟩
    · intro z hz
      refine ⟨z, hz, ?_⟩
      have := h' z hz
      rw [Homeomorph.symm_apply_eq] at this
      exact this.symm
  · ext y
    constructor
    · rintro ⟨z, hz, rfl⟩; rw [h z hz]; exact hz
    · intro hy; exact ⟨y, hy, h y hy⟩

end C2StabAux

theorem solution
    {X C₁ C₂ S : Scheme.{u}} (x : X ⟶ S) (c₂ : C₂ ⟶ S)
    (i₁ : C₁ ⟶ X) (i₂ : C₂ ⟶ X) (hi₂ : i₂ ≫ x = c₂)
    [IsClosedImmersion i₁] [IsClosedImmersion i₂] [IsIntegral C₂]
    (hcover : ∀ z : X, z ∈ Set.range i₁.base ∨ z ∈ Set.range i₂.base)
    (w : X ≅ X) (hw : w.hom ≫ x = x) (hfix : i₁ ≫ w.hom = i₁) :
    ∃ α₂ : C₂ ≅ C₂, α₂.hom ≫ c₂ = c₂ ∧ α₂.hom ≫ i₂ = i₂ ≫ w.hom  := by
  classical

  let e : ↥X ≃ₜ ↥X := TopCat.homeoOfIso (Scheme.forgetToTop.mapIso w)
  have he : ∀ z, e z = w.hom.base z := fun z => rfl
  have hfix' : ∀ z ∈ Set.range i₁.base, e z = z := by
    rintro _ ⟨c, rfl⟩
    have h := Scheme.Hom.comp_apply i₁ w.hom c
    rw [hfix] at h
    exact h.symm
  have hZ₁ : IsClosed (Set.range i₁.base) := i₁.isClosedEmbedding.isClosed_range
  have hZ₂ : IsClosed (Set.range i₂.base) := i₂.isClosedEmbedding.isClosed_range
  have hirr : IsPreirreducible (Set.range i₂.base) := by
    rw [← Set.image_univ]
    exact (IrreducibleSpace.isIrreducible_univ (X := ↥C₂)).isPreirreducible.image _ i₂.base.hom.continuous.continuousOn
  have himg : w.hom.base '' Set.range i₂.base = Set.range i₂.base :=
    C2StabAux.image_eq_of_forall_mem_or e _ _ hZ₁ hZ₂ hirr hcover hfix'
  have hrange : Set.range (i₂ ≫ w.hom).base = Set.range i₂.base := by
    have hc : ⇑(i₂ ≫ w.hom).base = w.hom.base ∘ i₂.base := funext fun c => Scheme.Hom.comp_apply i₂ w.hom c
    rw [hc, Set.range_comp, himg]

  have hker : i₂.ker = (i₂ ≫ w.hom).ker := by
    rw [C2StabAux.ker_eq_vanishingIdeal, C2StabAux.ker_eq_vanishingIdeal, hrange]
  haveI : IsClosedImmersion (i₂ ≫ w.hom) := inferInstance
  haveI := IsClosedImmersion.isIso_lift i₂ (i₂ ≫ w.hom) hker
  refine ⟨asIso (IsClosedImmersion.lift i₂ (i₂ ≫ w.hom) hker.le), ?_, ?_⟩
  · rw [asIso_hom, ← hi₂, ← Category.assoc, IsClosedImmersion.lift_fac, Category.assoc, hw]
  · rw [asIso_hom, IsClosedImmersion.lift_fac]

end S_AlgebraicGeometry_exists_iso_hom_comp_eq_comp_hom_of_comp_hom_eq_of_isClosedImmersion_of_forall_mem_range_or
end P2MW
export P2MW.S_AlgebraicGeometry_exists_iso_hom_comp_eq_comp_hom_of_comp_hom_eq_of_isClosedImmersion_of_forall_mem_range_or (solution)
