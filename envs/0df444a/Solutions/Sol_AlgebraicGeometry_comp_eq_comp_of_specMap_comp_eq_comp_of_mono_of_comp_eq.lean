-- Prove2me | solution 1 for AlgebraicGeometry.comp_eq_comp_of_specMap_comp_eq_comp_of_mono_of_comp_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.122355+00:00
-- url     : https://prove2.me/submissions/189d09ff-f79e-52d0-89d7-7e4153091b8b

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_comp_eq_comp_of_specMap_comp_eq_comp_of_mono_of_comp_eq

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry

theorem solution
    {A Q : Type u} [CommRing A] [CommRing Q] (π : A →+* Q)
    {Y K : Scheme.{u}} (ι : Spec (CommRingCat.of A) ⟶ Y) [Mono ι] (k₁ : K ⟶ Y)

    (pr : Spec (CommRingCat.of Q) ⟶ K)
    (hpr : Spec.map (CommRingCat.ofHom π) ≫ ι = pr ≫ k₁)

    (E₁ E₂ : Y ⟶ Y) (f₁ f₂ : A →+* A)
    (hf₁ : Spec.map (CommRingCat.ofHom f₁) ≫ ι = ι ≫ E₁)
    (hf₂ : Spec.map (CommRingCat.ofHom f₂) ≫ ι = ι ≫ E₂)

    (hK : k₁ ≫ E₁ = k₁ ≫ E₂) :
    π.comp f₁ = π.comp f₂ := by
  have hspec : Spec.map (CommRingCat.ofHom (π.comp f₁)) = Spec.map (CommRingCat.ofHom (π.comp f₂)) := by
    rw [CommRingCat.ofHom_comp, CommRingCat.ofHom_comp, Spec.map_comp, Spec.map_comp]
    apply (cancel_mono ι).mp
    rw [Category.assoc, Category.assoc, hf₁, hf₂, ← Category.assoc, ← Category.assoc, hpr, Category.assoc, Category.assoc, hK]
  have hinj := Spec.map_injective hspec
  have := congrArg CommRingCat.Hom.hom hinj
  simpa only [CommRingCat.hom_ofHom] using this

end S_AlgebraicGeometry_comp_eq_comp_of_specMap_comp_eq_comp_of_mono_of_comp_eq
end P2MW
export P2MW.S_AlgebraicGeometry_comp_eq_comp_of_specMap_comp_eq_comp_of_mono_of_comp_eq (solution)
