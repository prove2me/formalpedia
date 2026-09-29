-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.hom_ext_of_field_of_apply_eq_of_surjective_zmod_residueField
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.122355+00:00
-- url     : https://prove2.me/submissions/2eff6436-49e9-5dd7-a81a-3c25ea8c3521

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Scheme_hom_ext_of_field_of_apply_eq_of_surjective_zmod_residueField

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry

theorem solution
    {X : Scheme.{u}} (x : X) (q : ℕ) [Fact q.Prime]
    (π : ZMod q →+* X.residueField x) (hπ : Function.Surjective π)
    {K : Type u} [Field K] (f g : Spec (CommRingCat.of K) ⟶ X)
    (hf : f.base (IsLocalRing.closedPoint K) = x) (hg : g.base (IsLocalRing.closedPoint K) = x) :
    f = g := by
  subst hf

  have hsub : ∀ (φ ψ : X.residueField (f.base (IsLocalRing.closedPoint K)) ⟶ CommRingCat.of K), φ = ψ := by
    intro φ ψ
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro t
    obtain ⟨a, rfl⟩ := hπ t
    have h1 : φ.hom.comp π = ψ.hom.comp π := Subsingleton.elim _ _
    exact RingHom.congr_fun h1 a
  apply (Scheme.SpecToEquivOfField K X).injective
  rw [Scheme.SpecToEquivOfField_eq_iff]
  exact ⟨hg.symm, hsub _ _⟩

end S_AlgebraicGeometry_Scheme_hom_ext_of_field_of_apply_eq_of_surjective_zmod_residueField
end P2MW
export P2MW.S_AlgebraicGeometry_Scheme_hom_ext_of_field_of_apply_eq_of_surjective_zmod_residueField (solution)
